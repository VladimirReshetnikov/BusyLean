#!/usr/bin/env python3
"""Rebuild all custom Lean dependencies, audit axioms, and record honest timings.

The definition phase includes every local import of --definition. The proof
phase then builds every remaining local import of --proof. Both start from a
fresh directory containing .lean sources only. Only the official toolchain's
precompiled standard library is reused. No candidate value is evaluated.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time


MODULE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")


def measure(command: list[str], cwd: Path, env: dict[str, str], timeout: float) -> dict:
    """Capture each process's own wall time, CPU time, maximum RSS, and output."""
    with tempfile.TemporaryFile() as output:
        started = time.perf_counter()
        proc = subprocess.Popen(command, cwd=cwd, env=env, stdout=output,
                                stderr=subprocess.STDOUT, start_new_session=True)
        usage = None
        timed_out = False
        if hasattr(os, "wait4"):
            while True:
                pid, status, info = os.wait4(proc.pid, os.WNOHANG)
                if pid:
                    proc.returncode = os.waitstatus_to_exitcode(status)
                    usage = info
                    break
                if time.perf_counter() - started > timeout:
                    timed_out = True
                    os.killpg(proc.pid, signal.SIGKILL)
                    _, status, usage = os.wait4(proc.pid, 0)
                    proc.returncode = os.waitstatus_to_exitcode(status)
                    break
                time.sleep(0.01)
        else:
            try:
                proc.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                proc.kill()
                proc.wait()
        elapsed = time.perf_counter() - started
        output.seek(0)
        text = output.read().decode("utf-8", errors="replace")
    # Linux reports KiB; Darwin reports bytes. Other platforms report no RSS.
    rss = usage.ru_maxrss if usage else None
    if rss is not None and sys.platform == "darwin":
        rss /= 1024
    return {
        "command": command,
        "returncode": proc.returncode,
        "timed_out": timed_out,
        "wall_seconds": elapsed,
        "user_seconds": usage.ru_utime if usage else None,
        "system_seconds": usage.ru_stime if usage else None,
        "max_rss_kib": rss,
        "output": text,
    }


def source_path(root: Path, module: str) -> Path:
    if not MODULE.fullmatch(module):
        raise ValueError(f"Invalid Lean module name: {module}")
    return root.joinpath(*module.split(".")).with_suffix(".lean")


def local_order(root: Path, targets: list[str]) -> list[str]:
    result: list[str] = []
    state: dict[str, int] = {}

    def visit(module: str) -> None:
        status = state.get(module, 0)
        if status == 2:
            return
        if status == 1:
            raise ValueError(f"Cyclic local import at {module}")
        path = source_path(root, module)
        if not path.is_file():
            raise FileNotFoundError(path)
        state[module] = 1
        text = path.read_text(encoding="utf-8")
        # Project imports are ordinary top-level one-line import commands.
        for match in re.finditer(r"(?m)^\s*import\s+([^\n]+)$", text):
            for dep in match.group(1).split("--", 1)[0].split():
                if MODULE.fullmatch(dep) and source_path(root, dep).is_file():
                    visit(dep)
        state[module] = 2
        result.append(module)

    for target in targets:
        visit(target)
    return result


def host_info() -> dict:
    info = {"platform": platform.platform(), "machine": platform.machine(),
            "python": platform.python_version(), "cpu_count": os.cpu_count()}
    try:
        for line in Path("/proc/cpuinfo").read_text().splitlines():
            if line.startswith("model name"):
                info["cpu_model"] = line.split(":", 1)[1].strip()
                break
    except OSError:
        pass
    try:
        info["os_release"] = Path("/etc/os-release").read_text()
    except OSError:
        pass
    return info


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=os.environ.get("LEAN_BIN", "lean"))
    parser.add_argument("--root", type=Path,
                        default=Path(__file__).resolve().parents[1])
    parser.add_argument("--definition", action="append")
    parser.add_argument("--proof", action="append")
    parser.add_argument("--audit", action="append", default=[])
    parser.add_argument("--audit-file", type=Path)
    parser.add_argument("--dependency-root", default="BigNumber.contender_6",
                        help="Traverse this declaration's actual Lean constant dependencies")
    parser.add_argument("--forbid-dependency", action="append", default=[],
                        help="Additional forbidden dependency (the previous contender is always forbidden)")
    parser.add_argument("--no-dependency-audit", action="store_true",
                        help="For partial component validation only; omit the final-entry dependency audit")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--threads", type=int, default=1)
    parser.add_argument("--definition-budget", type=float, default=15.0)
    parser.add_argument("--proof-budget", type=float, default=60.0)
    parser.add_argument("--recheck", action="store_true",
                        help="Also directly recheck safe custom definition/theorem bodies through the C++ kernel")
    parser.add_argument("--recheck-timeout", type=float, default=120.0)
    parser.add_argument("--check-only", action="store_true",
                        help="Typecheck and emit .olean only; no C or executable is built (default)")
    args = parser.parse_args()
    root = args.root.resolve()
    lean = shutil.which(args.lean)
    if not lean:
        parser.error(f"Lean executable not found: {args.lean}")
    lean = str(Path(lean).absolute())
    definitions = args.definition or ["BigNumber.CandidateDefs"]
    proofs = args.proof or ["BigNumber.Baseline", "BigNumber.Amplifier",
                             "BigNumber.Candidate"]
    audit_file = args.audit_file or root / "scripts" / "audit_names.txt"
    names = list(args.audit)
    if audit_file.is_file():
        names += [line.split("#", 1)[0].strip()
                  for line in audit_file.read_text().splitlines()
                  if line.split("#", 1)[0].strip()]
    if not names:
        parser.error("Specify --audit names or supply scripts/audit_names.txt")
    for name in names:
        if not MODULE.fullmatch(name):
            parser.error(f"Invalid declaration name: {name}")
    forbidden = ["BigNumber.Baseline.contender_5"] + args.forbid_dependency
    if not args.no_dependency_audit:
        for name in [args.dependency_root] + forbidden:
            if not MODULE.fullmatch(name):
                parser.error(f"Invalid dependency declaration name: {name}")
    definition_order = local_order(root, definitions)
    all_order = local_order(root, definitions + proofs)
    proof_order = [name for name in all_order if name not in definition_order]
    output_path = (args.output or root / "validation" / "validation.json").resolve()
    output_path.parent.mkdir(parents=True, exist_ok=True)
    log_dir = output_path.parent / (output_path.stem + "_logs")
    log_dir.mkdir(parents=True, exist_ok=True)
    report = {"timestamp_utc": datetime.now(timezone.utc).isoformat(),
              "host": host_info(), "definition_order": definition_order,
              "proof_order": proof_order, "audit_declarations": names,
              "dependency_root": None if args.no_dependency_audit else args.dependency_root,
              "forbidden_dependencies": forbidden,
              "definitions_budget_seconds": args.definition_budget,
              "proofs_budget_seconds": args.proof_budget,
              "compiler_flags": [f"-j{args.threads}"],
              "timing_policy": "Fresh custom .olean files; cumulative custom-dependency wall time; official standard-library .oleans reused; no numeric evaluation",
              "runs": [], "passed": False}
    env = dict(os.environ)
    # Do not inherit a path that could silently supply old project .oleans.
    env.pop("LEAN_PATH", None)
    report["lean_version"] = subprocess.check_output([lean, "--version"],
        env=env, text=True).strip()
    report["lean_githash"] = subprocess.check_output([lean, "--githash"],
        env=env, text=True).strip()
    report["sources_sha256"] = {
        str(source_path(root, name).relative_to(root)):
        hashlib.sha256(source_path(root, name).read_bytes()).hexdigest()
        for name in all_order}
    report["source_counts"] = {
        str(source_path(root, name).relative_to(root)): {
            "utf8_bytes": source_path(root, name).stat().st_size,
            "lines": len(source_path(root, name).read_text().splitlines())}
        for name in all_order}
    report["total_source_lines"] = sum(v["lines"] for v in report["source_counts"].values())
    report["total_source_utf8_bytes"] = sum(v["utf8_bytes"] for v in report["source_counts"].values())

    try:
        with tempfile.TemporaryDirectory(prefix="lean-big-number-") as temporary:
            stage = Path(temporary)
            for module in all_order:
                target = source_path(stage, module)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source_path(root, module), target)
            env["LEAN_PATH"] = str(stage)

            def run(module: str, phase: str, timeout: float, *, trust: bool = False) -> None:
                path = source_path(stage, module).relative_to(stage)
                command = [lean, f"-j{args.threads}"]
                if trust:
                    command.append("--trust=0")
                command += ["-o", str(path.with_suffix(".olean")), str(path)]
                result = measure(command, stage, env, timeout)
                result.update({"module": module, "phase": phase})
                (log_dir / f"{phase}-{module}.log").write_text(result["output"])
                report["runs"].append(result)
                print(f"{phase}: {module}: {result['wall_seconds']:.3f}s, "
                      f"exit {result['returncode']}", flush=True)
                if result["returncode"] or result["timed_out"]:
                    raise RuntimeError(f"{phase} failed for {module}\n{result['output']}")

            for phase, order, budget in [
                ("definitions", definition_order, args.definition_budget),
                ("proofs", proof_order, args.proof_budget),
            ]:
                start = time.perf_counter()
                for module in order:
                    remaining = budget - (time.perf_counter() - start)
                    if remaining <= 0:
                        raise RuntimeError(f"{phase} exceeded its {budget}s budget")
                    run(module, phase, remaining)
                elapsed = time.perf_counter() - start
                report[f"{phase}_wall_seconds"] = elapsed
                report[f"{phase}_within_budget"] = elapsed <= budget
                if elapsed > budget:
                    raise RuntimeError(f"{phase} exceeded its {budget}s budget")

            audit_source = "import Lean\n" + "".join(f"import {m}\n" for m in proofs)
            audit_source += "\nopen Lean Elab Command\n\nrun_cmd do\n"
            audit_source += "  let names : List Name := [" + ", ".join("``" + n for n in names) + "]\n"
            audit_source += "  for name in names do\n"
            audit_source += "    unless ((← getEnv).find? name).isSome do\n"
            audit_source += '      throwError m!"Audit declaration missing: {name}"\n'
            audit_source += "    let axioms ← collectAxioms name\n"
            audit_source += '    logInfo m!"AXIOM_AUDIT {name}: {axioms}"\n'
            audit_source += "    unless axioms.isEmpty do\n"
            audit_source += '      throwError m!"Nonempty axiom dependency list for {name}: {axioms}"\n'
            if not args.no_dependency_audit:
                # collectAxioms traverses actual Lean Expr constants in both
                # declaration types and bodies. Its visited set includes all
                # transitive dependencies, not merely axiom declarations.
                audit_source += "\nrun_cmd do\n"
                audit_source += "  let env ← getEnv\n"
                audit_source += "  let root : Name := ``" + args.dependency_root + "\n"
                audit_source += "  unless (env.find? root).isSome do\n"
                audit_source += '    throwError m!"Dependency root missing: {root}"\n'
                audit_source += "  let (_, state) := ((Lean.CollectAxioms.collect root).run env).run {}\n"
                audit_source += "  let forbidden : List Name := [" + ", ".join("``" + n for n in forbidden) + "]\n"
                audit_source += "  for name in forbidden do\n"
                audit_source += "    if state.visited.contains name then\n"
                audit_source += '      throwError m!"Forbidden transitive dependency: {root} uses {name}"\n'
                audit_source += '    logInfo m!"DEPENDENCY_AUDIT {root}: does not use {name}"\n'
            audit_source += "\n" + "".join(f"#print axioms {n}\n" for n in names)
            (stage / "AxiomAudit.lean").write_text(audit_source)
            (log_dir / "AxiomAudit.lean").write_text(audit_source)
            run("AxiomAudit", "audit", args.proof_budget)
            report["axiom_audit_passed"] = True
            report["dependency_audit_passed"] = not args.no_dependency_audit
            report["proofs_and_audit_wall_seconds"] = (
                report["proofs_wall_seconds"] + report["runs"][-1]["wall_seconds"])
            report["proofs_and_audit_within_budget"] = (
                report["proofs_and_audit_wall_seconds"] <= args.proof_budget)

            if args.recheck:
                recheck_source = "import Lean\n" + "".join(f"import {m}\n" for m in proofs)
                recheck_source += """
open Lean Elab Command

/- Re-add each safe custom body under a fresh name through the C++ kernel.
   Original declaration types and universe parameters are preserved. This
   checks actual stored bodies, not merely references to imported constants.
   Standard-library and inductive metadata remain the imported environment. -/
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if "BigNumber.".isPrefixOf (privateToUserName name).toString &&
        !info.isUnsafe && !info.isPartial then
      let alias := Name.str name "_direct_kernel_recheck"
      let decl? : Option Declaration := match info with
        | .defnInfo value => some (.defnDecl { value with name := alias })
        | .thmInfo value => some (.thmDecl { value with name := alias })
        | .opaqueInfo value => some (.opaqueDecl { value with name := alias })
        | _ => none
      if let some decl := decl? then
        match env.toKernelEnv.addDeclCore 0 decl none with
        | .ok _ =>
            count := count + 1
            logInfo m!"KERNEL_BODY_RECHECK {name}: passed"
        | .error ex =>
            throwError m!"Direct kernel body recheck failed for {name}: {ex.toMessageData (← getOptions)}"
  if count == 0 then
    throwError "No custom definition/theorem bodies were rechecked"
  logInfo m!"KERNEL_BODY_RECHECK_COUNT {count}"
"""
                (stage / "KernelRecheck.lean").write_text(recheck_source)
                (log_dir / "KernelRecheck.lean").write_text(recheck_source)
                run("KernelRecheck", "kernel_recheck", args.recheck_timeout, trust=True)
                report["kernel_recheck_passed"] = True
                recheck_count = re.search(r"KERNEL_BODY_RECHECK_COUNT (\d+)",
                                          report["runs"][-1]["output"])
                report["kernel_recheck_body_count"] = (
                    int(recheck_count.group(1)) if recheck_count else None)
                report["kernel_recheck_method"] = (
                    "Explicit Kernel.Environment.addDeclCore on renamed copies of all "
                    "safe custom definition/theorem/opaque bodies, preserving original types "
                    "and universe parameters. Imported standard-library and inductive metadata retained. "
                    "The --trust=0 flag alone is not treated as rechecking imports.")
            report["max_rss_kib"] = max(
                (r["max_rss_kib"] or 0 for r in report["runs"]), default=0)
            report["max_rss_compilation_kib"] = max(
                (r["max_rss_kib"] or 0 for r in report["runs"]
                 if r["phase"] in ("definitions", "proofs")), default=0)
            report["passed"] = report["proofs_and_audit_within_budget"]
    except Exception as exc:
        report["error"] = str(exc)
        print(str(exc), file=sys.stderr)
    finally:
        output_path.write_text(json.dumps(report, indent=2) + "\n")
        print(f"Report: {output_path}", flush=True)
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
