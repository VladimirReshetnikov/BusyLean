#!/usr/bin/env python3
"""Build the Lean package from fresh objects and write reproducible evidence.

Typical use from the extracted package:
    python3 verification/verify.py --lean /path/to/lean

Only the standard Python library is required. LEAN may name a compiler or an
executable wrapper; otherwise --lean or a lean executable on PATH is used.
The caller's environment is inherited, including any local compatibility
settings. No compatibility shim is required by this script or by the entry.
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
import subprocess
import sys
import tempfile
import time


DEFINITION_MODULES = {"Baseline", "Oracle", "Trees", "Hierarchy"}
REQUIRED_MODULES = DEFINITION_MODULES | {
    "Comparison", "Checks", "Diagonal", "TreeMargin", "NumericTreeGrowth"
}
REQUIRED_DECLARATIONS = {
    "Biggest.contender_5",
    "Biggest.contender_6",
    "Biggest.contender_5_lt_contender_6",
    "Biggest.contender_6_fivefold_margin",
    "Biggest.no_fixed_program_defines_reflect",
    "Biggest.no_program_eventually_defines_reflect",
    "Biggest.numeric_finalStage_growth",
}
EXPECTED_CHECKS = {
    "type_counts": [0, 1, 2, 5, 26],
    "term_counts": [0, 2, 10, 146, 24976],
    "baseline_values": [0, 0, 1, 2, 3],
    "expression_counts": [0, 4, 28, 914],
    "raw_samples": [0, 0, 0, 1, 0, 1, 5, 7, 8],
    "quote_samples": [0, 0, 0, 1, 0, 1, 5, 7, 8],
    "oracle_samples": [7, 73, 3, 0],
    "reflect_samples": [4, 16, 64],
    "hierarchy_successor_samples": [4, 16, 64],
}

# This is external verification code. It is generated outside the contest's
# source directory and imports the freshly built environment without loading
# environment extensions or executing any contender. Lean supplies the exact
# dependencies of each compiled constant, including inductive/recursor data.
DEPENDENCY_PROBE = r"""import Lean.Environment
import Lean.Util.FoldConsts

#eval do
  let env ← Lean.importModules #[{ module := `Hierarchy }] {}
  let mut queue : List Lean.Name := [`Biggest.contender_6]
  let mut visited : Lean.NameSet := {}
  let mut count : Nat := 0
  let mut projectNames : Array String := #[]
  while !queue.isEmpty do
    let name := queue.head!
    queue := queue.tail!
    if visited.contains name then
      continue
    visited := visited.insert name
    count := count + 1
    if name.getRoot == `Biggest then
      projectNames := projectNames.push name.toString
    let some info := env.find? name
      | throw (IO.userError s!"Unknown compiled constant {name}")
    for dependency in info.getUsedConstantsAsSet do
      queue := dependency :: queue
  if visited.contains `Biggest.contender_5 then
    throw (IO.userError "Submitted definition depends on contender_5")
  if visited.contains `Biggest.baseline then
    throw (IO.userError "Submitted definition depends on baseline")
  IO.println s!"DEPENDENCY visited_count = {count}"
  IO.println s!"DEPENDENCY contender_5_reachable = {visited.contains `Biggest.contender_5}"
  IO.println s!"DEPENDENCY baseline_reachable = {visited.contains `Biggest.baseline}"
  for name in projectNames do
    IO.println s!"DEPENDENCY project_constant = {name}"
"""


class VerificationFailure(Exception):
    """A check failed; retain its evidence and exit unsuccessfully."""


def sha256(path: Path) -> str:
    with path.open("rb") as stream:
        digest = hashlib.sha256()
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def code_only(source: str) -> str:
    """Erase nested Lean comments and strings, preserving line positions."""
    out = list(source)
    i = 0
    depth = 0
    string = False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                out[i : i + 2] = "  "
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                out[i : i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        elif string:
            if source[i] == "\\" and i + 1 < len(source):
                out[i] = " "
                if source[i + 1] != "\n":
                    out[i + 1] = " "
                i += 2
            else:
                if source[i] == '"':
                    string = False
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        elif source.startswith("--", i):
            while i < len(source) and source[i] != "\n":
                out[i] = " "
                i += 1
        elif source.startswith("/-", i):
            out[i : i + 2] = "  "
            depth = 1
            i += 2
        elif source[i] == '"':
            out[i] = " "
            string = True
            i += 1
        else:
            i += 1
    if depth or string:
        raise VerificationFailure("Unclosed source comment or string.")
    return "".join(out)


def imports_from(code: str) -> list[str]:
    imports = []
    for line in code.splitlines():
        match = re.match(r"^\s*(?:public\s+)?import\s+(.+)$", line)
        if match:
            imports.extend(match.group(1).split())
    return imports


def public_declarations(code: str) -> list[str]:
    """Find the package's ordinary public declarations for #print axioms.

    This is a source inventory, not a replacement for the kernel audit. The
    indispensable contest and growth declarations are independently required below.
    """
    scope: list[tuple[str, str]] = []
    names = []
    declaration = re.compile(
        r"^\s*(?:(?:noncomputable|protected)\s+)?"
        r"(?:def|abbrev|theorem|inductive)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
    )
    for line in code.splitlines():
        match = re.match(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)", line)
        if match:
            scope.append(("namespace", match.group(1)))
            continue
        if re.match(r"^\s*section(?:\s|$)", line):
            scope.append(("section", ""))
            continue
        if re.match(r"^\s*end(?:\s|$)", line):
            if scope:
                scope.pop()
            continue
        match = declaration.match(line)
        if match:
            prefix = ".".join(name for kind, name in scope if kind == "namespace")
            names.append(".".join(filter(None, [prefix, match.group(1)])))
    return names


def module_order(dependencies: dict[str, list[str]]) -> list[str]:
    ordered = []
    visiting = set()
    done = set()

    def visit(module: str) -> None:
        if module in done:
            return
        if module in visiting:
            raise VerificationFailure(f"Cyclic module dependency at {module}.")
        visiting.add(module)
        for dependency in sorted(dependencies[module]):
            if dependency in dependencies:
                visit(dependency)
        visiting.remove(module)
        done.add(module)
        ordered.append(module)

    for module in sorted(dependencies):
        visit(module)
    return ordered


def normalize_output(output: str | bytes | None) -> str:
    if output is None:
        return ""
    return output.decode("utf-8", errors="replace") if isinstance(output, bytes) else output


def run_lean(
    compiler: str,
    arguments: list[str],
    source_dir: Path,
    env: dict[str, str],
    timeout: float,
    label: str,
) -> dict:
    if timeout <= 0:
        raise VerificationFailure(f"Time budget exhausted before {label}.")
    started = time.perf_counter()
    timed_out = False
    try:
        process = subprocess.run(
            [compiler, *arguments],
            cwd=source_dir,
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
        returncode = process.returncode
        stdout = process.stdout
        stderr = process.stderr
    except subprocess.TimeoutExpired as exc:
        timed_out = True
        returncode = None
        stdout = normalize_output(exc.stdout)
        stderr = normalize_output(exc.stderr)
    return {
        "label": label,
        "elapsed_seconds": time.perf_counter() - started,
        "returncode": returncode,
        "timed_out": timed_out,
        "stdout": stdout,
        "stderr": stderr,
    }


def require_clean(result: dict) -> None:
    label = result["label"]
    if result["timed_out"]:
        raise VerificationFailure(f"{label} exceeded its remaining time budget.")
    if result["returncode"] != 0:
        raise VerificationFailure(f"{label} returned exit code {result['returncode']}.")
    output = result["stdout"] + "\n" + result["stderr"]
    if re.search(r"\bsorry(?:Ax)?\b", output):
        raise VerificationFailure(f"{label} reported an incomplete proof or sorry axiom.")
    if re.search(r"\bdepends on axioms\b", output):
        raise VerificationFailure(f"{label} reported an axiom dependency.")


def verify(args: argparse.Namespace, report: dict) -> None:
    source_dir = args.source_dir.resolve()
    if not source_dir.is_dir():
        raise VerificationFailure(f"Lean source directory does not exist: {source_dir}")
    compiler = shutil.which(args.lean) if args.lean else None
    if compiler is None:
        raise VerificationFailure(
            "Lean was not found. Use --lean /path/to/lean, set LEAN, or install the pinned toolchain."
        )
    compiler = str(Path(compiler).resolve())
    report["compiler"] = {"path": compiler, "sha256": sha256(Path(compiler))}
    report["source_directory"] = str(source_dir)
    env = os.environ.copy()
    version = run_lean(compiler, ["--version"], source_dir, env, 10, "compiler_version")
    report["compiler"]["version_check"] = version
    require_clean(version)
    if not re.search(r"\bversion " + re.escape(args.expected_version) + r"\b", version["stdout"]):
        raise VerificationFailure(
            f"Expected Lean {args.expected_version}; received {version['stdout'].strip()!r}."
        )

    modules = {
        ".".join(path.relative_to(source_dir).with_suffix("").parts): path
        for path in sorted(source_dir.rglob("*.lean"))
    }
    missing = REQUIRED_MODULES - modules.keys()
    if missing:
        raise VerificationFailure(f"Missing required Lean modules: {', '.join(sorted(missing))}")
    declarations = set()
    dependencies = {}
    report["sources"] = []
    for name, path in modules.items():
        code = code_only(path.read_text(encoding="utf-8"))
        forbidden = re.search(
            r"\b(?:sorry|admit|axiom|unsafe|partial|native_decide|noncomputable)\b", code
        )
        if forbidden:
            line = code.count("\n", 0, forbidden.start()) + 1
            raise VerificationFailure(
                f"Forbidden source construct {forbidden.group()!r} in {name}:{line}."
            )
        dependencies[name] = imports_from(code)
        declarations.update(public_declarations(code))
        report["sources"].append(
            {"module": name, "file": str(path.relative_to(source_dir)), "sha256": sha256(path)}
        )
    missing_declarations = REQUIRED_DECLARATIONS - declarations
    if missing_declarations:
        raise VerificationFailure(
            "Missing required declarations: " + ", ".join(sorted(missing_declarations))
        )
    order = module_order(dependencies)
    for module in DEFINITION_MODULES:
        for dependency in dependencies[module]:
            if dependency in modules and dependency not in DEFINITION_MODULES:
                raise VerificationFailure(
                    f"Definition module {module} imports proof module {dependency}."
                )
    stages = [
        ("definitions", [name for name in order if name in DEFINITION_MODULES], args.definition_budget),
        ("proofs_and_checks", [name for name in order if name not in DEFINITION_MODULES], args.proof_budget),
    ]
    report["module_results"] = []
    report["stage_timings"] = {}
    report["axiom_audit"] = {"requested_declarations": sorted(declarations)}

    with tempfile.TemporaryDirectory(prefix="lean_big_number_verify_") as temporary:
        build = Path(temporary)
        objects = build / "objects"
        objects.mkdir()
        # Only these newly produced project objects are eligible for imports.
        # Lean appends the original pinned standard library search path itself.
        env["LEAN_PATH"] = str(objects)
        for stage, names, budget in stages:
            total = 0.0
            for name in names:
                source = modules[name]
                relative = source.relative_to(source_dir)
                output = (objects / relative).with_suffix(".olean")
                output.parent.mkdir(parents=True, exist_ok=True)
                result = run_lean(
                    compiler,
                    ["-o", str(output), str(relative)],
                    source_dir,
                    env,
                    budget - total,
                    name,
                )
                result["stage"] = stage
                total += result["elapsed_seconds"]
                report["module_results"].append(result)
                report["stage_timings"][stage] = {
                    "elapsed_seconds": total,
                    "budget_seconds": budget,
                    "within_budget": total < budget,
                }
                print(f"{name}: {result['elapsed_seconds']:.3f} s", flush=True)
                require_clean(result)
                if total >= budget:
                    raise VerificationFailure(f"The {stage} total exceeded {budget} seconds.")
                if not output.is_file():
                    raise VerificationFailure(f"{name} did not produce its fresh object file.")

            if stage == "proofs_and_checks":
                audit = build / "GeneratedAxiomAudit.lean"
                audit.write_text(
                    "\n".join(f"import {name}" for name in order)
                    + "\n\n"
                    + "\n".join(f"#print axioms {name}" for name in sorted(declarations))
                    + "\n",
                    encoding="utf-8",
                )
                result = run_lean(
                    compiler, [str(audit)], source_dir, env,
                    budget - total, "GeneratedAxiomAudit",
                )
                result["stage"] = stage
                total += result["elapsed_seconds"]
                report["module_results"].append(result)
                report["stage_timings"][stage] = {
                    "elapsed_seconds": total,
                    "budget_seconds": budget,
                    "within_budget": total < budget,
                }
                require_clean(result)
                if total >= budget:
                    raise VerificationFailure(f"The {stage} total exceeded {budget} seconds.")
                audited = set(re.findall(
                    r"^'([^']+)' does not depend on any axioms\s*$",
                    result["stdout"], re.MULTILINE,
                ))
                report["axiom_audit"]["confirmed_without_axioms"] = sorted(audited)
                report["axiom_audit"]["count"] = len(audited)
                absent = declarations - audited
                if absent:
                    raise VerificationFailure(
                        "No complete axiom-audit output for: " + ", ".join(sorted(absent))
                    )

                dependency_probe = build / "GeneratedDependencyAudit.lean"
                dependency_probe.write_text(DEPENDENCY_PROBE, encoding="utf-8")
                result = run_lean(
                    compiler, [str(dependency_probe)], source_dir, env,
                    budget - total, "GeneratedDependencyAudit",
                )
                result["stage"] = stage
                total += result["elapsed_seconds"]
                report["module_results"].append(result)
                report["stage_timings"][stage] = {
                    "elapsed_seconds": total,
                    "budget_seconds": budget,
                    "within_budget": total < budget,
                }
                require_clean(result)
                if total >= budget:
                    raise VerificationFailure(f"The {stage} total exceeded {budget} seconds.")
                dependencies_found = {}
                project_constants = []
                for line in result["stdout"].splitlines():
                    match = re.match(r"^DEPENDENCY ([a-z_0-9]+) = (.+)$", line)
                    if not match:
                        continue
                    name, value = match.groups()
                    if name == "project_constant":
                        project_constants.append(value)
                    else:
                        if name in dependencies_found:
                            raise VerificationFailure(f"Duplicate dependency-audit record: {name}")
                        dependencies_found[name] = json.loads(value)
                if (
                    dependencies_found.get("contender_5_reachable") is not False
                    or dependencies_found.get("baseline_reachable") is not False
                    or not isinstance(dependencies_found.get("visited_count"), int)
                    or dependencies_found["visited_count"] <= 0
                    or "Biggest.contender_6" not in project_constants
                    or len(project_constants) != len(set(project_constants))
                ):
                    raise VerificationFailure("Missing or invalid compiled dependency-audit evidence.")
                report["compiled_dependency_audit"] = {
                    "root": "Biggest.contender_6",
                    "method": "Transitive Lean.ConstantInfo.getUsedConstantsAsSet traversal",
                    "includes_types_values_constructors_and_recursors": True,
                    "project_constants": sorted(project_constants),
                    **dependencies_found,
                    "passed": True,
                }

    checks = {}
    for result in report["module_results"]:
        for line in result["stdout"].splitlines():
            match = re.match(r"^CHECK ([a-z_]+) = (.+)$", line)
            if match:
                name, encoded = match.groups()
                if name in checks:
                    raise VerificationFailure(f"Duplicate executable check record: {name}")
                checks[name] = json.loads(encoded)
    report["small_checks"] = {"expected": EXPECTED_CHECKS, "observed": checks}
    if checks != EXPECTED_CHECKS:
        wrong = [name for name, value in EXPECTED_CHECKS.items() if checks.get(name) != value]
        extra = sorted(checks.keys() - EXPECTED_CHECKS.keys())
        raise VerificationFailure(f"Executable check mismatch: {wrong}; unexpected records: {extra}.")
    report["small_checks"]["passed"] = True
    for source in report["sources"]:
        if sha256(source_dir / source["file"]) != source["sha256"]:
            raise VerificationFailure(f"Source changed during verification: {source['file']}")
    report["sources_unchanged_during_verification"] = True
    report["status"] = "passed"


def main() -> int:
    package = Path(__file__).resolve().parents[1]
    default_sources = package / "lean"
    if not default_sources.is_dir() and (package / "work").is_dir():
        default_sources = package / "work"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=os.environ.get("LEAN", "lean"))
    parser.add_argument("--source-dir", type=Path, default=default_sources)
    parser.add_argument("--output", type=Path, default=package / "verification" / "results.json")
    parser.add_argument("--expected-version", default="4.19.0")
    parser.add_argument("--definition-budget", type=float, default=15.0)
    parser.add_argument("--proof-budget", type=float, default=60.0)
    args = parser.parse_args()
    report = {
        "schema_version": 1,
        "status": "failed",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "platform": platform.platform(),
        "python_version": platform.python_version(),
        "configuration": {
            "expected_lean_version": args.expected_version,
            "definition_budget_seconds": args.definition_budget,
            "proof_budget_seconds": args.proof_budget,
            "fresh_project_objects": True,
            "maximum_executed_baseline_depth": 4,
            "contender_values_evaluated": False,
            "definition_modules": sorted(DEFINITION_MODULES),
        },
    }
    try:
        verify(args, report)
    except (VerificationFailure, OSError, ValueError, subprocess.SubprocessError) as exc:
        report["failure"] = str(exc)
        print(f"Verification failed: {exc}", file=sys.stderr)
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(f"Evidence: {args.output.resolve()}", flush=True)
    if report["status"] == "passed":
        print(
            f"Verification passed; {report['axiom_audit']['count']} declarations are axiom-free.",
            flush=True,
        )
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
