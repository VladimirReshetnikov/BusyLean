#!/usr/bin/env python3
"""Reproduce the independent Lean 4.34.0 verification for Contender 11.

The script downloads the pinned BusyLean snapshot, computes the import closure
of ``BusyLean.Comparison10``, concatenates that closure in topological order,
appends the exact local Contender 11 modules, and submits the resulting source
to AXLE's ``check`` endpoint.

It requires only Python's standard library and an Internet connection.  The
remote run is a strong elaborator/kernel check of the exact declarations, but
it is not a substitute for the repository's staged ``lake build``: AXLE checks
one reconstructed source unit (under its standard header) rather than the
original Lake module graph.  Run ``scripts/check_contender11.py`` after
integration to enforce BusyLean's local build-time budgets.
"""
from __future__ import annotations

import hashlib
import json
import re
import sys
import tempfile
import urllib.request
import zipfile
from collections import defaultdict, deque
from pathlib import Path
from typing import Any

SNAPSHOT = "4c4b03d0e2003c479e3bee90a21c8bea13f66c40"
ARCHIVE_URL = (
    "https://github.com/VladimirReshetnikov/BusyLean/archive/"
    f"{SNAPSHOT}.zip"
)
AXLE_URL = "https://axle.axiommath.ai/api/v1/check"
ENVIRONMENT = "lean-4.34.0"
IMPORT_RE = re.compile(r"(?m)^import\s+([A-Za-z0-9_.]+)\s*$")
REMOVE_IMPORT_RE = re.compile(r"(?m)^import\s+[^\n]*(?:\n|$)")
PERMITTED_AXIOMS = {"propext", "Quot.sound"}
AUDITED_DECLARATIONS = [
    "BusyLean.contender_11",
    "BusyLean.contender_10_lt_contender_11",
    "BusyLean.family10_lt_F11",
    "BusyLean.defined_tree_eventually_lt11",
    "BusyLean.fvalue_lt_contender_11",
]

CHECKS_AND_AUDIT = r"""
#print axioms BusyLean.contender_11
#print axioms BusyLean.contender_10_lt_contender_11
#print axioms BusyLean.family10_lt_F11
#print axioms BusyLean.defined_tree_eventually_lt11
#print axioms BusyLean.fvalue_lt_contender_11

open Lean Elab Command

/-- All constants reachable from `root` through declaration types and values. -/
def contender11ConstClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := #[root]
  while stack.size > 0 do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let body : Array Name := match ci with
      | .defnInfo v => v.value.getUsedConstants
      | .thmInfo v => v.value.getUsedConstants
      | .opaqueInfo v => v.value.getUsedConstants
      | _ => #[]
    stack := stack ++ ci.type.getUsedConstants ++ body
  return seen

/-- Fail if any listed constant lies in the closure of `root`. -/
elab "#assert_not_in_closure11 " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := contender11ConstClosure env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all {bad.size} forbidden names"

#assert_not_in_closure11 BusyLean.contender_11 :
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5
  BigNumber.contender_6 BigNumber.contender_5

#check @BusyLean.contender_10_lt_contender_11
#check @BusyLean.family10_lt_F11
#check @BusyLean.defined_tree_eventually_lt11
#check @BusyLean.fvalue_lt_contender_11
"""


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def module_name(path: Path, base: Path) -> str:
    rel = path.relative_to(base).with_suffix("")
    return ".".join(rel.parts)


def topological_closure(
    target: str, module_files: dict[str, Path], deps: dict[str, list[str]]
) -> list[str]:
    closure = {target}
    stack = [target]
    while stack:
        module = stack.pop()
        for dependency in deps.get(module, []):
            if dependency in module_files and dependency not in closure:
                closure.add(dependency)
                stack.append(dependency)

    outgoing: dict[str, list[str]] = defaultdict(list)
    indegree = {module: 0 for module in closure}
    for module in closure:
        for dependency in deps.get(module, []):
            if dependency in closure:
                outgoing[dependency].append(module)
                indegree[module] += 1

    queue = deque(sorted(module for module, degree in indegree.items() if degree == 0))
    order: list[str] = []
    while queue:
        module = queue.popleft()
        order.append(module)
        for successor in sorted(outgoing[module]):
            indegree[successor] -= 1
            if indegree[successor] == 0:
                queue.append(successor)
    if len(order) != len(closure):
        raise RuntimeError("import graph contains a cycle")
    return order


def download(url: str, destination: Path) -> None:
    request = urllib.request.Request(url, headers={"User-Agent": "BusyLean-C11/1.0"})
    with urllib.request.urlopen(request, timeout=120) as response:
        destination.write_bytes(response.read())


def build_merged_source(
    package_root: Path, workspace: Path
) -> tuple[str, list[str], dict[str, str]]:
    archive = workspace / "BusyLean.zip"
    download(ARCHIVE_URL, archive)
    with zipfile.ZipFile(archive) as zipped:
        zipped.extractall(workspace)

    candidates = [path for path in workspace.iterdir() if path.is_dir()]
    repo = next(path for path in candidates if (path / "BusyLean.lean").exists())
    dependency_root = repo / "proposals" / "P5-w-reflection" / "lean"

    module_files: dict[str, Path] = {}
    for path in (repo / "BusyLean").rglob("*.lean"):
        module_files[module_name(path, repo)] = path
    top = dependency_root / "BigNumber.lean"
    module_files[module_name(top, dependency_root)] = top
    for path in (dependency_root / "BigNumber").rglob("*.lean"):
        module_files[module_name(path, dependency_root)] = path

    dependencies: dict[str, list[str]] = {}
    for module, path in module_files.items():
        source = path.read_text(encoding="utf-8")
        dependencies[module] = [
            name for name in IMPORT_RE.findall(source) if name in module_files
        ]

    order = topological_closure("BusyLean.Comparison10", module_files, dependencies)
    pieces: list[str] = []
    for module in order:
        source = module_files[module].read_text(encoding="utf-8")
        source = REMOVE_IMPORT_RE.sub("", source)
        pieces.append(f"\n/-! ===== BEGIN {module} ===== -/\n{source}")

    local_hashes: dict[str, str] = {}
    for filename in ("Contender11.lean", "Comparison11.lean"):
        path = package_root / "BusyLean" / filename
        local_hashes[str(path.relative_to(package_root))] = sha256_file(path)
        source = REMOVE_IMPORT_RE.sub("", path.read_text(encoding="utf-8"))
        pieces.append(f"\n/-! ===== BEGIN BusyLean.{path.stem} ===== -/\n{source}")

    pieces.append(CHECKS_AND_AUDIT)
    return "\n".join(pieces), order, local_hashes


def submit(source: str) -> dict[str, Any]:
    payload = {
        "content": source,
        "environment": ENVIRONMENT,
        "ignore_imports": True,
        "theorems_only": False,
        "timeout_seconds": 300,
        "global_options": {"maxHeartbeats": 0},
    }
    data = json.dumps(payload, ensure_ascii=True).encode("ascii")
    request = urllib.request.Request(
        AXLE_URL,
        data=data,
        headers={
            "Content-Type": "application/json",
            "User-Agent": "BusyLean-C11/1.0",
        },
        method="POST",
    )
    with urllib.request.urlopen(request, timeout=360) as response:
        return json.loads(response.read().decode("utf-8"))


def parse_axiom_reports(infos: list[str]) -> dict[str, list[str]]:
    joined = "\n".join(infos)
    reports: dict[str, list[str]] = {}
    pattern = re.compile(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend)"
    )
    for name, axioms in pattern.findall(joined):
        reports[name] = [part.strip() for part in axioms.split(",") if part.strip()]
    return reports


def validate(result: dict[str, Any]) -> tuple[dict[str, list[str]], str]:
    if result.get("okay") is not True:
        raise RuntimeError("AXLE returned okay=false")
    failed = result.get("failed_declarations", [])
    if failed:
        raise RuntimeError(f"failed declarations: {failed}")

    messages = result.get("lean_messages", {})
    errors = messages.get("errors", [])
    if errors:
        raise RuntimeError("Lean errors:\n" + "\n".join(errors))
    infos = messages.get("infos", [])
    reports = parse_axiom_reports(infos)
    missing = [name for name in AUDITED_DECLARATIONS if name not in reports]
    if missing:
        raise RuntimeError(f"missing axiom reports for: {missing}")
    forbidden = {
        name: sorted(set(reports[name]) - PERMITTED_AXIOMS)
        for name in AUDITED_DECLARATIONS
        if set(reports[name]) - PERMITTED_AXIOMS
    }
    if forbidden:
        raise RuntimeError(f"forbidden axioms: {forbidden}")

    closure_line = next(
        (
            line.strip()
            for info in infos
            for line in info.splitlines()
            if "BusyLean.contender_11: closure of" in line
        ),
        "",
    )
    if "avoids all 8 forbidden names" not in closure_line:
        raise RuntimeError("dependency-closure audit report was not found")
    return reports, closure_line


def main() -> None:
    package_root = Path(__file__).resolve().parent.parent
    verification_dir = package_root / "verification"
    verification_dir.mkdir(parents=True, exist_ok=True)

    with tempfile.TemporaryDirectory(prefix="busylean-c11-") as temp:
        source, order, local_hashes = build_merged_source(
            package_root, Path(temp)
        )
        result = submit(source)

    reports, closure_line = validate(result)
    info = result.get("info", {})
    summary = {
        "proposal": "BusyLean Contender 11: self-indexed forest reflection of kind-polymorphic System F-omega",
        "busyLean_snapshot": SNAPSHOT,
        "lean_environment": ENVIRONMENT,
        "verification_method": "AXLE check over a reconstructed merged source unit",
        "dependency_module_count": len(order),
        "dependency_modules": order,
        "merged_source_characters": len(source),
        "merged_source_sha256": sha256_text(source),
        "local_source_sha256": local_hashes,
        "okay": result.get("okay"),
        "failed_declarations": result.get("failed_declarations", []),
        "axiom_reports": reports,
        "closure_audit": closure_line,
        "request_info": info,
        "caveat": (
            "This checks one reconstructed source unit under AXLE's standard "
            "header; it does not replace the staged Lake build and timing audit."
        ),
    }

    response_path = verification_dir / "AXLE_REPRODUCED_RESPONSE.json"
    response_path.write_text(
        json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    summary_path = verification_dir / "AXLE_REPRODUCED_SUMMARY.json"
    summary_path.write_text(
        json.dumps(summary, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )

    print(f"PASS: AXLE {ENVIRONMENT}, snapshot {SNAPSHOT}")
    print(f"dependency modules: {len(order)}")
    print(f"merged source SHA-256: {summary['merged_source_sha256']}")
    print(f"failed declarations: {summary['failed_declarations']}")
    print(closure_line)
    total_ms = info.get("total_request_time_ms")
    if total_ms is not None:
        print(f"total request time: {total_ms} ms")
    print(f"saved: {response_path.relative_to(package_root)}")
    print(f"saved: {summary_path.relative_to(package_root)}")


if __name__ == "__main__":
    try:
        main()
    except Exception as error:  # deliberate CLI boundary
        print(f"FAIL: {error}", file=sys.stderr)
        raise SystemExit(1) from error
