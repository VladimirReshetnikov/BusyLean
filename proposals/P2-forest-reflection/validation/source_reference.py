#!/usr/bin/env python3
"""Independent finite regression model of upstream Contender.v.

This compares every numerical evaluation, in the source enumeration order,
through depth four. It does not evaluate Contender 5 or any reflected number.
The only dependencies are Python's standard library and the pinned Lean
compiler; Original.olean must already have been compiled in ../lean.
"""

from __future__ import annotations

import argparse
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess


NAT = "N"
ZERO = ("O",)
SUCC = ("S",)


def error(tp):
    if tp == NAT:
        return 0
    return lambda _x: error(tp[1])


def casts(src, dst):
    """Both directions of the source cast_impl, including error casts."""
    if src == NAT and dst == NAT:
        return (lambda x: x), (lambda x: x)
    if isinstance(src, tuple) and isinstance(dst, tuple):
        a, b = src
        c, d = dst
        if a == c and b == d:
            ac, ca = casts(a, c)
            bd, db = casts(b, d)
            return (
                lambda f: lambda x: bd(f(ca(x))),
                lambda f: lambda x: db(f(ac(x))),
            )
    return (lambda _x: error(dst)), (lambda _x: error(src))


def nat_rec(initial):
    def with_step(step):
        def at(n):
            value = initial
            for predecessor in range(n):
                value = step(predecessor)(value)
            return value
        return at
    return with_step


def interp(env, term):
    tag, *args = term
    if tag == "V":
        index = args[0]
        return (NAT, 0) if len(env) <= index else env[len(env) - 1 - index]
    if tag == "L":
        a, b, body = args

        def function(x):
            src, value = interp(((a, x),) + env, body)
            return casts(src, b)[0](value)

        return ((a, b), function)
    if tag == "A":
        t1, t2 = args
        tp1, v1 = interp(env, t1)
        tp2, v2 = interp(env, t2)
        if tp1 == NAT:
            return NAT, 0
        a, b = tp1
        return b, v1(casts(tp2, a)[0](v2))
    if tag == "O":
        return NAT, 0
    if tag == "S":
        return (NAT, NAT), lambda n: n + 1
    if tag == "R":
        r = args[0]
        return (r, ((NAT, (r, r)), (NAT, r))), nat_rec
    raise AssertionError(f"unknown term tag {tag!r}")


def evaluate(term):
    tp, value = interp((), term)
    return value if tp == NAT else 0


@lru_cache(maxsize=None)
def types_up_to(n):
    if n == 0:
        return ()
    r = types_up_to(n - 1)
    return (NAT,) + tuple((a, b) for a in r for b in r)


@lru_cache(maxsize=None)
def terms_up_to(n):
    if n == 0:
        return ()
    m = n - 1
    ts = types_up_to(m)
    es = terms_up_to(m)
    return (
        tuple(("V", x) for x in range(m - 1, -1, -1))
        + tuple(("L", a, b, body) for a in ts for b in ts for body in es)
        + tuple(("A", f, x) for f in es for x in es)
        + (ZERO, SUCC)
        + tuple(("R", r) for r in ts)
    )


def expected_trace():
    lines = []
    counts = []
    for depth in range(5):
        ts = types_up_to(depth)
        es = terms_up_to(depth)
        values = [evaluate(term) for term in es]
        # This is the value tracked by source maxBy, including the seed zero.
        maximum = max([0] + values)
        counts.append({
            "depth": depth,
            "types": len(ts),
            "terms": len(es),
            "largest_value": maximum,
        })
        lines += [f"T {depth} {len(ts)}", f"L {depth} {len(es)}", f"M {depth} {maximum}"]
        lines += [f"V {depth} {index} {value}" for index, value in enumerate(values)]
    return lines, counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean", help="Path to the Lean 4.19.0 executable")
    parser.add_argument("--output", type=Path, help="Write the comparison report as JSON")
    parser.add_argument("--olean-path", type=Path,
                        help="Directory containing freshly checked Original.olean")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    environment = dict(os.environ)
    environment["LEAN_PATH"] = str(args.olean_path or (root / "lean")) + (
        os.pathsep + environment["LEAN_PATH"] if environment.get("LEAN_PATH") else ""
    )
    version = subprocess.run(
        [args.lean, "--version"], check=True, text=True, capture_output=True
    ).stdout.strip()
    trace = subprocess.run(
        [args.lean, "--run", str(root / "validation" / "SourceDump.lean")],
        cwd=root, env=environment, check=True, text=True, capture_output=True,
    ).stdout
    actual = trace.splitlines()
    expected, counts = expected_trace()
    if actual != expected:
        for index, (got, wanted) in enumerate(zip(actual, expected)):
            if got != wanted:
                raise AssertionError(
                    f"Trace mismatch at line {index + 1}: Lean {got!r}; Python {wanted!r}"
                )
        raise AssertionError(f"Trace length mismatch: Lean {len(actual)}; Python {len(expected)}")
    report = {
        "status": "PASS",
        "description": "Every enumerated original term value and enumeration count matches through depth 4.",
        "scope": "Finite independent regression evidence; no cross-prover equivalence theorem is claimed.",
        "lean_version": version,
        "python_version": platform.python_version(),
        "depth_results": counts,
        "term_values_compared": sum(row["terms"] for row in counts),
        "trace_lines_compared": len(expected),
        "trace_sha256": hashlib.sha256(trace.encode("utf-8")).hexdigest(),
        "contender5_evaluated": False,
        "reflector_evaluated": False,
    }
    rendered = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
