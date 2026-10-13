"""Reproducible small-case checks. They do not certify Lean compilation."""
from __future__ import annotations
import hashlib
import json
import time
from pathlib import Path
from reference import *


def main() -> dict:
    started = time.perf_counter()
    checks = 0
    def check(p: bool, message: str) -> None:
        nonlocal checks
        if not p:
            raise AssertionError(message)
        checks += 1

    counts = []
    maxima = []
    seed = lambda i: lambda n: i + n
    M = Model(lambda i: lambda fs: lambda n: (i + n) % 3,
              lambda i: lambda seed: lambda tree: lambda n: (i + n) % 3,
              lambda i: LEAF if i % 2 == 0 else Tree(lambda _: LEAF))
    for depth in range(5):
        terms = all_terms(depth)
        counts.append(len(terms))
        check(all(term_rank(t) <= depth for t in terms), "enumeration rank soundness")
        check(all(type_rank(t) <= depth for t in all_types(depth)), "type rank soundness")
        previous = set(all_terms(max(0, depth - 1)))
        check(previous.issubset(set(terms)), "enumeration monotonicity")
        budget = Budget(limit=5_000_000)
        env = model_env(M, lambda i: lambda n: 0, depth, seed)
        maxima.append(max((score(interpret(env, t, budget)) for t in terms), default=0))
    check(counts == [0, 2, 13, 308, 147129], "exact term counts")
    check(term_rank(amplified_call(("zero",))) == 11, "zero-certificate rank")
    check(term_rank(amplified_call(("var", 1))) == 11, "input-certificate rank")
    for k in range(100):
        check(term_rank(numeral(k)) == k + 1, "numeral rank")
        check(term_rank(amplified_call(numeral(k))) == max(11, k + 6), "literal rank")

    certificate_cases = 0
    for n in range(0, 61):
        for oracle_kind in range(4):
            fs = lambda i, q=oracle_kind: lambda x: (q + 1) * i + x * (q % 2)
            env = model_env(M, fs, n, seed)
            for selector, k in [(("zero",), 0), (("var", 1), n),
                                (numeral(2), 2), (numeral(9), 9)]:
                got = interpret(env, amplified_call(selector))
                expected = theta((k + n) % 3)
                check(got[0] == NAT and got[1] == expected, "oracle-uniform certificate")
                certificate_cases += 1

    # Every fixed interface slot keeps its oldest-first address under binders.
    for n in range(12):
        env = model_env(M, lambda _: lambda _: 0, n, seed, lambda x: x + 100)
        for slot in range(7):
            lifted = interpret([(NAT, 999)] + env, ("var", slot))
            direct = interpret(env, ("var", slot))
            check(lifted[0] == direct[0], "levels under binders: types")
            if direct[0] == NAT:
                check(lifted[1] == direct[1], "levels under binders: values")
        lam = ("lam", NAT, NAT, ("var", 7))
        check(interpret(env, app(lam, numeral(3)))[1] == 3, "new binder level 7")
        check(interpret(env, ("var", 1000)) == (NAT, 0), "out-of-range default")
        check(interpret(env, app(("zero",), ("zero",))) == (NAT, 0), "bad application")

    # W self-casts are EXTENSIONALLY identities, not pointer equalities.
    def tree_depth(t, word):
        for x in word:
            if t.children is None:
                return False
            t = t.children(x)
        return t.children is None
    w = Tree(lambda i: LEAF if i % 2 == 0 else Tree(lambda _: LEAF))
    wc = cast(TREE, TREE, w)
    for i in range(20):
        for j in range(20):
            check(tree_depth(w, [i, j]) == tree_depth(wc, [i, j]), "W self-cast")

    # Tests of the finite-maximum inequalities with arbitrary nonmonotone oracles.
    reflector_cases = 0
    for n in range(4):
        for q in range(12):
            fs = lambda i, q=q: lambda x: ((13 - i) * (x + q)) % 17
            env = model_env(M, fs, n, seed)
            scores = [score(interpret(env, t)) for t in all_terms(n)]
            top = n + 1 + max(max(fs(i)(n) for i in range(n + 1)), max(scores, default=0))
            check(all(v < top for v in scores), "program reflection inequality")
            check(all(fs(i)(n) < top for i in range(n + 1)), "oracle reflection inequality")
            reflector_cases += 1

    check(theta(0) == 2, "theta(0)")
    check(theta(1) == 16, "theta(1)")
    check(theta(2) == 2 ** 256, "theta(2)")
    check(all(theta(x) > x for x in range(3)), "small feedback inflation")
    check(theta(0) < theta(1) < theta(2), "small feedback monotonicity")
    refused = False
    try:
        theta(3)
    except BudgetExceeded:
        refused = True
    check(refused, "large numerical evaluation must be refused")

    # Individual programs need not be monotone in their oracles. This does NOT
    # by itself prove nonmonotonicity of the whole finite-maximum reflector.
    zero_test = app(app(app(("natrec", NAT), numeral(2)),
                       ("lam", NAT, NUM, ("lam", NAT, NAT, ("zero",)))),
                    app(app(("var", 0), ("zero",)), ("zero",)))
    check(interpret(model_env(M, lambda _: lambda _: 0, 0, seed), zero_test)[1] == 2,
          "zero-test at zero")
    check(interpret(model_env(M, lambda _: lambda _: 1, 0, seed), zero_test)[1] == 0,
          "zero-test after pointwise oracle increase")
    return {"status": "passed", "assertions": checks,
            "full_enumeration_term_counts": counts,
            "mock_environment_numerical_maxima": maxima,
            "certificate_semantics_cases": certificate_cases,
            "reflector_cases": reflector_cases,
            "certificate_depths": {"zero": 11, "input": 11},
            "theta_small_values": [2, 16, str(2 ** 256)],
            "seconds": round(time.perf_counter() - started, 3),
            "lean_kernel_validation": "not_run",
            "scope": "finite reference-model and symbolic syntax checks only"}

if __name__ == "__main__":
    report = main()
    destination = Path(__file__).resolve().parents[1] / "evidence" / "python_tests.json"
    destination.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
