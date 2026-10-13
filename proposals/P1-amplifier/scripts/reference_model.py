#!/usr/bin/env python3
"""Independent small-input model of the Coq computational definitions.

This is a smoke test for the translation, not a proof and not an attempt to
evaluate either contender.  It intentionally stops at syntax depth four.
"""

from functools import lru_cache
from itertools import product
import json

N = ("nat",)


def arr(a, b):
    return ("arr", a, b)


def default(tp):
    if tp == N:
        return 0
    return lambda _: default(tp[2])


def casts(source, target):
    if source == N and target == N:
        return (lambda x: x, lambda x: x)
    if source[0] == target[0] == "arr":
        a, b, c, d = source[1], source[2], target[1], target[2]
        if a == c and b == d:
            ac, ca = casts(a, c)
            bd, db = casts(b, d)
            return (lambda f: lambda x: bd(f(ca(x))),
                    lambda f: lambda x: db(f(ac(x))))
    return (lambda _: default(target), lambda _: default(source))


def interp(env, term):
    tag = term[0]
    if tag == "var":
        index = term[1]
        return env[len(env) - 1 - index] if index < len(env) else (N, 0)
    if tag == "lam":
        a, b, body = term[1:]

        def function(x):
            tp, value = interp([(a, x)] + env, body)
            return casts(tp, b)[0](value)

        return arr(a, b), function
    if tag == "app":
        tp1, f = interp(env, term[1])
        tp2, x = interp(env, term[2])
        if tp1 == N:
            return N, 0
        a, b = tp1[1:]
        return b, f(casts(tp2, a)[0](x))
    if tag == "zero":
        return N, 0
    if tag == "succ":
        return arr(N, N), lambda n: n + 1
    if tag == "rec":
        r = term[1]

        def recurse(z):
            def with_step(step):
                def with_count(count):
                    result = z
                    for predecessor in range(count):
                        result = step(predecessor)(result)
                    return result
                return with_count
            return with_step

        return arr(r, arr(arr(N, arr(r, r)), arr(N, r))), recurse
    raise ValueError(term)


def evaluate(term):
    tp, value = interp([], term)
    return value if tp == N else 0


@lru_cache(None)
def types_up_to(n):
    if n == 0:
        return ()
    previous = types_up_to(n - 1)
    return (N,) + tuple(arr(a, b) for a, b in product(previous, repeat=2))


@lru_cache(None)
def terms_up_to(n):
    if n == 0:
        return ()
    m = n - 1
    types, terms = types_up_to(m), terms_up_to(m)
    variables = tuple(("var", i) for i in reversed(range(m)))
    lambdas = tuple(("lam", a, b, t) for a, b, t in product(types, types, terms))
    apps = tuple(("app", t, u) for t, u in product(terms, repeat=2))
    return variables + lambdas + apps + (("zero",), ("succ",)) + tuple(
        ("rec", r) for r in types)


def app(f, x):
    return "app", f, x


def numeral(n):
    result = ("zero",)
    for _ in range(n):
        result = app(("succ",), result)
    return result


def main():
    rows = []
    for n in range(5):
        terms = terms_up_to(n)
        rows.append([n, len(types_up_to(n)), len(terms),
                     max((evaluate(t) for t in terms), default=0)])
    expected = [[0, 0, 0, 0], [1, 1, 2, 0], [2, 2, 10, 1],
                [3, 5, 146, 2], [4, 26, 24976, 3]]
    assert rows == expected, (rows, expected)
    rr = arr(N, N)
    double_step = ("lam", N, arr(rr, rr),
                   ("lam", rr, rr,
                    ("lam", N, N,
                     app(("var", 1), app(("var", 1), ("var", 2))))))
    higher_rec = app(app(app(app(("rec", rr), ("succ",)), double_step),
                        numeral(3)), numeral(0))
    assert evaluate(higher_rec) == 8
    outer = app(app(("lam", N, arr(N, N),
                     ("lam", N, N, ("var", 0))), numeral(1)), numeral(2))
    inner = app(app(("lam", N, arr(N, N),
                     ("lam", N, N, ("var", 1))), numeral(1)), numeral(2))
    assert evaluate(outer) == 1
    assert evaluate(inner) == 2
    print(json.dumps({"passed": True,
                      "columns": ["depth", "types", "raw_terms", "maximum"],
                      "rows": rows,
                      "higher_type_recursion": 8,
                      "reversed_indices": [1, 2]}, indent=2))


if __name__ == "__main__":
    main()
