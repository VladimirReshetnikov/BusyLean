"""Guarded reference interpreter for finite tests, NOT an evaluator for C7.

The syntax, casts, levels and enumeration follow the three vendored Lean files.
Finite test trees expose only the branches that a test actually visits. Limits
are engineering safeguards of this Python model, never part of the definition.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
from typing import Any, Callable

Ty = tuple
Term = tuple
NAT = ("nat",)

def arr(a: Ty, b: Ty) -> Ty:
    return ("arr", a, b)

def wt(a: Ty) -> Ty:
    return ("wt", a)

NUM = arr(NAT, NAT)
FAMILY = arr(NAT, NUM)
TREE = wt(NAT)
REFLECT = arr(FAMILY, NUM)
STAGE = arr(FAMILY, arr(TREE, NUM))

@dataclass(frozen=True)
class Tree:
    children: Callable[[Any], "Tree"] | None = None

LEAF = Tree()

class BudgetExceeded(RuntimeError):
    pass

@dataclass
class Budget:
    calls: int = 0
    limit: int = 3_000_000

    def tick(self) -> None:
        self.calls += 1
        if self.calls > self.limit:
            raise BudgetExceeded("Reference-model call budget exhausted")

def pow2(n: int, max_exponent: int = 100_000) -> int:
    if n < 0 or n > max_exponent:
        raise BudgetExceeded(f"Refusing exponent {n.bit_length()} bits long")
    return 1 << n

def iterate(f: Callable, k: int, x: Any) -> Any:
    if k < 0:
        raise ValueError("A natural iteration count is required")
    for _ in range(k):
        x = f(x)
    return x

def theta(x: int) -> int:
    if x < 0 or x > 100:
        raise BudgetExceeded("Refusing a large tower-height feedback input")
    return iterate(pow2, x + 1, x + 1)

def wmap(g: Callable, w: Tree) -> Tree:
    if w.children is None:
        return LEAF
    return Tree(lambda x: wmap(g, w.children(g(x))))

def default(ty: Ty) -> Any:
    if ty[0] == "nat":
        return 0
    if ty[0] == "arr":
        return lambda _: default(ty[2])
    return LEAF

def cast_pair(a: Ty, b: Ty) -> tuple[Callable, Callable]:
    if a == NAT and b == NAT:
        return (lambda x: x), (lambda x: x)
    if a[0] == b[0] == "arr" and a[1:] == b[1:]:
        ac = cast_pair(a[1], b[1])
        bd = cast_pair(a[2], b[2])
        return (lambda f: lambda x: bd[0](f(ac[1](x))),
                lambda f: lambda x: bd[1](f(ac[0](x))))
    if a[0] == b[0] == "wt" and a[1] == b[1]:
        ab = cast_pair(a[1], b[1])
        return (lambda w: wmap(ab[1], w)), (lambda w: wmap(ab[0], w))
    return (lambda _: default(b)), (lambda _: default(a))

def cast(a: Ty, b: Ty, value: Any) -> Any:
    return cast_pair(a, b)[0](value)

def lookup(env: list, level: int) -> tuple[Ty, Any]:
    return env[len(env) - level - 1] if 0 <= level < len(env) else (NAT, 0)

def interpret(env: list, t: Term, budget: Budget | None = None) -> tuple[Ty, Any]:
    budget = budget or Budget()
    budget.tick()
    tag = t[0]
    if tag == "var":
        return lookup(env, t[1])
    if tag == "zero":
        return NAT, 0
    if tag == "succ":
        return NUM, lambda x: x + 1
    if tag == "lam":
        _, a, b, body = t
        def function(x):
            rt, rv = interpret([(a, x)] + env, body, budget)
            return cast(rt, b, rv)
        return arr(a, b), function
    if tag == "app":
        ft, f = interpret(env, t[1], budget)
        at, a = interpret(env, t[2], budget)
        return (ft[2], f(cast(at, ft[1], a))) if ft[0] == "arr" else (NAT, 0)
    if tag == "natrec":
        r = t[1]
        def primitive(z):
            def stepper(s):
                def runner(n):
                    if n > 10_000:
                        raise BudgetExceeded("Refusing large natural recursion")
                    value = z
                    for i in range(n):
                        budget.tick()
                        value = s(i)(value)
                    return value
                return runner
            return stepper
        return arr(r, arr(arr(NAT, arr(r, r)), arr(NAT, r))), primitive
    if tag == "wzero":
        return wt(t[1]), LEAF
    if tag == "wnode":
        a = t[1]
        return arr(arr(a, wt(a)), wt(a)), lambda f: Tree(f)
    if tag == "wrec":
        a, r = t[1:]
        def primitive(z):
            def stepper(s):
                def fold(w):
                    budget.tick()
                    if w.children is None:
                        return z
                    return s(w.children)(lambda x: fold(w.children(x)))
                return fold
            return stepper
        return arr(r, arr(arr(arr(a, wt(a)), arr(arr(a, r), r)), arr(wt(a), r))), primitive
    raise ValueError(f"Unknown term constructor: {tag}")

@lru_cache(None)
def all_types(n: int) -> tuple[Ty, ...]:
    if n == 0:
        return ()
    ts = all_types(n - 1)
    return (NAT,) + tuple(arr(a, b) for a in ts for b in ts) + tuple(wt(a) for a in ts)

@lru_cache(None)
def all_terms(n: int) -> tuple[Term, ...]:
    if n > 4:
        raise BudgetExceeded("Enumerations above depth 4 are intentionally disabled")
    if n == 0:
        return ()
    ts, es = all_types(n - 1), all_terms(n - 1)
    return (tuple(("var", i) for i in range(n - 2, -1, -1))
            + tuple(("lam", a, b, e) for a in ts for b in ts for e in es)
            + tuple(("app", e, f) for e in es for f in es)
            + (("zero",), ("succ",))
            + tuple(("natrec", a) for a in ts)
            + tuple(("wzero", a) for a in ts)
            + tuple(("wnode", a) for a in ts)
            + tuple(("wrec", a, b) for a in ts for b in ts))

def type_rank(t: Ty) -> int:
    if t[0] == "nat":
        return 1
    if t[0] == "wt":
        return 1 + type_rank(t[1])
    return 1 + max(type_rank(t[1]), type_rank(t[2]))

def term_rank(t: Term) -> int:
    tag = t[0]
    if tag in ("zero", "succ"):
        return 1
    if tag == "var":
        return t[1] + 2
    if tag == "app":
        return 1 + max(term_rank(t[1]), term_rank(t[2]))
    if tag == "lam":
        return 1 + max(type_rank(t[1]), type_rank(t[2]), term_rank(t[3]))
    if tag == "wrec":
        return 1 + max(type_rank(t[1]), type_rank(t[2]))
    return 1 + type_rank(t[1])

def app(f: Term, x: Term) -> Term:
    return ("app", f, x)

def numeral(n: int) -> Term:
    return iterate(lambda t: app(("succ",), t), n, ("zero",))

def call_at(s: Term) -> Term:
    return app(app(app(app(("var", 4), s), ("var", 2)),
                   app(("var", 5), s)), ("var", 1))

def amplified_call(s: Term) -> Term:
    return app(("var", 6), call_at(s))

@dataclass(frozen=True)
class Model:
    reflectors: Callable
    forests: Callable
    trees: Callable

def model_env(M: Model, fs: Callable, n: int, seed: Callable,
              amplifier: Callable = theta) -> list:
    return [(NUM, amplifier), (arr(NAT, TREE), M.trees),
            (arr(NAT, STAGE), M.forests), (arr(NAT, REFLECT), M.reflectors),
            (FAMILY, seed), (NAT, n), (FAMILY, fs)]

def score(value: tuple[Ty, Any]) -> int:
    return value[1] if value[0] == "nat" or value[0] == NAT else 0
