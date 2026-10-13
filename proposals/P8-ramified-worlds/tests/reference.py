"""Small, executable reference for the comparison certificate.

This checks the new atom/application fragment only. It is NOT a replacement
for Lean or an implementation/test of the complete W-language maximum.
No full contender is evaluated.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Any, Callable

Ty = tuple
N: Ty = ("nat",)
def arr(a: Ty, b: Ty) -> Ty:
    return ("arr", a, b)
T: Ty = ("wt", N)
U = arr(N, N)
F = arr(N, U)
R = arr(F, arr(T, U))

ATOM_TYPES = {
    "zero": N, "succ": U, "input": N, "oracles": F,
    "lowerRun": arr(N, R), "lowerIndex": arr(N, T), "seed": F,
    "iterate": arr(U, arr(N, U)), "exp": U,
}

@dataclass(frozen=True)
class Tree:
    tag: str

@dataclass(frozen=True)
class World:
    run: Callable[[Any, Tree, int], int]
    index: Tree

@dataclass(frozen=True)
class Value:
    ty: Ty
    value: Any

@dataclass(frozen=True)
class Program:
    kind: str
    atom: str | None = None
    left: Program | None = None
    right: Program | None = None

def atom(name: str) -> Program:
    if name not in ATOM_TYPES:
        raise ValueError(f"Unknown atom: {name}")
    return Program("atom", atom=name)

def app(p: Program, q: Program) -> Program:
    return Program("app", left=p, right=q)

def numeral(i: int) -> Program:
    if i < 0:
        raise ValueError("A numeral must be nonnegative")
    p = atom("zero")
    for _ in range(i):
        p = app(atom("succ"), p)
    return p

def lower_function(i: int) -> Program:
    j = numeral(i)
    return app(app(app(atom("lowerRun"), j), atom("seed")),
               app(atom("lowerIndex"), j))

def lower_call(i: int) -> Program:
    return app(lower_function(i), atom("input"))

def tower_program(i: int) -> Program:
    b = lower_call(i)
    return app(app(app(atom("iterate"), atom("exp")), b), b)

def height(p: Program) -> int:
    if p.kind == "atom":
        return 1
    assert p.left is not None and p.right is not None
    return 1 + max(height(p.left), height(p.right))

def infer(p: Program) -> Ty:
    if p.kind == "atom":
        return ATOM_TYPES[p.atom]
    assert p.left is not None and p.right is not None
    f, x = infer(p.left), infer(p.right)
    if f[0] != "arr" or f[1] != x:
        raise TypeError(f"Ill-typed application: {f} to {x}")
    return f[2]

def oracle_free(p: Program) -> bool:
    if p.kind == "atom":
        return p.atom != "oracles"
    assert p.left is not None and p.right is not None
    return oracle_free(p.left) and oracle_free(p.right)

def exp2(n: int) -> int:
    if n < 0 or n > 2_000_000:
        raise ValueError("Reference evaluator safety limit, not a mathematical bound")
    return 1 << n

def iterate(f: Callable[[Any], Any], count: int, x: Any) -> Any:
    if count < 0 or count > 1_000:
        raise ValueError("Reference iteration safety limit")
    for _ in range(count):
        x = f(x)
    return x

def tower(x: int) -> int:
    return iterate(exp2, x, x)

def default(ty: Ty) -> Any:
    if ty[0] == "nat":
        return 0
    if ty[0] == "wt":
        return Tree("leaf")
    return lambda _: default(ty[2])

def apply_value(f: Value, x: Value) -> Value:
    if f.ty[0] != "arr":
        return Value(N, 0)
    a, b = f.ty[1:]
    v = x.value if x.ty == a else default(a)
    return Value(b, f.value(v))

def evaluate(p: Program, worlds: Callable[[int], World], forest: Any,
             seed: Any, n: int) -> Value:
    if p.kind == "app":
        assert p.left is not None and p.right is not None
        return apply_value(evaluate(p.left, worlds, forest, seed, n),
                           evaluate(p.right, worlds, forest, seed, n))
    a = p.atom
    values = {
        "zero": 0, "succ": lambda x: x + 1, "input": n,
        "oracles": forest, "seed": seed, "exp": exp2,
        "lowerRun": lambda i: lambda s: lambda t: lambda x: worlds(i).run(s, t, x),
        "lowerIndex": lambda i: worlds(i).index,
        "iterate": lambda f: lambda k: lambda x: iterate(f, k, x),
    }
    return Value(ATOM_TYPES[a], values[a])
