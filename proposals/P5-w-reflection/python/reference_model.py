"""Executable finite tests of the paper's semantics, not a proof of Lean compilation.

Only shallow syntax is enumerated. Resource guards are for this test harness;
they do not occur in the mathematical or Lean definitions.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from typing import Any, Callable, Iterable

Ty = tuple
Term = tuple
N: Ty = ('N',)
Z: Term = ('z',)
S: Term = ('s',)


def Arr(a: Ty, b: Ty) -> Ty:
    return ('arr', a, b)


def WT(a: Ty) -> Ty:
    return ('w', a)


def App(t: Term, u: Term) -> Term:
    return ('app', t, u)


@dataclass(frozen=True)
class Tree:
    children: Callable[[Any], 'Tree'] | None = None


LEAF = Tree()


class BudgetExceeded(RuntimeError):
    pass


@dataclass
class Budget:
    remaining: int = 2_000_000
    max_bits: int = 100_000

    def tick(self, amount: int = 1) -> None:
        self.remaining -= amount
        if self.remaining < 0:
            raise BudgetExceeded('test execution budget exhausted')

    def natural(self, n: int) -> int:
        if not isinstance(n, int) or n < 0:
            raise TypeError(f'not a natural number: {n!r}')
        if n.bit_length() > self.max_bits:
            raise BudgetExceeded('test integer bit-length limit exceeded')
        return n


@lru_cache(None)
def type_depth(a: Ty) -> int:
    if a[0] == 'N':
        return 1
    if a[0] == 'arr':
        return 1 + max(type_depth(a[1]), type_depth(a[2]))
    return 1 + type_depth(a[1])


@lru_cache(None)
def term_depth(t: Term) -> int:
    tag = t[0]
    if tag == 'var':
        return t[1] + 2
    if tag == 'lam':
        return 1 + max(type_depth(t[1]), type_depth(t[2]), term_depth(t[3]))
    if tag == 'app':
        return 1 + max(term_depth(t[1]), term_depth(t[2]))
    if tag in ('z', 's'):
        return 1
    if tag in ('rec', 'wz', 'wn'):
        return 1 + type_depth(t[1])
    if tag == 'wr':
        return 1 + max(type_depth(t[1]), type_depth(t[2]))
    raise ValueError(tag)


@lru_cache(None)
def types(depth: int, extended: bool = False) -> tuple[Ty, ...]:
    if depth < 0 or depth > 4:
        raise ValueError('this harness enumerates type depths 0..4 only')
    if depth == 0:
        return ()
    ts = types(depth - 1, extended)
    return (N,) + tuple(Arr(a, b) for a, b in product(ts, repeat=2)) + (
        tuple(WT(a) for a in ts) if extended else ())


@lru_cache(None)
def terms(depth: int, extended: bool = False) -> tuple[Term, ...]:
    if depth < 0 or depth > 4:
        raise ValueError('this harness enumerates term depths 0..4 only')
    if depth == 0:
        return ()
    ts = types(depth - 1, extended)
    es = terms(depth - 1, extended)
    out = tuple(('var', i) for i in reversed(range(depth - 1)))
    out += tuple(('lam', a, b, t) for a, b, t in product(ts, ts, es))
    out += tuple(App(t, u) for t, u in product(es, es))
    out += (Z, S) + tuple(('rec', a) for a in ts)
    if extended:
        out += tuple(('wz', a) for a in ts)
        out += tuple(('wn', a) for a in ts)
        out += tuple(('wr', a, b) for a, b in product(ts, ts))
    return out


def default_value(a: Ty) -> Any:
    if a[0] == 'N':
        return 0
    if a[0] == 'arr':
        return lambda _: default_value(a[2])
    return LEAF


def reindex(g: Callable[[Any], Any], tree: Tree, budget: Budget) -> Tree:
    budget.tick()
    if tree.children is None:
        return LEAF
    return Tree(lambda b: reindex(g, tree.children(g(b)), budget))


def cast_pair(a: Ty, b: Ty, budget: Budget) -> tuple[Callable, Callable]:
    budget.tick()
    if a == N and b == N:
        return (lambda x: x), (lambda x: x)
    if a[0] == b[0] == 'arr' and a[1:] == b[1:]:
        fw1, bw1 = cast_pair(a[1], b[1], budget)
        fw2, bw2 = cast_pair(a[2], b[2], budget)
        return ((lambda f: lambda x: fw2(f(bw1(x)))),
                (lambda f: lambda x: bw2(f(fw1(x)))))
    if a[0] == b[0] == 'w' and a[1] == b[1]:
        fw, bw = cast_pair(a[1], b[1], budget)
        return (lambda t: reindex(bw, t, budget)), (lambda t: reindex(fw, t, budget))
    return (lambda _: default_value(b)), (lambda _: default_value(a))


def natural_rec(z: Any, step: Callable, n: int, budget: Budget) -> Any:
    budget.natural(n)
    if n > budget.remaining:
        raise BudgetExceeded('natural-recursion count exceeds test budget')
    out = z
    for i in range(n):
        budget.tick()
        out = step(i)(out)
    return out


def tree_rec(z: Any, step: Callable, w: Tree, budget: Budget) -> Any:
    budget.tick()
    if w.children is None:
        return z
    return step(w.children)(lambda a: tree_rec(z, step, w.children(a), budget))


def interpret(env: tuple[tuple[Ty, Any], ...], t: Term, budget: Budget) -> tuple[Ty, Any]:
    budget.tick()
    tag = t[0]
    if tag == 'var':
        n = t[1]
        return env[len(env) - 1 - n] if n < len(env) else (N, 0)
    if tag == 'lam':
        a, b, body = t[1:]
        def closure(x: Any) -> Any:
            c, y = interpret(((a, x),) + env, body, budget)
            return cast_pair(c, b, budget)[0](y)
        return Arr(a, b), closure
    if tag == 'app':
        a, f = interpret(env, t[1], budget)
        b, x = interpret(env, t[2], budget)
        if a[0] != 'arr':
            return N, 0
        return a[2], f(cast_pair(b, a[1], budget)[0](x))
    if tag == 'z':
        return N, 0
    if tag == 's':
        return Arr(N, N), lambda x: budget.natural(x + 1)
    if tag == 'rec':
        r = t[1]
        return Arr(r, Arr(Arr(N, Arr(r, r)), Arr(N, r))), (
            lambda z: lambda s: lambda n: natural_rec(z, s, n, budget))
    if tag == 'wz':
        return WT(t[1]), LEAF
    if tag == 'wn':
        a = t[1]
        return Arr(Arr(a, WT(a)), WT(a)), lambda f: Tree(f)
    if tag == 'wr':
        a, r = t[1:]
        step_ty = Arr(Arr(a, WT(a)), Arr(Arr(a, r), r))
        return Arr(r, Arr(step_ty, Arr(WT(a), r))), (
            lambda z: lambda s: lambda w: tree_rec(z, s, w, budget))
    raise ValueError(tag)


def evaluate(t: Term, budget: Budget | None = None) -> int:
    budget = budget or Budget()
    a, value = interpret((), t, budget)
    return budget.natural(value) if a == N else 0


def scan_maxby(es: Iterable[Term]) -> tuple[int, Term]:
    best, score = Z, 0
    for t in es:
        value = evaluate(t)
        if score < value:
            best, score = t, value
    return score, best


# A closed double function with the repository's absolute de Bruijn levels.
DOUBLE: Term = ('lam', N, N,
    App(App(App(('rec', N), Z),
        ('lam', N, Arr(N, N),
            ('lam', N, N, App(S, App(S, ('var', 2)))))), ('var', 0)))


def binary_numeral(n: int) -> Term:
    if n < 0:
        raise ValueError('natural number required')
    if n == 0:
        return Z
    d = App(DOUBLE, binary_numeral(n // 2))
    return App(S, d) if n % 2 else d


def iterate(f: Callable[[int], int], count: int, x: int, budget: Budget) -> int:
    if count < 0 or count > budget.remaining:
        raise BudgetExceeded('iteration count exceeds test budget')
    for _ in range(count):
        budget.tick()
        x = budget.natural(f(x))
    return x


def row(f: Callable[[int], int], k: int, n: int, budget: Budget) -> int:
    budget.tick()
    if k == 0:
        return budget.natural(f(n))
    previous = lambda x: row(f, k - 1, x, budget)
    return budget.natural(previous(n) + iterate(previous, n+1, n+1, budget) + 1)
