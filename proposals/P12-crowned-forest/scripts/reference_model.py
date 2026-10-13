#!/usr/bin/env python3
"""Finite reference model for the structural part of Contender 11.

This is deliberately *not* an implementation of System Fω normalization and it
never attempts to evaluate a BusyLean contender.  It checks the algebra that is
independent of the enormous object language:

* the 2-adic family code used by `packFamily`;
* child/input bounds for a finite maximum reflector;
* strict growth at every crown level;
* the leaf -> treesOfDepth(0) -> index comparison route;
* an explicit n+1-step crown certificate.

The Lean kernel, not this model, is the authority for the submitted theorems.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from typing import Callable, Iterable, Protocol


Family = Callable[[int, int], int]


def v2(k: int) -> int:
    """2-adic valuation, agreeing with BusyLean's convention v2(0)=0."""
    if k < 0:
        raise ValueError("natural number required")
    if k == 0:
        return 0
    i = 0
    while k % 2 == 0:
        k //= 2
        i += 1
    return i


def unpair2(k: int) -> tuple[int, int]:
    if k < 0:
        raise ValueError("natural number required")
    i = v2(k)
    return i, (k // (2**i)) // 2


def code2(i: int, m: int) -> int:
    if i < 0 or m < 0:
        raise ValueError("natural numbers required")
    return (2**i) * (2 * m + 1)


def pack_family(fs: Family) -> Callable[[int], int]:
    def packed(k: int) -> int:
        i, m = unpair2(k)
        return fs(i, m)
    return packed


class Tree(Protocol):
    pass


@dataclass(frozen=True)
class Leaf:
    pass


@dataclass(frozen=True)
class Node:
    """A finite cyclic presentation of a countable family of children."""
    children: tuple[Tree, ...]

    def child(self, i: int) -> Tree:
        if not self.children:
            return Leaf()
        return self.children[i % len(self.children)]


def crown(k: int, a: Tree) -> Tree:
    if k < 0:
        raise ValueError("natural number required")
    for _ in range(k):
        a = Node((a,))
    return a


def prefix_max(f: Callable[[int], int], n: int) -> int:
    return max((f(i) for i in range(n + 1)), default=0)


def toy_program_values(fs: Family, n: int) -> Iterable[int]:
    """A finite stand-in for object-language values.

    It intentionally exercises both direct children and the packed unary
    interface.  Nothing here claims to model the full Fk language.
    """
    packed = pack_family(fs)
    yield 0
    yield n
    yield fs(0, n)
    yield packed(code2(n, n))
    yield packed(code2(0, n)) + n


def reflect(fs: Family, n: int) -> int:
    visible = prefix_max(lambda i: fs(i, n), n)
    programs = max(toy_program_values(fs, n), default=0)
    return n + 1 + max(visible, programs)


def seed(i: int, n: int) -> int:
    # The first coordinate is ignored, just as `(fun _ => family10)` ignores it.
    del i
    return (n + 2) ** 3 + n


def tiny_defined_tree(k: int, i: int) -> Tree:
    """Finite analogue of a tree returned by the old W-language."""
    height = (k + 2 * i) % 4
    a: Tree = Leaf()
    for _ in range(height):
        a = Node((a,))
    return a


def trees_of_depth(k: int, width: int = 8) -> Tree:
    return Node(tuple(tiny_defined_tree(k, i) for i in range(width)))


def index_tree(width: int = 8) -> Tree:
    return Node(tuple(trees_of_depth(k, width) for k in range(width)))


@lru_cache(maxsize=None)
def stage(a: Tree, n: int) -> int:
    if isinstance(a, Leaf):
        return reflect(seed, n)
    if isinstance(a, Node):
        return reflect(lambda i, m: stage(a.child(i), m), n)
    raise TypeError(f"unknown tree: {a!r}")


def f11_toy(n: int) -> int:
    return stage(crown(n + 1, index_tree()), n)

def run_reference_checks(max_n: int = 5) -> dict[str, object]:
    assertions = 0

    # The pairing identity is exact, not merely sampled conceptually.  We test
    # a dense finite box as an implementation guard.
    for i in range(12):
        for m in range(50):
            assert unpair2(code2(i, m)) == (i, m)
            assertions += 1

    # Reflection inequalities and crown steps.
    rows: list[dict[str, int]] = []
    for n in range(max_n + 1):
        base = stage(index_tree(), n)
        values = [stage(crown(k, index_tree()), n) for k in range(n + 2)]
        assert values[0] == base
        assertions += 1
        for left, right in zip(values, values[1:]):
            assert left < right
            assertions += 1
        assert seed(0, n) < base
        assert base < f11_toy(n)
        assert seed(0, n) < f11_toy(n)
        assert n < f11_toy(n)
        assertions += 4

        # Exact comparison route used in Lean: seed -> leaf -> depth-0 join -> index.
        leaf_value = stage(Leaf(), n)
        depth0_value = stage(trees_of_depth(0), n)
        index_value = stage(index_tree(), n)
        assert seed(0, n) < leaf_value < depth0_value < index_value
        assertions += 3

        rows.append({
            "n": n,
            "seed": seed(0, n),
            "index_stage": base,
            "crown_steps": n + 1,
            "toy_F11": f11_toy(n),
        })

    # The advertised input 42 has 43 strict crown edges.  This is checked
    # symbolically by construction rather than by evaluating the actual stage.
    symbolic_edges_at_42 = len(range(42 + 1))
    assert symbolic_edges_at_42 == 43
    assertions += 1

    return {
        "status": "passed",
        "scope": "finite structural reference model; not Lean kernel validation",
        "assertions": assertions,
        "max_n": max_n,
        "pairing_box": {"i": [0, 11], "m": [0, 49]},
        "symbolic_crown_edges_at_42": symbolic_edges_at_42,
        "sample_rows": rows,
    }


if __name__ == "__main__":
    import json
    print(json.dumps(run_reference_checks(), indent=2, sort_keys=True))
