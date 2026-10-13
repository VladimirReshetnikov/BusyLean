"""Memoized finite model of Diagonal Ramified Kind-Reflection (DRKR).

This is not an evaluator for the real BusyLean numeral.  It replaces the
object-language enumeration and the infinitely branching W-tree by finite
surrogates while retaining exactly the equations used by the proof:

* rank 0 is family-aware reflection;
* rank r+1 is autonomous W-tree lifting of rank r;
* the index contains leaf < treesOfDepth(0) < index;
* the selected rank is seed(n)+1.

Generated oracle families are hash-consed into integer identifiers.  This is
important: a direct higher-order evaluator already develops an enormous nested
closure graph at tiny ranks, whereas the hash-consed evaluator can regression-
test a useful finite domain.
"""
from __future__ import annotations

from functools import cache
import sys

sys.setrecursionlimit(200_000)
from typing import Final

# Finite trees, represented by IDs.
LEAF: Final[int] = 0
TREES_OF_DEPTH_ZERO: Final[int] = 1
SECOND_TREE: Final[int] = 2
INDEX: Final[int] = 3

_TREE_CHILDREN: Final[dict[int, tuple[int, ...]]] = {
    LEAF: (),
    TREES_OF_DEPTH_ZERO: (LEAF,),
    SECOND_TREE: (LEAF, LEAF),
    INDEX: (TREES_OF_DEPTH_ZERO, SECOND_TREE),
}


def tree_child(tree: int, index: int) -> int:
    children = _TREE_CHILDREN[tree]
    if 0 <= index < len(children):
        return children[index]
    return LEAF


# Family 0 is the base seed.  Other families are symbolic triples
# (operator rank, seed family ID, source node ID).
BASE: Final[int] = 0
_FAMILIES: list[tuple[int, int, int] | None] = [None]
_FAMILY_INTERN: dict[tuple[int, int, int], int] = {}


def child_family(rank: int, seed: int, tree: int) -> int:
    key = (rank, seed, tree)
    known = _FAMILY_INTERN.get(key)
    if known is not None:
        return known
    family_id = len(_FAMILIES)
    _FAMILIES.append(key)
    _FAMILY_INTERN[key] = family_id
    return family_id


@cache
def family_value(family: int, i: int, n: int) -> int:
    if i < 0 or n < 0:
        raise ValueError("indices must be nonnegative")
    if family == BASE:
        # Small stand-in for family10; it is increasing and exceeds n.
        return n + 1
    record = _FAMILIES[family]
    assert record is not None
    rank, seed, tree = record
    return lift_value(rank, seed, tree_child(tree, i), n)


@cache
def toy_program_values(family: int, n: int) -> tuple[int, ...]:
    """Finite stand-in for accepted kind-polymorphic program values."""
    visible = tuple(family_value(family, i, n) for i in range(n + 1))
    return (0, n, sum(visible), max(visible, default=0) + n)


@cache
def reflect_value(family: int, n: int) -> int:
    visible_max = max(
        (family_value(family, i, n) for i in range(n + 1)), default=0
    )
    program_max = max(toy_program_values(family, n), default=0)
    return n + 1 + max(visible_max, program_max)


@cache
def operator_value(rank: int, family: int, n: int) -> int:
    """Value of the finite analogue of RK.ramified rank."""
    if rank < 0:
        raise ValueError("rank must be nonnegative")
    if rank == 0:
        return reflect_value(family, n)
    return lift_value(rank - 1, family, INDEX, n)


@cache
def lift_value(rank: int, seed: int, tree: int, n: int) -> int:
    """Value of RK.lift (RK.ramified rank) seed tree n."""
    if tree == LEAF:
        return operator_value(rank, seed, n)
    return operator_value(rank, child_family(rank, seed, tree), n)


def autonomous_value(rank: int, family: int, n: int) -> int:
    """Autonomous lift of rank, definitionally rank+1 in the model."""
    return lift_value(rank, family, INDEX, n)


def toy_f11(n: int) -> int:
    rank = family_value(BASE, 0, n) + 1
    return operator_value(rank, BASE, n)


def verify_small_domain(max_n: int = 2, max_rank: int = 4) -> dict[str, int]:
    checks = 0

    for n in range(max_n + 1):
        reflected = reflect_value(BASE, n)
        assert n < reflected
        checks += 1
        for i in range(n + 1):
            assert family_value(BASE, i, n) < reflected
            checks += 1
        for program_value in toy_program_values(BASE, n):
            assert program_value < reflected
            checks += 1

    for rank in range(max_rank + 1):
        for n in range(max_n + 1):
            lower = operator_value(rank, BASE, n)
            lifted = autonomous_value(rank, BASE, n)
            higher = operator_value(rank + 1, BASE, n)
            assert lower < lifted
            assert lifted == higher
            checks += 2

    for n in range(max_n + 1):
        diagonal = toy_f11(n)
        assert family_value(BASE, 0, n) < diagonal
        checks += 1
        for rank in range(n + 1):
            assert operator_value(rank, BASE, n) < diagonal
            checks += 1

    return {
        "checks": checks,
        "max_n": max_n,
        "max_rank": max_rank,
        "interned_families": len(_FAMILIES),
        "cache_family": family_value.cache_info().currsize,
        "cache_reflect": reflect_value.cache_info().currsize,
        "cache_operator": operator_value.cache_info().currsize,
        "cache_lift": lift_value.cache_info().currsize,
        "sample_f11_0": toy_f11(0),
        "sample_f11_1": toy_f11(1),
        "sample_f11_2": toy_f11(2),
    }


if __name__ == "__main__":
    import json

    print(json.dumps(verify_small_domain(), indent=2, sort_keys=True))
