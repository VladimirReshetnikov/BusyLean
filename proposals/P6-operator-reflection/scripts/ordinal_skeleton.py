#!/usr/bin/env python3
"""Finite ordinal-exponent skeleton for operator reflection.

This is an explanatory regression model, not a Lean proof.  Under the article's
rank heuristic, a progressive transformer of increment lambda^e gains one
exponent when autonomously lifted along an index of height lambda.  Iterating
that lift down an outer tree therefore maps finite outer height h to exponent
h+2; a universal outer index of height lambda suggests lambda^lambda.
"""
from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Tree:
    children: tuple["Tree", ...] = ()

    @property
    def is_leaf(self) -> bool:
        return not self.children


def full_tree(height: int, width: int = 2) -> Tree:
    if height == 0:
        return Tree()
    child = full_tree(height - 1, width)
    return Tree(tuple(child for _ in range(width)))


def operator_stage_exponent(tree: Tree) -> int:
    """Exponent e in the finite proxy lambda^e.

    A leaf is one autonomous lift above primitive reflection, hence e=2.
    A node splices its children and autonomously lifts once more.
    """
    if tree.is_leaf:
        return 2
    return 1 + max(operator_stage_exponent(c) for c in tree.children)


def check() -> None:
    c6_exponent = 2
    rows = []
    for height in range(0, 9):
        tree = full_tree(height)
        exponent = operator_stage_exponent(tree)
        assert exponent == height + 2
        rows.append((height, exponent))

    # The actual comparison uses two visible outer edges, so even the tiny
    # height-2 fragment strictly exceeds the Contender-6 exponent.
    witness = operator_stage_exponent(full_tree(2))
    assert c6_exponent < witness

    print("PASS: finite exponent skeleton")
    print(f"Contender 6 proxy: lambda^{c6_exponent}")
    for height, exponent in rows:
        print(f"outer height {height}: lambda^{exponent}")
    print("universal outer height lambda: heuristic limit lambda^lambda")


if __name__ == "__main__":
    check()
