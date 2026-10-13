#!/usr/bin/env python3
"""Memoized finite analogue of BusyLean's reflection-power construction.

The model preserves the recursive shape and the inequality property used in the
Lean proof: a reflector exceeds every visible oracle value. Infinite branches
are replaced by finite tuples with a leaf default. The object-language maximum
is replaced by a harmless nonnegative bound. This is a sanity test, not a proof
about the Lean source.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
import json
from pathlib import Path
import sys
from typing import Tuple

sys.setrecursionlimit(100_000)


@dataclass(frozen=True)
class Tree:
    children: Tuple["Tree", ...] | None = None

    @property
    def is_leaf(self) -> bool:
        return self.children is None

    def child(self, i: int) -> "Tree":
        if self.children is None or i >= len(self.children):
            return LEAF
        return self.children[i]


LEAF = Tree()
DEPTH0 = Tree((LEAF, LEAF))
DEPTH1 = Tree((Tree((LEAF,)), LEAF, DEPTH0))
INDEX = Tree((DEPTH0, DEPTH1, LEAF))

# Families are interned and referred to by small integer IDs. This avoids
# recursively hashing the (potentially deep) expression that describes a
# promoted oracle family.
BASE = 0
_family_desc: dict[int, tuple[int, int, Tree] | None] = {BASE: None}
_family_intern: dict[tuple[int, int, Tree], int] = {}


def lift_family(order: int, seed_id: int, meta_tree: Tree) -> int:
    key = (order, seed_id, meta_tree)
    if key not in _family_intern:
        new_id = len(_family_desc)
        _family_intern[key] = new_id
        _family_desc[new_id] = key
    return _family_intern[key]


@lru_cache(maxsize=None)
def family_value(family_id: int, i: int, n: int) -> int:
    desc = _family_desc[family_id]
    if desc is None:
        return (i + 1) * (n + 2)
    order, seed_id, meta_tree = desc
    return lift_eval(order, seed_id, meta_tree.child(i), n)


@lru_cache(maxsize=None)
def reflect_family(family_id: int, n: int) -> int:
    visible = max(family_value(family_id, i, n) for i in range(n + 1))
    program_bound = 2 * n + 3
    return n + 1 + max(visible, program_bound)


@lru_cache(maxsize=None)
def stage_eval(seed_id: int, tree: Tree, n: int) -> int:
    if tree.is_leaf:
        return reflect_family(seed_id, n)
    visible = max(stage_eval(seed_id, tree.child(i), n) for i in range(n + 1))
    program_bound = 2 * n + 3
    return n + 1 + max(visible, program_bound)


@lru_cache(maxsize=None)
def order_eval(order: int, seed_id: int, tree: Tree, n: int) -> int:
    if order == 0:
        return stage_eval(seed_id, tree, n)
    return lift_eval(order - 1, seed_id, tree, n)


@lru_cache(maxsize=None)
def lift_eval(order: int, seed_id: int, meta_tree: Tree, n: int) -> int:
    if meta_tree.is_leaf:
        return order_eval(order, seed_id, INDEX, n)
    child_family_id = lift_family(order, seed_id, meta_tree)
    return order_eval(order, child_family_id, INDEX, n)


def run() -> dict:
    rows = []
    tested_orders = list(range(4))
    tested_inputs = list(range(3))
    for n in tested_inputs:
        values = [order_eval(k, BASE, INDEX, n) for k in tested_orders]
        assert all(values[k] < values[k + 1] for k in range(len(values) - 1))
        for k in tested_orders:
            for i in range(n + 1):
                assert family_value(BASE, i, n) < order_eval(k, BASE, INDEX, n)
        rows.append({"n": n, "orders_0_through_3": values})

    chains = []
    for n in tested_inputs:
        for order in tested_orders:
            leaf = lift_eval(order, BASE, LEAF, n)
            depth0 = lift_eval(order, BASE, DEPTH0, n)
            index = lift_eval(order, BASE, INDEX, n)
            assert leaf < depth0 < index
            chains.append({
                "n": n,
                "scheduler_order": order,
                "leaf": leaf,
                "depth0": depth0,
                "index": index,
            })

    return {
        "status": "PASS",
        "rows": rows,
        "comparison_chains": chains,
        "tested_orders": tested_orders,
        "tested_inputs": tested_inputs,
        "interned_family_count": len(_family_desc),
        "cache": {
            "family_value": family_value.cache_info()._asdict(),
            "stage_eval": stage_eval.cache_info()._asdict(),
            "order_eval": order_eval.cache_info()._asdict(),
            "lift_eval": lift_eval.cache_info()._asdict(),
        },
        "claims_checked": [
            "visible base-seed values are dominated at every tested order",
            "each scheduler order is strictly larger than its predecessor",
            "the leaf -> depth-0 join -> universal-index chain is strict",
        ],
        "disclaimer": "Finite analogue only; not a Lean kernel proof.",
    }


def main() -> None:
    report = run()
    root = Path(__file__).resolve().parents[1]
    out = root / "logs" / "finite_model.json"
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
