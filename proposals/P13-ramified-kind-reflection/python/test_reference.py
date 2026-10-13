from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from reference_model import (
    BASE,
    INDEX,
    LEAF,
    TREES_OF_DEPTH_ZERO,
    autonomous_value,
    family_value,
    operator_value,
    reflect_value,
    toy_f11,
    toy_program_values,
    tree_child,
    verify_small_domain,
)


class DRKRReferenceTests(unittest.TestCase):
    def test_index_contains_required_path(self) -> None:
        self.assertEqual(tree_child(INDEX, 0), TREES_OF_DEPTH_ZERO)
        self.assertEqual(tree_child(TREES_OF_DEPTH_ZERO, 0), LEAF)

    def test_reflection_dominates_visible_data(self) -> None:
        for n in range(3):
            value = reflect_value(BASE, n)
            self.assertGreater(value, n)
            for i in range(n + 1):
                self.assertGreater(value, family_value(BASE, i, n))
            for program_value in toy_program_values(BASE, n):
                self.assertGreater(value, program_value)

    def test_autonomous_lift_is_next_rank_and_strict(self) -> None:
        for rank in range(5):
            for n in range(3):
                lower = operator_value(rank, BASE, n)
                lifted = autonomous_value(rank, BASE, n)
                self.assertEqual(lifted, operator_value(rank + 1, BASE, n))
                self.assertGreater(lifted, lower)

    def test_diagonal_dominates_seed_and_fixed_visible_ranks(self) -> None:
        for n in range(3):
            diagonal = toy_f11(n)
            self.assertGreater(diagonal, family_value(BASE, 0, n))
            for rank in range(n + 1):
                self.assertGreater(diagonal, operator_value(rank, BASE, n))

    def test_reference_summary(self) -> None:
        summary = verify_small_domain(max_n=2, max_rank=4)
        self.assertGreater(summary["checks"], 0)
        self.assertGreater(summary["interned_families"], 1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
