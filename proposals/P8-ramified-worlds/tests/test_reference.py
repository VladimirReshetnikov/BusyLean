import json
from pathlib import Path
import unittest
from reference import *

class WitnessTests(unittest.TestCase):
    def test_types_all_visible_children(self):
        for i in range(36):
            with self.subTest(i=i):
                self.assertEqual(infer(lower_function(i)), U)
                self.assertEqual(infer(lower_call(i)), N)
                self.assertEqual(infer(tower_program(i)), N)

    def test_exact_height_certificate(self):
        for i in range(100):
            with self.subTest(i=i):
                self.assertEqual(height(numeral(i)), i + 1)
                self.assertEqual(height(lower_function(i)), i + 4)
                self.assertEqual(height(lower_call(i)), i + 5)
                self.assertEqual(height(tower_program(i)), i + 7)

    def test_no_numeric_forest_oracle(self):
        for i in range(36):
            self.assertTrue(oracle_free(tower_program(i)))
        self.assertFalse(oracle_free(atom("oracles")))

    def test_witness_values_and_world_routing(self):
        seed = object()
        forest = lambda *_: (_ for _ in ()).throw(AssertionError("unexpected oracle call"))
        for b in range(4):
            worlds = {}
            for i in range(36):
                tree = Tree(f"world-{i}")
                def run(s, t, n, *, expected=tree, value=b):
                    self.assertIs(s, seed)
                    self.assertIs(t, expected)
                    self.assertEqual(n, 42)
                    return value
                worlds[i] = World(run, tree)
            for i in range(36):
                with self.subTest(b=b, i=i):
                    v = evaluate(tower_program(i), worlds.__getitem__, forest, seed, 42)
                    self.assertEqual(v.ty, N)
                    self.assertEqual(v.value, tower(b))

    def test_small_tower_values(self):
        self.assertEqual([tower(i) for i in range(4)], [0, 2, 16, 2**256])

    def test_exponential_inflation_and_monotonicity(self):
        for n in range(100):
            self.assertGreaterEqual(exp2(n), n)
            self.assertLessEqual(exp2(n), exp2(n + 1))
        self.assertEqual(sorted(tower(i) for i in range(4)),
                         [tower(i) for i in range(4)])

    def test_exact_cast_retains_tree(self):
        tree = Tree("identity-test")
        f = Value(arr(T, T), lambda x: x)
        self.assertIs(apply_value(f, Value(T, tree)).value, tree)
        self.assertEqual(apply_value(f, Value(N, 7)).value, Tree("leaf"))

    def test_bad_function_application_returns_zero(self):
        self.assertEqual(apply_value(Value(N, 10), Value(N, 11)), Value(N, 0))

    def test_finite_reflection_inequality(self):
        # A finite test of the generic arithmetic lemma, NOT the full C_n.
        for n in range(12):
            for values in [[], [0], [0, 1, 5], [7, 99, 1000]]:
                forest_max = max(i + n for i in range(n + 1))
                result = n + 1 + max(forest_max, max(values, default=0))
                self.assertGreater(result, n)
                for x in values:
                    self.assertGreater(result, x)

if __name__ == "__main__":
    unittest.main(verbosity=2)
