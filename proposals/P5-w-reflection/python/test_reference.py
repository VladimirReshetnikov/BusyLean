"""Run with: python python/test_reference.py [--json PATH]."""
from __future__ import annotations
import argparse
import json
import platform
import time
import unittest
from pathlib import Path
from reference_model import *

RESULTS: dict = {}

class SemanticsTests(unittest.TestCase):
    def test_01_lookup_and_errors(self):
        env = ((N, 10), (N, 11), (N, 12))
        self.assertEqual([interpret(env, ('var', i), Budget())[1] for i in range(4)],
                         [12, 11, 10, 0])
        self.assertEqual(evaluate(App(Z, S)), 0)
        # Applying successor to an arrow silently casts that argument to zero.
        self.assertEqual(evaluate(App(S, S)), 1)
        self.assertEqual(evaluate(('lam', N, N, S)), 0)

    def test_02_finite_enumeration(self):
        rows = []
        for d in range(5):
            for extended in (False, True):
                es, ts = terms(d, extended), types(d, extended)
                self.assertEqual(len(set(es)), len(es))
                self.assertEqual(len(set(ts)), len(ts))
                self.assertTrue(all(term_depth(t) <= d for t in es))
                self.assertTrue(all(type_depth(t) <= d for t in ts))
                if d:
                    self.assertTrue(set(terms(d-1, extended)).issubset(es))
                if extended:
                    self.assertTrue(set(terms(d, False)).issubset(es))
                score, best = scan_maxby(es)
                self.assertEqual(evaluate(best), score)
                self.assertEqual(max((evaluate(t) for t in es), default=0), score)
                rows.append({'depth': d, 'language': 'W' if extended else 'T',
                             'types': len(ts), 'terms': len(es), 'maximum': score})
        RESULTS['enumeration'] = rows

    def test_03_binary_numerals(self):
        self.assertEqual(term_depth(DOUBLE), 11)
        for n in range(257):
            self.assertEqual(evaluate(App(DOUBLE, binary_numeral(n))), 2*n)
            self.assertEqual(evaluate(binary_numeral(n)), n)
            self.assertLessEqual(term_depth(binary_numeral(n)), 11+2*n.bit_length())
            if n >= 32:
                self.assertLessEqual(term_depth(binary_numeral(n))+1, n)
        RESULTS['binary_numerals_checked'] = [0, 256]
        RESULTS['double_depth'] = term_depth(DOUBLE)

    def test_04_tree_recursion(self):
        tree = LEAF
        for k in range(31):
            b = Budget()
            depth = tree_rec(0, lambda f: lambda ih: ih(0)+1, tree, b)
            self.assertEqual(depth, k)
            casted = cast_pair(WT(N), WT(N), b)[0](tree)
            self.assertEqual(tree_rec(0, lambda f: lambda ih: ih(0)+1, casted, b), k)
            child = tree
            tree = Tree(lambda _, child=child: child)
        # W(N -> N): genuinely function-indexed branching, not just Nat-indexed.
        w = Tree(lambda f: LEAF if f(0) == 0 else Tree(lambda _: LEAF))
        self.assertEqual(tree_rec(0, lambda f: lambda ih: ih(lambda _: 1)+1,
                                 w, Budget()), 2)

    def test_05_rows(self):
        for n in range(7):
            f = lambda x: x + 1
            self.assertEqual(row(f, 1, n, Budget()), 3*n+4)
            self.assertEqual(row(f, 2, n, Budget()), 3**(n+1)*(n+3)+3*n+3)
        RESULTS['row_identities_checked'] = {'ranks': [1, 2], 'inputs': [0, 6]}

    def test_06_guards(self):
        with self.assertRaises(ValueError):
            terms(42)
        with self.assertRaises(BudgetExceeded):
            iterate(lambda x: x+1, 100, 0, Budget(remaining=10))

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--json', type=Path)
    args = p.parse_args()
    start = time.perf_counter()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(SemanticsTests)
    run = unittest.TextTestRunner(verbosity=2).run(suite)
    RESULTS.update({'tests_run': run.testsRun, 'failures': len(run.failures),
                    'errors': len(run.errors), 'successful': run.wasSuccessful(),
                    'elapsed_seconds': time.perf_counter()-start,
                    'python': platform.python_version(),
                    'scope': 'finite Python regression tests; not Lean kernel verification'})
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(RESULTS, indent=2)+'\n')
    raise SystemExit(0 if run.wasSuccessful() else 1)
