#!/usr/bin/env python3
"""Deterministic exact finite tests; outputs JSON, never evaluates contender_7."""
from __future__ import annotations
import json
from pathlib import Path
from reference import *

ROOT = Path(__file__).resolve().parents[1]
results = {}
counts = []
for d in range(5):
    ts, es = all_types(d), all_terms(d)
    assert all(type_rank(t) <= d for t in ts)
    assert all(term_rank(t) <= d for t in es)
    assert len(set(ts)) == len(ts) and len(set(es)) == len(es)
    if d:
        assert set(all_types(d - 1)) <= set(ts)
        assert set(all_terms(d - 1)) <= set(es)
    counts.append({'depth': d, 'types': len(ts), 'terms': len(es)})
results['enumeration'] = counts
results['compiler_ranks'] = [type_rank(TREE), term_rank(INDEX_PROGRAM),
                             term_rank(NUMBER_PROGRAM), term_rank(BOOST_PROGRAM)]
assert results['compiler_ranks'] == [2, 14, 16, 17]
cert = rank_certificate(BOOST_PROGRAM, 17)
(ROOT / 'evidence' / 'comparison_rank_certificate.json').write_text(json.dumps(cert, indent=2))

checks = 0
for phase in range(5):
    g = lambda k, phase=phase: lambda i: finite_tree((k + 2 * i + phase) % 4, phase)
    for offset in range(4):
        s = lambda i, offset=offset: lambda x: 2 * x + i + offset
        for n in range(8):
            for oracle_offset in range(3):
                fs = lambda i, off=oracle_offset: lambda x: off + i + 3 * x
                def h(seed, phase=phase, offset=offset):
                    def on_tree(t):
                        def on_input(x):
                            shape = path_signature(t, [x % 3, (x + 1) % 4, 0, 1, 2])
                            return ((phase + 1) * seed(x % 2)(x + 1) + (offset + 1) * x
                                    + sum((i+1)*b for i,b in enumerate(shape)))
                        return on_input
                    return on_tree
                amplifier = lambda x, p=phase, o=offset: (p + 1) * x * x + o + 7
                env = environment(h, g, s, n, amplifier, fs)
                idx = Tree(lambda k: Tree(lambda i: g(k)(i)))
                want = amplifier(h(s)(idx)(n))
                assert numeric(env, BOOST_PROGRAM) == want
                iv = interpret(env, INDEX_PROGRAM)
                assert iv.ty == TREE
                for p in ([0, 0, 0], [1, 2, 3, 0], [2, 3, 1, 2, 0]):
                    assert path_signature(iv.value, p) == path_signature(idx, p)
                checks += 1
results['generic_compiler_environment_cases'] = checks
results['sampled_tree_paths_per_case'] = 3

cast_checks = 0
for height in range(6):
    t = finite_tree(height)
    t2 = cast(Value(TREE, t), TREE)
    for p in ([0], [1, 1, 1], [2, 2, 1, 1, 1, 1], [3, 2, 1, 0]):
        assert path_signature(t, p) == path_signature(t2, p)
        cast_checks += 1
results['w_cast_identity_path_tests'] = cast_checks

# Exact program-level counterexample; this does NOT prove nonmonotonicity
# of a maximum over all programs.
one = app(('succ',), ('zero',))
step = ('lam', N, UNARY, ('lam', N, N, ('zero',)))
oracle_input = app(app(var(0), ('zero',)), ('zero',))
zero_test = app(app(app(('natrec', N), one), step), oracle_input)
f0 = lambda i: lambda n: 0
f1 = lambda i: lambda n: 1
out0 = numeric((Value(FAMILY, f0),), zero_test)
out1 = numeric((Value(FAMILY, f1),), zero_test)
assert (out0, out1) == (1, 0)
results['program_nonmonotonicity'] = {'smaller_oracle_output': out0,
    'larger_oracle_output': out1, 'claim_scope': 'one program, not the full maximum'}

assert [boost(i) for i in range(3)] == [3, 18, (1 << 256) + 3]
results['boost_small_values'] = [str(boost(i)) for i in range(3)]
checks = 0
for h in range(4):
    for k in range(h, 4):
        for a in range(4):
            for b in range(a, 4):
                try: lhs, rhs = tower(h, a), tower(k, b)
                except OverflowError: continue
                assert lhs <= rhs
                checks += 1
results['bounded_tower_monotonicity_tests'] = checks

# Exact original family at input zero: no nonzero-depth terms are generated.
def reflect_at_zero(fs):
    def value(n):
        assert n == 0
        return 1 + fs(0)(0)
    return value

def walk(r, s, tree):
    if tree.children is None: return r(s)
    return r(lambda i: walk(r, s, tree.children(i)))
old_index_at_zero = Tree(lambda k: Tree(lambda i: LEAF) if k == 0 else LEAF)
assert walk(reflect_at_zero, f0, old_index_at_zero)(0) == 3
results['original_finalFamily_zero'] = 3
results['submitted_number_evaluated'] = False
results['full_rank_17_enumeration_materialized'] = False
results['lean_kernel_verification'] = 'not performed by this Python test'
results['status'] = 'PASS'
(ROOT / 'evidence' / 'python_tests.json').write_text(json.dumps(results, indent=2) + '\n')
print(json.dumps(results, indent=2))
