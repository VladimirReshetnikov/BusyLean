"""Independent finite tests of the raw interpreter and comparison compiler.

This is NOT an evaluator for the submitted large number. Concrete tests use
small total semantic libraries and never enumerate allTerms at rank 17.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Any, Callable, Iterable

Ty = tuple
Term = tuple
N: Ty = ('nat',)
def arr(a: Ty, b: Ty) -> Ty: return ('arr', a, b)
def wt(a: Ty) -> Ty: return ('wt', a)
TREE = wt(N)
UNARY = arr(N, N)
FAMILY = arr(N, UNARY)
GENERATOR = arr(N, arr(N, TREE))
HIERARCHY = arr(FAMILY, arr(TREE, UNARY))

@dataclass(frozen=True)
class Tree:
    children: Callable[[Any], 'Tree'] | None = None

LEAF = Tree()
@dataclass(frozen=True)
class Value:
    ty: Ty
    value: Any

def wmap(g: Callable, tree: Tree) -> Tree:
    if tree.children is None:
        return LEAF
    return Tree(lambda b: wmap(g, tree.children(g(b))))

def wfold(z: Any, step: Callable, tree: Tree) -> Any:
    if tree.children is None:
        return z
    return step(tree.children)(lambda a: wfold(z, step, tree.children(a)))

def default(a: Ty) -> Any:
    if a[0] == 'nat': return 0
    if a[0] == 'arr': return lambda _: default(a[2])
    if a[0] == 'wt': return LEAF
    raise ValueError(f'Invalid type: {a!r}')

def cast_pair(a: Ty, b: Ty) -> tuple[Callable, Callable]:
    if a[0] == b[0] == 'nat':
        return (lambda x: x), (lambda x: x)
    if a[0] == b[0] == 'arr' and a == b:
        ac, ca = cast_pair(a[1], b[1])
        bd, db = cast_pair(a[2], b[2])
        return (lambda f: lambda x: bd(f(ca(x)))), (lambda f: lambda x: db(f(ac(x))))
    if a[0] == b[0] == 'wt' and a[1] == b[1]:
        ab, ba = cast_pair(a[1], b[1])
        return (lambda t: wmap(ba, t)), (lambda t: wmap(ab, t))
    return (lambda _: default(b)), (lambda _: default(a))

def cast(v: Value, target: Ty) -> Any:
    return cast_pair(v.ty, target)[0](v.value)

def natrec(z: Any, step: Callable, n: int) -> Any:
    if n < 0: raise ValueError('Natural number required')
    acc = z
    for i in range(n): acc = step(i)(acc)
    return acc

def interpret(env: tuple[Value, ...], t: Term) -> Value:
    """Faithful oldest-first levels; newest binding is stored at env[0]."""
    tag = t[0]
    if tag == 'var':
        i = t[1]
        return env[len(env) - (i + 1)] if i < len(env) else Value(N, 0)
    if tag == 'lam':
        _, a, b, body = t
        return Value(arr(a, b), lambda x: cast(interpret((Value(a, x),) + env, body), b))
    if tag == 'app':
        f, x = interpret(env, t[1]), interpret(env, t[2])
        if f.ty[0] != 'arr': return Value(N, 0)
        return Value(f.ty[2], f.value(cast(x, f.ty[1])))
    if tag == 'zero': return Value(N, 0)
    if tag == 'succ': return Value(UNARY, lambda x: x + 1)
    if tag == 'natrec':
        r = t[1]
        return Value(arr(r, arr(arr(N, arr(r, r)), arr(N, r))),
                     lambda z: lambda s: lambda n: natrec(z, s, n))
    if tag == 'wzero': return Value(wt(t[1]), LEAF)
    if tag == 'wnode':
        a = t[1]
        return Value(arr(arr(a, wt(a)), wt(a)), lambda f: Tree(f))
    if tag == 'wrec':
        a, r = t[1:]
        rt = arr(r, arr(arr(arr(a, wt(a)), arr(arr(a, r), r)), arr(wt(a), r)))
        return Value(rt, lambda z: lambda s: lambda w: wfold(z, s, w))
    raise ValueError(f'Invalid term: {t!r}')

def numeric(env: tuple[Value, ...], t: Term) -> int:
    v = interpret(env, t)
    return v.value if v.ty == N else 0

def type_rank(a: Ty) -> int:
    if a[0] == 'nat': return 1
    if a[0] == 'arr': return max(type_rank(a[1]), type_rank(a[2])) + 1
    return type_rank(a[1]) + 1

def term_rank(t: Term) -> int:
    tag = t[0]
    if tag == 'var': return t[1] + 2
    if tag == 'lam': return max(type_rank(t[1]), type_rank(t[2]), term_rank(t[3])) + 1
    if tag == 'app': return max(term_rank(t[1]), term_rank(t[2])) + 1
    if tag in ('zero', 'succ'): return 1
    if tag in ('natrec', 'wzero', 'wnode'): return type_rank(t[1]) + 1
    if tag == 'wrec': return max(type_rank(t[1]), type_rank(t[2])) + 1
    raise ValueError(tag)

def all_types(d: int) -> list[Ty]:
    if not 0 <= d <= 4:
        raise ValueError('Test enumerator is intentionally restricted to depths 0--4')
    if d == 0: return []
    ts = all_types(d - 1)
    return [N] + [arr(a, b) for a in ts for b in ts] + [wt(a) for a in ts]

def all_terms(d: int) -> list[Term]:
    if not 0 <= d <= 4:
        raise ValueError('Test enumerator is intentionally restricted to depths 0--4')
    if d == 0: return []
    ts, es = all_types(d - 1), all_terms(d - 1)
    return ([('var', i) for i in reversed(range(d - 1))]
            + [('lam', a, b, e) for a in ts for b in ts for e in es]
            + [('app', e, f) for e in es for f in es]
            + [('zero',), ('succ',)]
            + [('natrec', a) for a in ts]
            + [('wzero', a) for a in ts]
            + [('wnode', a) for a in ts]
            + [('wrec', a, b) for a in ts for b in ts])

def app(f: Term, x: Term) -> Term: return ('app', f, x)
def var(i: int) -> Term: return ('var', i)
INDEX_PROGRAM = app(('wnode', N),
    ('lam', N, TREE, app(('wnode', N),
      ('lam', N, TREE, app(app(var(1), var(6)), var(7))))))
NUMBER_PROGRAM = app(app(app(var(0), var(2)), INDEX_PROGRAM), var(3))
BOOST_PROGRAM = app(var(4), NUMBER_PROGRAM)

def environment(h: Callable, g: Callable, s: Callable, n: int,
                amplifier: Callable, fs: Callable) -> tuple[Value, ...]:
    return (Value(FAMILY, fs), Value(UNARY, amplifier), Value(N, n),
            Value(FAMILY, s), Value(GENERATOR, g), Value(HIERARCHY, h))

def path_signature(tree: Tree, path: Iterable[int]) -> tuple[int, ...]:
    out = []
    for i in path:
        out.append(0 if tree.children is None else 1)
        if tree.children is None: break
        tree = tree.children(i)
    out.append(0 if tree.children is None else 1)
    return tuple(out)

def finite_tree(height: int, phase: int = 0) -> Tree:
    if height == 0: return LEAF
    return Tree(lambda i: finite_tree((height - 1) if (i + phase) % 3 else 0, phase + 1))

def tower(height: int, top: int, bit_limit: int = 4096) -> int:
    out = top
    for _ in range(height):
        if out > bit_limit: raise OverflowError('test-only bit limit')
        out = 1 << out
    return out

def boost(x: int) -> int:
    return x + 1 + tower(x + 1, x + 1)

def rank_certificate(t: Term, depth: int) -> dict:
    """Checks the actual enumeration production rules without building its list."""
    if depth <= 0: raise AssertionError('No production exists at depth zero')
    tag = t[0]
    children = []
    if tag == 'var': assert t[1] < depth - 1
    elif tag == 'lam':
        assert type_rank(t[1]) <= depth - 1 and type_rank(t[2]) <= depth - 1
        children.append(rank_certificate(t[3], depth - 1))
    elif tag == 'app':
        children.extend(rank_certificate(u, depth - 1) for u in t[1:])
    elif tag in ('natrec', 'wzero', 'wnode'): assert type_rank(t[1]) <= depth - 1
    elif tag == 'wrec': assert max(map(type_rank, t[1:])) <= depth - 1
    elif tag not in ('zero', 'succ'): raise AssertionError(tag)
    assert term_rank(t) <= depth
    return {'constructor': tag, 'available_depth': depth,
            'required_rank': term_rank(t), 'children': children}
