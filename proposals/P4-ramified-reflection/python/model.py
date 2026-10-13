"""Executable small-instance model, not a Lean proof checker.

The mathematical definitions have no resource bounds. This test model refuses
large enumerations, rather than replacing their values with approximations.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from typing import Any, Callable

N = ('N',)
W = ('W',)
def A(a: tuple, b: tuple) -> tuple:
    return ('A', a, b)

def type_depth(a: tuple) -> int:
    return 1 if a[0] != 'A' else 1 + max(type_depth(a[1]), type_depth(a[2]))

@dataclass(frozen=True)
class Term:
    op: str
    args: tuple = ()

def var(i: int) -> Term: return Term('var', (i,))
def lam(a: tuple, b: tuple, body: Term) -> Term: return Term('lam', (a, b, body))
def app(f: Term, x: Term) -> Term: return Term('app', (f, x))
def rec(a: tuple) -> Term: return Term('rec', (a,))
def wrec(a: tuple) -> Term: return Term('wrec', (a,))
def quote(t: Term) -> Term: return Term('quote', (t,))
Z, S, WZ, WS, Q = (Term(k) for k in ('zero','succ','wzero','wsup','oracle'))

@dataclass(eq=False)
class Tree:
    children: Callable[[int], 'Tree'] | None = None

LEAF = Tree()

def tree_fold(z: Any, step: Callable, t: Tree) -> Any:
    if t.children is None:
        return z
    f = t.children
    return step(f)(lambda i: tree_fold(z, step, f(i)))

def default(a: tuple) -> Any:
    if a == N: return 0
    if a == W: return LEAF
    return lambda _: default(a[2])

def cast_pair(a: tuple, b: tuple) -> tuple[Callable, Callable]:
    """The recursive computational casts used by the Coq source."""
    if a == b == N or a == b == W:
        return lambda x: x, lambda x: x
    if a[0] == b[0] == 'A' and a[1] == b[1] and a[2] == b[2]:
        ac, ca = cast_pair(a[1], b[1])
        bd, db = cast_pair(a[2], b[2])
        return (lambda f: lambda x: bd(f(ca(x))),
                lambda f: lambda x: db(f(ac(x))))
    return lambda _: default(b), lambda _: default(a)

def cast(b: tuple, v: tuple[tuple, Any]) -> Any:
    return cast_pair(v[0], b)[0](v[1])

def lookup(env: tuple, i: int) -> Any | None:
    return None if i >= len(env) else env[len(env) - i - 1]

def nat_fold(z: Any, step: Callable, n: int) -> Any:
    if not isinstance(n, int) or n < 0:
        raise ValueError('Nat recursor received a non-natural value')
    if n > 1_000_000:
        raise RuntimeError('Small-instance model refuses this recursion length')
    ans = z
    for i in range(n):
        ans = step(i)(ans)
    return ans

def interpret(t: Term, q: Callable[[int,int],int] = lambda i,n: 0,
              env: tuple = ()) -> tuple[tuple, Any]:
    op, ar = t.op, t.args
    if op == 'var':
        found = lookup(env, ar[0])
        return (N, 0) if found is None else found
    if op == 'lam':
        a,b,body = ar
        return A(a,b), lambda x: cast(b, interpret(body, q, ((a,x),)+env))
    if op == 'app':
        ft,f = interpret(ar[0], q, env)
        xv = interpret(ar[1], q, env)
        return (N,0) if ft[0] != 'A' else (ft[2], f(cast(ft[1], xv)))
    if op == 'zero': return N,0
    if op == 'succ': return A(N,N),lambda x: x+1
    if op == 'wzero': return W,LEAF
    if op == 'wsup': return A(A(N,W),W),lambda f: Tree(f)
    if op == 'oracle': return A(N,A(N,N)),lambda i: lambda n: q(i,n)
    if op == 'rec':
        r, = ar
        return A(r,A(A(N,A(r,r)),A(N,r))), lambda z: lambda s: lambda n: nat_fold(z,s,n)
    if op == 'wrec':
        r, = ar
        return A(r,A(A(A(N,W),A(A(N,r),r)),A(W,r))), lambda z: lambda s: lambda t: tree_fold(z,s,t)
    if op == 'quote': return N,value(ar[0])
    raise ValueError(f'Unknown constructor: {op}')

def value(t: Term, q: Callable[[int,int],int] = lambda i,n: 0) -> int:
    ty,v = interpret(t,q)
    return v if ty == N else 0

def depth(t: Term) -> int:
    op, ar = t.op,t.args
    if op == 'var': return ar[0]+2
    if op == 'lam': return 1+max(type_depth(ar[0]),type_depth(ar[1]),depth(ar[2]))
    if op == 'app': return 1+max(depth(ar[0]),depth(ar[1]))
    if op in ('rec','wrec'): return 1+type_depth(ar[0])
    if op == 'quote': return 1+depth(ar[0])
    return 1

@lru_cache(None)
def types(d: int, extended: bool=False) -> tuple:
    if d < 0: raise ValueError('Negative depth')
    if d == 0: return ()
    if d > 5: raise RuntimeError('Small-instance type-enumeration limit')
    previous = types(d-1,extended)
    return ((N,W) if extended else (N,)) + tuple(A(a,b) for a,b in product(previous, repeat=2))

@lru_cache(None)
def terms(d: int, extended: bool=False) -> tuple[Term,...]:
    if d < 0: raise ValueError('Negative depth')
    if d == 0: return ()
    if d > (3 if extended else 4):
        raise RuntimeError('Refusing infeasible enumeration; no approximate value is returned')
    ts,es = types(d-1,extended),terms(d-1,extended)
    variables = tuple(var(i) for i in range(d-2,-1,-1))
    lambdas = tuple(lam(a,b,t) for a,b,t in product(ts,ts,es))
    applications = tuple(app(f,x) for f,x in product(es,repeat=2))
    recursors = tuple(rec(a) for a in ts)
    if not extended:
        return variables+lambdas+applications+(Z,S)+recursors
    return (es+(Z,S,WZ,WS,Q)+variables+lambdas+applications+recursors+
            tuple(wrec(a) for a in ts)+tuple(quote(t) for t in terms(d-1)))

def scan_best(xs: tuple[Term,...]) -> Term:
    current,best = 0,Z
    for t in xs:
        v = value(t)
        if current < v:
            current,best = v,t
    return best

def unary(n: int) -> Term:
    if n < 0: raise ValueError('Negative numeral')
    t = Z
    for _ in range(n): t=app(S,t)
    return t

def double_at(environment_size: int) -> Term:
    """n |-> 2n, with absolute binder levels adjusted to the environment."""
    if environment_size < 0: raise ValueError('Negative environment size')
    body=app(S,app(S,var(environment_size+1)))
    return app(app(rec(N),Z),lam(N,A(N,N),lam(N,N,body)))

# Closed term denoting n |-> 2n. Its exact upstream depth is 8.
DOUBLE = double_at(0)

# Closed term denoting n |-> 2**n, depth 14. The internal doubling term
# lies below the two outer step binders, so its accumulator is variable 3.
POW2 = app(app(rec(N),app(S,Z)),
           lam(N,A(N,N),lam(N,N,app(double_at(2),var(1)))))

def binary(n: int) -> Term:
    if n < 0: raise ValueError('Negative numeral')
    t=Z
    if n == 0: return t
    for bit in bin(n)[2:]:
        t=app(DOUBLE,t)
        if bit == '1': t=app(S,t)
    return t

def witness(i: int,n: int) -> Term:
    return app(S,app(app(Q,unary(i)),unary(n)))

def binary_witness(i: int,n: int) -> Term:
    return app(S,app(app(Q,binary(i)),binary(n)))

def feedback_witness(n: int) -> Term:
    """Denotes g^[g(n)](n)+1 for g(x)=q(0,x), using no shifted numerals."""
    bn=binary(n)
    length=app(app(Q,Z),bn)
    step_term=lam(N,A(N,N),lam(N,N,app(app(Q,Z),var(1))))
    return app(S,app(app(app(rec(N),bn),step_term),length))

# Higher-type construction: observations of finite branches only, no reflection evaluations.
def iterate(f: Callable, n: int, x: Any) -> Any:
    for _ in range(n): x=f(x)
    return x

def step(a: Tree) -> Tree: return Tree(lambda _: a)

def sup_level(k: int,f: Callable) -> Any:
    return Tree(f) if k == 0 else lambda x: sup_level(k-1,lambda n:f(n)(x))

def omega_level(k: int) -> Callable:
    return lambda f: lambda x: sup_level(k,lambda n:iterate(f,n,x))

def seed(a: Tree,s: Callable,k: int) -> Any:
    return a if k == 0 else s if k == 1 else omega_level(k-2)

def collapse(a: Tree,s: Callable,k: int,x: Any) -> Tree:
    if k == 0: return x
    return collapse(a,s,k-1,x(seed(a,s,k-1)))

def high(a: Tree,s: Callable,k: int) -> Tree:
    return collapse(a,s,k+2,omega_level(k))

def observation(t: Tree,height: int,branches: tuple[int,...]=(0,1)) -> tuple:
    if t.children is None: return ('zero',)
    if height == 0: return ('sup',)
    return ('sup',tuple(observation(t.children(i),height-1,branches) for i in branches))
