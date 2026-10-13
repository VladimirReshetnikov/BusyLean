"""Reproducible finite tests; does not certify Lean elaboration or a giant value."""
import json
import time
from pathlib import Path
from model import *

ROOT=Path(__file__).resolve().parents[1]
checks=0

def check(p: bool, label: str) -> None:
    global checks
    checks += 1
    if not p: raise AssertionError(label)

def main() -> None:
    start=time.perf_counter()
    old_rows=[]
    for d in range(1,5):
        es=terms(d)
        vals=[value(t) for t in es]
        for t in es:
            check(depth(t)<=d,f'legacy depth {d}')
        best=scan_best(es)
        check(best in es,'maxBy witness membership')
        check(value(best)==max([0]+vals),'maxBy/max agreement')
        check(value(app(S,quote(best)))==max(vals)+1,'legacy successor-quotation bridge')
        old_rows.append(dict(depth=d,term_count=len(es),type_count=len(types(d)),maximum=max(vals)))
    new_rows=[]
    qs=[lambda i,n:0,lambda i,n:3*i+n+7,lambda i,n:(17-i-n if i+n<=17 else 0)]
    for d in range(1,4):
        es=terms(d,True)
        for t in es: check(depth(t)<=d,f'extended depth {d}')
        if d>1: check(set(terms(d-1,True))<=set(es),'cumulative inclusion')
        check(all(quote(t) in es for t in terms(d-1)),'quote coverage')
        maxima=[max(value(t,q) for t in es) for q in qs]
        new_rows.append(dict(depth=d,term_count=len(es),type_count=len(types(d,True)),maxima=maxima))
    for i in range(4):
        check(lookup((10,11,12),i)==([12,11,10,None][i]),'binder levels')
    for n in range(129):
        check(value(app(DOUBLE,unary(n)))==2*n,'double')
        check(value(binary(n))==n,'binary numeral')
        check(depth(binary(n))<=8+2*n.bit_length(),'binary depth bound')
    check(depth(DOUBLE)==8,'exact double depth')
    check(depth(POW2)==14,'exact power-of-two depth')
    for n in range(13):
        check(value(app(POW2,binary(n)))==2**n,'power-of-two semantics')
    for n in range(17):
        check(depth(feedback_witness(n))<=max(9,12+2*n.bit_length()),'feedback depth')
        for q in (lambda i,x:0, lambda i,x:x+1, lambda i,x:x+3):
            g=lambda x:q(0,x)
            check(value(feedback_witness(n),q)==iterate(g,g(n),n)+1,'feedback semantics')
    for i in (0,1,63,64,2**27,2**28-1):
        check(depth(binary_witness(i,64))<=68,'large visible-child index budget')
    check(depth(feedback_witness(64))==20,'exact feedback witness at 64')
    for n in range(32,10000):
        check(10+2*n.bit_length()<=n,'explicit diagonal threshold')
        check(max(9,12+2*n.bit_length())<=n+4,'uniform feedback threshold')
        check(1+max(14,8+2*n.bit_length())<=n+4,'uniform exponential lower bound')
    for n in range(11):
        for i in range(n+1):
            check(depth(witness(i,n))<=n+4,'visible-child witness cost')
            for q in qs: check(value(witness(i,n),q)==q(i,n)+1,'visible-child witness semantics')
    for a in (N,W,A(N,N),A(W,N),A(N,A(N,N))):
        v=default(a)
        check(value(app(S,Term('wzero')))==1,'non-numerical default projection')
        for b in (N,W,A(N,N)):
            if a != b:
                out=cast_pair(a,b)[0](v)
                if b==N: check(out==0,'mismatched cast to Nat')
                if b==W: check(out.children is None,'mismatched cast to Tree')
    # The original total semantics does not reject this malformed term.
    check(value(app(S,S))==1,'malformed term is defaulted, not rejected')
    for k in range(5):
        current=high(LEAF,step,k)
        nxt=high(LEAF,step,k+1)
        check(nxt.children is not None,'high-level root')
        check(observation(nxt.children(1),3)==observation(current,3),'adjacent high-level branch-one law')
    for j in range(6):
        h0=high(LEAF,step,0)
        check(observation(h0.children(j),8)==observation(iterate(step,j,LEAF),8),'high-zero law')
    try:
        terms(4,True)
        raise AssertionError('guard did not reject extended depth 4')
    except RuntimeError:
        checks_before=checks
        check(True,'resource guard refuses rather than approximates')
    report=dict(status='passed',assertions=checks,elapsed_seconds=time.perf_counter()-start,
                legacy=old_rows,extended=new_rows,
                scope='Finite Python model only. No Lean kernel or giant numeral evaluated.')
    target=ROOT/'validation'/'python_tests.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__': main()
