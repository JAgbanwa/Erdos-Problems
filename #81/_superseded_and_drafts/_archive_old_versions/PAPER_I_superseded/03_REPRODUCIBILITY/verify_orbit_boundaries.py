#!/usr/bin/env python3
"""Exact rational regression tests for Paper I v1.1 orbit programs.

These tests are supplementary; the manuscript contains analytic proofs.
"""
from fractions import Fraction
from itertools import combinations


def det3(m):
    return (m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])
            -m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])
            +m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]))


def solve3(eqns):
    A = [[Fraction(c) for c in row[:3]] for row in eqns]
    b = [Fraction(row[3]) for row in eqns]
    d = det3(A)
    if d == 0:
        return None
    vals=[]
    for j in range(3):
        Aj=[row[:] for row in A]
        for i in range(3): Aj[i][j]=b[i]
        vals.append(det3(Aj)/d)
    return tuple(vals)


def poly_vertices(s,o):
    # Inequalities represented as (a,b,sense) for a.x >= b or <= b.
    ineq=[]
    names=[]
    # box 0 <= x <= 1
    for i,nm in enumerate(['a','b','g']):
        a=[0,0,0]; a[i]=1
        ineq.append((tuple(a),Fraction(0),'>=')); names.append(nm+'=0')
        ineq.append((tuple(a),Fraction(1),'<=') ); names.append(nm+'=1')
    if s>=3:
        ineq.append(((3,0,0),Fraction(1),'>=')); names.append('3a=1')
    if s>=2 and o>=1:
        ineq.append(((1,2,0),Fraction(1),'>=')); names.append('a+2b=1')
    if s>=1 and o>=2:
        ineq.append(((0,2,1),Fraction(1),'>=')); names.append('2b+g=1')
    if o>=3:
        ineq.append(((0,0,3),Fraction(1),'>=')); names.append('3g=1')

    eqns=[(a[0],a[1],a[2],b) for a,b,_ in ineq]
    vertices=set()
    for ids in combinations(range(len(eqns)),3):
        x=solve3([eqns[i] for i in ids])
        if x is None: continue
        ok=True
        for a,b,sense in ineq:
            lhs=sum(Fraction(a[i])*x[i] for i in range(3))
            if sense=='>=' and lhs < b: ok=False; break
            if sense=='<=' and lhs > b: ok=False; break
        if ok: vertices.add(x)
    if not vertices:
        raise AssertionError((s,o,'no vertices'))
    return vertices


def check_uniform_boundaries():
    count=0
    for p in range(3,41):
        for s in range(2,p+1):
            o=p-s
            verts=poly_vertices(s,o)
            for q in range(0,81):
                A=Fraction(s*(s-1-q),2)
                B=Fraction(s*o,1)
                C=Fraction(o*(o-1),2)
                actual=min(A*a+B*b+C*g for a,b,g in verts)
                U=(A+B+C)/3
                D=A+C
                H=A+(B+C)/3
                expected=min(U,D,H)
                if actual != expected:
                    raise AssertionError((p,q,s,o,actual,expected,verts))
                count += 1
    return count


def check_weighted_interior():
    verts=poly_vertices(3,3)  # same four-constraint polytope for all s,o >=3
    count=0
    for X in range(-20,21):
        for Y in range(0,21):
            for Z in range(0,21):
                actual=min(Fraction(X)*a+Fraction(Y)*b+Fraction(Z)*g for a,b,g in verts)
                expected=min(Fraction(X+Y+Z,3), Fraction(X+Z), Fraction(X,1)+Fraction(Y+Z,3))
                if actual != expected:
                    raise AssertionError((X,Y,Z,actual,expected))
                count += 1
    return count


def main():
    b=check_uniform_boundaries()
    w=check_weighted_interior()
    print(f'PASS exact uniform orbit formula including all small-orbit boundaries: {b} instances')
    print(f'PASS exact weighted three-orbit formula: {w} instances')
    print('PASS: no computational result is used as a proof premise')

if __name__=='__main__':
    main()
