#!/usr/bin/env python3
"""verify_fractional_margin.py  (Paper III, Appendix C.2)
Exact-rational check of Theorem 4.2 (uniform fractional margin) over the corridor
    3 <= p <= 80,  1 <= q <= 2p,  0 <= d <= p.
For the common-profile value F(p,q,d) = min of the three branches of Theorem 3.1,
verifies  F(p,q,d) >= q*d/2 + (C_a + mu)*p^2 - p/2,  with
    alpha = q/p,  C_a = (2 - 2*alpha - alpha^2)/12,
    mu = alpha^2/12          if alpha <= 2/3
       = (2 - alpha)^2/48     otherwise.
No solver, no floating point: everything is exact (fractions.Fraction).
"""
from fractions import Fraction as Fr
def c2(x): return x*(x-1)//2
def F_formula(p,q,d):
    r=p-d
    return min(Fr(c2(p)+q*d,3), Fr(c2(d)+c2(r)), Fr(c2(d))+Fr(d*r+c2(r),3))
def margin_rhs(p,q,d):
    al=Fr(q,p)
    Ca=(2-2*al-al*al)/12
    mu=al*al/12 if al<=Fr(2,3) else (2-al)**2/48
    return Fr(q*d,2)+(Ca+mu)*p*p-Fr(p,2)
def main():
    n=0; fails=0; worst=None
    for p in range(3,81):
        for q in range(1,2*p+1):
            for d in range(0,p+1):
                n+=1
                slack=F_formula(p,q,d)-margin_rhs(p,q,d)
                if slack<0:
                    fails+=1
                    if worst is None or slack<worst[0]: worst=(slack,p,q,d)
    print(f"verify_fractional_margin: Theorem 4.2 over 3<=p<=80, 1<=q<=2p, 0<=d<=p")
    print(f"  cases checked : {n}")
    print(f"  violations    : {fails}")
    if worst: print(f"  min slack     : {worst[0]} at (p,q,d)={worst[1:]}")
    print("  RESULT        :", "PASS" if fails==0 else "FAIL")
    return fails==0
if __name__=="__main__": import sys; sys.exit(0 if main() else 1)
