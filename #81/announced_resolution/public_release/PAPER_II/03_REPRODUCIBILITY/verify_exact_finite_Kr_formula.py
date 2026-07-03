#!/usr/bin/env python3
from math import comb, floor, ceil

def formula_nu(p,q,r):
    if p<r-1: return 0.0
    if p==r-1: return 1.0 if q>=1 else 0.0
    P=comb(p,2); m=comb(r,2); c=comb(r-1,2)
    return P/m+(P/c-P/m)*min(1.0,(r-2)*q/(p-1))

def phi(p,q,r):
    return comb(p,2)+p*q-(comb(r,2)-1)*formula_nu(p,q,r)

def exact(n,r):
    ell=min(n,r-2)
    L=ell*(2*n-ell-1)/2
    if n<r: return L
    p0=((r-1)*n+1)/(2*r)
    b=max(r-1,p0)
    C={max(r-1,min(n,floor(b))),max(r-1,min(n,ceil(b)))}
    A=max(phi(p,n-p,r) for p in C)
    return max(L,A)

def main():
    pairs=free=sat=0
    for r in range(3,31):
        for n in range(1,501):
            true=max(phi(p,n-p,r) for p in range(n+1))
            pred=exact(n,r)
            assert abs(true-pred)<1e-9,(r,n,true,pred)
            ell=min(n,r-2); L=ell*(2*n-ell-1)/2
            if abs(pred-L)<1e-9: free+=1
            else: sat+=1
            pairs+=1
    print(f'PASS: exact finite K_r formula on {pairs} (r,n) pairs')
    print(f'Observed winning branches: K_r-free {free}, saturated {sat}')

    tested=0
    for n in range(1,501):
        for p in range(n+1):
            q=n-p
            # q isolated vertices followed by p universal vertices create
            # exactly C(p,2)+pq edges, the complete-split edge count.
            created=sum(q+i for i in range(p))
            expected=comb(p,2)+p*q
            assert created==expected
            tested+=1
    print(f'PASS: threshold creation words for {tested} complete-split graphs')

if __name__=='__main__': main()
