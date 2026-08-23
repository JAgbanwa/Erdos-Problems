#!/usr/bin/env python3
"""verify_shifted_center.py  (Paper III, Appendix C.3)
Small binary edge-capacity ILP audit of the shifted-center gain-completion bound
Lemma 7.1 / (7.6): on instances satisfying hypotheses (7.1)-(7.2),
  Phi(G) <= n^2/6 + p/2 - s^2/6 + s*rho - 2 rho^2 + kappa*BR + ((s-2 rho-1)AR - A2R)/q.
Exact integral triangle packings via ILP.
"""
import random
from itertools import combinations
from _common import chi_prime, c2, nu3_exact
def main():
    rng=random.Random(11); out=[]; f=n=skip=0
    for p in [8,9]:
        for rho in [0,1,2]:
            for _ in range(2):
                s=2*rho+3+rng.randint(0,2); q=2*p-s
                R=set(range(rho)); b=p-rho; Ns=[]
                for _ in range(q):
                    Ti=set(rng.sample(range(rho,p),rng.randint(0,1)))
                    inR=set(x for x in R if rng.random()<0.5)
                    Ns.append(set(range(p))-(Ti|inR))
                rb=chi_prime(b); u=q-rb
                ok=(b>=2 and q>=rb and b>=chi_prime(rho))
                tis=[len((set(range(p))-N)-R) for N in Ns]; gis=[len(R-(set(range(p))-N)) for N in Ns]
                if ok:
                    for ti in tis:
                        if b-ti<max(rho,u): ok=False; break
                if not ok: skip+=1; continue
                AR=sum(tis); A2R=sum(t*t for t in tis); BR=sum(gis)
                thet=max(rho-1,0)/b; kap=1-2*(1-thet)*u/q
                E=c2(p)+sum(len(N) for N in Ns); nu=nu3_exact(p,Ns); Phi=E-2*nu; nn=p+q
                bound=nn*nn/6+p/2-s*s/6+s*rho-2*rho*rho+kap*BR+((s-2*rho-1)*AR-A2R)/q; n+=1
                if Phi>bound+1e-9: f+=1; out.append(f"L7.1 FAIL p={p} rho={rho} s={s} Phi={Phi} bound={bound:.3f}")
    out.append(f"Lemma 7.1 (shifted-center gain completion, (7.6)): {n} valid cases ({skip} skipped by hypotheses), {f} violations")
    out.append("RESULT: "+("PASS" if f==0 else "FAIL"))
    print("\n".join(out)); return f==0
if __name__=="__main__": import sys; sys.exit(0 if main() else 1)
