#!/usr/bin/env python3
"""verify_factor_rounding.py  (Paper III, Appendix C.3)
Small binary edge-capacity ILP audit of the averaged / double-factor rounding lemmas:
 - Lemma 5.1 (averaged factorization):  nu3(G) >= (1/q) * sum_i C(|N_i|,2).
 - Lemma 5.2 (double-factor inequality), bound (5.4):
     Phi(G) = |E|-2 nu3 <= n^2/6 + p/2 - s^2/6 + ((s-1)M - S2)/q - 2*delta*V/(q(q-1)).
Exact integral triangle packings via ILP; profiles are randomized dense residuals.
"""
import random
from itertools import combinations
from _common import chi_prime, c2, nu3_exact
def main():
    rng=random.Random(7); out=[]
    # Lemma 5.1
    f=n=0
    for p in [6,7,8]:
        rp=chi_prime(p)
        for _ in range(2):
            q=rp+rng.randint(0,3)
            Ns=[set(rng.sample(range(p),rng.randint(max(2,p-3),p))) for _ in range(q)]
            lb=sum(c2(len(N)) for N in Ns)/q; nu=nu3_exact(p,Ns); n+=1
            if nu<lb-1e-9: f+=1; out.append(f"L5.1 FAIL p={p} q={q} nu={nu} lb={lb:.3f}")
    out.append(f"Lemma 5.1 (averaged factorization): {n} cases, {f} violations")
    # Lemma 5.2 / (5.4)
    f=n=0
    for p in [6,7]:
        rp=chi_prime(p)
        for s in [1,2,3]:
            q=2*p-s
            if q<rp: continue
            for _ in range(2):
                Ns=[set(range(p))-set(rng.sample(range(p),rng.randint(0,min(2,s)))) for _ in range(q)]
                M=sum(p-len(N) for N in Ns); S2=sum((p-len(N))**2 for N in Ns)
                h=min(rp,q-rp); delta=h/rp
                V=sum((lambda be:be*(q-be))(sum(1 for N in Ns if not(a in N and b in N))) for a,b in combinations(range(p),2))
                E=c2(p)+sum(len(N) for N in Ns); nu=nu3_exact(p,Ns); Phi=E-2*nu; nn=p+q
                bound=nn*nn/6+p/2-s*s/6+((s-1)*M-S2)/q-2*delta*V/(q*(q-1)); n+=1
                if Phi>bound+1e-9: f+=1; out.append(f"L5.2 FAIL p={p} s={s} Phi={Phi} bound={bound:.3f}")
    out.append(f"Lemma 5.2 (double-factor inequality, (5.4)): {n} cases, {f} violations")
    ok=all("FAIL" not in l for l in out)
    out.append("RESULT: "+("PASS" if ok else "FAIL"))
    print("\n".join(out)); return ok
if __name__=="__main__": import sys; sys.exit(0 if main() else 1)
