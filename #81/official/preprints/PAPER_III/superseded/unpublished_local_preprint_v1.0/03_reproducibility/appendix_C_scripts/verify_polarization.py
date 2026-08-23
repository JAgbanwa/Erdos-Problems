#!/usr/bin/env python3
"""verify_polarization.py  (Paper III, Appendix C.4)
Exhaustive small-profile and randomized exact-integer checks of Lemma 6.1 (6.2):
  if 2p-3m-1 >= 0 then  V >= (2p-3m-1)/4 * sum_{i,j} |S_i \\triangle S_j|,
where S_i \\subseteq [p] are the deleted-neighborhood sets (m = max_i |S_i|),
and V = sum_{a<b} beta_e (q - beta_e), beta_e = #{ i : edge (a,b) meets S_i }.
Checked as 4V >= (2p-3m-1) * sum|S_i triangle S_j|  (exact integers).
"""
import random
from itertools import combinations, product
def V_and_rhs(p,Ss):
    q=len(Ss); m=max((len(S) for S in Ss), default=0)
    V=0
    for a,b in combinations(range(p),2):
        be=sum(1 for S in Ss if (a in S or b in S))
        V+=be*(q-be)
    tot=sum(len(Ss[i]^Ss[j]) for i in range(q) for j in range(q))
    return V,(2*p-3*m-1),tot
def check(p,Ss):
    V,coef,tot=V_and_rhs(p,Ss)
    if coef<0: return True
    return 4*V>=coef*tot
def main():
    n=0; f=0
    # exhaustive tiny: p<=4, all families of q in {2,3} profiles with |S|<=2
    for p in range(3,5):
        subs=[set(c) for r in range(0,3) for c in combinations(range(p),r)]
        for q in (2,3):
            for fam in product(subs,repeat=q):
                n+=1
                if not check(p,list(fam)): f+=1
    # randomized larger
    rng=random.Random(3)
    for _ in range(20000):
        p=rng.randint(3,9); m=rng.randint(0,p); q=rng.randint(2,6)
        Ss=[set(rng.sample(range(p),rng.randint(0,m))) for _ in range(q)]
        n+=1
        if not check(p,Ss): f+=1
    print(f"verify_polarization: Lemma 6.1 (6.2)")
    print(f"  cases checked : {n} (exhaustive p<=4 + 20000 randomized, exact integers)")
    print(f"  violations    : {f}")
    print("  RESULT        :", "PASS" if f==0 else "FAIL")
    return f==0
if __name__=="__main__": import sys; sys.exit(0 if main() else 1)
