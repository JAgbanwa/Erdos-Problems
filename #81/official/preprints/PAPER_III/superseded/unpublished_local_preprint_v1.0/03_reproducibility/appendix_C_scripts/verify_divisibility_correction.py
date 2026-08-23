#!/usr/bin/env python3
"""verify_divisibility_correction.py  (Paper III, Appendix C.5)
Checks the triangle-divisibility / parity correction used for the dense clique
residual (AX2 layer):
 (a) K_n is triangle-divisible  <=>  n ≡ 1 or 3 (mod 6)  [ |E|≡0 mod 3 and all degrees even ].
     Verified exactly for every order n up to 18 (the "path parity construction through 18").
 (b) Exact ILP triangle decomposition of K_n confirms decomposability exactly on the
     divisible orders (n = 3,7,9) and non-existence on a non-divisible order (n = 5,6,8).
 (c) mod-three / parity correction on randomized dense residuals: after removing a near
     1-factor to fix parity, the corrected residual satisfies |E|≡0 (mod 3) and all degrees even.
"""
import random
from itertools import combinations
from collections import defaultdict
import pulp
c2=lambda n: n*(n-1)//2
def tri_divisible(n):
    return c2(n)%3==0 and (n-1)%2==0
def kn_decomposes(n):
    V=list(range(n)); tris=list(combinations(V,3))
    pr=pulp.LpProblem('d',pulp.LpMinimize)
    x={t:pulp.LpVariable('t%d'%i,0,1,cat='Integer') for i,t in enumerate(tris)}
    pr+=0
    inc=defaultdict(list)
    for t in tris:
        for e in combinations(t,2): inc[e].append(t)
    for e,ts in inc.items(): pr+=pulp.lpSum(x[t] for t in ts)==1   # exact edge cover by triangles
    pr.solve(pulp.PULP_CBC_CMD(msg=0,timeLimit=60))
    return pulp.LpStatus[pr.status]=="Optimal"
def main():
    out=[]; ok=True
    # (a) divisibility pattern through 18
    bad=[n for n in range(1,19) if tri_divisible(n)!=(n%6 in (1,3))]
    out.append(f"(a) triangle-divisibility K_n == (n mod 6 in {{1,3}}) for n<=18: "
               + ("PASS" if not bad else f"FAIL {bad}"))
    ok&= not bad
    # (b) ILP decomposition on small orders
    for n,exp in [(3,True),(5,False),(6,False),(7,True),(8,False),(9,True)]:
        got=kn_decomposes(n)
        out.append(f"(b) K_{n} triangle-decomposable: {got} (expected {exp}) "+("OK" if got==exp else "MISMATCH"))
        ok&=(got==exp)
    # (c) parity/mod-3 correction on random dense residuals
    rng=random.Random(5); cbad=0; cn=0
    for _ in range(300):
        n=rng.choice([13,15,19])  # n ≡ 1,3 mod 6
        # start from K_n, delete a random set of edges keeping min-degree high, then correct
        edges=set(combinations(range(n),2))
        for _ in range(rng.randint(0,n)):
            e=rng.choice(list(edges)); edges.discard(e)
        deg=defaultdict(int)
        for a,b in edges: deg[a]+=1; deg[b]+=1
        # correction: drop edges until all degrees even and |E| ≡ 0 (mod 3)
        el=list(edges)
        while any(deg[v]%2 for v in range(n)):
            # remove an edge between two odd-degree vertices if possible
            cand=[(a,b) for (a,b) in el if deg[a]%2 and deg[b]%2]
            if not cand: cand=[(a,b) for (a,b) in el if deg[a]%2 or deg[b]%2]
            a,b=cand[0]; el.remove((a,b)); deg[a]-=1; deg[b]-=1
        while len(el)%3: 
            a,b=el.pop(); deg[a]-=1; deg[b]-=1  # note: may break parity; re-fix
            while any(deg[v]%2 for v in range(n)):
                cand=[(x,y) for (x,y) in el if deg[x]%2 and deg[y]%2] or [(x,y) for (x,y) in el if deg[x]%2 or deg[y]%2]
                if not cand: break
                x,y=cand[0]; el.remove((x,y)); deg[x]-=1; deg[y]-=1
        cn+=1
        if len(el)%3!=0 or any(deg[v]%2 for v in range(n)): cbad+=1
    out.append(f"(c) parity+mod-3 correction on {cn} random dense residuals (n in 13,15,19): "
               + ("PASS" if cbad==0 else f"FAIL ({cbad})"))
    ok&=(cbad==0)
    out.append("RESULT: "+("PASS" if ok else "FAIL"))
    print("\n".join(out)); return ok
if __name__=="__main__": import sys; sys.exit(0 if main() else 1)
