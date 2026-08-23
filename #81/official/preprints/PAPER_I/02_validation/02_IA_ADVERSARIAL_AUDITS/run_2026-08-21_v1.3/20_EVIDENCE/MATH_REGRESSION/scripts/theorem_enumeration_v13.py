#!/usr/bin/env python3
"""RESIDUAL AUDIT, PAPER_I v1.3: direct falsification of Theorem 1.1 on enumerated
split graphs, rerun against the v1.3 statement (unchanged from v1.2 per the diff).
nu_3^* by exact rational simplex (Bland). Deterministic, no seeds."""
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement
import json, sys

def simplex_max(A,b,c):
    m,n=len(A),len(c)
    T=[[F(v) for v in A[i]]+[F(1) if j==i else F(0) for j in range(m)]+[F(b[i])] for i in range(m)]
    obj=[-F(v) for v in c]+[F(0)]*m+[F(0)]; basis=list(range(n,n+m)); N=n+m
    while True:
        e=next((j for j in range(N) if obj[j]<0),None)
        if e is None: return obj[N]
        piv=best=None
        for i in range(m):
            if T[i][e]>0:
                r=T[i][N]/T[i][e]
                if best is None or r<best or (r==best and basis[i]<basis[piv]): best,piv=r,i
        if piv is None: return None
        pv=T[piv][e]; T[piv]=[x/pv for x in T[piv]]
        for i in range(m):
            if i!=piv and T[i][e]!=0:
                f=T[i][e]; T[i]=[T[i][k]-f*T[piv][k] for k in range(N+1)]
        if obj[e]!=0:
            f=obj[e]; obj=[obj[k]-f*T[piv][k] for k in range(N+1)]
        basis[piv]=e

def nu3(n,E):
    es=sorted(E)
    if not es: return F(0)
    ei={e:i for i,e in enumerate(es)}
    tr=[(a,b,c) for a,b,c in combinations(range(n),3) if (a,b) in ei and (a,c) in ei and (b,c) in ei]
    if not tr: return F(0)
    A=[[0]*len(tr) for _ in es]
    for tj,(a,b,c) in enumerate(tr):
        for e in ((a,b),(a,c),(b,c)): A[ei[e]][tj]=1
    return simplex_max(A,[1]*len(es),[1]*len(tr))

def build(p,nb):
    n=p+len(nb); E=set()
    for a,b in combinations(range(p),2): E.add((a,b))
    for i,S in enumerate(nb):
        v=p+i
        for u in S: E.add((min(u,v),max(u,v)))
    return n,E

PMAX=int(sys.argv[1]); IMAX=int(sys.argv[2])
viol=[]; tested=0; worst=None; cs=[]
for p in range(0,PMAX+1):
    subs=[frozenset(s) for k in range(0,p+1) for s in combinations(range(p),k)]
    for ni in range(0,IMAX+1):
        for combo in combinations_with_replacement(subs,ni):
            n,E=build(p,combo)
            if n==0: continue
            tested+=1
            nu=nu3(n,E); lhs=F(len(E))-2*nu; rhs=F(n*n,6)+F(n,2); sl=rhs-lhs
            if sl<0: viol.append({"p":p,"n":n,"lhs":str(lhs),"rhs":str(rhs)})
            if worst is None or sl<worst[0]: worst=(sl,{"p":p,"n":n,"E":len(E),"nu":str(nu)})
for p in range(2,9):
    K=frozenset(range(p)); n,E=build(p,[K]*(2*p)); nu=nu3(n,E)
    cs.append({"p":p,"n":n,"nu3star":str(nu),"eq_binom":nu==F(p*(p-1),2),
               "lhs":str(F(len(E))-2*nu),"n2_6_plus_n_6":str(F(n*n,6)+F(n,6)),
               "match":(F(len(E))-2*nu)==F(n*n,6)+F(n,6),
               "satisfies_thm":(F(len(E))-2*nu)<=F(n*n,6)+F(n,2)})
print(json.dumps({"spec":"RESIDUAL_AUDIT_REQUEST_SPEC.md","target":"preprint_draft_v1.3",
 "claim":"|E(G)| - 2 nu_3^*(G) <= n^2/6 + n/2 for every split graph",
 "arithmetic":"exact Fraction, exact rational simplex, deterministic, no seeds",
 "domain":{"clique_size":[0,PMAX],"independent_vertices":[0,IMAX]},
 "graphs_tested":tested,"violations":len(viol),"violation_detail":viol[:5],
 "min_slack":str(worst[0]),"min_slack_witness":worst[1],
 "complete_split_family":cs},indent=1))
