#!/usr/bin/env python3
"""
Independent computational audit - Paper II, Theorem 1.1 (global maximum).

 (F1) EXHAUSTIVE: over ALL non-isomorphic graphs on 1..7 vertices (networkx atlas),
      restricted to chordal graphs, computes Phi_tau exactly (LP) and verifies, for
      each n,   max_{chordal, |V|=n} Phi_tau(G) = floor((2n+1)^2/24),
      and that at least one maximizer is a complete-split graph.

 (F2) SAMPLED: for n = 8..SMAX, draws K random chordal graphs (built by repeatedly
      adding a vertex whose neighborhood is a random existing clique -> chordal by
      construction) plus the full complete-split family {S_{p,q}: p+q=n}, and checks
      that NO sampled chordal graph exceeds the floor, while the floor IS attained by
      a complete-split (attainment value computed by the exact Section-6 formula).

This is exhaustive for n<=7 and a (large) random sample for n>=8; the report states
this scope explicitly.

Config via env: AUDIT_SMAX(12), AUDIT_K(3000), AUDIT_SEED(20260709).
Self-contained. Requires: numpy, scipy, networkx.
"""
import itertools, json, os, sys, time, random
from fractions import Fraction
import networkx as nx
from scipy.optimize import linprog

HERE=os.path.dirname(os.path.abspath(__file__)); RES=os.path.join(HERE,"results")
os.makedirs(RES,exist_ok=True)
SMAX=int(os.environ.get("AUDIT_SMAX","12")); K=int(os.environ.get("AUDIT_K","3000"))
SEED=int(os.environ.get("AUDIT_SEED","20260709")); TOL=1e-7

def triangles(G):
    return [(a,b,c) for a,b,c in itertools.combinations(list(G.nodes()),3)
            if G.has_edge(a,b) and G.has_edge(a,c) and G.has_edge(b,c)]
def tau3_star(G):
    edges=[frozenset(e) for e in G.edges()]
    if not edges: return 0.0
    idx={e:i for i,e in enumerate(edges)}; tris=triangles(G)
    if not tris: return 0.0
    m=len(edges); A=[]; b=[]
    for (a,bb,c) in tris:
        row=[0.0]*m
        for e in (frozenset((a,bb)),frozenset((a,c)),frozenset((bb,c))): row[idx[e]]-=1.0
        A.append(row); b.append(-1.0)
    r=linprog([1.0]*m,A_ub=A,b_ub=b,bounds=[(0,None)]*m,method="highs"); assert r.success
    return float(r.fun)
def phi_tau(G): return G.number_of_edges()-2.0*tau3_star(G)
def floor_val(n): return ((2*n+1)**2)//24
def is_complete_split(G):
    n=G.number_of_nodes(); V=set(G.nodes())
    U={v for v in V if G.degree(v)==n-1}; I=V-U
    if any(G.has_edge(a,b) for a,b in itertools.combinations(I,2)): return False
    return all(frozenset(G.neighbors(v))==frozenset(U) for v in I)
def tau_formula(p,q):
    P=p*(p-1)//2
    if p<=1: return Fraction(0)
    if p==2 and q==0: return Fraction(0)
    if p>=3 and q<=p-1: return Fraction(P+p*q,3)
    return Fraction(P)
def phi_cs(p,q):
    P=p*(p-1)//2; return Fraction(P+p*q)-2*tau_formula(p,q)
def best_completesplit(n):
    return max((phi_cs(p,n-p),p) for p in range(0,n+1))
def random_chordal(n,rng):
    G=nx.Graph(); G.add_node(0)
    for i in range(1,n):
        r=rng.choice(list(G.nodes()))
        clique=[r]; cand=list(G.neighbors(r)); rng.shuffle(cand)
        for c in cand:
            if all(G.has_edge(c,x) for x in clique): clique.append(c)
        k=rng.randint(0,len(clique)); nb=clique[:k]
        G.add_node(i)
        for x in nb: G.add_edge(i,x)
    return G

def main():
    t0=time.time(); rng=random.Random(SEED)
    # F1 exhaustive
    atlas=nx.graph_atlas_g(); best={}
    for G in atlas:
        n=G.number_of_nodes()
        if not (1<=n<=7): continue
        G=nx.convert_node_labels_to_integers(G)
        if not nx.is_chordal(G): continue
        ph=phi_tau(G)
        cur=best.get(n)
        if cur is None or ph>cur["max_phi"]+1e-12:
            best[n]={"max_phi":ph,"edges":list(map(list,G.edges())),
                     "argmax_is_complete_split":is_complete_split(G)}
        elif abs(ph-cur["max_phi"])<=1e-9 and is_complete_split(G):
            cur["argmax_is_complete_split"]=True
    f1=[]; f1_pass=True
    for n in sorted(best):
        fl=floor_val(n); mx=best[n]["max_phi"]
        ok=abs(mx-fl)<=TOL and best[n]["argmax_is_complete_split"]
        f1.append({"n":n,"max_phi":round(mx,6),"floor":fl,
                   "match":abs(mx-fl)<=TOL,
                   "argmax_complete_split":best[n]["argmax_is_complete_split"]})
        f1_pass=f1_pass and ok
    print(f"   F1 exhaustive n<=7 done, pass={f1_pass} (t={time.time()-t0:.1f}s)")
    # F2 sampled
    f2=[]; f2_pass=True
    for n in range(8,SMAX+1):
        fl=floor_val(n); exceed=0; worst=-1.0; nonchordal=0
        for _ in range(K):
            G=random_chordal(n,rng)
            if not nx.is_chordal(G): nonchordal+=1; continue
            ph=phi_tau(G); worst=max(worst,ph)
            if ph>fl+TOL: exceed+=1
        bcs=best_completesplit(n); attain=(bcs[0]==fl)
        row={"n":n,"floor":fl,"samples":K,"max_sampled_phi":round(worst,6),
             "sampled_exceed_floor":exceed,"nonchordal_built":nonchordal,
             "completesplit_attains_floor":attain,"best_cs_p":bcs[1]}
        f2.append(row); f2_pass=f2_pass and exceed==0 and attain
        print(f"   F2 n={n}: max_sampled={worst:.4f} floor={fl} exceed={exceed} attain={attain} (t={time.time()-t0:.1f}s)")
    S={"section":"F","paper_ref":"Paper II, Theorem 1.1 (global maximum)",
       "F1_exhaustive_n_le_7":{"per_n":f1,"PASS":f1_pass,
           "note":"all non-isomorphic chordal graphs via networkx atlas"},
       "F2_sampled_n_8_to_%d"%SMAX:{"per_n":f2,"PASS":f2_pass,"K_per_n":K,"seed":SEED,
           "note":"random chordal sample + full complete-split family; NOT exhaustive"},
       "runtime_sec":round(time.time()-t0,2)}
    S["PASS"]=f1_pass and f2_pass
    return S

if __name__=="__main__":
    print(f"[Section F] global Theorem 1.1: exhaustive n<=7, sampled 8..{SMAX} (K={K})")
    s=main(); json.dump(s,open(os.path.join