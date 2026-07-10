#!/usr/bin/env python3
"""
Independent computational audit - Paper II, Section 3 (vertex-copy inequality).

Exhaustive over all non-isomorphic graphs on 2..N vertices (networkx graph atlas,
N<=7). For EVERY nonadjacent pair (u,v) it verifies:

  (I)   Lemma 3.1 :  Phi_tau(G_{v->u}) + Phi_tau(G_{u->v}) >= 2 Phi_tau(G)
  (II)  eq. 3.4   :  e(G_{v->u}) + e(G_{u->v}) = 2 e(G)
  (III) eq. 3.3   :  tau3*(G_{v->u}) + tau3*(G_{u->v}) <= 2 tau3*(G)

tau3* is computed by exact LP; the dual packing nu3* is computed independently and
LP-duality tau3*==nu3* is checked as an internal consistency test.

Config via env: AUDIT_NMAX (default 7).
Self-contained. Requires: numpy, scipy, networkx.
"""
import itertools, json, os, time, sys
import networkx as nx
from scipy.optimize import linprog

HERE = os.path.dirname(os.path.abspath(__file__))
RES  = os.path.join(HERE, "results"); os.makedirs(RES, exist_ok=True)
NMAX = int(os.environ.get("AUDIT_NMAX", "7"))
TOL  = 1e-7

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

def nu3_star(G):
    edges=[frozenset(e) for e in G.edges()]; tris=triangles(G)
    if not edges or not tris: return 0.0
    nt=len(tris); A=[]; b=[]
    for e in edges:
        row=[1.0 if e in {frozenset((a,bb)),frozenset((a,c)),frozenset((bb,c))} else 0.0
             for (a,bb,c) in tris]
        A.append(row); b.append(1.0)
    r=linprog([-1.0]*nt,A_ub=A,b_ub=b,bounds=[(0,None)]*nt,method="highs"); assert r.success
    return float(-r.fun)

def phi_tau(G): return G.number_of_edges()-2.0*tau3_star(G)

def copy_vertex(G,v,u):
    H=nx.Graph(); H.add_nodes_from(G.nodes())
    for a,b in G.edges():
        if a!=v and b!=v: H.add_edge(a,b)
    for x in G.neighbors(u):
        if x!=v: H.add_edge(v,x)
    return H

def main():
    t0=time.time(); atlas=nx.graph_atlas_g(); by_n={}
    for G in atlas:
        n=G.number_of_nodes()
        if 2<=n<=NMAX: by_n.setdefault(n,[]).append(G)
    S={"section":"A","paper_ref":"Paper II, Section 3 (Lemma 3.1, eqs 3.3-3.4)",
       "claims":{"I":"Phi(G_{v->u})+Phi(G_{u->v}) >= 2 Phi(G)",
                 "II":"e(G_{v->u})+e(G_{u->v}) = 2 e(G)",
                 "III":"tau3*(G_{v->u})+tau3*(G_{u->v}) <= 2 tau3*(G)",
                 "dual":"tau3*(G)==nu3*(G)"},
       "tolerance":TOL,"per_n":{},"violations":[],
       "min_slack_I":float("inf"),"max_abs_err_II":0.0,
       "max_slack_III_violation":0.0,"max_abs_dualgap":0.0}
    tg=tp=0
    for n in sorted(by_n):
        pn=0
        for G in by_n[n]:
            G=nx.convert_node_labels_to_integers(G)
            t=tau3_star(G); nu=nu3_star(G)
            S["max_abs_dualgap"]=max(S["max_abs_dualgap"],abs(t-nu))
            phiG=G.number_of_edges()-2.0*t
            for u,v in itertools.combinations(list(G.nodes()),2):
                if G.has_edge(u,v): continue
                pn+=1; tp+=1
                Gvu=copy_vertex(G,v,u); Guv=copy_vertex(G,u,v)
                sI=(phi_tau(Gvu)+phi_tau(Guv))-2.0*phiG
                S["min_slack_I"]=min(S["min_slack_I"],sI)
                eII=abs((Gvu.number_of_edges()+Guv.number_of_edges())-2*G.number_of_edges())
                S["max_abs_err_II"]=max(S["max_abs_err_II"],eII)
                sIII=(tau3_star(Gvu)+tau3_star(Guv))-2.0*t
                if sIII>TOL: S["max_slack_III_violation"]=max(S["max_slack_III_violation"],sIII)
                if sI<-TOL or eII>TOL or sIII>TOL:
                    S["violations"].append({"n":n,"edges":list(map(list,G.edges())),
                        "u":u,"v":v,"slackI":sI,"errII":eII,"slackIII":sIII})
            tg+=1
        S["per_n"][n]={"graphs":len(by_n[n]),"nonadjacent_pairs_tested":pn}
        print(f"  n={n}: {len(by_n[n])} graphs, {pn} pairs  (t={time.time()-t0:.1f}s)")
    S["totals"]={"graphs_tested":tg,"pairs_tested":tp,"max_n_reached":max(by_n),
                 "runtime_sec":round(time.time()-t0,2)}
    S["min_slack_I"]=None if S["min_slack_I"]==float("inf") else S["min_slack_I"]
    S["PASS"]=(len(S["violations"])==0 and S["min_slack_I"]>=-TOL
               and S["max_abs_err_II"]<=TOL and S["max_slack_III_violation"]<=TOL)
    return S

if __name__=="__main__":
    print(f"[Section A] vertex-copy inequality, atlas n=2..{NMAX}")
    s=main()
    json.dump(s,open(os.path.join(RES,"summary.json"),"w"),indent=2)
    print(json.dumps({k:s[k] for k in ["totals","min_slack_I","max_abs_err_II",
        "max_slack_III_violation","max_abs_dualgap","PASS"]},indent=2))
    print("RESU