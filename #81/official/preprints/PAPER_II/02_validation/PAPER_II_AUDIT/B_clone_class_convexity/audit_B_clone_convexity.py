#!/usr/bin/env python3
"""
Independent computational audit - Paper II, Section 4 (clone-class operations).

Three sub-audits:

 (B1) Lemma 4.1  discrete convexity of f(k)=Phi_tau(H_k):
      over small base graphs W and all neighborhood pairs (N_A,N_B), building the
      interpolation family H_k (k class-vertices attached to N_A, s-k to N_B, all
      class-vertices pairwise nonadjacent), verify
          f(k-1)+f(k+1) >= 2 f(k)   (1<=k<=s-1)
      and hence  f(k) <= max(f(0),f(s)) for all interior k.

 (B2) Lemma 4.2  copying a whole clone class onto another (target neighborhood B):
      source and target classes merge, NO other clone class splits, so the number
      of maximal clone classes strictly decreases. Verified over chordal graphs.

 (B3) Lemma 4.3 + necessity: copying onto a SIMPLICIAL target class preserves
      chordality (verified over all chordal graphs, all admissible class pairs);
      and an explicit example is found where copying onto a NON-simplicial target
      breaks chordality (so the simpliciality hypothesis is necessary).

Config via env: AUDIT_WMAX (default 4), AUDIT_SMAX (default 4), AUDIT_NMAX (default 7).
Self-contained. Requires: numpy, scipy, networkx.
"""
import itertools, json, os, time, sys
import networkx as nx
from scipy.optimize import linprog

HERE=os.path.dirname(os.path.abspath(__file__)); RES=os.path.join(HERE,"results")
os.makedirs(RES,exist_ok=True)
WMAX=int(os.environ.get("AUDIT_WMAX","4")); SMAX=int(os.environ.get("AUDIT_SMAX","4"))
NMAX=int(os.environ.get("AUDIT_NMAX","7")); TOL=1e-7

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
def is_clique(G,S):
    S=list(S)
    return all(G.has_edge(a,b) for a,b in itertools.combinations(S,2))
def clone_classes(G):
    d={}
    for v in G.nodes(): d.setdefault(frozenset(G.neighbors(v)),[]).append(v)
    return list(d.values())
def simplicial_class(G,cls):
    nb=frozenset(G.neighbors(cls[0]))
    return is_clique(G,nb)

# ---------- B1: convexity ----------
def build_Hk(W,nbA,nbB,s,k):
    H=nx.Graph(); H.add_nodes_from(W.nodes())
    H.add_edges_from(W.edges())
    base=max(W.nodes())+1 if W.number_of_nodes() else 0
    for i in range(s):
        cv=base+i; H.add_node(cv)
        nb=nbA if i<k else nbB
        for x in nb: H.add_edge(cv,x)
    return H
def audit_B1():
    atlas=nx.graph_atlas_g()
    Ws=[G for G in atlas if 1<=G.number_of_nodes()<=WMAX]
    worst_conv=float("inf"); worst_endpoint=float("inf"); tested=0; viol=[]
    for W in Ws:
        W=nx.convert_node_labels_to_integers(W); nodes=list(W.nodes())
        subs=[frozenset(c) for r in range(len(nodes)+1)
              for c in itertools.combinations(nodes,r)]
        for nbA in subs:
            for nbB in subs:
                if nbA==nbB: continue
                for s in range(2,SMAX+1):
                    f=[phi_tau(build_Hk(W,nbA,nbB,s,k)) for k in range(s+1)]
                    for k in range(1,s):
                        c=(f[k-1]+f[k+1])-2.0*f[k]
                        worst_conv=min(worst_conv,c)
                        if c<-TOL: viol.append({"W":list(map(list,W.edges())),
                            "nbA":sorted(nbA),"nbB":sorted(nbB),"s":s,"k":k,"conv":c})
                    mx=max(f[0],f[s])
                    for k in range(1,s):
                        e=mx-f[k]; worst_endpoint=min(worst_endpoint,e)
                        if e<-TOL: viol.append({"endpoint_fail":True,"s":s,"k":k})
                    tested+=1
    return {"configs_tested":tested,"min_second_difference":worst_conv,
            "min_endpoint_margin":worst_endpoint,"violations":viol,
            "PASS":(len(viol)==0 and worst_conv>=-TOL and worst_endpoint>=-TOL)}

# ---------- B2/B3: class copy on chordal graphs ----------
def class_copy(G,U,B):
    """copy source class U onto target neighborhood B (frozenset)."""
    H=nx.Graph(); H.add_nodes_from(G.nodes())
    Uset=set(U)
    for a,b in G.edges():
        if a in Uset or b in Uset: continue
        H.add_edge(a,b)
    for u in U:
        for x in B:
            if x!=u: H.add_edge(u,x)
    return H
def audit_B2_B3():
    atlas=nx.graph_atlas_g()
    Gs=[G for G in atlas if 1<=G.number_of_nodes()<=NMAX]
    b2_tested=0; b2_viol=[]; b3_tested=0; b3_viol=[]
    for G in Gs:
        G=nx.convert_node_labels_to_integers(G)
        if not nx.is_chordal(G): continue
        cc=clone_classes(G); m_old=len(cc)
        for U in cc:
            for V in cc:
                if U is V: continue
                # nonadjacent distinct classes, different neighborhoods
                nbU=frozenset(G.neighbors(U[0])); nbV=frozenset(G.neighbors(V[0]))
                if nbU==nbV: continue
                if any(G.has_edge(a,b) for a in U for b in V): continue  # nonadjacent
                if not simplicial_class(G,V): continue                   # target simplicial
                H=class_copy(G,U,nbV)
                # B3: chordality preserved
                b3_tested+=1
                if not nx.is_chordal(H):
                    b3_viol.append({"edges":list(map(list,G.edges())),"U":U,"V":V})
                # B2: clone-class count strictly decreases, no other class splits
                b2_tested+=1
                m_new=len(clone_classes(H))
                if not (m_new<m_old):
                    b2_viol.append({"edges":list(map(list,G.edges())),"U":U,"V":V,
                                    "m_old":m_old,"m_new":m_new})
                # no split: every other class stays inside one new class
                new_of={}; 
                for cls in clone_classes(H):
                    for w in cls: new_of[w]=frozenset(cls)
                for C in cc:
                    if C is U or C is V: continue
                    if len({new_of[w] for w in C})!=1:
                        b2_viol.append({"split":True,"edges":list(map(list,G.edges())),"C":C})
    # necessity: search an explicit non-simplicial-target example breaking chordality
    necessity=None
    for G in Gs:
        G=nx.convert_node_labels_to_integers(G)
        if not nx.is_chordal(G): continue
        cc=clone_classes(G)
        for U in cc:
            for V in cc:
                if U is V: continue
                nbU=frozenset(G.neighbors(U[0])); nbV=frozenset(G.neighbors(V[0]))
                if nbU==nbV: continue
                if any(G.has_edge(a,b) for a in U for b in V): continue
                if simplicial_class(G,V): continue        # NON-simplicial target
                H=class_copy(G,U,nbV)
                if not nx.is_chordal(H):
                    necessity={"chordal_G_edges":list(map(list,G.edges())),
                               "source_U":U,"target_V":V,"target_nbhd":sorted(nbV),
                               "result_edges":list(map(list,H.edges())),
                               "result_is_chordal":False}
                    break
            if necessity: break
        if necessity: break
    return ({"B2_pairs_tested":b2_tested,"B2_violations":b2_viol,
             "B2_PASS":len(b2_viol)==0},
            {"B3_pairs_tested":b3_tested,"B3_violations":b3_viol,
             "B3_PASS":len(b3_viol)==0,
             "necessity_example_found":necessity is not None,
             "necessity_example":necessity})

def main():
    t0=time.time()
    print("[Section B] B1 convexity ..."); b1=audit_B1()
    print(f"   configs={b1['configs_tested']} min_2nd_diff={b1['min_second_difference']:.3g} PASS={b1['PASS']}")
    print("[Section B] B2/B3 class-copy on chordal graphs ..."); b2,b3=audit_B2_B3()
    print(f"   B2 pairs={b2['B2_pairs_tested']} PASS={b2['B2_PASS']}")
    print(f"   B3 pairs={b3['B3_pairs_tested']} PASS={b3['B3_PASS']} necessity_example={b3['necessity_example_found']}")
    S={"section":"B","paper_ref":"Paper II, Section 4 (Lemmas 4.1-4.3)",
       "B1_convexity":b1,"B2_clone_count":b2,"B3_chordality_and_necessity":b3,
       "runtime_sec":round(time.time()-t0,2)}
    S["PASS"]=b1["PASS"] and b2["B2_PASS"] and b3["B3_PASS"] and b3["necessity_example_found"]
    return S

if __name__=="__main__":
    print(f"[Section B] clone-class ops (WMAX={WMAX},SMAX={SM