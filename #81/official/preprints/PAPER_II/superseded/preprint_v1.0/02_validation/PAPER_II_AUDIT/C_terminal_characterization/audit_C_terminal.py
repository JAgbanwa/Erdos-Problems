#!/usr/bin/env python3
"""
Independent computational audit - Paper II, Section 5 (terminal characterization
and symmetrization).

 (C1) Lemma 5.1 : over ALL non-isomorphic chordal graphs on 1..N vertices,
      the property
         P(H) := every two nonadjacent simplicial vertices have equal open nbhd
      holds  IF AND ONLY IF  H is complete-split.  (equivalence checked both ways)

 (C2) Theorem 5.3 : the clone-class symmetrization, applied to each chordal graph,
      (a) stays chordal at every step, (b) strictly decreases the clone-class count,
      (c) is Phi_tau-nondecreasing at every step (Lemma 4.1 direction), and
      (d) terminates at a complete-split S_{p,q} with p+q=n and
          Phi_tau(final) >= Phi_tau(start).

complete-split test: U = universal vertices; H is complete-split iff V\\U is
independent and every non-universal vertex has open neighborhood exactly U.

Config via env: AUDIT_NMAX (default 7).
Self-contained. Requires: numpy, scipy, networkx.
"""
import itertools, json, os, time, sys
import networkx as nx
from scipy.optimize import linprog

HERE=os.path.dirname(os.path.abspath(__file__)); RES=os.path.join(HERE,"results")
os.makedirs(RES,exist_ok=True)
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
    S=list(S); return all(G.has_edge(a,b) for a,b in itertools.combinations(S,2))
def is_simplicial(G,v): return is_clique(G,list(G.neighbors(v)))
def clone_classes(G):
    d={}
    for v in G.nodes(): d.setdefault(frozenset(G.neighbors(v)),[]).append(v)
    return list(d.values())

def is_complete_split(G):
    n=G.number_of_nodes(); V=set(G.nodes())
    U={v for v in V if G.degree(v)==n-1}     # universal
    I=V-U
    if any(G.has_edge(a,b) for a,b in itertools.combinations(I,2)): return False
    for v in I:
        if frozenset(G.neighbors(v))!=frozenset(U): return False
    return True

def prop_P(G):
    simp=[v for v in G.nodes() if is_simplicial(G,v)]
    for x,y in itertools.combinations(simp,2):
        if not G.has_edge(x,y):
            if frozenset(G.neighbors(x))!=frozenset(G.neighbors(y)): return False
    return True

def class_copy_dir(G,U,V):
    """copy source class U onto target class V (U adopts N(V))."""
    nbV=frozenset(G.neighbors(V[0])); Uset=set(U)
    H=nx.Graph(); H.add_nodes_from(G.nodes())
    for a,b in G.edges():
        if a in Uset or b in Uset: continue
        H.add_edge(a,b)
    for u in U:
        for x in nbV:
            if x!=u: H.add_edge(u,x)
    return H

def symmetrize(G):
    """returns dict trace with checks; picks the Phi-nondecreasing class-copy dir."""
    G=nx.convert_node_labels_to_integers(G); n=G.number_of_nodes()
    phi0=phi_tau(G); cur=G; steps=0; ok=True; details={"stayed_chordal":True,
        "m_strictly_decreasing":True,"phi_nondecreasing":True}
    m_prev=len(clone_classes(cur)); phi_prev=phi0
    guard=0
    while not is_complete_split(cur):
        guard+=1
        if guard>3*n+5: details["nonterminating"]=True; ok=False; break
        cc=clone_classes(cur)
        # Cor 5.2 pair: distinct nonadjacent simplicial classes, different nbhd
        pair=None
        for U in cc:
            for V in cc:
                if U is V: continue
                nbU=frozenset(cur.neighbors(U[0])); nbV=frozenset(cur.neighbors(V[0]))
                if nbU==nbV: continue
                if any(cur.has_edge(a,b) for a in U for b in V): continue
                if is_clique(cur,nbU) and is_clique(cur,nbV):
                    pair=(U,V); break
            if pair: break
        if pair is None:
            details["cor52_pair_missing"]=True; ok=False; break
        U,V=pair
        H1=class_copy_dir(cur,U,V); H2=class_copy_dir(cur,V,U)
        cand=H1 if phi_tau(H1)>=phi_tau(H2) else H2
        # checks
        if not nx.is_chordal(cand): details["stayed_chordal"]=False; ok=False
        m_new=len(clone_classes(cand))
        if not (m_new<m_prev): details["m_strictly_decreasing"]=False; ok=False
        if phi_tau(cand)<phi_prev-TOL: details["phi_nondecreasing"]=False; ok=False
        m_prev=m_new; phi_prev=phi_tau(cand); cur=cand; steps+=1
    terminal_cs=is_complete_split(cur)
    return {"n":n,"steps":steps,"terminal_complete_split":terminal_cs,
            "phi_start":phi0,"phi_final":phi_tau(cur),
            "phi_final_ge_start":phi_tau(cur)>=phi0-TOL,
            "checks":details,"ok":ok and terminal_cs}

def main():
    t0=time.time(); atlas=nx.graph_atlas_g()
    Gs=[G for G in atlas if 1<=G.number_of_nodes()<=NMAX]
    # C1
    c1_tested=0; c1_viol=[]
    for G in Gs:
        G=nx.convert_node_labels_to_integers(G)
        if not nx.is_chordal(G): continue
        c1_tested+=1
        if prop_P(G)!=is_complete_split(G):
            c1_viol.append({"edges":list(map(list,G.edges())),
                            "P":prop_P(G),"complete_split":is_complete_split(G)})
    print(f"   C1: chordal graphs tested={c1_tested} equivalence_violations={len(c1_viol)} (t={time.time()-t0:.1f}s)")
    # C2
    c2_tested=0; c2_viol=[]; max_steps=0
    for G in Gs:
        Gi=nx.convert_node_labels_to_integers(G)
        if not nx.is_chordal(Gi): continue
        r=symmetrize(Gi); c2_tested+=1; max_steps=max(max_steps,r["steps"])
        if not r["ok"] or not r["phi_final_ge_start"]:
            c2_viol.append(r)
    print(f"   C2: chordal graphs symmetrized={c2_tested} violations={len(c2_viol)} max_steps={max_steps} (t={time.time()-t0:.1f}s)")
    S={"section":"C","paper_ref":"Paper II, Section 5 (Lemma 5.1, Theorem 5.3)",
       "C1_terminal_equiv":{"chordal_tested":c1_tested,"violations":c1_viol,
                            "PASS":len(c1_viol)==0},
       "C2_symmetrization":{"chordal_tested":c2_tested,"violations":c2_viol[:20],
                            "n_violations":len(c2_viol),"max_steps":max_steps,
                            "PASS":len(c2_viol)==0},
       "runtime_sec":round(time.time()-t0,2)}
    S["PASS"]=S["C1_terminal_equiv"]["PASS"] and S["C2_symmetrization"]["PASS"]
    return S

if __name__=="__main__":
    print(f"[Section C] terminal characterization + symmetrization, atlas n=1..{NMAX}")
    s=main(); 