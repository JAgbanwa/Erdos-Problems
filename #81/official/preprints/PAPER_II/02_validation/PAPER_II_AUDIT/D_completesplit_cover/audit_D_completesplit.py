#!/usr/bin/env python3
"""
Independent computational audit - Paper II, Section 6 (complete-split cover program).

For every complete-split S_{p,q}=K_p v ~K_q with p in 0..PMAX, q in 0..QMAX,
p+q<=SUMMAX, it verifies:

 (D1) Prop 6.2 : the exact fractional triangle-cover number tau3*(S_{p,q}), computed
      by a full LP on the actual graph, equals the closed-form
         0                    if p<=1, or (p,q)=(2,0);
         (C(p,2)+p q)/3       if p>=3 and q<=p-1   (non-saturated);
         C(p,2)               if p>=2 and q>=p-1   (saturated).
 (D2) Cor 6.3 : Phi_tau(S_{p,q}) = |E|-2 tau3* equals  pq-C(p,2) (saturated) or
         (C(p,2)+pq)/3 (non-saturated).
 (D3) Lemma 6.1 : the orbit-averaged 2-variable LP  min P x + pq y  s.t.
         3x>=1 (if p>=3), x+2y>=1 (if p>=2,q>=1), x,y>=0
      attains the SAME optimum as the full LP (symmetrization loses nothing).

Config via env: AUDIT_PMAX(12), AUDIT_QMAX(14), AUDIT_SUMMAX(16).
Self-contained. Requires: numpy, scipy, networkx.
"""
import itertools, json, os, time, sys
from fractions import Fraction
import networkx as nx
from scipy.optimize import linprog

HERE=os.path.dirname(os.path.abspath(__file__)); RES=os.path.join(HERE,"results")
os.makedirs(RES,exist_ok=True)
PMAX=int(os.environ.get("AUDIT_PMAX","12")); QMAX=int(os.environ.get("AUDIT_QMAX","14"))
SUMMAX=int(os.environ.get("AUDIT_SUMMAX","16")); TOL=1e-7

def complete_split(p,q):
    G=nx.Graph(); G.add_nodes_from(range(p+q))
    for a,b in itertools.combinations(range(p),2): G.add_edge(a,b)
    for a in range(p):
        for b in range(p,p+q): G.add_edge(a,b)
    return G
def triangles(G):
    return [(a,b,c) for a,b,c in itertools.combinations(list(G.nodes()),3)
            if G.has_edge(a,b) and G.has_edge(a,c) and G.has_edge(b,c)]
def tau3_star_LP(G):
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
def tau_formula(p,q):
    P=p*(p-1)//2
    if p<=1: return Fraction(0)
    if p==2 and q==0: return Fraction(0)
    if p>=3 and q<=p-1: return Fraction(P+p*q,3)
    return Fraction(P)
def phi_formula(p,q):
    P=p*(p-1)//2
    return Fraction(P+p*q)-2*tau_formula(p,q)
def orbit_LP(p,q):
    P=p*(p-1)//2; A=[]; b=[]
    if p>=3: A.append([-3.0,0.0]); b.append(-1.0)        # 3x>=1
    if p>=2 and q>=1: A.append([-1.0,-2.0]); b.append(-1.0)  # x+2y>=1
    if not A: return 0.0
    r=linprog([float(P),float(p*q)],A_ub=A,b_ub=b,bounds=[(0,None),(0,None)],method="highs")
    assert r.success; return float(r.fun)

def main():
    t0=time.time(); rows=[]; d1v=[]; d2v=[]; d3v=[]
    for p in range(0,PMAX+1):
        for q in range(0,QMAX+1):
            if p+q>SUMMAX or p+q==0: continue
            G=complete_split(p,q)
            lp=tau3_star_LP(G); fo=float(tau_formula(p,q))
            phi_lp=G.number_of_edges()-2.0*lp; phi_fo=float(phi_formula(p,q))
            orb=orbit_LP(p,q)
            e1=abs(lp-fo); e2=abs(phi_lp-phi_fo); e3=abs(orb-lp)
            rows.append({"p":p,"q":q,"tau_LP":round(lp,6),"tau_formula":fo,
                         "phi_LP":round(phi_lp,6),"phi_formula":phi_fo,
                         "orbit_LP":round(orb,6)})
            if e1>TOL: d1v.append({"p":p,"q":q,"tau_LP":lp,"formula":fo,"err":e1})
            if e2>TOL: d2v.append({"p":p,"q":q,"phi_LP":phi_lp,"formula":phi_fo,"err":e2})
            if e3>TOL: d3v.append({"p":p,"q":q,"orbit":orb,"full":lp,"err":e3})
    print(f"   cases tested={len(rows)}  D1v={len(d1v)} D2v={len(d2v)} D3v={len(d3v)} (t={time.time()-t0:.1f}s)")
    S={"section":"D","paper_ref":"Paper II, Section 6 (Prop 6.2, Cor 6.3, Lemma 6.1)",
       "range":{"PMAX":PMAX,"QMAX":QMAX,"SUMMAX":SUMMAX},"cases_tested":len(rows),
       "D1_tau_formula":{"violations":d1v,"PASS":len(d1v)==0},
       "D2_phi_formula":{"violations":d2v,"PASS":len(d2v)==0},
       "D3_orbit_equals_full":{"violations":d3v,"PASS":len(d3v)==0},
       "sample_rows":[{**r,"tau_formula":str(r["tau_formula"]),
                       "phi_formula":str(r["phi_formula"])} for r in rows[:24]],
       "runtime_sec":round(time.time()-t0,2)}
    S["PASS"]=S["D1_tau_formula"]["PASS"] and S["D2_phi_formula"]["PASS"] and S["D3_orbit_equals_full"]["PASS"]
    return S

if __name__=="__main__":
    print(f"[Section D] complete-split cover (p<= {PMAX}, q<= {QMAX}, p+q<= {SUMMAX})")
    s=main(); json.dump(s,open(os.path.join(RES,"summary.json"),"w"),i