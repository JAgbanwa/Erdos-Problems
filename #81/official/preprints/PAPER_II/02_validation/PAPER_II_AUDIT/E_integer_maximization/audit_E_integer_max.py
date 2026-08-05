#!/usr/bin/env python3
"""
Independent computational audit - Paper II, Section 7 (exact integer maximization).

Exact rational arithmetic (fractions). For every n in 1..NMAX it verifies:

 (E1) Theorem 1.1 value:  max_{p+q=n} Phi_tau(S_{p,q}) = floor((2n+1)^2/24).
 (E2) the maximum is attained in the SATURATED branch (q>=p-1) by the integer p
      nearest to (2n+1)/6.
 (E3) the NON-saturated branch never exceeds the floor.
 (E4) residue identity: (2n+1)^2 mod 24 in {1,9}, and the closed floor matches
      ((2n+1)^2 - r2)/24 with r2 in {1,9}.

Phi_tau uses the exact branch formulas of Prop 6.2 / Cor 6.3.
Config via env: AUDIT_NMAX (default 2000).
Self-contained. Requires: (stdlib only).
"""
import json, os, sys, time
from fractions import Fraction

HERE=os.path.dirname(os.path.abspath(__file__)); RES=os.path.join(HERE,"results")
os.makedirs(RES,exist_ok=True)
NMAX=int(os.environ.get("AUDIT_NMAX","2000"))

def tau_formula(p,q):
    P=p*(p-1)//2
    if p<=1: return Fraction(0)
    if p==2 and q==0: return Fraction(0)
    if p>=3 and q<=p-1: return Fraction(P+p*q,3)
    return Fraction(P)
def phi(p,q):
    P=p*(p-1)//2
    return Fraction(P+p*q)-2*tau_formula(p,q)
def floor_val(n): return ((2*n+1)**2)//24
def nearest_int(num,den):
    # nearest integer to num/den (den>0), ties to even not needed; use round-half-up
    q,r=divmod(num,den)
    return q + (1 if 2*r>=den else 0)

def main():
    t0=time.time(); e1=e2=e3=e4=0; V=[]
    worst=None
    for n in range(1,NMAX+1):
        vals=[(phi(p,n-p),p) for p in range(0,n+1)]
        M=max(vals); Mval=M[0]
        fl=floor_val(n)
        if Mval!=fl:
            e1+=1; V.append({"n":n,"max":str(Mval),"floor":fl,"claim":"E1"})
        # E2 nearest p in saturated branch achieves floor
        pstar=nearest_int(2*n+1,6)
        qstar=n-pstar
        okp = 0<=pstar<=n and qstar>=pstar-1 and phi(pstar,qstar)==fl
        if not okp:
            e2+=1; V.append({"n":n,"pstar":pstar,"qstar":qstar,
                             "phi_pstar":str(phi(pstar,max(qstar,0))) if 0<=pstar<=n else None,
                             "claim":"E2"})
        # E3 nonsat branch <= floor
        nonsat_max=max([phi(p,n-p) for p in range(0,n+1) if (n-p)<=p-1] or [Fraction(-1)])
        if nonsat_max>fl:
            e3+=1; V.append({"n":n,"nonsat_max":str(nonsat_max),"floor":fl,"claim":"E3"})
        # E4 residue
        r2=((2*n+1)**2)%24
        if r2 not in (1,9) or ((2*n+1)**2 - r2)//24 != fl:
            e4+=1; V.append({"n":n,"r2":r2,"claim":"E4"})
    print(f"   n=1..{NMAX} checked. E1={e1} E2={e2} E3={e3} E4={e4} viol (t={time.time()-t0:.1f}s)")
    S={"section":"E","paper_ref":"Paper II, Section 7 (Prop 7.1, Theorem 1.1 arithmetic)",
       "NMAX":NMAX,
       "E1_value_equals_floor":{"violations":e1,"PASS":e1==0},
       "E2_maximizer_saturated_nearest":{"violations":e2,"PASS":e2==0},
       "E3_nonsaturated_le_floor":{"violations":e3,"PASS":e3==0},
       "E4_residue_identity":{"violations":e4,"PASS":e4==0},
       "examples":[{"n":n,"floor":floor_val(n),
                    "pstar":nearest_int(2*n+1,6)} for n in [1,2,3,5,8,12,13,50,100,1000]
                   if n<=NMAX],
       "violations_sample":V[:20],"runtime_sec":round(time.time()-t0,2)}
    S["PASS"]=all(S[k]["PASS"] for k in
        ["E1_value_equals_floor","E2_maximizer_saturated_nearest",
         "E3_nonsaturated_le_floor","E4_residue_identity"])
    return S

if __name__=="__main__":
    print(f"[Section E] integer maximization, n=1..{NMAX} (exact rational)")
    s=main(); json.dump(s,open(os.path.join(RES,"summary.json"),"w"),indent=2)
    pri