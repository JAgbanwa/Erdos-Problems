# CTRL-02  Paper II, Proposition 6.2 & Corollary 6.3
# Verify by LP that tau3*(S_{p,q}) matches the closed form, incl. degenerate (2,0) and p<=1,
# and that Phi_tau(S_{p,q}) matches Cor 6.3.
from itertools import combinations as C
from scipy.optimize import linprog
def Cp2(p): return p*(p-1)//2
def split_graph(p,q):
    V=list(range(p+q)); K=list(range(p))
    E=set()
    for a,b in C(K,2): E.add((a,b))
    for u in range(p,p+q):
        for a in K: E.add((min(u,a),max(u,a)))
    return V,sorted(E)
def tau3star(p,q):
    V,E=split_graph(p,q)
    Es=set(E); T=[t for t in C(sorted(V),3) if (t[0],t[1]) in Es and (t[0],t[2]) in Es and (t[1],t[2]) in Es]
    if not T: return 0.0
    ei={e:i for i,e in enumerate(E)}
    Aub=[];bub=[]
    for (a,b,c) in T:
        row=[0.0]*len(E)
        for e in [(a,b),(a,c),(b,c)]: row[ei[e]]=-1.0
        Aub.append(row); bub.append(-1.0)
    return linprog([1.0]*len(E),A_ub=Aub,b_ub=bub,bounds=[(0,None)]*len(E),method='highs').fun
def formula_tau(p,q):
    if p<=1 or (p==2 and q==0): return 0.0
    if q<=p-1: return (Cp2(p)+p*q)/3.0
    return float(Cp2(p))
def formula_phi(p,q):
    n=p+q
    if p<=1 or (p==2 and q==0): return float(Cp2(p)+p*q)
    if q>=p-1: return p*(2*n+1-3*p)/2.0
    return (Cp2(p)+p*q)/3.0
bad_t=0; bad_p=0; checked=0
print("p  q | LP tau3*  formula | Phi_LP  Phi_formula")
for p in range(0,8):
    for q in range(0,11):
        if p+q<1 or p+q>12: continue
        t=tau3star(p,q); ft=formula_tau(p,q)
        phi_lp=Cp2(p)+p*q-2*t; phi_f=formula_phi(p,q)
        checked+=1
        okt=abs(t-ft)<1e-6; okp=abs(phi_lp-phi_f)<1e-6
        if not okt: bad_t+=1
        if not okp: bad_p+=1
        if p<=3 and q<=4:
            print(f"{p}  {q} | {t:7.4f}  {ft:7.4f} | {phi_lp:6.3f} {phi_f:6.3f}  {'OK' if okt and okp else 'MISMATCH'}")
print(f"checked (p,q) pairs           : {checked}")
print(f"tau3* LP vs formula mismatches: {bad_t}")
print(f"Phi_tau LP vs formula mismatch: {bad_p}")
print(f"degenerate S_2,0 (K_2): LP tau3*={tau3star(2,0):.4f} (formula 0)")
print("RESULT:", "PASS" if bad_t==0 and bad_p==0 else "FAIL")
