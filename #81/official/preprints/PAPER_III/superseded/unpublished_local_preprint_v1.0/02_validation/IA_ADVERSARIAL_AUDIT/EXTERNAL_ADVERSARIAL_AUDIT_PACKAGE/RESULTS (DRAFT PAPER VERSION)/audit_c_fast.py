# Auditoria PAPER C - capa rapida.
# A: Teorema 3.1 (formula common-profile) vs LP directo de triangulos en H(p,q,d).
# B: Teorema 4.2 (margen fraccionario): cada rama de F >= qd/2 + (C_a+mu)p^2 - p/2, aritmetica exacta.
# C: dominancia de la tercera rama residual (Apendice A).
from fractions import Fraction as Fr
from itertools import combinations
import pulp

def F_formula(p,q,d):
    r=p-d
    c2=lambda x: x*(x-1)//2
    return min(Fr(c2(p)+q*d,3), Fr(c2(d)+c2(r)), Fr(c2(d))+Fr(d*r+c2(r),3))

def nu3star_H(p,q,d):
    # H(p,q,d): clique 0..p-1, indep p..p+q-1 todos con vecindario N={0..d-1}
    K=list(range(p)); I=list(range(p,p+q)); N=set(range(d))
    tris=[tuple(t) for t in combinations(K,3)]
    for v in I:
        for a,b in combinations(sorted(N),2): tris.append((a,b,v))
    pr=pulp.LpProblem('x',pulp.LpMaximize)
    x={t:pulp.LpVariable('t%d'%i,0,None) for i,t in enumerate(tris)}
    pr+=pulp.lpSum(x.values())
    from collections import defaultdict
    inc=defaultdict(list)
    def edges(t):
        a,b,c=t
        if c>=p: return [(a,b),(a,c),(b,c)]
        return [(a,b),(a,c),(b,c)]
    for t in tris:
        for e in edges(t): inc[e].append(t)
    for e,ts in inc.items(): pr+=pulp.lpSum(x[t] for t in ts)<=1
    pr.solve(pulp.PULP_CBC_CMD(msg=0))
    return pulp.value(pr.objective) or 0.0

failA=0; nA=0
for p in range(3,10):
    for q in range(1,6):
        for d in range(0,p+1):
            nA+=1
            lp=nu3star_H(p,q,d); fm=float(F_formula(p,q,d))
            if abs(lp-fm)>1e-5:
                failA+=1; print("A-FALLA p=%d q=%d d=%d LP=%.4f F=%.4f"%(p,q,d,lp,fm))
print("A: Teorema 3.1: %d casos, %d fallas"%(nA,failA))

failB=0; nB=0; worst=None
for p in range(3,41):
    for q in range(1,2*p+1):
        al=Fr(q,p)
        Ca=(2-2*al-al*al)/12
        mu=al*al/12 if al<=Fr(2,3) else (2-al)**2/48
        for d in range(0,p+1):
            nB+=1
            lhs=F_formula(p,q,d)
            rhs=Fr(q*d,2)+(Ca+mu)*p*p-Fr(p,2)
            if lhs<rhs:
                failB+=1
                if worst is None or lhs-rhs<worst[0]: worst=(lhs-rhs,p,q,d)
print("B: Teorema 4.2: %d casos, %d fallas"%(nB,failB))
if worst: print("   peor:",worst)

# C: tercera rama residual >= min(primeras dos), grid racional fino
failC=0
for num in range(0,241):
    al=Fr(num,120)  # 0..2
    r1=al*al/12; r2=(2-al)**2/48
    r3=al*(8-5*al)/48 if al<=Fr(4,3) else (2-al)**2/12
    if r3<min(r1,r2)-0: failC+=1; print("C-FALLA alpha=",al)
print("C: dominancia tercera rama: %d fallas en 241 puntos"%failC)
