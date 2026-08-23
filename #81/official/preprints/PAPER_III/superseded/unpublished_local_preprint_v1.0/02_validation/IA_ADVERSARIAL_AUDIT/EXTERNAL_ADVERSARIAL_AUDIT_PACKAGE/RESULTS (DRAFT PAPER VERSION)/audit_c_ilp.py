# Auditoria PAPER C - capa ILP: Lemas 5.1, 5.2 (via 5.4) y 7.1 (7.6) contra nu3 exacto.
import random, pulp
from itertools import combinations
from collections import defaultdict

def chi_prime(t): return 0 if t<2 else (t-1 if t%2==0 else t)

def nu3_exact(p,Ns):
    K=list(range(p)); tris=[tuple(t) for t in combinations(K,3)]
    for i,N in enumerate(Ns):
        v=p+i
        for a,b in combinations(sorted(N),2): tris.append((a,b,v))
    pr=pulp.LpProblem('x',pulp.LpMaximize)
    x={t:pulp.LpVariable('t%d'%i,0,1,cat='Integer') for i,t in enumerate(tris)}
    pr+=pulp.lpSum(x.values()); inc=defaultdict(list)
    for t in tris:
        a,b,c=t
        for e in [(a,b),(a,c),(b,c)]: inc[e].append(t)
    for e,ts in inc.items(): pr+=pulp.lpSum(x[t] for t in ts)<=1
    pr.solve(pulp.PULP_CBC_CMD(msg=0,timeLimit=120))
    return int(round(pulp.value(pr.objective) or 0))

def log(m):
    with open("audit_c_ilp_results.txt","a") as f: f.write(m+"\n")

open("audit_c_ilp_results.txt","w").close()
rng=random.Random(7)
c2=lambda x: x*(x-1)//2

# --- Lema 5.1: nu3 >= (1/q) sum C(d_i,2), instancias aleatorias con q>=chi'(K_p)
fail=0; n=0
for p in [6,7,8,9]:
    rp=chi_prime(p)
    for trial in range(4):
        q=rp+rng.randint(0,3)
        Ns=[set(rng.sample(range(p),rng.randint(max(2,p-3),p))) for _ in range(q)]
        lb=sum(c2(len(N)) for N in Ns)/q
        nu=nu3_exact(p,Ns); n+=1
        if nu<lb-1e-9: fail+=1; log("L5.1-FALLA p=%d q=%d nu=%d lb=%.3f"%(p,q,nu,lb))
log("Lema 5.1: %d casos, %d fallas"%(n,fail))

# --- Lema 5.2 via (5.4): Phi <= n^2/6 + p/2 - s^2/6 + ((s-1)M-S2)/q - 2*delta*V/(q(q-1))
fail=0; n=0
for p in [6,7,8]:
    rp=chi_prime(p)
    for s in [1,2,3]:
        q=2*p-s
        if q<rp: continue
        for trial in range(3):
            Ns=[]
            for _ in range(q):
                mi=rng.randint(0,min(2,(s)//1))
                Si=set(rng.sample(range(p),mi)); Ns.append(set(range(p))-Si)
            M=sum(p-len(N) for N in Ns); S2=sum((p-len(N))**2 for N in Ns)
            h=min(rp,q-rp); delta=h/rp
            V=0
            for a,b in combinations(range(p),2):
                be=sum(1 for N in Ns if not(a in N and b in N))
                V+=be*(q-be)
            E=c2(p)+sum(len(N) for N in Ns); nu=nu3_exact(p,Ns)
            Phi=E-2*nu; nn=p+q
            bound=nn*nn/6+p/2-s*s/6+((s-1)*M-S2)/q-2*delta*V/(q*(q-1))
            n+=1
            if Phi>bound+1e-9: fail+=1; log("L5.2-FALLA p=%d s=%d Phi=%d bound=%.3f"%(p,s,Phi,bound))
log("Lema 5.2/(5.4): %d casos, %d fallas"%(n,fail))

# --- Lema 7.1 (7.6): construir instancias que cumplan (7.1)-(7.2) y verificar
fail=0; n=0; skipped=0
for p in [8,9,10,11]:
    for rho in [0,1,2]:
        for trial in range(4):
            s=2*rho+3+rng.randint(0,2); q=2*p-s
            R=set(range(rho)); b=p-rho
            Ns=[]
            for _ in range(q):
                ti=rng.randint(0,1)
                Ti=set(rng.sample(range(rho,p),ti))
                inR=set(x for x in R if rng.random()<0.5)
                Si=Ti|inR; Ns.append(set(range(p))-Si)
            rb=chi_prime(b); u=q-rb
            # hipotesis (7.1)-(7.2)
            ok=(b>=2 and q>=rb and b>=chi_prime(rho))
            tis=[len((set(range(p))-N)-R) for N in Ns]
            gis=[len(R-(set(range(p))-N)) for N in Ns]
            if ok:
                for ti in tis:
                    if b-ti<max(rho,u): ok=False; break
            if not ok: skipped+=1; continue
            AR=sum(tis); A2R=sum(t*t for t in tis); BR=sum(gis)
            thet=max(rho-1,0)/b; kap=1-2*(1-thet)*u/q
            E=c2(p)+sum(len(N) for N in Ns); nu=nu3_exact(p,Ns)
            Phi=E-2*nu; nn=p+q
            bound=nn*nn/6+p/2-s*s/6+s*rho-2*rho*rho+kap*BR+((s-2*rho-1)*AR-A2R)/q
            n+=1
            if Phi>bound+1e-9: fail+=1; log("L7.1-FALLA p=%d rho=%d s=%d Phi=%d bound=%.3f"%(p,rho,s,Phi,bound))
log("Lema 7.1/(7.6): %d casos validos (%d saltados por hipotesis), %d fallas"%(n,skipped,fail))
log("FIN")
