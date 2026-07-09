# CTRL-01  Paper II, Lemma 3.1 (vertex-copy inequality)
# Phi_tau(G_{v->u}) + Phi_tau(G_{u->v}) >= 2 Phi_tau(G),  Phi_tau=|E|-2 tau3*.
import random
from itertools import combinations as C
from scipy.optimize import linprog
def tau3(n,adj):
    E=[(a,b) for a,b in C(range(n),2) if adj[a][b]]
    if not E: return 0.0
    idx={e:i for i,e in enumerate(E)}
    T=[(a,b,c) for a,b,c in C(range(n),3) if adj[a][b] and adj[a][c] and adj[b][c]]
    if not T: return 0.0
    Aub=[];bub=[]
    for a,b,c in T:
        row=[0.0]*len(E)
        for e in [(a,b),(a,c),(b,c)]: row[idx[e]]=-1.0
        Aub.append(row);bub.append(-1.0)
    return linprog([1.0]*len(E),A_ub=Aub,b_ub=bub,bounds=[(0,None)]*len(E),method='highs').fun
def edges(n,adj): return sum(1 for a,b in C(range(n),2) if adj[a][b])
def phi(n,adj): return edges(n,adj)-2*tau3(n,adj)
def copy(n,adj,x,y):
    A=[r[:] for r in adj]
    for w in range(n):
        if w==x: continue
        val = adj[y][w] if w!=y else False
        A[x][w]=val; A[w][x]=val
    A[x][x]=False; return A
random.seed(20260707)
viol=0; tested=0; worst=1e9
for t in range(1200):
    n=random.randint(4,7); p=random.random()*0.7+0.15
    adj=[[False]*n for _ in range(n)]
    for a,b in C(range(n),2):
        if random.random()<p: adj[a][b]=adj[b][a]=True
    pairs=[(x,y) for x,y in C(range(n),2) if not adj[x][y]]
    if not pairs: continue
    x,y=random.choice(pairs)
    lhs=phi(n,copy(n,adj,x,y))+phi(n,copy(n,adj,y,x)); rhs=2*phi(n,adj)
    tested+=1; s=lhs-rhs; worst=min(worst,s)
    if s<-1e-6:
        viol+=1
        if viol<=5: print(f"VIOLATION n={n} slack={s:.4f}")
print("Random graphs n=4..7, one random nonadjacent pair each (seed 20260707)")
print(f"instances tested        : {tested}")
print(f"inequality violations   : {viol}")
print(f"min slack (lhs-rhs)      : {worst:.4f}  (>=0 required; 0 => tight)")
print("RESULT:", "PASS" if viol==0 else "FAIL")
