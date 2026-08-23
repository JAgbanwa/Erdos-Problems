import random
from itertools import combinations
from collections import defaultdict
import pulp
def chi_prime(t): return 0 if t<2 else (t-1 if t%2==0 else t)
c2=lambda x: x*(x-1)//2
def nu3_exact(p,Ns):
    K=list(range(p)); tris=[tuple(t) for t in combinations(K,3)]
    for i,N in enumerate(Ns):
        v=p+i
        for a,b in combinations(sorted(N),2): tris.append((a,b,v))
    pr=pulp.LpProblem('x',pulp.LpMaximize)
    x={t:pulp.LpVariable('t%d'%i,0,1,cat='Integer') for i,t in enumerate(tris)}
    pr+=pulp.lpSum(x.values()); inc=defaultdict(list)
    for t in tris:
        a,b,cc=t
        for e in [(a,b),(a,cc),(b,cc)]: inc[e].append(t)
    for e,ts in inc.items(): pr+=pulp.lpSum(x[t] for t in ts)<=1
    pr.solve(pulp.PULP_CBC_CMD(msg=0,timeLimit=120))
    return int(round(pulp.value(pr.objective) or 0))
