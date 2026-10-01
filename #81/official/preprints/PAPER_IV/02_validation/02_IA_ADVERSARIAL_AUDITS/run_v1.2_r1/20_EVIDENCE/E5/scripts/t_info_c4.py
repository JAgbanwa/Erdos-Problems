"""INFO (not predeclared): c4 of every atlas graph n<=7 versus Q_{rsd(G)}(n) (Theorem C is only eventual;
Appendix G.1 asks whether b=0).  c4 by CBC with exact partition verification; exact lower bound ceil(F_4) from the
exact W* of t_graphs.py (every order-4 partition Q has |Q| = e - g(Q) >= e - W*)."""
import sys, os, time, json, math
from fractions import Fraction as Fr
import networkx as nx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e5lib import *

t0 = time.time()
atlas = nx.graph_atlas_g()
RSD = json.load(open(os.path.join(RES, 'atlas_rsd.json')))['rsd']
WS = json.load(open(os.path.join(RES, 'atlas_Wstar.json')))['Wstar']
exceed, certified, solver_only, bad = [], 0, 0, []
maxratio = []
for i, g in enumerate(atlas):
    n, adj = from_nx(g)
    e = len(edges_of(n, adj))
    st, val, P = ilp_partition(n, adj, rmax=4)
    ok, why = verify_partition(n, adj, P, rmax=4)
    if not ok:
        bad.append((i, why)); continue
    lb = math.ceil(Fr(e) - Fr(WS[i][0]))
    if val == lb:
        certified += 1
    else:
        solver_only += 1
    s = RSD[i]
    if val > Q(s, n):
        exceed.append({'atlas_index': i, 'n': n, 'rsd': s, 'c4': val, 'Q_s(n)': Q(s, n), 'certified': val == lb, 'edges': edges_of(n, adj)})
out = {'id': 'INFO_c4', 'claim': 'information only: c4(G) vs Q_{rsd}(n) for all graphs n<=7 (Theorem C asserts c4<=Q_s(n) only for n>=N_s)',
       'graphs': len(atlas), 'c4_certified_by_LP_ceiling': certified, 'c4_solver_dependent_only': solver_only, 'verification_failures': bad,
       'graphs_with_c4_greater_than_Q_rsd': exceed, 'chordal_graphs_with_c4>M(n)': [x for x in exceed if x['rsd'] == 0],
       'runtime_s': round(time.time() - t0, 1)}
dump('info_c4.json', out)
print({k: (v if not isinstance(v, list) else len(v)) for k, v in out.items()})
