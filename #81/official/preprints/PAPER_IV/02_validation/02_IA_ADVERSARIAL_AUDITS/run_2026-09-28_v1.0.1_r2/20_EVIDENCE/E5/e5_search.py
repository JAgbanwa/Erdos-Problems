"""E5 — bounded exact searches (auditor-written). Exact ILP (CBC via pulp) for clique partitions and LP (HiGHS)
for the mixed fractional optimum. Bounded tests can refute but never prove universal statements.
Predeclared expectations are in the check names; negative controls must fail."""
import itertools, json, random, time
import networkx as nx
import pulp
from scipy.optimize import linprog

random.seed(20260928)
res = []
def check(name, cond, detail=''):
    res.append({'check': name, 'result': 'PASS' if cond else 'FAIL', 'detail': str(detail)[:300]})
def negctrl(name, cond, detail=''):
    res.append({'check': 'NEG:' + name, 'result': 'NEGCTRL ok' if not cond else 'NEGCTRL VIOLATED', 'detail': str(detail)[:300]})
M = lambda n: n * (n + 1) // 6

def cliques(G, lo=2, hi=None):
    out = []
    for c in nx.enumerate_all_cliques(G):
        if len(c) >= lo and (hi is None or len(c) <= hi):
            out.append(frozenset(c))
    return out

def min_partition(G, hi=None, time_limit=120):
    E = [frozenset(e) for e in G.edges()]
    if not E:
        return 0, []
    C = cliques(G, 2, hi)
    prob = pulp.LpProblem('cp', pulp.LpMinimize)
    x = {c: pulp.LpVariable('x%d' % i, cat='Binary') for i, c in enumerate(C)}
    prob += pulp.lpSum(x.values())
    for e in E:
        prob += pulp.lpSum(x[c] for c in C if e <= c) == 1
    prob.solve(pulp.PULP_CBC_CMD(msg=0, timeLimit=time_limit))
    status = pulp.LpStatus[prob.status]
    assert status == 'Optimal', status
    sol = [c for c in C if x[c].value() > 0.5]
    return len(sol), sol

def wstar(G):
    E = [frozenset(e) for e in G.edges()]
    items = [c for c in cliques(G, 3, 4)]
    if not items:
        return 0.0
    idx = {e: i for i, e in enumerate(E)}
    A = [[0] * len(items) for _ in E]
    for j, c in enumerate(items):
        for e in itertools.combinations(sorted(c), 2):
            A[idx[frozenset(e)]][j] = 1
    gain = [-(len(c) * (len(c) - 1) // 2 - 1) for c in items]
    r = linprog(gain, A_ub=A, b_ub=[1] * len(E), bounds=[(0, None)] * len(items), method='highs')
    return -r.fun

def split(k, h, s=0):
    """(K_{k-s} disjoint-union independent D_s) join independent H_h: C complete, D,H independent, (C u D)-H complete."""
    G = nx.Graph(); Cn = ['c%d' % i for i in range(k - s)]; Dn = ['d%d' % i for i in range(s)]; Hn = ['h%d' % i for i in range(h)]
    G.add_nodes_from(Cn + Dn + Hn)
    G.add_edges_from(itertools.combinations(Cn, 2))
    G.add_edges_from((u, v) for u in Cn + Dn for v in Hn)
    return G

t0 = time.time()
# (a) complete split: cp = c3 = c4 = kh - C(k,2), W* = 2C(k,2)
ok = True; det = []
for k in range(2, 6):
    for h in range(k, 8):
        G = split(k, h)
        target = k * h - k * (k - 1) // 2
        cp, _ = min_partition(G)
        c4, _ = min_partition(G, 4)
        c3, _ = min_partition(G, 3)
        w = wstar(G)
        good = cp == c3 == c4 == target and abs(w - k * (k - 1)) < 1e-7
        ok &= good; det.append((k, h, cp, c4, c3, target, round(w, 6)))
check('(6.2)+(6.10): cp=c3=c4=kh-C(k,2), W*=2C(k,2), 2<=k<=5, k<=h<=7', ok, det[:6])
# negative control: h < k-1 breaks the construction (k=5,h=2)
G = split(5, 2); cp, _ = min_partition(G)
negctrl('cp(K5 v I2) = kh-C(k,2) outside 2<=k<=h', cp == 5 * 2 - 10, cp)

# (b) complete graphs: c4(K_n) <= M(n); order 3 insufficient at n=10
ok = True; det = []
for n in range(0, 11):
    G = nx.complete_graph(n)
    c4, _ = min_partition(G, 4, time_limit=300)
    ok &= c4 <= M(n); det.append((n, c4, M(n)))
check('Prop D.1: c4(K_n) <= M(n), 0<=n<=10', ok, det)
c3_10, _ = min_partition(nx.complete_graph(10), 3, time_limit=300)
check('Prop D.2: c3(K_10) >= 19 > M(10)=18', c3_10 >= 19, c3_10)
negctrl('c3(K_10) <= M(10)', c3_10 <= M(10), c3_10)

# (c) exhaustive small chordal graphs (networkx atlas, <=7 vertices): compare c4 and cp with M(n)
atlas = nx.graph_atlas_g()
viol = []; cnt = 0; worst = {}
for G in atlas:
    n = G.number_of_nodes()
    if n == 0 or not nx.is_chordal(G):
        continue
    cnt += 1
    c4, _ = min_partition(G, 4)
    worst[n] = max(worst.get(n, -99), c4 - M(n))
    if c4 > M(n):
        viol.append((n, sorted(G.edges()), c4, M(n)))
check('all chordal graphs n<=7 (atlas): c4(G) <= M(n) [informational for b=0; not a claim of the paper]', not viol,
      {'graphs': cnt, 'max_c4_minus_M_by_n': worst, 'violations': viol[:3]})

# (d) Lemma 4.1 (4.4): W*(G_{u->v}) + W*(G_{v->u}) <= 2 W*(G) and F4 step existence, random chordal graphs
def random_chordal(n, p):
    # random graph then minimal-ish chordal completion via networkx
    G = nx.gnp_random_graph(n, p, seed=random.randrange(10**9))
    H, _ = nx.complete_to_chordal_graph(G)
    return nx.Graph(H)
def copy(G, u, v):
    """v receives u's open neighbourhood (u,v nonadjacent)."""
    H = G.copy(); H.remove_edges_from(list(H.edges(v))); H.add_edges_from((v, w) for w in G.neighbors(u) if w != v); return H
ok = True; tested = 0; fok = True
for trial in range(120):
    G = random_chordal(random.randint(5, 9), random.uniform(0.25, 0.6))
    simp = [x for x in G if all(G.has_edge(a, b) for a, b in itertools.combinations(list(G.neighbors(x)), 2))]
    pairs = [(u, v) for u, v in itertools.combinations(simp, 2) if not G.has_edge(u, v)]
    if not pairs:
        continue
    u, v = random.choice(pairs)
    w0, w1, w2 = wstar(G), wstar(copy(G, u, v)), wstar(copy(G, v, u))
    tested += 1
    ok &= (w1 + w2 <= 2 * w0 + 1e-7)
    e0 = G.number_of_edges(); e1 = copy(G, u, v).number_of_edges(); e2 = copy(G, v, u).number_of_edges()
    fok &= (e1 + e2 == 2 * e0) and (max(e1 - w1, e2 - w2) >= e0 - w0 - 1e-7)
    ok &= nx.is_chordal(copy(G, u, v)) and nx.is_chordal(copy(G, v, u))
check('(4.4) transport inequality + chordality preserved (random chordal, n<=9)', ok, {'instances': tested})
check('one copy direction does not decrease F4', fok, tested)
# negative control: the averaging bound fails if we drop the factor 1/2 (i.e. claim W*(G_uv)+W*(G_vu) <= W*(G))
negctrl('W*(G_uv)+W*(G_vu) <= W*(G) (missing averaging)', all(
    wstar(copy(G, u, v)) + wstar(copy(G, v, u)) <= wstar(G) + 1e-7 for G, u, v in
    [(split(3, 4), 'h0', 'h1'), (split(4, 5), 'h0', 'h2')]))

# (e) identity (6.7b) on exact optimal partitions of random chordal graphs and random clique roots
ok = True; tested = 0
for trial in range(60):
    G = random_chordal(random.randint(5, 9), random.uniform(0.3, 0.7))
    cl = [c for c in cliques(G, 1)]
    R = set(random.choice(cl))
    n = G.number_of_nodes(); p = len(R)
    _, Q = min_partition(G)
    m = sum(1 for a, b in G.edges() if a not in R and b not in R)
    A = sum(1 for x in R for y in G if y not in R and not G.has_edge(x, y))
    lhs = sum(1 + (len(K & R) * (len(K & R) - 1)) // 2 + 3 * (len(K - R) * (len(K - R) - 1)) // 2 - len(K & R) * len(K - R) for K in Q)
    B = p * (n - p) - p * (p - 1) // 2
    ok &= lhs == len(Q) - B + A + 3 * m; tested += 1
check('(6.7b) sum d_R = |Q| - B_n(|R|) + A + 3m (exact partitions, random chordal/root)', ok, tested)

# (f) Theorem C witness: rooted defect <= s (brute force) and cp = Q_s(n) (unrestricted ILP), and not <= s-1
def rooted_defect_le(G, s):
    V = list(G)
    for r in range(len(V) + 1):
        for U in itertools.combinations(V, r):
            Us = set(U)
            sub = G.subgraph(U)
            for Rc in [set(c) for c in nx.enumerate_all_cliques(sub)] + [set()]:
                if Rc == Us:
                    continue
                okv = False
                for v in Us - Rc:
                    N = set(sub.neighbors(v))
                    om = max((len(c) for c in nx.enumerate_all_cliques(sub.subgraph(N))), default=0)
                    if len(N) - om <= s:
                        okv = True; break
                if not okv:
                    return False
    return True
Qs = lambda s, n: M(n + s) - s * (s + 1) // 2
ok = True; det = []
for s in range(0, 3):
    for n in range(2 * s + 2, 2 * s + 6):
        k = (n + s + 1) // 3
        G = split(k, n - k, s)
        rd = rooted_defect_le(G, s)
        rd_lower = (s == 0) or not rooted_defect_le(G, s - 1)
        cp, _ = min_partition(G)
        good = rd and cp == Qs(s, n)
        ok &= good; det.append((s, n, k, rd, rd_lower, cp, Qs(s, n)))
check('E.3 witness: rsd<=s and cp=Q_s(n) (s<=2, 2s+2<=n<=2s+5)', ok, det)
negctrl('E.3 witness with s=1 has rooted defect 0', rooted_defect_le(split(3, 3, 1), 0))
# class definition sanity: s=0 class = chordal on atlas n<=6
okc = all(rooted_defect_le(G, 0) == nx.is_chordal(G) for G in atlas if 0 < G.number_of_nodes() <= 6)
check('RootedDefectAt 0 <=> chordal (all graphs n<=6)', okc)

res.append({'check': 'runtime_seconds', 'result': 'INFO', 'detail': round(time.time() - t0, 1)})
json.dump(res, open('e5_search_results.json', 'w'), indent=1)
for r_ in res:
    print(r_['result'].ljust(16), r_['check'], ('| ' + str(r_['detail']))[:160] if r_['detail'] else '')
print('FAILURES', sum(r_['result'] in ('FAIL', 'NEGCTRL VIOLATED') for r_ in res))
