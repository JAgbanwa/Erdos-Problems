"""E5 common library (independent implementation by the E5 sub-auditor).

Graphs are given as (n, adj) with adj a list of int bitmasks.
All arithmetic that decides a verdict is exact (int / Fraction).
Floating point solvers are only used to *propose* solutions that are
then re-verified exactly.
"""
import itertools, json, os, time, math
from fractions import Fraction as Fr

E5 = os.path.normpath(os.path.join(os.path.dirname(__file__), '..'))
RES = os.path.join(E5, 'results')
LOGS = os.path.join(E5, 'logs')


# ---------------------------------------------------------------- numbers
def C2(x):
    """binomial(x,2) as the integer polynomial x(x-1)/2 (valid for all ints)."""
    return x * (x - 1) // 2


def M(n):
    assert n >= 0
    return n * (n + 1) // 6


def Q(s, n):
    return M(n + s) - C2(s + 1)


def Bn(n, p):
    return p * (n - p) - C2(p)


def Bsn(s, n, k):
    return k * (n - k) - C2(k - s)


# ---------------------------------------------------------------- graphs
def popcount(x):
    return bin(x).count('1')


def bits(x):
    while x:
        b = x & -x
        yield b.bit_length() - 1
        x ^= b


def from_nx(g):
    nodes = sorted(g.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    n = len(nodes)
    adj = [0] * n
    for u, v in g.edges():
        a, b = idx[u], idx[v]
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    return n, adj


def from_edges(n, edges):
    adj = [0] * n
    for a, b in edges:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    return n, adj


def edges_of(n, adj):
    return [(i, j) for i in range(n) for j in range(i + 1, n) if adj[i] >> j & 1]


def is_clique(mask, adj):
    for v in bits(mask):
        if (mask & ~(1 << v)) & ~adj[v]:
            return False
    return True


def all_cliques(n, adj, minsize=1, maxsize=None):
    """All cliques (as bitmasks) of size in [minsize,maxsize]."""
    out = []

    def rec(R, P, size):
        if size >= minsize:
            out.append(R)
        if maxsize is not None and size == maxsize:
            return
        for v in bits(P):
            P2 = P & adj[v] & ~((1 << (v + 1)) - 1)
            rec(R | (1 << v), P2, size + 1)

    for v in range(n):
        rec(1 << v, adj[v] & ~((1 << (v + 1)) - 1), 1)
    return out


class Omega:
    """clique number of induced subgraphs, memoised on masks."""

    def __init__(self, adj):
        self.adj = adj
        self.memo = {0: 0}

    def __call__(self, mask):
        memo = self.memo
        if mask in memo:
            return memo[mask]
        stack = [mask]
        # iterative-ish recursion (depth <= n, fine to recurse)
        v = (mask & -mask).bit_length() - 1
        rest = mask & ~(1 << v)
        r = max(self(rest), 1 + self(rest & self.adj[v]))
        memo[mask] = r
        return r


def maximal_cliques_in(U, adj):
    out = []

    def bk(R, P, X):
        if P == 0 and X == 0:
            out.append(R)
            return
        PX = P | X
        best, bu = -1, None
        for u in bits(PX):
            c = popcount(P & adj[u])
            if c > best:
                best, bu = c, u
        for v in bits(P & ~adj[bu]):
            bk(R | (1 << v), P & adj[v], X & adj[v])
            P &= ~(1 << v)
            X |= (1 << v)

    bk(0, U, 0)
    return out


def rsd(n, adj, return_witness=False):
    """Rooted simplicial defect, by brute force over all U and all cliques R (proper subset of U).

    Definition used (manuscript l.84, audit brief): rsd(G) <= s iff for every U and every
    clique R of G with R strictly contained in U there is v in U\\R such that N_U(v)
    contains a clique P with |N_U(v)\\P| <= s.  f(U,v) := |N_U(v)| - omega(G[N_U(v)]).
    rsd = max_U max_{R} min_{v in U\\R} f(U,v).  Max over R is attained at maximal cliques
    of G[U] (min over a smaller set is larger); if U is a clique the value is 0.
    """
    om = Omega(adj)
    best = 0
    wit = None
    full = (1 << n) - 1
    for U in range(1, full + 1):
        if is_clique(U, adj):
            continue
        f = {}
        for v in bits(U):
            Nv = adj[v] & U
            f[v] = popcount(Nv) - om(Nv)
        if max(f.values()) <= best:
            continue
        for R in maximal_cliques_in(U, adj):
            val = min(f[v] for v in bits(U & ~R))
            if val > best:
                best = val
                wit = (U, R)
    if return_witness:
        return best, wit
    return best


def ordNE(D, adj):
    """ordered pairs of distinct nonadjacent vertices of D."""
    c = 0
    for v in bits(D):
        c += popcount(D & ~adj[v] & ~(1 << v))
    return c


# ---------------------------------------------------------------- exact LP for W*
def mixed_copies(n, adj):
    tri = [K for K in all_cliques(n, adj, 3, 3)]
    k4 = [K for K in all_cliques(n, adj, 4, 4)]
    return tri, k4


def pairs_of(K):
    vs = list(bits(K))
    return [(a, b) for a, b in itertools.combinations(vs, 2)]


def exact_Wstar(n, adj):
    """Return (W*, x, y, status) with exact Fractions verified.
    Primal: max sum g_K x_K, sum_{K ni e} x_K <= 1, x>=0.  Dual: min sum y_e, sum_{e in K} y_e >= g_K, y>=0.
    status 'exact' if both certificates verified exactly and objectives equal."""
    import numpy as np
    from scipy.optimize import linprog
    E = edges_of(n, adj)
    eidx = {e: i for i, e in enumerate(E)}
    tri, k4 = mixed_copies(n, adj)
    copies = [(K, 2) for K in tri] + [(K, 5) for K in k4]
    if not copies:
        return Fr(0), {}, {e: Fr(0) for e in E}, 'exact'
    m, N = len(E), len(copies)
    A = np.zeros((m, N))
    rows = []
    for j, (K, g) in enumerate(copies):
        r = [eidx[p] for p in pairs_of(K)]
        rows.append(r)
        for i in r:
            A[i, j] = 1
    c = np.array([-g for K, g in copies], dtype=float)
    res = linprog(c, A_ub=A, b_ub=np.ones(m), bounds=(0, None), method='highs')
    if res.status != 0:
        return None, None, None, 'solver_fail'
    xf = res.x
    yf = -res.ineqlin.marginals
    for D in (1, 2, 6, 12, 60, 360, 2520, 27720, 10 ** 6):
        x = [Fr(v).limit_denominator(D) for v in xf]
        y = [Fr(v).limit_denominator(D) for v in yf]
        x = [v if v > 0 else Fr(0) for v in x]
        y = [v if v > 0 else Fr(0) for v in y]
        ok = True
        load = [Fr(0)] * m
        for j, r in enumerate(rows):
            for i in r:
                load[i] += x[j]
        if any(l > 1 for l in load):
            ok = False
        if ok:
            for j, (K, g) in enumerate(copies):
                if sum(y[i] for i in rows[j]) < g:
                    ok = False
                    break
        if ok:
            P = sum(g * x[j] for j, (K, g) in enumerate(copies))
            Dv = sum(y)
            if P == Dv:
                return P, {copies[j][0]: x[j] for j in range(N) if x[j]}, {E[i]: y[i] for i in range(m)}, 'exact'
    # fallback: exact solve of the optimal simplex basis returned by HiGHS
    r = _basis_exact(rows, [g for K, g in copies], m)
    if r is not None:
        x, y = r
        P = sum(copies[j][1] * x[j] for j in range(N))
        return P, {copies[j][0]: x[j] for j in range(N) if x[j]}, {E[i]: y[i] for i in range(m)}, 'exact'
    return Fr(-res.fun).limit_denominator(10 ** 6), None, None, 'INCONCLUSIVE_no_exact_certificate'


def _solve_exact(Amat, b):
    """Gaussian elimination over Fractions; Amat square list of lists. Returns x or None if singular."""
    nrow = len(Amat)
    Mx = [list(map(Fr, Amat[i])) + [Fr(b[i])] for i in range(nrow)]
    for col in range(nrow):
        piv = next((r for r in range(col, nrow) if Mx[r][col] != 0), None)
        if piv is None:
            return None
        Mx[col], Mx[piv] = Mx[piv], Mx[col]
        pv = Mx[col][col]
        Mx[col] = [v / pv for v in Mx[col]]
        for r in range(nrow):
            if r != col and Mx[r][col] != 0:
                fct = Mx[r][col]
                Mx[r] = [a - fct * c for a, c in zip(Mx[r], Mx[col])]
    return [Mx[i][nrow] for i in range(nrow)]


def _basis_exact(rows, gains, m):
    """Solve max g.x, A x <= 1, x >= 0 with highspy; rebuild the optimal basis exactly and verify
    primal feasibility, dual feasibility and equal objective in exact arithmetic."""
    import highspy, numpy as np
    N = len(rows)
    h = highspy.Highs()
    h.setOptionValue('output_flag', False)
    h.setOptionValue('solver', 'simplex')
    lp = highspy.HighsLp()
    lp.num_col_ = N
    lp.num_row_ = m
    lp.col_cost_ = np.array(gains, dtype=float)
    lp.col_lower_ = np.zeros(N)
    lp.col_upper_ = np.full(N, highspy.kHighsInf)
    lp.row_lower_ = np.full(m, -highspy.kHighsInf)
    lp.row_upper_ = np.ones(m)
    lp.sense_ = highspy.ObjSense.kMaximize
    starts, idx, val = [0], [], []
    for r in rows:
        for i in sorted(r):
            idx.append(i); val.append(1.0)
        starts.append(len(idx))
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    lp.a_matrix_.start_ = np.array(starts, dtype=np.int32)
    lp.a_matrix_.index_ = np.array(idx, dtype=np.int32)
    lp.a_matrix_.value_ = np.array(val)
    lp.a_matrix_.num_col_ = N
    lp.a_matrix_.num_row_ = m
    h.passModel(lp)
    h.run()
    bs = h.getBasis()
    B = [j for j in range(N) if bs.col_status[j] == highspy.HighsBasisStatus.kBasic]
    NBrows = [i for i in range(m) if bs.row_status[i] != highspy.HighsBasisStatus.kBasic]
    if len(B) != len(NBrows):
        return None
    colset = [set(rows[j]) for j in range(N)]
    Amat = [[1 if i in colset[j] else 0 for j in B] for i in NBrows]
    xb = _solve_exact(Amat, [1] * len(NBrows)) if B else []
    if xb is None:
        return None
    AT = [[Amat[r][c] for r in range(len(NBrows))] for c in range(len(B))]
    yb = _solve_exact(AT, [gains[j] for j in B]) if B else []
    if yb is None:
        return None
    x = [Fr(0)] * N
    for j, v in zip(B, xb):
        x[j] = v
    y = [Fr(0)] * m
    for i, v in zip(NBrows, yb):
        y[i] = v
    if any(v < 0 for v in x) or any(v < 0 for v in y):
        return None
    load = [Fr(0)] * m
    for j in range(N):
        if x[j]:
            for i in rows[j]:
                load[i] += x[j]
    if any(l > 1 for l in load):
        return None
    for j in range(N):
        if sum(y[i] for i in rows[j]) < gains[j]:
            return None
    if sum(gains[j] * x[j] for j in range(N)) != sum(y):
        return None
    return x, y


# ---------------------------------------------------------------- clique partitions
def verify_partition(n, adj, pieces, rmax=None):
    """pieces: list of bitmasks. Exact check that it is a clique partition of E(G)."""
    E = set(edges_of(n, adj))
    seen = set()
    for K in pieces:
        if popcount(K) < 2:
            return False, 'piece of order <2'
        if rmax is not None and popcount(K) > rmax:
            return False, 'piece too large'
        if not is_clique(K, adj):
            return False, 'piece not a clique'
        for p in pairs_of(K):
            if p in seen:
                return False, 'edge covered twice'
            seen.add(p)
    if seen != E:
        return False, 'edges not covered'
    return True, 'ok'


def ilp_partition(n, adj, rmax=None, ub=None, time_limit=120, feas_target=None):
    """Minimum clique partition by CBC.  Returns (status, value, pieces).
    If ub is given, adds sum x <= ub (used for infeasibility re-checks)."""
    import pulp
    E = edges_of(n, adj)
    if not E:
        return 'Optimal', 0, []
    cl = all_cliques(n, adj, 2, rmax)
    prob = pulp.LpProblem('cp', pulp.LpMinimize)
    x = [pulp.LpVariable(f'x{j}', cat='Binary') for j in range(len(cl))]
    prob += pulp.lpSum(x)
    cover = {e: [] for e in E}
    for j, K in enumerate(cl):
        for p in pairs_of(K):
            cover[p].append(x[j])
    for e in E:
        prob += pulp.lpSum(cover[e]) == 1
    if ub is not None:
        prob += pulp.lpSum(x) <= ub
    st = prob.solve(pulp.PULP_CBC_CMD(msg=0, timeLimit=time_limit))
    status = pulp.LpStatus[prob.status]
    if status != 'Optimal':
        return status, None, None
    pieces = [cl[j] for j in range(len(cl)) if x[j].value() is not None and x[j].value() > 0.5]
    return status, len(pieces), pieces


def weight_lower_bound(n, adj, w):
    """w: dict edge->Fraction.  Exact check that every clique (order>=2) has weight <=1;
    returns (valid, sum_w).  If valid, every clique partition has >= sum_w pieces."""
    for K in all_cliques(n, adj, 2, None):
        if sum(w[p] for p in pairs_of(K)) > 1:
            return False, None
    return True, sum(w.values())


# ---------------------------------------------------------------- templates
def template(sizes_C, sizes_D, sizes_H, C_clique=True):
    """(K_C disjoint-union I_D) join I_H on vertices 0..n-1: C first, then D, then H."""
    c, d, h = sizes_C, sizes_D, sizes_H
    n = c + d + h
    C = list(range(c)); D = list(range(c, c + d)); H = list(range(c + d, n))
    edges = []
    if C_clique:
        edges += list(itertools.combinations(C, 2))
    for u in C + D:
        for v in H:
            edges.append((u, v))
    return from_edges(n, edges), (C, D, H)


# ---------------------------------------------------------------- io
def dump(name, obj):
    os.makedirs(RES, exist_ok=True)
    with open(os.path.join(RES, name), 'w', encoding='utf-8') as f:
        json.dump(obj, f, indent=1, default=str)


def fr(x):
    return str(x)


class Timer:
    def __enter__(self):
        self.t = time.time()
        return self

    def __exit__(self, *a):
        self.dt = time.time() - self.t
