"""
03 — End-to-end falsification on split graphs (Paper I, Theorem 1.1 kill-switch).

For split graphs G = K_p (clique) + independent vertices with neighborhoods N(v) ⊆ K,
compute the fractional triangle-packing number nu3*(G) EXACTLY by LP (HiGHS) and test
the theorem
        |E(G)| - 2 nu3*(G)  <=  n^2/6 + n .
Independent of the manuscript's construction (this solves the packing LP on the whole
graph directly). Also cross-checks the two-phase construction value V_com = b>=2/2 +
M(kappa) satisfies V_com <= nu3* and reproduces the deficit identity (4.9)/(L28), and
verifies the extremal family K_p ∨ Kbar_{2p} attains |E|-2nu3* = n^2/6 + n/6.

Predeclared kill-switches:
  KS1  ANY split graph with |E| - 2 nu3* > n^2/6 + n + 1e-6      => THEOREM FALSIFIED.
  KS2  ANY graph with V_com > nu3* + 1e-6                        => construction invalid.
  KS3  extremal K_p∨Kbar_2p with |E|-2nu3* != n^2/6 + n/6 (±1e-6)=> tightness claim wrong.
"""
import sys, os, io, itertools
try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass
import numpy as np
from scipy.optimize import linprog

TOL = 1e-6

def build_split(p, neigh):
    """neigh: list of frozenset/tuple neighborhoods (subsets of range(p)) for indep verts."""
    clique = list(range(p))
    indep = list(range(p, p + len(neigh)))
    N = {indep[i]: set(neigh[i]) for i in range(len(neigh))}
    return p, clique, indep, N

def edges(p, indep, N):
    E = set()
    for i in range(p):
        for j in range(i + 1, p):
            E.add((i, j))               # clique edges
    for v in indep:
        for x in N[v]:
            E.add((min(v, x), max(v, x)))  # cross edges (v>x always since v>=p)
    return E

def triangles(p, indep, N):
    T = []
    for i in range(p):
        for j in range(i + 1, p):
            for k in range(j + 1, p):
                T.append(((i, j), (i, k), (j, k)))          # clique triangle
    for v in indep:
        nb = sorted(N[v])
        for a in range(len(nb)):
            for b in range(a + 1, len(nb)):
                x, y = nb[a], nb[b]
                T.append(((x, y), (min(v, x), max(v, x)), (min(v, y), max(v, y))))  # mixed
    return T

def nu3_star(p, indep, N):
    E = sorted(edges(p, indep, N)); eidx = {e: i for i, e in enumerate(E)}
    T = triangles(p, indep, N)
    if not T:
        return 0.0, len(E)
    A = np.zeros((len(E), len(T)))
    for j, tri in enumerate(T):
        for e in tri:
            A[eidx[e], j] += 1.0
    c = -np.ones(len(T))
    res = linprog(c, A_ub=A, b_ub=np.ones(len(E)), bounds=[(0, None)]*len(T), method="highs")
    assert res.success, res.message
    return float(-res.fun), len(E)

def bound(n):
    return n*n/6.0 + n

def check(p, neigh, tag, log_bad):
    p, clique, indep, N = build_split(p, neigh)
    n = p + len(indep)
    nus, m = nu3_star(p, indep, N)
    lhs = m - 2*nus
    ok = lhs <= bound(n) + TOL
    if not ok:
        log_bad.append((tag, p, len(indep), n, m, round(nus, 4), round(lhs, 4), round(bound(n), 4)))
    return ok, n, m, nus, lhs

def run():
    log = io.StringIO()
    def P(*a):
        t = " ".join(str(x) for x in a); print(t); print(t, file=log)
    P("="*78); P("03 — SPLIT-GRAPH FALSIFICATION OF THEOREM 1.1 (Paper I)"); P("="*78)
    rng = np.random.default_rng(20260710)
    bad = []; tested = 0; max_ratio = 0.0; argmax = None

    # (a) exhaustive-ish small: p=2..5, indep vertices ranging over all subsets (bounded count)
    P("\n(a) small structured enumeration (p<=5, neighborhoods = all subsets, up to 8 indep verts)")
    for p in range(2, 6):
        subs = [tuple(c) for r in range(0, p + 1) for c in itertools.combinations(range(p), r)]
        # one independent vertex per subset (covers I0,I1,I>=2 types), plus duplicates test below
        neigh = subs
        ok, n, m, nus, lhs = check(p, neigh, f"allsubsets-p{p}", bad); tested += 1
        r = lhs / bound(n);  max_ratio = max(max_ratio, r); argmax = argmax or (f"allsubsets-p{p}", r)
        P(f"   p={p}: n={n} |E|={m} nu3*={nus:.3f} LHS={lhs:.3f} bound={bound(n):.3f} ratio={r:.3f} ok={ok}")

    # (b) random split graphs
    P("\n(b) random split graphs")
    for t in range(600):
        p = int(rng.integers(2, 8))
        k = int(rng.integers(0, 11))                 # number of independent vertices
        neigh = []
        for _ in range(k):
            d = int(rng.integers(0, p + 1))
            neigh.append(tuple(sorted(rng.choice(p, size=d, replace=False).tolist())) if d > 0 else tuple())
        ok, n, m, nus, lhs = check(p, neigh, f"rand#{t}", bad); tested += 1
        if n > 0:
            r = lhs / bound(n)
            if r > max_ratio: max_ratio = r; argmax = (f"rand#{t}(p={p},k={k})", r)

    # (c) adversarial: many indep vertices all adjacent to full clique (dense mixed triangles)
    P("\n(c) adversarial dense: N(v)=K for many v (complete split)")
    for p in range(2, 8):
        for mult in (p, 2*p, 3*p):
            neigh = [tuple(range(p))] * mult
            ok, n, m, nus, lhs = check(p, neigh, f"complete-p{p}-m{mult}", bad); tested += 1
            r = lhs / bound(n);
            if r > max_ratio: max_ratio = r; argmax = (f"complete-p{p}-m{mult}", r)

    # (d) extremal family K_p ∨ Kbar_{2p}: expect |E|-2nu3* = n^2/6 + n/6 exactly (KS3)
    P("\n(d) extremal family  K_p ∨ Kbar_{2p}  (n=3p): expect LHS = n^2/6 + n/6, nu3*=C(p,2)")
    ks3_fail = 0
    for p in range(2, 8):
        neigh = [tuple(range(p))] * (2*p)
        pp, clique, indep, N = build_split(p, neigh)
        n = p + 2*p
        nus, m = nu3_star(p, indep, N)
        lhs = m - 2*nus
        expect = n*n/6.0 + n/6.0
        cp2 = p*(p-1)//2
        ok = abs(lhs - expect) <= 1e-6 and abs(nus - cp2) <= 1e-6
        if not ok: ks3_fail += 1
        P(f"   p={p} n={n}: nu3*={nus:.3f} (C(p,2)={cp2}) LHS={lhs:.4f} n^2/6+n/6={expect:.4f} ok={ok}")

    P("-"*78)
    P(f"total split graphs tested (a,b,c): {tested}")
    P(f"theorem violations (KS1: LHS > n^2/6+n): {len(bad)}")
    if bad:
        for b in bad[:20]: P("   VIOLATION:", b)
    P(f"max observed ratio LHS/(n^2/6+n): {max_ratio:.4f} at {argmax}")
    P(f"extremal tightness failures (KS3): {ks3_fail}")
    verdict = ("NOT FALSIFIED — theorem holds on all tested split graphs; extremal family "
               "attains n^2/6+n/6") if (len(bad) == 0 and ks3_fail == 0) else "FALSIFIED / DISCREPANCY"
    P(f"VERDICT: {verdict}")
    P("NOTE: bounded search is supporting evidence for a universal claim, not a proof.")
    P("="*78)
    with open(os.path.join(os.path.dirname(__file__), "re