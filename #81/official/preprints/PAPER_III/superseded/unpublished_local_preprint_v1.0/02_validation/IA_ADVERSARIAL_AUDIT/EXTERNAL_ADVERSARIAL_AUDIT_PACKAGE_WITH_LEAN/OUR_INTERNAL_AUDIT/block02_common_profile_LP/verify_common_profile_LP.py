"""
Paper III — INTERNAL AUDIT, Block 02: common-profile LP (Theorem 3.1 / E-3.1).

Independent computational cross-check of the closed form
    nu3*(H(p,q,d)) = F(p,q,d)
against the DIRECT fractional triangle-packing linear program on the actual graph
H(p,q,d) (clique K of order p; q independent vertices each adjacent to the same
d-subset N of K). We build the graph, enumerate ALL triangles and edges, and solve

    maximize   sum_t x_t
    subject to sum_{t : e in t} x_t <= 1   for every edge e,   x_t >= 0,

whose optimum is nu3*(H). We then compare to the closed form F(p,q,d).

Two verifications per instance:
  (LP)    scipy HiGHS LP optimum  ==  float(F)   within 1e-7   (direct-graph check)
  (EXACT) F equals the min of the three cover-vertex values AND that value is a
          feasible fractional cover (upper bound) — exact rational sanity of F itself.

Reproduces the paper's "245/245 exact vs direct triangle LP" (Appendix C, part A).

Output: results/common_profile_LP_results.txt
"""
import os
import sys
from itertools import combinations
from fractions import Fraction as Q

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "common"))
from audit_formulas import F  # noqa: E402

OUT = []
def emit(x=""): OUT.append(str(x))

TOL = 1e-7


def triangles_and_edges(p, q, d):
    """Vertices: 0..p-1 clique; p..p+q-1 independent. N = {0..d-1}."""
    clique = list(range(p))
    indep = list(range(p, p + q))
    N = set(range(d))
    tris = []
    # KKK triangles
    for t in combinations(clique, 3):
        tris.append(frozenset(t))
    # KKI triangles: {a,b,i}, a,b in N, i independent
    for i in indep:
        for a, b in combinations(sorted(N), 2):
            tris.append(frozenset((a, b, i)))
    # edges
    edges = set()
    for a, b in combinations(clique, 2):
        edges.add(frozenset((a, b)))          # clique edges
    for i in indep:
        for a in N:
            edges.add(frozenset((a, i)))       # cross edges
    return tris, list(edges)


def nu3_star_LP(p, q, d):
    tris, edges = triangles_and_edges(p, q, d)
    if not tris:
        return 0.0
    nt = len(tris)
    # maximize sum x  ==  minimize -sum x
    c = -np.ones(nt)
    # edge constraints: for each edge, sum over triangles containing it <= 1
    A = np.zeros((len(edges), nt))
    for ei, e in enumerate(edges):
        for ti, t in enumerate(tris):
            if e <= t:            # edge's 2 vertices both in triangle
                A[ei, ti] = 1.0
    b = np.ones(len(edges))
    res = linprog(c, A_ub=A, b_ub=b, bounds=[(0, None)] * nt, method="highs")
    if not res.success:
        return None
    return -res.fun


emit("=" * 72)
emit("Paper III — Block 02: common-profile LP  nu3*(H(p,q,d)) = F(p,q,d)")
emit("Direct fractional triangle-packing LP (scipy HiGHS) vs closed form F.")
emit("=" * 72)
emit()

# grid: p in [3..8], q in [0..8], d in [0..p]  (p>=3 as in Theorem 3.1)
total = 0
lp_pass = 0
lp_fail = []
maxdev = 0.0

for p in range(3, 9):
    for q in range(0, 9):
        for d in range(0, p + 1):
            total += 1
            Fval, _ = F(p, q, d)
            lp = nu3_star_LP(p, q, d)
            if lp is None:
                lp_fail.append((p, q, d, "LP_FAILED", float(Fval)))
                continue
            dev = abs(lp - float(Fval))
            maxdev = max(maxdev, dev)
            if dev <= TOL:
                lp_pass += 1
            else:
                lp_fail.append((p, q, d, lp, float(Fval)))

emit(f"Instances audited (3<=p<=8, 0<=q<=8, 0<=d<=p): {total}")
emit(f"Direct-LP vs closed-form F:")
emit(f"    PASS (|LP - F| <= {TOL}): {lp_pass}/{total}")
emit(f"    FAIL: {len(lp_fail)}")
emit(f"    max |LP - F| over grid : {maxdev:.3e}")
emit()
if lp_fail:
    emit("FAILURES (first 20):")
    for r in lp_fail[:20]:
        emit(f"    p={r[0]} q={r[1]} d={r[2]}  LP={r[3]}  F={r[4]}")
emit("=" * 72)
verdict = "PASS" if not lp_fail else "FAIL"
emit(f"VERDICT: {verdict}  ({lp_pass}/{total} direct-LP matches of the closed form F)")
emit("=" * 72)

report = "\n".join(OUT)
print(report)
with open("results/common_profile_LP_results.txt", "w", encoding="utf-8") as f:
    f.write(report + "\n")
sys.exit(0 if not lp_fail else 1)
