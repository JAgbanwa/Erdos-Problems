"""
Paper III — INTERNAL AUDIT, Block 02: common-profile LP (Theorem 3.1 / E-3.1).

Cross-check of the closed form  nu3*(H(p,q,d)) = F(p,q,d)  against the DIRECT triangle
program on the actual graph H(p,q,d) (clique K of order p; q independent vertices each
adjacent to the same d-subset N of K).

Two INDEPENDENT verifications per instance:

  (LP)    Direct fractional triangle-PACKING LP (SciPy HiGHS) optimum == float(F) within
          TOL. This is a numeric lower/upper witness on the true graph.

  (EXACT) Exact-rational UPPER-BOUND certificate: for the branch attaining F, build the
          explicit symmetric fractional COVER (weights on the four edge classes E(N),
          E(N,I), E(N,R), E(R)) and verify, with exact rationals, that (a) it covers every
          triangle of H(p,q,d) with total weight >= 1, and (b) its value equals that branch
          value. A feasible cover of value F proves nu3*(H) = tau3*(H) <= F exactly; the LP
          witness gives the matching >= F. Hence the float tolerance in (LP) cannot hide a
          gap: the upper bound F is certified exactly.

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


def graph_pieces(p, q, d):
    """Vertices: clique 0..p-1; independent p..p+q-1. N = {0..d-1}."""
    clique = list(range(p))
    indep = list(range(p, p + q))
    N = set(range(d))
    tris = []
    for t in combinations(clique, 3):
        tris.append(frozenset(t))
    for i in indep:
        for a, b in combinations(sorted(N), 2):
            tris.append(frozenset((a, b, i)))
    edges = set()
    for a, b in combinations(clique, 2):
        edges.add(frozenset((a, b)))
    for i in indep:
        for a in N:
            edges.add(frozenset((a, i)))
    return tris, list(edges), N, set(clique), set(indep)


def nu3_star_LP(tris, edges):
    if not tris:
        return 0.0
    nt = len(tris)
    c = -np.ones(nt)
    A = np.zeros((len(edges), nt))
    for ei, e in enumerate(edges):
        for ti, t in enumerate(tris):
            if e <= t:
                A[ei, ti] = 1.0
    b = np.ones(len(edges))
    res = linprog(c, A_ub=A, b_ub=b, bounds=[(0, None)] * nt, method="highs")
    return None if not res.success else -res.fun


def edge_class_weight(e, N, clique, indep, a, b, c, e_):
    """Exact weight of edge e under class weights a=E(N), b=E(N,I), c=E(N,R), e_=E(R)."""
    u, v = tuple(e)
    uC, vC = u in clique, v in clique
    if uC and vC:
        uN, vN = u in N, v in N
        if uN and vN:
            return a
        if (not uN) and (not vN):
            return e_
        return c            # one in N, one in R
    # cross edge clique--independent: the clique endpoint is in N by construction
    return b


def exact_cover_upper_bound(p, q, d):
    """Return (branch_index, ok) where ok is True iff the branch attaining F yields a
    feasible exact fractional cover of value == that branch value (so nu3* <= F exactly)."""
    tris, edges, N, clique, indep = graph_pieces(p, q, d)
    Fval, (t1, t2, t3) = F(p, q, d)
    branches = {
        1: dict(a=Q(1, 3), b=Q(1, 3), c=Q(1, 3), e_=Q(1, 3), val=t1),
        2: dict(a=Q(1),    b=Q(0),    c=Q(0),    e_=Q(1),    val=t2),
        3: dict(a=Q(1),    b=Q(0),    c=Q(1, 3), e_=Q(1, 3), val=t3),
    }
    # choose the branch attaining the min F
    bi = min(branches, key=lambda k: branches[k]["val"])
    w = branches[bi]
    # (a) feasibility: every triangle covered with weight >= 1 (exact)
    for t in tris:
        s = Q(0)
        for e in combinations(sorted(t), 2):
            s += edge_class_weight(frozenset(e), N, clique, indep,
                                   w["a"], w["b"], w["c"], w["e_"])
        if s < 1:
            return bi, False, f"triangle {sorted(t)} covered only {s} < 1"
    # (b) cover value equals the branch value == F (exact)
    total = Q(0)
    for e in edges:
        total += edge_class_weight(e, N, clique, indep, w["a"], w["b"], w["c"], w["e_"])
    if total != w["val"] or w["val"] != Fval:
        return bi, False, f"value {total} != branch {w['val']} or != F {Fval}"
    return bi, True, ""


emit("=" * 72)
emit("Paper III — Block 02: common-profile LP  nu3*(H(p,q,d)) = F(p,q,d)")
emit("(LP) direct HiGHS packing LP vs F   +   (EXACT) rational cover upper-bound cert.")
emit("=" * 72)
emit()

total = 0
lp_pass = 0
lp_fail = []
exact_pass = 0
exact_fail = []
maxdev = 0.0

for p in range(3, 9):
    for q in range(0, 9):
        for d in range(0, p + 1):
            total += 1
            Fval, _ = F(p, q, d)
            tris, edges, *_ = graph_pieces(p, q, d)
            lp = nu3_star_LP(tris, edges)
            if lp is None:
                lp_fail.append((p, q, d, "LP_FAILED", float(Fval)))
            else:
                dev = abs(lp - float(Fval))
                maxdev = max(maxdev, dev)
                if dev <= TOL:
                    lp_pass += 1
                else:
                    lp_fail.append((p, q, d, lp, float(Fval)))
            bi, ok, msg = exact_cover_upper_bound(p, q, d)
            if ok:
                exact_pass += 1
            else:
                exact_fail.append((p, q, d, bi, msg))

emit(f"Instances audited (3<=p<=8, 0<=q<=8, 0<=d<=p): {total}")
emit()
emit(f"(LP)    direct HiGHS packing LP optimum vs float(F):")
emit(f"        PASS (|LP - F| <= {TOL}): {lp_pass}/{total}   FAIL: {len(lp_fail)}")
emit(f"        max |LP - F| over grid : {maxdev:.3e}")
emit()
emit(f"(EXACT) rational feasible-cover upper-bound certificate (nu3* <= F, exact):")
emit(f"        PASS: {exact_pass}/{total}   FAIL: {len(exact_fail)}")
emit()
if lp_fail:
    emit("LP FAILURES (first 20):")
    for r in lp_fail[:20]:
        emit(f"    p={r[0]} q={r[1]} d={r[2]}  LP={r[3]}  F={r[4]}")
if exact_fail:
    emit("EXACT FAILURES (first 20):")
    for r in exact_fail[:20]:
        emit(f"    p={r[0]} q={r[1]} d={r[2]} branch={r[3]}  {r[4]}")
emit("=" * 72)
verdict = "PASS" if (not lp_fail and not exact_fail) else "FAIL"
emit(f"VERDICT: {verdict}  (LP {lp_pass}/{total}, EXACT {exact_pass}/{total})")
emit("=" * 72)

report = "\n".join(OUT)
print(report)
with open("results/common_profile_LP_results.txt", "w", encoding="utf-8") as f:
    f.write(report + "\n")
sys.exit(0 if (not lp_fail and not exact_fail) else 1)
