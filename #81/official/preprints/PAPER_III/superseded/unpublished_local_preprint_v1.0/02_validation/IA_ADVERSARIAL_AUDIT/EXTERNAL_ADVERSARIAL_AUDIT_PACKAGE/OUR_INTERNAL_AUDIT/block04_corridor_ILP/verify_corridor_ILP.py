"""
Paper III — INTERNAL AUDIT, Block 04: corridor integral packing (Lemma 5.1 / E-5.1
and Corollary 5.3), by EXACT integer linear programming.

For systematically generated split graphs G (clique K of order p; q independent
vertices with arbitrary neighbourhoods N_i in K) we compute the maximum edge-disjoint
triangle packing number nu3(G) EXACTLY via a 0/1 ILP (PuLP + CBC):

    maximize   sum_t x_t
    subject to sum_{t : e in t} x_t <= 1  for every edge e,   x_t in {0,1},

and then verify, with exact rational arithmetic on the closed forms:

  (E-5.1)  if q >= r_p := chi'(K_p):   nu3(G) >= (1/q) * sum_i C(d_i, 2).
  (5.3)    if q >= r_p:   Phi(G) <= n^2/6 + p/2 + (s^2 - 6s + 3)/12,  s = 2p - q, n = p+q.
  (basic)  0 <= Phi(G) = |E| - 2 nu3(G)  and  3*nu3(G) <= |E|.

This reproduces the paper's exact-ILP corridor audits (Appendix C).

Output: results/corridor_ILP_results.txt
"""
import os
import sys
import itertools
from fractions import Fraction as Q

import pulp

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "common"))
from audit_formulas import C2, rp  # noqa: E402

OUT = []
def emit(x=""): OUT.append(str(x))


def build_graph(p, neighborhoods):
    """clique 0..p-1 ; independent p..p+q-1 with given neighborhoods (list of sets)."""
    q = len(neighborhoods)
    clique = list(range(p))
    tris, edges = [], set()
    for a, b in itertools.combinations(clique, 2):
        edges.add(frozenset((a, b)))
    for t in itertools.combinations(clique, 3):
        tris.append(frozenset(t))
    for idx, N in enumerate(neighborhoods):
        i = p + idx
        for a in N:
            edges.add(frozenset((a, i)))
        for a, b in itertools.combinations(sorted(N), 2):
            tris.append(frozenset((a, b, i)))
    return tris, list(edges), q


def nu3_ILP(tris, edges):
    if not tris:
        return 0
    prob = pulp.LpProblem("nu3", pulp.LpMaximize)
    x = [pulp.LpVariable(f"x{i}", cat="Binary") for i in range(len(tris))]
    prob += pulp.lpSum(x)
    for e in edges:
        inc = [x[ti] for ti, t in enumerate(tris) if e <= t]
        if inc:
            prob += pulp.lpSum(inc) <= 1
    prob.solve(pulp.PULP_CBC_CMD(msg=0))
    return int(round(pulp.value(prob.objective)))


def profiles(p, q):
    """A deterministic, reproducible family of neighbourhood profiles for (p,q)."""
    subsets = [frozenset(s) for k in range(p + 1)
               for s in itertools.combinations(range(p), k)]
    out = []
    # (a) all independent vertices share one neighbourhood (common profile), each size
    for N in subsets:
        out.append([N] * q)
    # (b) a "staircase": vertex i gets the first (i mod (p+1)) clique vertices
    out.append([frozenset(range(i % (p + 1))) for i in range(q)])
    # (c) alternating full / empty / half
    half = frozenset(range((p + 1) // 2))
    full = frozenset(range(p))
    pat = [full, frozenset(), half]
    out.append([pat[i % 3] for i in range(q)])
    return out


emit("=" * 72)
emit("Paper III — Block 04: corridor integral packing (E-5.1 & Cor 5.3), exact ILP")
emit("nu3(G) computed by 0/1 ILP (PuLP/CBC); bounds checked with exact rationals.")
emit("=" * 72)
emit()

total = 0
e51_applicable = 0
e51_pass = 0
e51_fail = []
c53_applicable = 0
c53_pass = 0
c53_fail = []
basic_fail = []

# small grid so ILP is fast and exact
for p in range(3, 6):
    for q in range(1, 7):
        for neighborhoods in profiles(p, q):
            total += 1
            tris, edges, qq = build_graph(p, neighborhoods)
            E = len(edges)
            nu3 = nu3_ILP(tris, edges)
            Phi = E - 2 * nu3
            # basic sanity
            if not (0 <= Phi and 3 * nu3 <= E):
                basic_fail.append((p, q, [sorted(N) for N in neighborhoods], nu3, E))
            d = [len(N) for N in neighborhoods]
            r_p = rp(p)
            # E-5.1 (requires q >= r_p)
            if q >= r_p:
                e51_applicable += 1
                rhs = sum((C2(di) for di in d), Q(0)) / q
                if Q(nu3) >= rhs:
                    e51_pass += 1
                else:
                    e51_fail.append((p, q, d, nu3, rhs))
                # Corollary 5.3
                c53_applicable += 1
                n = p + q
                s = 2 * p - q
                bound = Q(n) ** 2 / 6 + Q(p, 2) + (Q(s) ** 2 - 6 * Q(s) + 3) / 12
                if Q(Phi) <= bound:
                    c53_pass += 1
                else:
                    c53_fail.append((p, q, Phi, bound))

emit(f"Split-graph instances audited: {total}")
emit(f"Basic sanity (0 <= Phi, 3*nu3 <= |E|): "
     f"{total - len(basic_fail)}/{total} pass")
emit()
emit(f"E-5.1  nu3 >= (1/q) sum C(d_i,2)   (applicable when q >= r_p):")
emit(f"    applicable instances: {e51_applicable}")
emit(f"    PASS: {e51_pass}/{e51_applicable}   FAIL: {len(e51_fail)}")
emit()
emit(f"Corollary 5.3  Phi <= n^2/6 + p/2 + (s^2-6s+3)/12   (q >= r_p):")
emit(f"    applicable instances: {c53_applicable}")
emit(f"    PASS: {c53_pass}/{c53_applicable}   FAIL: {len(c53_fail)}")
emit()
if e51_fail:
    emit("E-5.1 FAILURES (first 10):")
    for r in e51_fail[:10]:
        emit(f"    p={r[0]} q={r[1]} d={r[2]} nu3={r[3]} rhs={r[4]}")
if c53_fail:
    emit("Cor 5.3 FAILURES (first 10):")
    for r in c53_fail[:10]:
        emit(f"    p={r[0]} q={r[1]} Phi={r[2]} bound={r[3]}")
if basic_fail:
    emit("BASIC FAILURES (first 10):")
    for r in basic_fail[:10]:
        emit(f"    {r}")

emit("=" * 72)
ok = (not e51_fail) and (not c53_fail) and (not basic_fail)
emit(f"VERDICT: {'PASS' if ok else 'FAIL'}  "
     f"(E-5.1 {e51_pass}/{e51_applicable}, Cor5.3 {c53_pass}/{c53_applicable}, "
     f"basic {total - len(basic_fail)}/{total})")
emit("=" * 72)

report = "\n".join(OUT)
print(report)
with open("results/corridor_ILP_results.txt", "w", encoding="utf-8") as f:
    f.write(report + "\n")
sys.exit(0 if ok else 1)
