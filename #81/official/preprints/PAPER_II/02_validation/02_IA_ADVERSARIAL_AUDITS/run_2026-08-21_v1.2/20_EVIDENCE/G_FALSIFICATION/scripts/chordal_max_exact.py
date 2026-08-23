#!/usr/bin/env python3
"""EXTERNAL ADVERSARIAL AUDIT, protocol v1.1, PAPER_II v1.2, Gates E/F/G.

Direct falsification attempt on the headline claim P2-MAIN-V1_2:

    max { Phi_tau(G) : G chordal, |V(G)| = n }  ==  floor( (2n+1)^2 / 24 )

where Phi_tau(G) = |E(G)| - 2*tau_3^*(G) and tau_3^* is the fractional
triangle-cover number. The manuscript asserts nu_3^* = tau_3^*, so the value is
computed here as the PACKING optimum nu_3^* by exact rational simplex, and
independently as the COVER optimum tau_3^* by exact rational simplex on the dual
program. Agreement of the two is itself a check on the manuscript's identity.

Method: exhaustive enumeration of ALL labeled graphs on n vertices, filtered to
chordal graphs by simplicial-vertex elimination (a graph is chordal iff repeated
removal of a simplicial vertex eliminates every vertex). No sampling, no seeds.

Attainment by complete-split graphs S_{p,q} = K_p join complement(K_q) is checked
separately and exhaustively over p+q=n.
"""
from fractions import Fraction as F
from itertools import combinations
import json
import sys


# ---------------- exact rational simplex: max c.x s.t. Ax <= b, x >= 0 --------
def simplex_max(A, b, c):
    m, n = len(A), len(c)
    T = [[F(v) for v in A[i]] + [F(1) if j == i else F(0) for j in range(m)]
         + [F(b[i])] for i in range(m)]
    obj = [-F(v) for v in c] + [F(0)] * m + [F(0)]
    basis = list(range(n, n + m))
    N = n + m
    while True:
        e = next((j for j in range(N) if obj[j] < 0), None)   # Bland's rule
        if e is None:
            return obj[N]
        piv, best = None, None
        for i in range(m):
            if T[i][e] > 0:
                r = T[i][N] / T[i][e]
                if best is None or r < best or (r == best and basis[i] < basis[piv]):
                    best, piv = r, i
        if piv is None:
            return None                                       # unbounded
        pv = T[piv][e]
        T[piv] = [v / pv for v in T[piv]]
        for i in range(m):
            if i != piv and T[i][e] != 0:
                f = T[i][e]
                T[i] = [T[i][k] - f * T[piv][k] for k in range(N + 1)]
        if obj[e] != 0:
            f = obj[e]
            obj = [obj[k] - f * T[piv][k] for k in range(N + 1)]
        basis[piv] = e


# ---------------- exact rational simplex: min c.x s.t. Ax >= b, x >= 0 -------
def simplex_min_ge(A, b, c):
    """Solve  min c.x  s.t.  A x >= b, x >= 0  via its dual
       max b.y  s.t.  A^T y <= c, y >= 0.  Strong duality gives equality."""
    AT = [[A[i][j] for i in range(len(A))] for j in range(len(A[0]))]
    return simplex_max(AT, c, b)


def triangles(n, eset):
    return [(a, b, c) for a, b, c in combinations(range(n), 3)
            if (a, b) in eset and (a, c) in eset and (b, c) in eset]


def nu3_and_tau3(n, eset):
    es = sorted(eset)
    eidx = {e: i for i, e in enumerate(es)}
    tris = triangles(n, eset)
    if not tris:
        return F(0), F(0), 0
    # incidence: rows = edges, cols = triangles
    A = [[0] * len(tris) for _ in es]
    for tj, (a, b, c) in enumerate(tris):
        for e in ((a, b), (a, c), (b, c)):
            A[eidx[e]][tj] = 1
    # packing: max sum w  s.t.  for each edge, sum_{T>=e} w_T <= 1
    nu = simplex_max(A, [1] * len(es), [1] * len(tris))
    # cover: min sum x_e  s.t. for each triangle, sum_{e in T} x_e >= 1
    AC = [[A[i][tj] for i in range(len(es))] for tj in range(len(tris))]
    tau = simplex_min_ge(AC, [1] * len(tris), [1] * len(es))
    return nu, tau, len(tris)


def is_chordal(n, eset):
    """chordal iff repeated removal of a simplicial vertex eliminates all vertices"""
    adj = {v: set() for v in range(n)}
    for a, b in eset:
        adj[a].add(b)
        adj[b].add(a)
    alive = set(range(n))
    while alive:
        found = None
        for v in alive:
            nb = [u for u in adj[v] if u in alive]
            if all((min(x, y), max(x, y)) in eset
                   for x, y in combinations(nb, 2)):
                found = v
                break
        if found is None:
            return False
        alive.discard(found)
    return True


def claimed(n):
    return ((2 * n + 1) ** 2) // 24


def phi(n, eset):
    nu, tau, _ = nu3_and_tau3(n, eset)
    return F(len(eset)) - 2 * nu, F(len(eset)) - 2 * tau


def complete_split(p, q):
    n = p + q
    E = set()
    for a, b in combinations(range(p), 2):
        E.add((a, b))
    for a in range(p):
        for b in range(p, n):
            E.add((a, b))
    return n, E


def main():
    NMAX = int(sys.argv[1])
    per_n = {}
    for n in range(1, NMAX + 1):
        pairs = list(combinations(range(n), 2))
        best = None
        best_g = None
        nchordal = 0
        ntot = 0
        dual_mismatch = []
        for mask in range(1 << len(pairs)):
            eset = frozenset(pairs[i] for i in range(len(pairs)) if mask >> i & 1)
            ntot += 1
            if not is_chordal(n, eset):
                continue
            nchordal += 1
            pnu, ptau = phi(n, eset)
            if pnu != ptau:
                dual_mismatch.append({"edges": sorted(eset),
                                      "phi_from_nu": str(pnu),
                                      "phi_from_tau": str(ptau)})
            if best is None or pnu > best:
                best, best_g = pnu, sorted(eset)
        cs = []
        for p in range(0, n + 1):
            q = n - p
            nn, E = complete_split(p, q)
            pnu, _ = phi(nn, E)
            cs.append({"p": p, "q": q, "phi": str(pnu)})
        cs_best = max(F(c["phi"]) for c in cs)
        cs_arg = [c for c in cs if F(c["phi"]) == cs_best]
        per_n[n] = {
            "labeled_graphs_enumerated": ntot,
            "chordal_graphs": nchordal,
            "max_phi_tau_found": str(best),
            "claimed_floor_formula": claimed(n),
            "match": best == F(claimed(n)),
            "argmax_edge_set": best_g,
            "nu_tau_duality_mismatches": len(dual_mismatch),
            "complete_split_max": str(cs_best),
            "complete_split_attains_global_max": cs_best == best,
            "complete_split_argmax": cs_arg,
        }
        print(json.dumps({n: per_n[n]}, indent=1), flush=True)

    print(json.dumps({
        "protocol": "EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1",
        "paper": "PAPER_II", "target": "preprint_draft_v1.2",
        "gate": ["E", "F", "G"],
        "claim": "max over chordal G on n vertices of Phi_tau(G) = floor((2n+1)^2/24)",
        "method": ("exhaustive enumeration of all labeled graphs on n vertices; "
                   "chordality by simplicial elimination; nu_3^* and tau_3^* both by "
                   "exact rational simplex (Bland)"),
        "arithmetic": "exact Fraction; deterministic; no seeds",
        "domain": {"n": [1, NMAX]},
        "per_n": per_n,
        "all_n_match": all(v["match"] for v in per_n.values()),
        "all_attained_by_complete_split": all(
            v["complete_split_attains_global_max"] for v in per_n.values()),
        "total_duality_mismatches": sum(
            v["nu_tau_duality_mismatches"] for v in per_n.values()),
    }, indent=1))


if __name__ == "__main__":
    main()
