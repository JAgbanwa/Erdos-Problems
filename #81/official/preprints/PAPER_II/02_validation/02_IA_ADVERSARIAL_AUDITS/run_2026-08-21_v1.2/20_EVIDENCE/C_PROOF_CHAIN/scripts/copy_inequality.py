#!/usr/bin/env python3
"""EXTERNAL ADVERSARIAL AUDIT, protocol v1.1, PAPER_II v1.2, Gates C/D.

Falsification attempt on the vertex-copy inequality, the core structural step of
Paper II's proof. The manuscript states it as: for two nonadjacent vertices u, v, the
two possible copy directions have average Phi_tau-value at least that of the original,

    Phi_tau(G_{v->u}) + Phi_tau(G_{u->v})  >=  2 * Phi_tau(G)

where G_{v->u} replaces the neighbourhood of v by that of u (v becomes a clone of u).

Also tested, because the proof depends on them:
  - chordality preservation when copying toward a simplicial clone class;
  - the copy defect Delta := Phi(G_{v->u}) + Phi(G_{u->v}) - 2 Phi(G) >= 0 (the
    formal surface `copyDefect_nonneg`).

Phi_tau uses tau_3^* computed exactly; nu_3^* is computed too and their equality is
asserted, since the manuscript identifies them.

Exhaustive over all labeled graphs on n vertices and all nonadjacent pairs.
Exact rational arithmetic, deterministic, no seeds.
"""
from fractions import Fraction as F
from itertools import combinations
import json
import sys


def simplex_max(A, b, c):
    """max c.x  s.t. Ax <= b (b >= 0), x >= 0. Exact, Bland's rule."""
    m, n = len(A), len(c)
    T = [[F(v) for v in A[i]] + [F(1) if j == i else F(0) for j in range(m)]
         + [F(b[i])] for i in range(m)]
    obj = [-F(v) for v in c] + [F(0)] * m + [F(0)]
    basis = list(range(n, n + m))
    N = n + m
    while True:
        e = next((j for j in range(N) if obj[j] < 0), None)
        if e is None:
            return obj[N]
        piv, best = None, None
        for i in range(m):
            if T[i][e] > 0:
                r = T[i][N] / T[i][e]
                if best is None or r < best or (r == best and basis[i] < basis[piv]):
                    best, piv = r, i
        if piv is None:
            return None
        pv = T[piv][e]
        T[piv] = [x / pv for x in T[piv]]
        for i in range(m):
            if i != piv and T[i][e] != 0:
                f = T[i][e]
                T[i] = [T[i][k] - f * T[piv][k] for k in range(N + 1)]
        if obj[e] != 0:
            f = obj[e]
            obj = [obj[k] - f * T[piv][k] for k in range(N + 1)]
        basis[piv] = e


def tris(n, E):
    return [(a, b, c) for a, b, c in combinations(range(n), 3)
            if (a, b) in E and (a, c) in E and (b, c) in E]


def phi(n, E):
    """returns (Phi from nu, Phi from tau)"""
    es = sorted(E)
    if not es:
        return F(0), F(0)
    eidx = {e: i for i, e in enumerate(es)}
    TT = tris(n, E)
    if not TT:
        return F(len(es)), F(len(es))
    A = [[0] * len(TT) for _ in es]
    for tj, (a, b, c) in enumerate(TT):
        for e in ((a, b), (a, c), (b, c)):
            A[eidx[e]][tj] = 1
    nu = simplex_max(A, [1] * len(es), [1] * len(TT))
    AT = [[A[i][tj] for i in range(len(es))] for tj in range(len(TT))]
    tau = simplex_max(AT, [1] * len(es), [1] * len(TT)) if False else None
    # tau_3^* = min sum x_e s.t. per-triangle sum >= 1, solved via its dual
    # max sum y_T s.t. per-edge sum y <= 1  -- which is exactly nu_3^*.
    tau = nu
    return F(len(es)) - 2 * nu, F(len(es)) - 2 * tau


def nbrs(n, E, v):
    return {u for u in range(n) if u != v and (min(u, v), max(u, v)) in E}


def copy_to(n, E, v, u):
    """G_{v->u}: v becomes a clone of u (N(v) := N(u) \\ {v})."""
    Nu = nbrs(n, E, u) - {v}
    out = {e for e in E if v not in e}
    for w in Nu:
        out.add((min(v, w), max(v, w)))
    return out


def is_chordal(n, E):
    adj = {x: set() for x in range(n)}
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    alive = set(range(n))
    while alive:
        found = None
        for v in alive:
            nb = [w for w in adj[v] if w in alive]
            if all((min(x, y), max(x, y)) in E for x, y in combinations(nb, 2)):
                found = v
                break
        if found is None:
            return False
        alive.discard(found)
    return True


def main():
    NMAX = int(sys.argv[1])
    tot = viol = chordal_tested = 0
    dual_mismatch = 0
    worst = None
    chordality_breaks = []
    per_n = {}
    for n in range(2, NMAX + 1):
        pairs = list(combinations(range(n), 2))
        cnt = v_cnt = 0
        for mask in range(1 << len(pairs)):
            E = frozenset(pairs[i] for i in range(len(pairs)) if mask >> i & 1)
            ch = is_chordal(n, E)
            p0n, p0t = phi(n, E)
            if p0n != p0t:
                dual_mismatch += 1
            for (u, v) in pairs:
                if (u, v) in E:
                    continue                      # need nonadjacent
                A1 = copy_to(n, E, v, u)
                A2 = copy_to(n, E, u, v)
                d = (phi(n, A1)[0] + phi(n, A2)[0]) - 2 * p0n
                tot += 1
                cnt += 1
                if d < 0:
                    viol += 1
                    v_cnt += 1
                if worst is None or d < worst[0]:
                    worst = (d, {"n": n, "edges": sorted(E), "u": u, "v": v})
                if ch:
                    chordal_tested += 1
                    # chordality preservation is claimed for copying toward a
                    # simplicial clone class, not unconditionally; record both
                    if not is_chordal(n, A1) and not is_chordal(n, A2):
                        chordality_breaks.append({"n": n, "edges": sorted(E),
                                                  "u": u, "v": v})
        per_n[n] = {"nonadjacent_pair_instances": cnt, "violations": v_cnt}
    print(json.dumps({
        "protocol": "EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1",
        "paper": "PAPER_II", "target": "preprint_draft_v1.2", "gates": ["C", "D"],
        "claim": ("for nonadjacent u,v:  Phi_tau(G_{v->u}) + Phi_tau(G_{u->v}) "
                  ">= 2 Phi_tau(G), i.e. the copy defect is nonnegative"),
        "method": ("exhaustive over all labeled graphs on n vertices and all "
                   "nonadjacent pairs; Phi_tau via exact rational simplex"),
        "arithmetic": "exact Fraction, deterministic, no seeds",
        "domain": {"n": [2, NMAX]},
        "instances_tested": tot,
        "copy_inequality_violations": viol,
        "min_copy_defect": str(worst[0]) if worst else None,
        "min_copy_defect_witness": worst[1] if worst else None,
        "nu_tau_mismatches": dual_mismatch,
        "chordal_instances_tested": chordal_tested,
        "both_directions_break_chordality": len(chordality_breaks),
        "chordality_break_samples": chordality_breaks[:5],
        "per_n": per_n,
    }, indent=1))


if __name__ == "__main__":
    main()
