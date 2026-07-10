#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
P3 -- Complete-split cover value & closed form (Prop 6.2 / Cor 6.3, ledger L9/L10)
==================================================================================
Paper II external adversarial audit, spec gate E.

CLAIMS UNDER TEST
-----------------
Prop 6.2 (L9): tau3*(S_{p,q}) =
    0                       if p<=1, or (p,q)=(2,0);
    (P+pq)/3                if p>=3 and 0<=q<=p-1        (non-saturated branch);
    P                       if p>=2 and q>=p-1           (saturated branch);
  where P = C(p,2) = p(p-1)/2.
Cor 6.3 (L10): Phi_tau(S_{p,q}) = P+pq - 2*tau3*(S_{p,q}), giving
    pq - P = p(2n+1-3p)/2   (saturated, n=p+q),
    (P+pq)/3 = p(2n-p-1)/6  (non-saturated).

METHOD
------
For every (p,q) in a wide range: build S_{p,q}, solve the FULL cover LP directly
(auditor's own, over all triangles/edges -- NOT the symmetrized 2-variable LP),
and compare to the closed form. Also check the two Phi_tau closed forms and the
degenerate cases (p<=1, S_{2,0}).

KILL-SWITCH (declared BEFORE running)
-------------------------------------
H3a: |tau3*_LP(S_{p,q}) - closed_form| < 1e-6 for every (p,q) tested.
H3b: both Phi_tau closed forms match P+pq-2*tau3*_LP.
H3c: branch boundary q=p-1 gives equal values from both formulas.
Falsify on any mismatch. Evidence: EXACT_REPRODUCIBLE (LP is exact); the (p,q)
grid is finite/sampled, so universal p,q is supported not proven.
"""
import sys, os, json, platform, itertools
import numpy as np
import networkx as nx
from scipy.optimize import linprog
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from audit_lib import build_pdf, package

RESULTS_TXT = os.path.join(HERE, "p3_results.txt")
RESULTS_CSV = os.path.join(HERE, "p3_results.csv")
PDF = os.path.join(HERE, "P3_report.pdf")


def complete_split(p, q):
    G = nx.Graph()
    K = [("K", i) for i in range(p)]; I = [("I", j) for j in range(q)]
    G.add_nodes_from(K + I)
    for a, b in itertools.combinations(K, 2):
        G.add_edge(a, b)
    for a in K:
        for b in I:
            G.add_edge(a, b)
    return G


def triangles(G):
    nodes = sorted(G.nodes, key=str); adj = {v: set(G.neighbors(v)) for v in nodes}
    return [(a, b, c) for a, b, c in itertools.combinations(nodes, 3)
            if b in adj[a] and c in adj[a] and c in adj[b]]


def tau3_star_LP(G):
    tris = triangles(G)
    if not tris:
        return 0.0
    edges = [tuple(sorted(e, key=str)) for e in G.edges]; eidx = {e: i for i, e in enumerate(edges)}
    A = np.zeros((len(tris), len(edges)))
    for ti, (a, b, c) in enumerate(tris):
        for e in (tuple(sorted((a, b), key=str)), tuple(sorted((a, c), key=str)),
                  tuple(sorted((b, c), key=str))):
            A[ti, eidx[e]] = -1.0
    res = linprog(np.ones(len(edges)), A_ub=A, b_ub=-np.ones(len(tris)),
                  bounds=[(0, None)] * len(edges), method="highs")
    return res.fun


def tau3_closed(p, q):
    P = Fraction(p * (p - 1), 2)
    if p <= 1 or (p == 2 and q == 0):
        return Fraction(0)
    if p >= 3 and q <= p - 1:
        return Fraction(P + p * q, 3)
    # saturated: p>=2 and q>=p-1
    return P


def phi_saturated(p, q):
    n = p + q
    return Fraction(p * (2 * n + 1 - 3 * p), 2)


def phi_nonsat(p, q):
    n = p + q
    return Fraction(p * (2 * n - p - 1), 6)


def main():
    rows = []
    tau_fail = phi_fail = boundary_fail = 0
    n_tested = 0
    for p in range(0, 13):
        for q in range(0, 13):
            if p + q == 0:
                continue
            G = complete_split(p, q)
            lp = tau3_star_LP(G)
            cf = tau3_closed(p, q)
            tau_ok = abs(lp - float(cf)) < 1e-6
            if not tau_ok:
                tau_fail += 1
            e = G.number_of_edges()
            phi_lp = e - 2 * lp
            # which branch?
            saturated = (p >= 2 and q >= p - 1)
            nonsat = (p >= 3 and q <= p - 1)
            phi_cf = None
            if saturated:
                phi_cf = float(phi_saturated(p, q))
            elif nonsat:
                phi_cf = float(phi_nonsat(p, q))
            else:
                phi_cf = e - 2 * float(cf)  # degenerate: tau=0 mostly
            phi_ok = abs(phi_lp - phi_cf) < 1e-6
            if not phi_ok:
                phi_fail += 1
            # boundary q=p-1: both formulas agree
            if p >= 3 and q == p - 1:
                if abs(float(phi_saturated(p, q)) - float(phi_nonsat(p, q))) > 1e-9:
                    boundary_fail += 1
            n_tested += 1
            rows.append(dict(p=p, q=q, n=p + q, edges=e,
                             tau_LP=round(lp, 4), tau_closed=round(float(cf), 4),
                             tau_ok=tau_ok, phi_LP=round(phi_lp, 4),
                             phi_closed=round(phi_cf, 4), phi_ok=phi_ok,
                             branch=("sat" if saturated else "nonsat" if nonsat else "degen")))

    h3a = (tau_fail == 0); h3b = (phi_fail == 0); h3c = (boundary_fail == 0)
    verdict = ("VERIFIED: closed forms for tau3*(S_{p,q}) and Phi_tau(S_{p,q}) match the "
               "direct full cover-LP on the whole (p,q) grid; branch boundary q=p-1 is "
               "consistent; degenerate cases handled."
               if (h3a and h3b and h3c) else
               "FALSIFIED: " + (f"{tau_fail} tau mismatches " if not h3a else "")
               + (f"{phi_fail} phi mismatches " if not h3b else "")
               + (f"{boundary_fail} boundary mismatches " if not h3c else ""))

    with open(RESULTS_TXT, "w", encoding="utf-8") as f:
        f.write("P3 -- Complete-split cover value & closed form (Prop 6.2 / Cor 6.3)\n")
        f.write("=" * 66 + "\n")
        f.write(f"python/networkx : {platform.python_version()} / nx {nx.__version__}\n")
        f.write(f"tau3* method    : auditor's own FULL cover-LP (scipy HiGHS), all triangles\n")
        f.write(f"(p,q) grid      : 0..12 x 0..12 ({n_tested} nondegenerate cells)\n")
        f.write("-" * 66 + "\n")
        f.write("KILL-SWITCH:\n")
        f.write(f"  H3a tau3*_LP == closed form        : "
                f"{'HOLDS' if h3a else 'VIOLATED'} ({tau_fail} mismatches)\n")
        f.write(f"  H3b Phi_tau closed forms == LP     : "
                f"{'HOLDS' if h3b else 'VIOLATED'} ({phi_fail} mismatches)\n")
        f.write(f"  H3c branch boundary q=p-1 agrees   : "
                f"{'HOLDS' if h3c else 'VIOLATED'} ({boundary_fail} mismatches)\n")
        f.write(f"  VERDICT                            : {verdict}\n")
        f.write("-" * 66 + "\n")
        f.write("Sample (p,q, edges, tau_LP, tau_closed, phi_LP, phi_closed, branch):\n")
        for row in rows:
            if row["p"] <= 6 and row["q"] <= 6:
                f.write(f"  p={row['p']} q={row['q']}: e={row['edges']:>3} "
                        f"tauLP={row['tau_LP']:>6} tauCF={row['tau_closed']:>6} "
                        f"phiLP={row['phi_LP']:>6} phiCF={row['phi_closed']:>6} "
                        f"[{row['branch']}]\n")
        f.write("\nDegenerate cases: p<=1 and S_{2,0} give tau3*=0 (no triangles) -- "
                "confirmed. See p3_results.csv for the full grid.\n")

    import csv
    with open(RESULTS_CSV, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        for row in rows:
            w.writerow(row)

    meta = [
        ("Test", "P3 -- Complete-split closed form (Prop 6.2 / Cor 6.3)"),
        ("Gate", "E"),
        ("Evidence", "EXACT_REPRODUCIBLE (full cover-LP) over (p,q) grid 0..12"),
        ("Method", "auditor's own full cover-LP vs ledger closed forms"),
        ("Environment", f"Python {platform.python_version()} / networkx {nx.__version__}"),
    ]
    tbl = [["p", "q", "edges", "tau3*_LP", "tau3*_closed", "Phi_LP", "Phi_closed", "branch", "ok?"]]
    for row in rows:
        if row["p"] <= 6 and row["q"] <= 5:
            tbl.append([row["p"], row["q"], row["edges"], f'{row["tau_LP"]:.2f}',
                        f'{row["tau_closed"]:.2f}', f'{row["phi_LP"]:.2f}',
                        f'{row["phi_closed"]:.2f}', row["branch"],
                        "y" if (row["tau_ok"] and row["phi_ok"]) else "N"])
    sections = [
        {"h": "1. Claims under test (Prop 6.2 / Cor 6.3)"},
        {"p": "tau3*(S_{p,q}) has a two-branch closed form (non-saturated (P+pq)/3 for "
              "q&lt;=p-1, saturated P for q&gt;=p-1, and 0 in the degenerate cases), and "
              "Phi_tau(S_{p,q}) equals p(2n+1-3p)/2 (saturated) or p(2n-p-1)/6 "
              "(non-saturated). We solve the FULL cover-LP directly and compare."},
        {"h": "2. Kill-switch (declared before running)"},
        {"p": "<b>H3a</b> LP == closed tau3*; <b>H3b</b> Phi_tau closed forms == LP; "
              "<b>H3c</b> the two formulas agree at the branch boundary q=p-1. Falsify on "
              "any mismatch."},
        {"h": "3. Result"},
        {"p": f"Cells tested: <b>{n_tested}</b>. tau3* mismatches: <b>{tau_fail}</b>. "
              f"Phi_tau mismatches: <b>{phi_fail}</b>. Branch-boundary mismatches: "
              f"<b>{boundary_fail}</b>."},
        {"p": f"<b>Verdict: {verdict}</b>"},
        {"h": "4. Sample of the (p,q) grid"},
        {"table": tbl, "header": True},
        {"h": "5. Scope"},
        {"p": "The cover-LP is solved exactly (HiGHS) over all triangles/edges -- this is "
              "the FULL LP, not the symmetrized 2-variable LP of Lemma 6.1, so it also "
              "cross-validates the orbit-averaging reduction. The (p,q) grid is finite; the "
              "closed forms are algebraic in (p,q), so agreement across the grid strongly "
              "supports them. Degenerate cases p&lt;=1 and S_{2,0} (no triangles, tau3*=0) "
              "are confirmed."},
    ]
    build_pdf(PDF, "Paper II Audit -- P3: Complete-split closed form (Prop 6.2 / Cor 6.3)",
              meta, sections)
    zp, sp, dg = package(HERE, "P3_completesplit_closedform",
                         ["p3_completesplit.py", "p3_results.txt", "p3_results.csv",
                          "P3_report.pdf", "audit_lib.py"])
    p