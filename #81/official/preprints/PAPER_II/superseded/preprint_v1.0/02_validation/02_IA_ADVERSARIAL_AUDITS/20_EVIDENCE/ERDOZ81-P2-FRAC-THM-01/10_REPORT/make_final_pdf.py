#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Render FINAL_AUDIT_REPORT.pdf for the Paper II external audit."""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "00_CONTROL"))
from audit_lib import build_pdf

PDF = os.path.join(HERE, "FINAL_AUDIT_REPORT.pdf")

# axiom string is read from the H log at render time (fallback text if absent)
AXIOM_LOG = os.path.join(HERE, "..", "20_TESTS", "H_lean_verification", "print_axioms.log")
axioms_excerpt = "(see 20_TESTS/H_lean_verification/print_axioms.log)"
try:
    with open(AXIOM_LOG, encoding="utf-8") as f:
        txt = f.read().strip()
    if txt:
        axioms_excerpt = txt[:1200]
except Exception:
    pass

meta = [
    ("Audit ID", "PAPER-II-EXT-AUDIT-001"),
    ("Date", "2026-07-10"),
    ("Target", "max over chordal G (|E|-2 tau3*(G)) = floor((2n+1)^2/24), attained by S_{p,q}"),
    ("Environment", "Python 3.14.4 / scipy 1.17.1 HiGHS / networkx 3.6.1; Lean v4.28.0 / lake 5.0.0"),
    ("Master seed", "20260710"),
    ("EXECUTIVE STATUS", "<b>PASS</b>"),
]

gate_tbl = [
    ["Gate", "Status", "Basis"],
    ["A Definitions", "VERIFIED", "consistent manuscript/ledger/Lean"],
    ["B Lemma 3.1 vertex-copy", "VERIFIED (in range)", "P2: 11032 pairs, 0 violations"],
    ["C Lemma 4.1-4.3 + C4 necessity", "VERIFIED", "P5: C4 necessity confirmed"],
    ["D Lemma 5.1 terminal char.", "VERIFIED", "P5: exhaustive n<=6, 0 counterex."],
    ["E Sec6 complete-split cover", "VERIFIED", "P3: closed forms == full LP"],
    ["F Sec7 integer maximization", "VERIFIED", "P4: exact n<=5000"],
    ["G Global assembly (Thm 1.1)", "VERIFIED", "P1: exhaustive n<=6 max=M(n)"],
    ["H Formal certificate", "VERIFIED_WITH_RESIDUAL_RISK", "build OK; axioms; SHA/indep. residual"],
    ["I Citations", "VERIFIED", "A1-A6 standard, in-scope"],
    ["J Over-claim / scope", "VERIFIED (no over-claim)", "cp/#81 explicitly out of scope"],
]

comp_tbl = [
    ["Test", "Gate", "Coverage", "Verdict"],
    ["P1 max Phi_tau", "F,G", "exhaustive n<=6 + CS scan n<=60 + random", "VERIFIED / no counterexample"],
    ["P2 vertex-copy", "B", "exhaustive n<=5 + random (11032 pairs)", "VERIFIED"],
    ["P3 closed forms", "E", "full cover-LP vs closed form, (p,q) 0..12", "VERIFIED"],
    ["P4 integer max", "F", "exact Fraction, n=1..5000", "VERIFIED"],
    ["P5 terminal + C4", "C,D", "exhaustive chordal n<=6", "VERIFIED"],
    ["H Lean", "H", "lake build (8057 jobs) + #print axioms", "build OK; residual on indep/SHA"],
]

sections = [
    {"h": "Executive Verdict -- PASS"},
    {"p": "Every gate of the specification was checked and none failed. The three distinct "
          "claim-types are kept separate and each is supported on its own terms: (i) the "
          "ANALYTIC PROOF is internally correct -- Lemmas 3.1 and 5.1, the C4 necessity, the "
          "complete-split closed forms (Prop 6.2/Cor 6.3), and the integer maximization "
          "(Prop 7.1) were independently re-derived/reproduced with the auditor's own code "
          "and matched the manuscript; (ii) the LEAN CERTIFICATE holds -- PaperII.theorem_1_2 "
          "re-elaborated (lake build, 8057 jobs, success), hypotheses exactly the standard "
          "IsChordal, content = upper bound AND attainment; (iii) the COMPUTATION found no "
          "counterexample -- exhaustive over all labelled chordal graphs n&lt;=6, max = "
          "floor((2n+1)^2/24), attained by a complete-split, 0 violations."},
    {"p": "The only honest residual is on INDEPENDENCE of the Lean build (Mathlib came from "
          "the project's pinned cache, not a clean-room from-scratch rebuild) and on the "
          "commit-5f2d448 SHA match, which could not be verified here (no git history "
          "reachable; the release package does not bundle the lean/ tree). These are "
          "provenance caveats, not mathematical defects. The manuscript does NOT over-claim: "
          "cp(G) and Erdos #81 are explicitly out of scope."},
    {"h": "Gate table (A-J)"},
    {"table": gate_tbl, "header": True, "wrap": True, "colWidths": [150, 150, 210]},
    {"h": "Computational tests (P1-P5) + Lean (H)"},
    {"table": comp_tbl, "header": True, "wrap": True, "colWidths": [95, 55, 205, 155]},
    {"h": "Gate H -- Lean axiom footprint (#print axioms PaperII.theorem_1_2)"},
    {"p": "Build: 'Build completed successfully (8057 jobs)'. Statement hypotheses exactly "
          "IsChordal (Unconditional.lean:72-79); IsChordal is the standard chord definition "
          "(every cycle of length &gt;=4 has a chord, Chordal.lean:35). Captured axioms:"},
    {"code": axioms_excerpt},
    {"h": "Falsification log (all NEGATIVE)"},
    {"p": "No chordal G with Phi_tau &gt; floor((2n+1)^2/24) (exhaustive n&lt;=6: 18154 "
          "chordal graphs at n=6; CS scan n&lt;=60; random chordal n=7..14). No "
          "non-complete-split maximiser. No vertex-copy failure in 11032 pairs. No "
          "statement divergence manuscript/ledger/Lean. A bounded search is supporting "
          "evidence, not proof; the n&lt;=6 enumeration is exhaustive hence conclusive for "
          "those n."},
    {"h": "Coverage & residual risk"},
    {"p": "Checked: all definitions; Lemmas 3.1/4.3/5.1; Sec6 closed forms; Sec7 integer max "
          "(exact to n=5000); global exhaustive max n&lt;=6; Lean build + statement shape + "
          "axioms; citations; scope. Not checked / residual: clean-room Mathlib rebuild; "
          "commit-5f2d448 SHA match (git unreachable here); exhaustive chordal n&gt;=7 "
          "(infeasible; covered by sampling + analytic proof + Lean); Spanish _es manuscript "
          "beyond spot check."},
    {"h": "Final recommendation"},
    {"p": "PASS. No mathematical objection to the boxed theorem; analytic proof, formal "
          "certificate, and exhaustive small-case computation agree. Non-blocking closures: "
          "(1) reproduce lake build + #print axioms at commit 5f2d448 in a clean-room "
          "environment with a from-scratch Mathlib; (2) publish the lean/ tree with a SHA-256 "
          "manifest inside the release package. This internal adversarial audit confers NO "
          "peer-review or publication status."},
]

build_pdf(PDF, "External Adversarial Audit -- Paper II (exact fractional-c