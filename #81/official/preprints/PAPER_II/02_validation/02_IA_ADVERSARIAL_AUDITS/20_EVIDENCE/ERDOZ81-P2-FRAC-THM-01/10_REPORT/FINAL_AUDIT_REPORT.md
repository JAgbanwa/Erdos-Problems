# External Adversarial Audit — Paper II (exact fractional-cover theorem)

**Audit ID:** PAPER-II-EXT-AUDIT-001  **Date:** 2026-07-10
**Auditor:** external AI auditor (adversarial-math-audit protocol v1.0)
**Target (the ONLY claim of Paper II):** for every integer `n ≥ 1`,
`max over chordal G on n vertices of (|E(G)| − 2·τ₃*(G)) = ⌊(2n+1)²/24⌋`,
attained by a complete-split `S_{p,q} = K_p ∨ K̄_q`.
**Reproducibility:** Python 3.14.4 / scipy 1.17.1 (HiGHS) / networkx 3.6.1 /
reportlab 5.0.0; Lean toolchain `leanprover/lean4:v4.28.0`, lake 5.0.0; master
seed 20260710. Per-test artifacts (script + results + English PDF + zip + SHA-256)
in `PAPER_II_EXT_AUDIT/20_TESTS/`.

---

## Executive Verdict

### Status: **PASS**

Every gate of the specification was checked and none failed. The three distinct
claim-types are separated and each is supported on its own terms:
(i) **the analytic proof is internally correct** — the vertex-copy inequality
(Lemma 3.1), the terminal characterization (Lemma 5.1) and the simpliciality
necessity, the complete-split closed forms (Prop 6.2 / Cor 6.3), and the integer
maximization (Prop 7.1) were all independently re-derived/reproduced with the
auditor's own code and matched the manuscript;
(ii) **the Lean certificate holds** — `PaperII.theorem_1_2` was re-elaborated by
the auditor (`lake build`, 8057 jobs, "Build completed successfully"), its
statement's hypotheses are exactly the standard `IsChordal` and its content is
both the `∀` upper bound and the `∃` attainment, and `#print axioms` confirms the
footprint is exactly `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
project-specific axiom (`20_TESTS/H_lean_verification/print_axioms.log`; see Gate H);
(iii) **the computation found no counterexample** — an EXHAUSTIVE search over all
labelled chordal graphs on `n ≤ 6` vertices found the maximum equals `⌊(2n+1)²/24⌋`
and is attained by a complete-split, with zero violations, and no violation arose
in any larger structured/random test.
The one honest residual is on **independence of the Lean build** (the Mathlib
dependency came from the project's pinned cache, not a from-scratch rebuild) and
on the **commit-`5f2d448` SHA match**, which could not be verified in this
environment (no git history reachable; the release package does not bundle the
`lean/` tree). These are provenance caveats, not mathematical defects, and are
recorded below. The manuscript does **not** over-claim: `cp`/Erdős #81 are
explicitly out of scope. Accordingly the audit returns **PASS**, with the two
provenance items flagged for closure and the standing note that this internal
audit is **not** peer review.

---

## Gate Table (A–J)

| Gate | Status | Evidence checked | Objections / residual |
|------|--------|------------------|------------------------|
| **A. Definitions** | VERIFIED | τ₃* (cover LP D2), Φτ=|E|−2τ₃* (Model.lean `phiTau`), S_{p,q}, clone class, simplicial, copy op D7 — consistent across manuscript, ledger v1.1, and Lean | none |
| **B. Lemma 3.1 (vertex-copy)** | VERIFIED (in range) | P2: 1576 graphs, 11032 nonadjacent pairs (exhaustive n≤5 + random general & chordal n=6–9); 0 inequality/corollary violations; edge-count identity exact | universal lemma → existential evidence; no violation found |
| **C. Lemma 4.1–4.3 (convexity/progress/chordality)** | VERIFIED | P5: simpliciality necessity independently confirmed — non-simplicial-target copies break chordality, and the C₄ `{0,1},{0,2},{1,3},{2,3}` arises (matches internal audit) | convexity lift itself is elementary (read) |
| **D. Lemma 5.1 (terminal characterization)** | VERIFIED | P5: EXHAUSTIVE over all labelled chordal graphs n≤6 — every graph with property (H) is complete-split; 0 counterexamples; disconnected case included | conclusive for n≤6; manuscript (clique-tree) and Lean (clique-tree-free) target the SAME statement |
| **E. §6 (complete-split cover)** | VERIFIED | P3: full cover-LP vs closed forms over (p,q) grid 0..12; τ₃* and Φτ closed forms match; branch boundary q=p−1 consistent; degenerate p≤1, S_{2,0} handled | orbit-averaging cross-validated by the full (non-symmetrized) LP agreeing |
| **F. §7 (integer maximization)** | VERIFIED | P4: EXACT (Fraction) for n=1..5000 — max_{p+q=n} Φτ = ⌊(2n+1)²/24⌋; complete-the-square identity exact; odd-square mod-24 residues (==1, or ==9 if 3∣m); saturated-branch attainment | conclusive over the range; the identity/residue engine (universal) checked exactly |
| **G. Global assembly (Thm 1.1)** | VERIFIED | P1: EXHAUSTIVE n≤6 max = M(n), attained by complete-split (0 violations); reduction 5.3 ∘ §7 read and non-circular (L5←L7 contrapositive, no forward ref) | larger n supporting only |
| **H. Formal certificate** | VERIFIED_WITH_RESIDUAL_RISK | `lake build PaperII` = "Build completed successfully (8057 jobs)", no error/sorry; `#print axioms PaperII.theorem_1_2` = **`[propext, Classical.choice, Quot.sound]`** (no `sorryAx`, no project axiom) — captured in `print_axioms.log`; statement hypotheses exactly `IsChordal` with BOTH `∀` bound and `∃` attainment (Unconditional.lean:72–79); `IsChordal` = standard chord def (Chordal.lean:35) | axiom footprint & statement CONFIRMED; residual only on provenance: Mathlib from project cache (not clean rebuild) and commit-5f2d448 SHA match NOT verifiable here (no git; release lacks lean/) |
| **I. Citations** | VERIFIED | chordal facts A1–A6 are standard textbook results and used within hypotheses; no external theorem applied outside its scope | ledger uses only elementary counting + cover LP + A1–A6 |
| **J. Over-claim / scope** | VERIFIED (no over-claim) | ledger explicitly states cp(G) and Erdős #81 are OUT OF SCOPE; no integral-packing/clique-partition claim anywhere | clean separation from the (open) Paper III route |

---

## Falsification / kill-switch log

Actively attempted, all NEGATIVE (no defeater found):
- chordal `G` with `Φτ(G) > ⌊(2n+1)²/24⌋`: **none** — exhaustive n≤6 (18154 chordal
  graphs at n=6), complete-split scan n≤60, random chordal n=7–14.
- non-complete-split chordal graph beating the best complete-split: **none** — the
  exhaustive maximiser is always a complete-split.
- vertex-copy inequality failure: **none** in 11032 nonadjacent pairs.
- `#print axioms` containing `sorryAx` / project axiom: see Gate H log.
- divergence manuscript ↔ ledger ↔ Lean statement: **none** — all state
  `max (|E|−2τ₃*) = ⌊(2n+1)²/24⌋` on `IsChordal`.

A bounded computational search finding no counterexample is **supporting evidence,
not proof**; the n≤6 enumeration is exhaustive and hence **conclusive for those n**.

## Coverage statement

**Checked:** definitions; Lemma 3.1; Lemma 4.3 necessity (C₄); Lemma 5.1
(exhaustive n≤6, incl. disconnected); §6 closed forms vs full LP; §7 integer max
(exact to n=5000); global exhaustive max (n≤6); Lean re-elaboration + statement
shape + axioms; citations; scope.
**Not checked / residual:** a fully clean-room Mathlib rebuild; the SHA match to
commit 5f2d448 (git not reachable here); exhaustive chordal enumeration for n≥7
(infeasible in Python — covered by random/structured sampling + the analytic
proof + the Lean certificate); the Spanish `_es` manuscript beyond spot cross-check.

## Distinct-claims discipline (per spec §6)

- "Analytic proof correct" — supported by P1–P5 reproducing every lemma/closed
  form with independent code.
- "Lean certificate holds" — supported by an independent `lake build` + axioms
  check (statement shape verified by source read); residual on build independence
  and commit SHA.
- "Computation found no counterexample" — supported, and conclusive for n≤6.

## Final recommendation

**PASS.** No mathematical objection to the boxed theorem was found; the analytic
proof, the formal certificate, and the exhaustive small-case computation agree.
Recommended (non-blocking) closures: (1) reproduce `lake build` + `#print axioms`
at commit `5f2d448` in a clean-room environment with a from-scratch Mathlib to
discharge the independence residual; (2) publish the `lean/` tree with a SHA-256
manifest inside the release package so the commit match i