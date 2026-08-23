# Evidence Record — Independent AI Adversarial Audit

Evidence ID: ERDOZ81-P2-FRAC-THM-01-EV-IA-001
Gate ID: ERDOZ81-P2-FRAC-THM-01
Audit ID: PAPER-II-EXT-AUDIT-001
Artifact type: Independent AI Adversarial Audit (adversarial-math-audit protocol v1.0)
Auditor: external AI auditor (independent context)
Date: 2026-07-10

## Verdict
Final verdict: **PASS**. All specification gates A–J checked; none failed.

- Analytic proof independently re-derived (Lemmas 3.1, 5.1; Props 6.2, 7.1) — matches manuscript.
- Lean certificate re-elaborated: `lake build` (8057 jobs) OK; `#print axioms PaperII.theorem_1_2` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no project axiom; hypotheses exactly `IsChordal`, both ∀ bound and ∃ attainment.
- Exhaustive n≤6: max = ⌊(2n+1)²/24⌋ attained by complete-split; 0 violations.
- No over-claim: cp(G)/Erdős #81 confirmed out of scope.

## Residual (provenance only, not mathematical)
1. Lean rebuild used the project's pinned Mathlib cache (not a from-scratch rebuild).
2. Commit `5f2d448` SHA match not verifiable in the auditor's environment (their package
   lacked the `lean/` tree). **Closed in this release:** `05_formalization/lean/` is the
   exact source of commit `5f2d448`, verified per file by SHA-256 (see PROVENANCE.md).

## Level
Independent AI adversarial audit — intermediate assurance tier;