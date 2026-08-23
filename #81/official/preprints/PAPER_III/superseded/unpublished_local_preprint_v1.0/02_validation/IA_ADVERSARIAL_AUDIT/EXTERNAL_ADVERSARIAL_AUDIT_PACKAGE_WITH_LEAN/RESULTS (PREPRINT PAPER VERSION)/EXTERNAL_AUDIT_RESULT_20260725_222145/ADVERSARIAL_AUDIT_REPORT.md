# External Adversarial Audit Report

## Executive verdict

PASS_WITH_OBSERVATIONS

The previous blocker was environmental: Block F had not completed. In this local rerun, Lean completed successfully:

- `lake exe cache get`: completed successfully.
- `lake build`: completed successfully, 8058 jobs.
- `lake env lean gate.lean`: exit 0, expected axiom/signature report.

No blocking defect was found in the completed checks. The only observation is coverage-related: Block B was a limited source-page bibliographic check, not a line-by-line audit of the full external papers.

## Per-claim table

| Claim | Mathematical audit | Lean column | Evidence |
|---|---|---|---|
| Theorem 1.1 / E-9 | Axiom-relative; no counterexample found in completed checks | PASS: AX1+AX2 exactly in axiom report | blockF_lean_formalization/results/axioms_report.txt |
| Corollary 1.2 | Axiom-relative; follows Lean gate signature | PASS: AX1+AX2 exactly in axiom report | blockF_lean_formalization/results/axioms_report.txt |
| Proposition 10.1 | Internal audit rerun passed | PASS: Layer E clean | blockF_lean_formalization/results/axioms_report.txt |
| Theorem 3.1 / E-3.1 | Exact F branch scan confirmed on p<=80 grid | PASS: Layer E clean | blockC_counterexample_search/results/blockC_results.txt |
| Theorem 4.2 / E-4.2 | Exact margin scan confirmed on p<=80 grid | PASS: Layer E clean | blockC_counterexample_search/results/blockC_results.txt |
| Lemmas 5.1/5.2/6.1/7.1 | Internal audit rerun passed after dependency install | PASS: Layer E clean | blockE_audit_the_audit/results/blockE_results.txt |
| Appendix B / D | Static/textual scan plus Lean gate | PASS: Layer E clean | blockF_lean_formalization/results/axioms_report.txt |
| AX1 / AX2 | Limited bibliographic plausibility check | PASS as declared axioms; no extra axioms | blockB_external_inputs/results/blockB_results.txt |

## Findings

See `findings/FINDINGS.csv`.

## Coverage statement

Block C exact grid: p=3..80, q=1..2p, d=0..p for closed-form F and Theorem 4.2 margin inequality. No violations found.

Block D exact arithmetic: selected coefficient/threshold identities confirmed.

Block E: copied internal scripts reran successfully after installing sympy/numpy/scipy/pulp locally.

Block F: fully executed locally from `C:\Users\jtrav\Documents\Codex\leanrun_erdos81`; logs were written into this output folder. Toolchain: leanprover/lean4:v4.28.0. Mathlib revision from lake-manifest: 8f9d9cff6bd728b17a24e163c9402775d9e6a365.

Block B remains limited: source-page evidence was checked, not full-paper theorem-by-theorem bibliographic certification.

## Reproduction appendix

For Block F:

```powershell
cd C:\Users\jtrav\Documents\Codex\leanrun_erdos81
lake exe cache get
lake build
lake env lean gate.lean
```
