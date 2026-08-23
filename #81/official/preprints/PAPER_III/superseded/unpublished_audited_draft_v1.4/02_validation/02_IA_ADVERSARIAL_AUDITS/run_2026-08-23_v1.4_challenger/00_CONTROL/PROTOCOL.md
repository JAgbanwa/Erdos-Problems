# Protocol — Paper III v1.4 external challenger and correction review

Run: `run_2026-08-23_v1.4_challenger`. Commissioned by the principal researcher in
`EXTERNAL_CHALLENGER_CORRECTION_REVIEW_REQUEST_v1.4.md`
(SHA-256 `06051b3fb31ba05b36c83ddae736f108fd04a374b9765531d976d48be2919ac5`),
delivered in `PAPER_III_v1.4_EXTERNAL_CHALLENGER_CORRECTION_REVIEW_INSTRUCTIONS.zip`
(SHA-256 `e88cd5e8ff2a742023176a37efd642aacef0bdc66b7b6af1d9f1acb92983419e`, sidecar matches,
10 members, `testzip()` clean).

## Standing of this run

The external adversarial audit of Paper III is this auditor's function; the internal audits are
author-side. The prior external run `run_2026-08-22_v1.4_residual` withheld plain `PASS` partly
on the ground that no adversarial challenger had examined the package. That ground is withdrawn
here as a category error: the number of commissioned external reviewers is a property of the
review programme, not a defect of the target, and conditioning closure on a further reviewer
makes external closure unreachable in principle. It is restated in this run as a declared scope
limitation. See `30_REPORT/FINAL_AUDIT_REPORT.md`, section on limits.

## Scope

Reviewed in this run:
- `EXT-V14-M01` — Spanish Section 2.4 correction, propagation and bilingual integrity.
- `EXT-V14-M02` — Appendix D audited as a proof, independently derived.
- `EXT-V14-N01` — carry-forward disposition.
- The regression boundary between the prior external target and the corrected target.
- Correction of two absolute novelty formulations in the prior report.

Carried forward on verified byte identity, not re-executed: gates 1–7 and 9 of the prior
external run, E2 (mathematical rederivation), E6 (prior art and novelty), and the Lean gates.
Basis recorded in `20_EVIDENCE/C_REGRESSION/regression_boundary.txt`.

Not in scope, and stated as such: the truth of Theorem 1.1; the Lean nibble chain's internal
parameter ledger; human peer review.

## Rules applied

- No manuscript, formalization or prior-audit artifact was modified. The prior sealed report is
  corrected by addendum, never by rewriting.
- The author-side ledger for Appendix D was opened only after the independent derivation was
  written, and the derivation records that ordering.
- Overall verdict no stronger than the weakest mandatory gate; plain `PASS` must not conceal
  residuals.
- Novelty is stated only in corpus-bounded form.
