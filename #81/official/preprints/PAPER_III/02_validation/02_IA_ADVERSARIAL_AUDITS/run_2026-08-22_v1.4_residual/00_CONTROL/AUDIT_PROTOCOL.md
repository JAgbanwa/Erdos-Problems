# Audit protocol as executed -- Paper III v1.4 residual

**Governing document:** `EXTERNAL_RESIDUAL_AUDIT_REQUEST_v1.4.md`, delivered in
`PAPER_III_v1.4_EXTERNAL_RESIDUAL_AUDIT_INSTRUCTIONS.zip`, SHA-256
`0dd44c49c43bff8cb6d7880b4d2825c83c1a88cf30d2be2111772b5e418854c0`, CRC intact.

## Independence

Primary auditor only. **No adversarial challenger** -- the single reason the overall verdict is
`CONDITIONAL_PASS` rather than `PASS`.

Internal evidence was treated as intake, never as authority. Specifically: the v1.4 internal
audit, `ESCAPE_HATCH_ASSESSMENT.md`, `FREEZE_METADATA.json`, `BUILD_INPUT_METADATA.json`,
`LEAN_FINDINGS_CLOSURE_MATRIX.md` and the `E2_RESIDUAL_v1.4` ledger were read as claims to be
tested. The E2 ledger was used as a map of obligations only, and every formula was derived
before comparison, as the request directs. The 315,183 author-side exact checks were **not**
rerun; independently written tests were used instead.

## Order of work

1. Gate 1 intake, before substantive work. A byte mismatch would have stopped the audit.
2. The two v1.3 MAJOR findings, checked first as the fastest high-value signal.
3. Gates 2, 3, 4: claims, block-aligned bilingual comparison, page-by-page render.
4. Gate 5 the clean-room Lean reproduction, following the request's mandated command sequence.
5. Gates 6, 7: import closure and the auditor-built conformance bridge.
6. E2 rederivation, and the v1.3-to-v1.4 mathematics delta.
7. Gate 8 citation and novelty refresh.
8. Gate 9 regression of every v1.3 finding, folded into this consolidated verdict.

## Deviation, disclosed

`lake exe cache get` hung on network: 3.7 s of CPU across roughly 40 minutes of wall clock, no
output, no download process. The dependency cache was already complete and pin-verified (7,655
Mathlib `.olean`, 1.76 GB, `Mathlib.olean` present, plus all eight other packages), and in the
v1.3 audit the same command reported "No files to download". The request asks for it "when
available"; it was terminated, the state that made it unnecessary was recorded in
`20_EVIDENCE/G5_LEAN/results/01_cache_get.log`, and the build proceeded. No project object was
reused: `.lake/build` was proved absent and all 429 project objects were created by this run.

## Epistemic rules applied

- `#print axioms` was never treated as semantic conformance; gate 7 uses an auditor-built bridge.
- Compilation, semantic correspondence, axiom footprint and independent rederivation are
  reported as four separate statuses.
- No universal claim is reported as proved from finite testing.
- Every auditor tool artifact found during the run is recorded rather than quietly fixed; five
  are listed in the report, three of which first looked like real defects.
