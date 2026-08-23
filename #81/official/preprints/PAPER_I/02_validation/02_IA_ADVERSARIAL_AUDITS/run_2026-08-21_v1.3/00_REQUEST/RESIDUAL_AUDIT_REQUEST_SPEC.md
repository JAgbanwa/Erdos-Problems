# Paper I v1.3 — external residual adversarial re-audit instructions

**Request date:** 2026-08-21  
**Audit class:** external residual adversarial re-audit  
**Target:** immutable `preprint_draft_v1.3` package  
**Required outcome:** a new, standalone verdict for v1.3  
**Input mutation:** prohibited

## 1. Purpose

Audit Paper I v1.3 after the editorial and artifact corrections prompted by the
external v1.2 report. The new run must independently validate every correction,
perform a general regression against the complete manuscript/package, and issue a
new standalone v1.3 report. Do not rewrite or relabel the v1.2 report, and do not
merge evidence across different manuscript hashes into a synthetic v1.2 `PASS`.

The theorem statements, proof, numerical constants and Lean sources did not change.
The exact Lean archive was already rebuilt in the external v1.2 clean room. This
run may reuse that expensive Gate H evidence only under the byte-identity rule in
Section 5 below.

## 2. Immutable target and anchor hashes

Target root:

`preprints/PAPER_I/active/preprint_draft_v1.3/`

The audit-output subtree
`02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-21_v1.3/` is excluded from
the input target.

| Artifact | SHA-256 |
|---|---|
| English Markdown | `f3094b670c93ff622c3f573cdab61bdd0f5d84007f04b1888b364e0183565bea` |
| Spanish Markdown | `57ba967fc2de805b7bbb4cf5f937727bde43c2ada80fa794bcbb5a727db05b8b` |
| English LaTeX | `1a87de70548879ca90a714ec9e1b10c8576b380a749785916e5d59176e479465` |
| Spanish LaTeX | `f83ee709c1168b5b9afe504e6b6a43763bf3bb2a08f674f2031f83670ba9bb56` |
| English PDF | `7d04c47692b613c8d6e2cc4471f0205128b4ae06ca11d581a08d020eb2236db0` |
| Spanish PDF | `3ad16ae86e8fcad358bf964a6ae98ae053b0bde2fdf3140e008cedab78b90c2a` |
| Lean archive | `0181506408644fc1f8872d711de5a98a500f4052aa295bcd6f8c82776694fd3a` |
| Internal-audit ZIP | `f261add8050f1ab8779d9e25f345475790768368f4c056067358153db6639382` |

Before analysis, recompute every anchor, verify the six-entry LF-safe manuscript
sidecar and seal an input inventory. Any mismatch is a `BLOCKER`.

## 3. Required reference material

Read these as audit inputs, not as authority that substitutes for independent
checking:

- `04_integrity/EXTERNAL_AUDIT_CORRECTION_MATRIX.md`
- `04_integrity/CURRENT_TARGET_SHA256.txt`
- `02_validation/00_intake/EXTERNAL_AUDIT_v1.2_FINAL_REPORT.md`
- `02_validation/01_INTERNAL_AUDITS/10_REPORT/INTERNAL_AUDIT_FINAL_REPORT.md`
- `02_validation/01_INTERNAL_AUDITS/30_PACKAGE/INTERNAL_AUDIT_PACKAGE.zip`
- `CHANGELOG_v1.3.md`

The manuscript itself must remain self-contained and must not depend on any of
these records.

## 4. Mandatory correction validation

Validate each disposition independently in English and Spanish Markdown, LaTeX
and PDF where applicable:

1. `EXT-P1-L-001`: duplicated Spanish prose/code blocks are removed and no new
   duplicated pages, paragraphs or sequences exist.
2. `EXT-P1-M-001`: integrity metadata and manifests identify the v1.3 target and
   verify exactly.
3. `EXT-P1-D-001`: the derivation of (4.7) explicitly states the substitution
   `z=x` and accounts for every edge of `H`.
4. `EXT-P1-E-002`: Appendix A.2 restricts the displayed excess formula to
   `o>=3`, with the boundary cases handled separately.
5. `EXT-P1-J-001`: “sharp” unambiguously refers to the quadratic coefficient
   `1/6`, not to an optimal additive coefficient.
6. `EXT-P1-I-001`: the Chen--Erdős--Ordman primary author-hosted scan is directly
   cited and the attributed `3/16` statement is supported.
7. `EXT-P1-I-002`: the unverified pinpoint “Corollary 7.1g” is absent from all six
   artifacts; Schrijver is cited only at the verified chapter level.
8. `EXT-P1-I-003`: the unused/stale repository citation is absent.
9. Internal regression `P1-IA-V13-001`: confirm that no residual occurrence of the
   old Schrijver pinpoint remains after the final regeneration.

For duplication, do not limit the test to known phrases. Perform a general exact
and near-duplicate scan of normalized long paragraphs/sequences in all six
artifacts, inspect every candidate manually, and check page images for duplicated
or repeated pages. Report thresholds, exclusions and results.

## 5. Lean Gate H reuse rule

Do not rerun `lake update`, `lake exe cache get` or the 8,034-job build merely
because the manuscript version changed. Gate H may reuse the prior external
clean-room build and theorem-level axiom evidence only if all of the following are
shown in the new report:

- the received Lean archive hash is exactly
  `0181506408644fc1f8872d711de5a98a500f4052aa295bcd6f8c82776694fd3a`;
- it is byte-identical to the archive previously rebuilt externally;
- no Lean source, manifest, toolchain pin or axiom-query file changed;
- the v1.3 manuscript's formal claims are checked against those unchanged sources;
- the reused build log and verbatim theorem-level axiom outputs are cited by direct
  evidence path and explicitly labelled `REUSED_BYTE_IDENTICAL_EXTERNAL_EVIDENCE`.

If any condition fails, Gate H reopens and a clean build is mandatory. Reuse of the
formal evidence does not authorize reuse of the earlier manuscript, citation,
bilingual, PDF or package verdicts.

## 6. General regression

In addition to the nine mandatory controls:

- rebuild a fresh claim map for v1.3 and compare every headline statement,
  hypothesis, constant, exceptional branch and scope limitation;
- independently rerun a proportionate mathematical regression over the critical
  identities, tightness boundary, orbit program, final assembly and complete-split
  benchmark; preserve domains and raw outputs;
- confirm the complete English/Spanish semantic chain;
- verify Markdown -> LaTeX -> PDF consistency, embedded fonts, PDF structure,
  citations, figures, tables and all 39 rendered pages;
- recheck current open-problem status, citation accuracy, prior-art positioning and
  overclaim language through the audit date;
- verify that the manuscript contains no internal version-history narrative or
  dependency on audit documents;
- verify package completeness, LF-safe hashes, no zero-byte stray file, no `$o`,
  no compiler residue, no stale version/path/hash, and no truncated report/script.

A spot check is insufficient. A correction-only note without general regression
cannot receive the requested standalone v1.3 verdict.

## 7. Findings and verdict rules

Use `BLOCKER`, `MAJOR`, `MINOR` and `NOTE`. A final `PASS` requires:

- all mandatory correction controls pass;
- the general regression passes;
- no unresolved blocker or major finding;
- every minor finding is either corrected in a new target or explicitly compatible
  with the protocol's PASS rule;
- every reused item satisfies the exact byte-identity rule;
- the report states that the audit is not human peer review and does not prove
  global novelty.

If the target must change, stop and request a new immutable version. Do not edit the
target yourself.

## 8. Required output location and structure

Write results only under:

`02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-21_v1.3/`

Required structure:

- `00_REQUEST/`: this specification, input inventory/freeze manifest and auditor
  declaration;
- `10_CONTROL/`: audit index, environment, claim map, findings table, gate status
  and open risks;
- `20_EVIDENCE/`: correction-by-correction evidence, general mathematical
  regression, Gate H byte-identity/reuse evidence, citation/novelty work,
  bilingual/duplicate analysis, rendered-page QA and manifests;
- `30_REPORT/FINAL_AUDIT_REPORT.md`: semantic source of the new standalone report;
- `30_REPORT/FINAL_AUDIT_REPORT.tex`: generated from the final Markdown;
- `30_REPORT/FINAL_AUDIT_REPORT.pdf`: compiled from the final LaTeX and visually
  checked;
- `30_REPORT/FINAL_AUDIT_SUMMARY.json`: machine-readable verdict and gate results;
- final evidence manifest, sealed archive and SHA-256 sidecar generated last.

The final report must identify the v1.3 hashes, disposition each of the nine controls,
report the general regression gate by gate, distinguish fresh from reused evidence,
list all residual risks and end normally without truncation. A PASS must be a new
complete v1.3 verdict, not a renamed v1.2 report.

