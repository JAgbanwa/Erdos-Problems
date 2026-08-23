# Paper III v1.5 — request to close EXT-V15-M01 and issue PASS

## Mandate

Perform only the residual closure test specified in Section 2 of the preserved external
report `run_2026-08-23_v1.5_residual/30_REPORT/FINAL_AUDIT_REPORT.md`. Do not rewrite that
sealed `CONDITIONAL_PASS` report. Create a new closure run under:

`02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-23_v1.5_residual_closure/`

If the evidence below verifies and no new defect is introduced by this correction, close
`EXT-V15-M01` and issue a consolidated `PASS`, as the source report explicitly permits
without further work.

## Preserved external authority

```text
4f4537816840c62fb23521190fab4fa1a860085e05a4cb956d8afe1eb3b67596  run_2026-08-23_v1.5_residual/30_REPORT/FINAL_AUDIT_REPORT.md
```

The preserved run is byte-identical to the auditor's `C:\v15r` package across 48/48 files.

## Correction performed

1. The 29 historical compiler logs formerly at the generic
   `manuscript_build_logs/` root were moved byte-for-byte into
   `manuscript_build_logs/v1.3_legacy/`.
2. The stale generic `MANUSCRIPT_CONSISTENCY_RESULTS.json` was removed. Its identical v1.4
   historical copy remains inside the preserved superseded v1.4 package.
3. Current evidence remains only in explicitly versioned locations:
   - `manuscript_build_logs/v1.5/` — six v1.5 logs;
   - `MANUSCRIPT_CONSISTENCY_RESULTS_v1.5.json` — `PASS` 61/61.

No manuscript, TeX, PDF, figure, mathematical text, citation, formal source, Lean archive or
prior external-audit byte changed.

## Evidence to verify

Run:

```text
python 02_validation/02_IA_ADVERSARIAL_AUDITS/REQUEST_v1.5_PASS_CLOSURE/verify_EXT_V15_M01_closure.py
```

Expected result: `PASS`, 16/16.

Evidence files:

- `EXT_V15_M01_CLOSURE_RESULTS.json` — targeted machine-readable result;
- `LEGACY_V1.3_LOGS_SHA256.txt` — hashes of all 29 relocated historical logs;
- `CURRENT_V1.5_LOGS_SHA256.txt` — hashes of the six current logs;
- `04_integrity/EXT_V15_M01_CORRECTION_RECORD.md` — author correction record;
- `02_validation/01_INTERNAL_AUDITS/run_2026-08-23_v1.5_internal_residual/20_EVIDENCE/internal_residual_results_v1.5.json`
  — expanded full internal regression, `PASS` 79/79.

Current evidence hashes:

```text
ad4a6284dad8c0d6f2580aa75d3594ddd5f2e122193c479122f688f5886d5221  EXT_V15_M01_CLOSURE_RESULTS.json
20909ae83a2c6f0975bf2e388b7b56936f8f7591a9a9900accbc84dd5bb9e435  internal_residual_results_v1.5.json
f42225bdf74aaa2a66c18fd78e8ca46cba568f8c07f3847011852a46b03a7fce  FINAL_INTERNAL_RESIDUAL_AUDIT_REPORT.md
04d9e9e95f1e3a9743fa7d286aadfe0f51b4fb7c94b468b13980dc4346d19e7f  MANUSCRIPT_CONSISTENCY_RESULTS_v1.5.json
```

## Required independent closure checks

1. Confirm no file remains directly under `manuscript_build_logs/`.
2. Confirm all 29 relocated logs are in `v1.3_legacy/`, their hashes match the supplied
   manifest and their contents genuinely describe v1.3.
3. Confirm the six files in `manuscript_build_logs/v1.5/` name the v1.5 artifact and retain
   the correct 46/47-page, zero-prohibited-diagnostic evidence.
4. Confirm the generic consistency JSON is absent and the versioned v1.5 JSON is `PASS`
   61/61 with English Markdown hash `a98e9313…c99a`.
5. Recompute the six manuscript hashes and Lean ZIP hash. They must remain exactly the hashes
   accepted in the source external report.
6. Confirm no prior audit report was modified.

The intentionally current v1.4 references to the immutable Lean freeze and its build evidence
are outside `EXT-V15-M01`; the finding concerns stale generic **manuscript** evidence only.

## No broad rerun requested

Do not repeat E0–E6, the mathematical rederivation, literature search, PDF rebuild or Lean
build. The source report already passed those gates and states: “On its closure this becomes
`PASS` with no further work required.” This request supplies exactly that closure evidence.

## Deliverables and verdict

Create:

```text
run_2026-08-23_v1.5_residual_closure/
  00_CONTROL/CLOSURE_PROTOCOL.md
  20_EVIDENCE/EXT_V15_M01_INDEPENDENT_CHECK.json
  30_REPORT/FINAL_CLOSURE_REPORT.md
  30_REPORT/FINAL_CLOSURE_SUMMARY.json
  40_PACKAGE/  sealed ZIP, manifest and SHA-256 sidecar
```

The report must preserve the original `CONDITIONAL_PASS` report, disposition
`EXT-V15-M01`, and state one consolidated current verdict. If checks 1–6 pass and no new
correction-induced defect is found, the required verdict is:

> **`PASS`**

