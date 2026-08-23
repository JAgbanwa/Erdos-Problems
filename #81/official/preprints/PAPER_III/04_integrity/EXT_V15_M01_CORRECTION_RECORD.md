# EXT-V15-M01 correction record

**Finding:** stale generically named manuscript evidence shadowed current v1.5 evidence.  
**Source report:** `run_2026-08-23_v1.5_residual/30_REPORT/FINAL_AUDIT_REPORT.md`  
**Source-report SHA-256:** `4f4537816840c62fb23521190fab4fa1a860085e05a4cb956d8afe1eb3b67596`  
**Correction class:** package hygiene only; no manuscript, PDF, mathematical or Lean change.

## Correction

1. All 29 compiler-log files formerly located directly under
   `03_reproducibility/manuscript_build_logs/` were moved without changing their bytes to
   `03_reproducibility/manuscript_build_logs/v1.3_legacy/`. This includes the ten generic
   `LUALATEX_DIRECT_*`, `LUALATEX_*_PASS*` and `LUALATEX_FINAL_*` files identified by the
   auditor. The remaining nineteen files already contained `v1.3` in their filenames but were
   moved with the same historical group so the root has no ambiguous compiler evidence.
2. `03_reproducibility/MANUSCRIPT_CONSISTENCY_RESULTS.json` was removed from the active
   package. Its byte-identical historical copy remains at
   `superseded/unpublished_audited_draft_v1.4/03_reproducibility/` with SHA-256
   `2be045e5a9377285ef7d3b7bd1c41664e6959874be15c0edeac3461345d7ce40`.
3. The only current consistency result is now
   `03_reproducibility/MANUSCRIPT_CONSISTENCY_RESULTS_v1.5.json`, which records `PASS` 61/61
   and binds to English Markdown hash
   `a98e9313bfe5f1f98cc92bb29ba97386e8178e38c0201854cf40bd255066c99a`.
4. The only current compiler logs are the six files under
   `03_reproducibility/manuscript_build_logs/v1.5/`; each names
   `PAPER_III_preprint_v1.5` and records the correct 46/47-page build.

## Regression evidence

- Targeted `EXT-V15-M01` closure suite: `PASS` 16/16.
- Expanded complete internal residual audit: `PASS` 79/79.
- All six manuscript hashes are unchanged from the externally audited target.
- Lean archive hash remains
  `79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104`.
- No prior external report or audit evidence was rewritten.

**Disposition requested:** `EXT-V15-M01` `CLOSED`; external consolidated verdict `PASS`.

