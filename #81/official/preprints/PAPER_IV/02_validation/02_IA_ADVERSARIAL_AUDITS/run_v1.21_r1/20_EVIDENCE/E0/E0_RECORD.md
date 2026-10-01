# E0 — Identity (run_v1.21_r1)

Script: `e0_v121.py` (auditor-written, read-only). Runs: `E0_INITIAL.json` at start (2026-09-30 ~23:04 UTC) and
`E0_FINAL.json` at close — **identical**.

- `AUDIT_TARGET_v1.21.json` sha256 574352e8…af2a7 = sidecar. Request b360c967…, manuscript manifest
  abae830f…, review ZIP r1 5fc4099a…, source manifest fb459343…, evidence binding efa96178…: all sha and byte
  counts match.
- MANUSCRIPT_REVIEW_MANIFEST: 88 files, all match the directory; ZIP r1: 90 members (88 + manifest + its
  sidecar), CRC OK, no unsafe paths, all member hashes equal; six manuscripts listed.
- PDFs: EN 71 pages, ES 72 pages.
- Lean cut: 615/615 manifest entries match the frozen directory, no extra files; source ZIP cb274145… unchanged.
- Reused evidence: all 1097 files of `run_v1.2_r1/40_PACKAGE/RUN_MANIFEST.json` unchanged on disk; sealed ZIP
  886ed7f0… matches its sidecar (1098 members, CRC OK); all 18 items and the archive of the author's
  `EXTERNAL_EVIDENCE_BINDING.json` match.

**E0 verdict: PASS.**
