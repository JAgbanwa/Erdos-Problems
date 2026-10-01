# E4 — Documentary closure (method: `reused_verified_external_build`)

**No Lean, Lake, leanchecker, compilation or negative-control compilation was run in this cycle.** The E4
PASS of run_v1.2_r1 is reused after re-verification. Nothing was recompiled in this cycle.

Identity (E0): all 1097 files of `run_v1.2_r1/40_PACKAGE/RUN_MANIFEST.json` still match on disk. The sealed
ZIP `EXTERNAL_AUDIT_run_v1.2_r1.zip` (sha256 886ed7f0…5e2b, 1098 members, CRC OK) matches its sidecar. Every
item of the author's `EXTERNAL_EVIDENCE_BINDING.json` matches. The Lean source cut is unchanged (615/615).

Coverage re-verified by `e4_reuse_check.py` → `E4_REUSE_CHECK.json`, which does **not** use
`10_LOGS/E4_main/SUMMARY.json` (that file was overwritten by the AuditorChecks invocation, C-06):
- `records.jsonl`: 608 records and 608 distinct modules, all PASS. That is the 607 modules of the cut plus
  the auditor file `AuditorChecks`. All exit codes are 0 and no sorry flag is set.
- The source hashes in the records equal SOURCE_MANIFEST for all 607.
- `E4_main_console.log` final summary: modules_planned 607, pass 607, fail_or_blocked [], finished
  2026-09-30T21:33:08Z. All 19 targets are PASS, the console ends with "EXIT 0", and there are 607
  "PASS i 607" lines.
- 608 module logs; case-insensitive "sorry" appears in none. The four log sets (auditor main 608, annex 50,
  author segment 1 422, segment 2 186) were rescanned with the corrected detector: 0 hits.
- 19 target logs: 461 records under the author rule, 314 of them `#print axioms`, with no non-standard axiom.
- 224 `#check` lines in `ReleaseExportCheck.lean`; its log has 0 error lines.
- Annex: 50 records, 50 PASS. BoundedCliqueGap audit line: 633 declarations with standard axioms; the five
  cited theorems depend on exactly [propext, Classical.choice, Quot.sound].
- `olean_vs_author.json`: 607/607 byte-identical. `AuditorChecks.log`: "AUDITOR CONE SUMMARY: 50
  declarations; problems=0". `cache_diff.json`: shared cache unchanged.
- Types and axioms of the headline declarations are as recorded in run_v1.2_r1 E3/E4 and are unchanged,
  because the source is unchanged.

Limits kept: same machine; shared pinned third-party oleans, not rebuilt; no independent kernel replay.

**E4 verdict: PASS (reused_verified_external_build).**
