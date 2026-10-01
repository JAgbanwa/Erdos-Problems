# E4 — Formal build: documentary confirmation (no recompilation)

**Status: PASS — reused_verified_external_build.** No Lean, Lake, leanchecker or other build was run in this cycle (mandate §2). No pin, cache or compiled object was touched.

## Why reuse is permitted (identity)
- The source cut is identical to the one built in run_v1.2_r1: 615/615 SOURCE_MANIFEST entries (fb459343…) match, with no extra files (E0 initial and final).
- The Lean source ZIP (cb274145…) and the annex ZIP (2847a422…) are unchanged (E0).
- The run_v1.2_r1 evidence is intact: its 1097 manifest files are unchanged on disk and the ZIP sidecar matches (E0).
- v1.22 changes the manuscript only, not Lean (E3).

## Documentary re-verification
`e4_reuse_check.py` (the run_v1.21_r1 script, reused verbatim) → `E4_REUSE_CHECK.json`; the log is `10_LOGS/E4_reuse_check.log` (see C2-06). By design it does **not** rely on `E4_main/SUMMARY.json`. Its sources are `records.jsonl`, the console log, the 608 module logs, the annex records, `AuditorChecks.log`, `olean_vs_author.json`, `cache_diff.json` and the source manifest.

| Required evidence | Found |
|---|---|
| 607 main modules | records.jsonl: 607/607 cut modules PASS (608 records including AuditorChecks); console `modules_planned 607, pass 607, fail_or_blocked []`; 607 `PASS n 607` lines; `EXIT 0`; record source hashes equal the manifest for all 607 |
| 19 targets | console `targets_status`: all 19 FREEZE_SCOPE targets PASS |
| 224 export controls | `ReleaseExportCheck.lean` has 224 `#check`; its log has 0 error lines |
| 50 annex modules | annex records.jsonl: 50/50 PASS; BoundedCliqueGap axiom check: 633 declarations, axioms ⊆ {propext, Classical.choice, Quot.sound} |
| Axioms and sorry | 461 axiom records, none non-standard; 0 module logs with sorry text; the 1266-log detector scan has 0 hits (E8) |
| Byte identity and cache | 607/607 oleans identical to the author's; auditor cone summary: 50 declarations, problems = 0; Mathlib cache unchanged (113821 files; no file changed, added or removed) |

The resulting JSON is **identical** to the run_v1.21_r1 `E4_REUSE_CHECK.json`.

I reread the run_v1.2_r1 `E4_RECORD.md`. Its limitations remain in force: same machine and cache, a two-segment author build, and no kernel replay.
