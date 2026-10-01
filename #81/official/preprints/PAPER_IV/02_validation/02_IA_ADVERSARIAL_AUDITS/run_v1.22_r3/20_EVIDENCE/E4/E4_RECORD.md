# E4 — Formal reproduction (r3): external build inherited, documentary confirmation

**No new build, Lake run or kernel replay was performed. Lean was not executed.**

## Original build (run_v1.2_r1, 2026-09-30, attempt 2, 15:09–21:33 UTC)
- **Runner.** The auditor's own runner, without Lake, Lean 4.28.0. Sources freshly extracted from the ZIP (615/615). New objects; no author `.olean` used. Mathlib read-only; cache of 113 821 files unchanged.
- **Console** `10_LOGS/E4_main_console.log` (ef5b01c7…): `modules_planned 607, pass 607, fail_or_blocked []`; 607 lines `PASS n 607`; `EXIT 0`; the 19 FREEZE_SCOPE targets all PASS.
- **`records.jsonl`** (0f2d8495…): 608 rows (607 + AuditorChecks), all PASS, exit 0; source hashes equal the manifest.
- **Logs.** 608 module logs, none containing "sorry". `ReleaseExportCheck` has 224 `#check` and 0 errors.
- **Annex.** 50/50 PASS (57ce1895…); 633 declarations audited, with axioms ⊆ {propext, Classical.choice, Quot.sound}.
- **Byte identity.** All 607 `.olean` files are byte-identical to the author's.
- **Axioms. These are records, not distinct theorems.**
  - 461 axiom records under the author's rule, of which 314 are genuine `#print axioms` outputs; the rest are repeated audit lines.
  - The exact scope: `#print axioms` on **18 headline declarations** = {propext, Classical.choice, Quot.sound}.
  - The auditor's own cone traversal over **50 public declarations**: 0 non-standard axioms, 0 `sorryAx`, 0 `Erdos81` constants.
- **SUMMARY.json.** `E4_main/SUMMARY.json` ("555 planned", AuditorChecks only) was overwritten and **is not used**.

## Confirmation in r3
- `10_SCRIPTS/e4_reuse_check.py` (sha256 db2eddb8…, identical to the r1 and r2 copies) produces `E4_REUSE_CHECK.json`. Its result is **identical** to r2: 607 modules, 19 targets, 224 exports, 50 annex modules, 461/314 axiom records, cones problems = 0.
- The supplementary log verifier (E8) independently re-hashes and re-scans the same 608 + 50 logs, plus the 608 author logs.

## Why validity carries over to r3
- r3 changes only documentary prose in the manuscripts. Lean, its ZIP and the annex are unchanged (E0 initial and final).
- The run_v1.2_r1 evidence is intact: 1097 manifest files.
- The compiled object is therefore exactly the cut cited by the r3 manuscripts.

## Limits
- Same machine and shared cache; not a clean-room build.
- No kernel replay.
- The original build was made by this same auditor and session.

**E4 verdict (r3): PASS — reused_verified_external_build.** Inherited and revalidated by identity.
