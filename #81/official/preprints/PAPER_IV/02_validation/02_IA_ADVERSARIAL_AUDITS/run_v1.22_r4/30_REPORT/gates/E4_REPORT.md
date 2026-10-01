# Informe de puerta E4 — run_v1.22_r4 (Paper IV v1.22-r4)

Veredicto actual: **PASS — reused_verified_external_build**. Evidencia: `20_EVIDENCE/E4/`. Auditor: Claude Opus 5.5, misma sesión que las ejecuciones anteriores; no se ejecutó Lean.

---

# E4 — Formal reproduction (r4)
**Status: PASS — reused_verified_external_build, inherited and revalidated by identity. No new build, Lake, Lean or kernel replay was run.**

The original external build is run_v1.2_r1, attempt 2, 2026-09-30, 15:09–21:33 UTC.
- **Console** `10_LOGS/E4_main_console.log` (ef5b01c7…): `modules_planned 607, pass 607`, no failures; 607 lines `PASS n 607`; `EXIT 0`; all 19 FREEZE_SCOPE targets PASS.
- **`records.jsonl`** (0f2d8495…): 608 rows, all PASS, exit 0.
- **`ReleaseExportCheck`**: 224 `#check` lines, 0 errors.
- **Annex** (57ce1895…): 50/50 PASS; 633 declarations with standard axioms.
- **Objects**: 607 oleans byte-identical to the author's.
- **Axioms**: 461 *records*, of which 314 are `#print axioms` outputs and the rest repetitions, **not distinct theorems**. The 18 headline declarations depend on {propext, Classical.choice, Quot.sound}. In the 50 public cones there are 0 non-standard axioms, 0 `sorryAx` and 0 `Erdos81` constants.
- `E4_main/SUMMARY.json` was overwritten by AuditorChecks and is **not used**.

**r4 confirmation.** `10_SCRIPTS/e4_reuse_check.py` (db2eddb8…) produces `E4_REUSE_CHECK.json`, **identical** to r3 and r2.

**Validity.** r4 changes only two ES documentary phrases. Lean, the source ZIP, the annex and the run_v1.2_r1 evidence (1097 files) are unchanged (E0 initial and final).

**Limits.** Same machine and cache; no clean-room build; no kernel replay; the build was produced by the same auditor and session.
