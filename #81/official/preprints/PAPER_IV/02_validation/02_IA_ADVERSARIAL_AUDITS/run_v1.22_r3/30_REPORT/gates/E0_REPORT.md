# Informe de puerta E0 — run_v1.22_r3 (Paper IV v1.22-r3)

Veredicto actual: **PASS**. Evidencia: `20_EVIDENCE/E0/`. Auditor: Claude Opus 5.5, misma sesión que las ejecuciones anteriores; no se ejecutó Lean.

---

# E0 — Identity (r3)

Script: `10_SCRIPTS/e0_v122r3.py` (read-only). It runs twice: `E0_INITIAL.json` before the review and `E0_FINAL.json` after it. The comparison between the two runs is in `30_REPORT/FINAL_CONSOLIDATED_AUDIT_REPORT.md` §11.

| Check | Result |
|---|---|
| `AUDIT_TARGET_v1.22_r3.json` (df89c3dd…) vs. its sidecar | match |
| r3 manifest (82217fe3…), r3 package (c1acd866…), mandate (abfcaec9…), source manifest (fb459343…), source ZIP (cb274145…), annex (2847a422…), base target r2 (f9317763…) | hash and bytes match |
| Earlier evidence: r2, r1, v1.21 and v1.2 ZIPs, source ZIP, annex | hash and bytes match |
| r3 manifest vs. directory: 226 files | 0 mismatches. Excluded by declaration: the manifest and its sidecar, the ZIP and its sidecar, `.aux`, `__pycache__` |
| r3 ZIP: 228 members (226 + manifest + sidecar) | CRC OK; no unsafe paths; no missing members; 0 hash mismatches; the 2 extra members equal the files on disk |
| Other ZIPs in r3 | none |
| EN/ES MD, TeX and PDF vs. r2 | **all six differ, as declared**. Byte identity is recorded but not required (mandate §1). The protected content is checked in E6. |
| r3 figures vs. r2 (figures/, figures_en/; 18 files) | **identical**; no file missing |
| r2 and r1 comparison cuts | directory = manifest (0f…, d9…); unchanged |
| Lean: 615/615 entries, no extras; source ZIP with 615 members, CRC OK, = manifest | OK |
| Annex: 40 members, CRC OK | OK |
| run_v1.2_r1, run_v1.21_r1, run_v1.22_r1, run_v1.22_r2 | 1097 / 340 / 188 / 182 manifest files unchanged; ZIP sidecars and CRC OK |

**E0 verdict (r3): PASS.**
