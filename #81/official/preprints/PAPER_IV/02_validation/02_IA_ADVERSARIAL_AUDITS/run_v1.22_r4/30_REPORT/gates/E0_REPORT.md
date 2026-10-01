# Informe de puerta E0 — run_v1.22_r4 (Paper IV v1.22-r4)

Veredicto actual: **PASS**. Evidencia: `20_EVIDENCE/E0/`. Auditor: Claude Opus 5.5, misma sesión que las ejecuciones anteriores; no se ejecutó Lean.

---

# E0 — Identity (r4)

Script: `10_SCRIPTS/e0_v122r4.py` (read-only). It produces `E0_INITIAL.json` and `E0_FINAL.json`; the comparison between them is in report §11.

| Check | Result |
|---|---|
| `AUDIT_TARGET_v1.22_r4.json` (99ff96c9…) vs. sidecar | match |
| r4 manifest (f35bf2a9…, 129 files), r4 ZIP (8f20048c…), mandate (5d89f1c9…), source manifest, source ZIP, annex, base target r3 (df89c3dd…) | hash and bytes match |
| Earlier evidence: the r3, r2, r1, v1.21 and v1.2 ZIPs, source ZIP, annex | match |
| r4 manifest vs. directory | 0 mismatches. Excluded by declaration: manifest/sidecar, ZIP/sidecar, `.aux`, `__pycache__` |
| r4 ZIP: 131 members (129 + manifest + sidecar) | CRC OK; nothing missing or extra; 0 hash mismatches |
| **EN MD/TeX/PDF vs. r3** | **byte-identical** |
| ES MD/TeX/PDF vs. r3 | differ, as declared (see E6) |
| `verify_frozen_logs.py` (c55225f3…) and `LOG_INVENTORY.json` (938dcdcc…) vs. r3 | **identical** |
| Figures (18 files + svg) vs. r3 | identical; none missing |
| r3 and r2 comparison cuts | unchanged |
| Lean 615/615; source ZIP = manifest; annex has 40 members, CRC OK | OK |
| run_v1.2_r1, v1.21, r1, r2, r3 | 1097 / 340 / 188 / 182 / 165 manifest files unchanged; sidecars and CRC OK |

**E0 verdict (r4): PASS.**
