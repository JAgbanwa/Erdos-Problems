# Audit index - Paper I v1.3 pkgfix, run_2026-08-21_v1.3_pkgfix

**Verdict:** `PASS`. **Paper I v1.3 is externally closed.**

| I want | Path |
|---|---|
| the verdict and reasoning | `30_REPORT/FINAL_AUDIT_REPORT.md` (also `.tex`, `.pdf`) |
| machine-readable verdict | `30_REPORT/FINAL_AUDIT_SUMMARY.json` |
| findings ledger | `10_CONTROL/FINDINGS.csv` |
| control status | `10_CONTROL/GATE_STATUS.json` |
| conflicts and limitations | `10_CONTROL/AUDITOR_DECLARATION.md` |
| frozen target identity | `00_REQUEST/INPUT_TARGET_INVENTORY.json`, `INPUT_TARGET_MANIFEST.sha256` |

## Evidence map

| Area | Directory | Result |
|---|---|---|
| target inventory and anchors | `20_EVIDENCE/TARGET_VERIFICATION/` | 308 files / 37,763,479 bytes as declared; 10/10 anchors; owner manifest 219/219 |
| Control A, scratch removal | `20_EVIDENCE/RES_V13_001_SCRATCH/` | PASS - RES-V13-001 closed |
| Control B, changelog names | `20_EVIDENCE/RES_V13_002_CHANGELOG/` | PASS - RES-V13-002 closed |
| Control C, package regression | `20_EVIDENCE/PACKAGE_REGRESSION/` | PASS - 37/37 sidecars, 0 unannounced delta |
| byte-identity reuse | `20_EVIDENCE/BYTE_IDENTITY_REUSE/` | 32/32 members identical |

## Summary of the three Paper I runs

| Run | Target | Verdict |
|---|---|---|
| `run_2026-08-21_v1.2` | `preprint_draft_v1.2` | `FAIL` (Gate L, five duplicated Spanish blocks) |
| `run_2026-08-21_v1.3` | `preprint_draft_v1.3` | `PASS_WITH_RESIDUALS` (nine controls pass, two MINOR package defects open) |
| `run_2026-08-21_v1.3_pkgfix` | `preprint_draft_v1.3` corrected | **`PASS`** |

None of the earlier reports is relabelled. Each stands against its own hashes.
