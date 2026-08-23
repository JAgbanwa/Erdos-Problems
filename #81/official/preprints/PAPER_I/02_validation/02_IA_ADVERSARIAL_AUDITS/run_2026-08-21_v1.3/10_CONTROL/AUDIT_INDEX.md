# Audit index — Paper I v1.3 residual re-audit, run_2026-08-21_v1.3

**Verdict:** `PASS_WITH_RESIDUALS` — all nine mandatory correction controls pass; 0 blocker,
0 major, 2 open minor, 1 note.

## Where to look

| I want | Path |
|---|---|
| the verdict and full reasoning | `30_REPORT/FINAL_AUDIT_REPORT.md` (also `.tex`, `.pdf`) |
| machine-readable verdict | `30_REPORT/FINAL_AUDIT_SUMMARY.json` |
| findings ledger | `10_CONTROL/FINDINGS.csv` |
| control and gate status | `10_CONTROL/GATE_STATUS.json` |
| who audited, with what, and the conflicts | `00_REQUEST/AUDITOR_DECLARATION.md` |
| frozen input identity | `00_REQUEST/INPUT_INVENTORY.json`, `INPUT_FREEZE_MANIFEST.sha256` |
| residual risk | `10_CONTROL/OPEN_RISKS.md` |

## Evidence map

| Area | Directory | Result |
|---|---|---|
| target freeze and anchors | `20_EVIDENCE/G0_TARGET_FREEZE/` | 8/8 anchors match |
| correction validation, controls 1–9 | `20_EVIDENCE/CORRECTIONS_VALIDATION/` | all 9 pass |
| mathematical regression | `20_EVIDENCE/MATH_REGRESSION/` | 14/14 symbolic; 6,732 LP cases, 0 mismatches; 5,429 split graphs, 0 violations |
| Gate H reuse under byte identity | `20_EVIDENCE/H_LEAN_REUSE/` | 32/32 members byte-identical; labelled `REUSED_BYTE_IDENTICAL_EXTERNAL_EVIDENCE` |
| citations and the `3/16` constant | `20_EVIDENCE/I_CITATIONS_NOVELTY/` | verified, pinpoint Theorem 1 p. 23 |
| bilingual and duplicate analysis | `20_EVIDENCE/L_BILINGUAL_DUPLICATES/` | 0 genuine duplicates in six artifacts |
| rendered-page QA and page duplicates | `20_EVIDENCE/PDF_PAGE_QA/` | 39 pages, 0 duplicate pages, 0 anomalies |
| package integrity | `20_EVIDENCE/M_PACKAGE_INTEGRITY/` | 28/28 sidecars verify; 1 residue finding |

## Reproducing

All scripts are Python 3.14 needing only `sympy` and `Pillow`; each evidence record states
its invocation. Arithmetic is exact throughout and no random seeds are used. Gate H is
reused, not rerun; the byte-identity proof is in
`20_EVIDENCE/H_LEAN_REUSE/results/BYTE_IDENTITY_PROOF.txt`.

## Relationship to the v1.2 report

The v1.2 report is **not** rewritten, relabelled or superseded. It stands with its own
`FAIL` verdict against its own hashes. No evidence is merged across the two runs.
