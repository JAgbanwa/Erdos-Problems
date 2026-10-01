# Paper IV v1.22-r4 — Final consolidated external adversarial audit report (E0–E8)

> **English translation supplied with the v1.23 editorial revision.** This document translates the auditor's Spanish report; it is not a new audit, a new verdict, or a statement newly issued by the auditor. First-person statements below belong to the original auditor. The unchanged Spanish original is [available here](../../02_IA_ADVERSARIAL_AUDITS/run_v1.22_r4/30_REPORT/FINAL_CONSOLIDATED_AUDIT_REPORT.md). Paths in the translated report retain the original audit-relative notation. Section 11 describes the production of the original report, not of this translation. Hashes, counts, labels and limitations are retained as written; translation does not correct or reinterpret them.

**Run:** `run_v1.22_r4`, completed on 2026-10-01. Actual timestamps are in `00_CONTROL/AUDITOR_DECLARATION.json` and in `20_EVIDENCE/E0/E0_INITIAL.json` and `E0_FINAL.json`. The owner requested it in the chat under the mandate `EXTERNAL_ADVERSARIAL_REVALIDATION_v1.22_r4.md`.

## Global verdict: PASS

For the E0–E8 adversarial audit process for the Paper IV version 1.22, r4 package, all applicable criteria are satisfied and no corrective action remains open:

- NEW-05 is closed following verification.
- No new defect was found.
- E4 is an inherited PASS, revalidated by identity: **no new build or independent kernel replay was performed**.

**What this PASS means.** It does not mean that there are no limitations, that human review has been performed, or that publication is authorized. Accepted limitations and historical facts (§8 and §9) remain disclosed. Milestones outside this assignment are listed in §10.

## 1. Current identity

| Object | Path | SHA-256 |
|---|---|---|
| r4 target | `02_validation/02_IA_ADVERSARIAL_AUDITS/AUDIT_TARGET_v1.22_r4.json` | `99ff96c9cb51c0d887548333ad41a7b6af0c1fc3523345ba0ec2f6dd03bce888` (= sidecar) |
| r4 mandate | `…/EXTERNAL_ADVERSARIAL_REVALIDATION_v1.22_r4.md` | `5d89f1c9f8af371989bbeb2b0d847b17891eceb8fb4b9413b5b6b2c27c2733fa` |
| Manuscript | **version 1.22**, **r4** package: `01_manuscript/v1.22_editorial_candidate_r4/` | — |
| r4 manifest (129 files) | `MANUSCRIPT_REVIEW_MANIFEST.json` | `f35bf2a9c383f6cf814bbca6a67a2fc2337eb051b97521ad492a79cae8fc1075` |
| r4 ZIP (131 members, correct CRC) | `PAPER_IV_v1.22_REVIEW_PACKAGE_r4.zip` | `8f20048c50968c93f768be774f2f6a571301dc67fe3c9023b331d15a359494e9` |
| ES MD / TeX / PDF (73 pp.) | `PAPER_IV_preprint_v1.22_es.*` | `a8e20305…` / `e5a26672…` / `638cad07…` |
| EN MD / TeX / PDF (72 pp.), **byte-identical to r3** | `PAPER_IV_preprint_v1.22_en.*` | `d3415df3…` / `c6b14105…` / `4280b03e…` |
| Supplemental verifier and inventory (= r3) | `verify_frozen_logs.py`, `LOG_INVENTORY.json` | `c55225f3…` / `938dcdcc…` |
| Lean freeze (615 entries) | `05_formalization/lean_piv-v12-fb459343d234/` | manifest `fb459343d234f968d7d32eff1491ea8a09aa2e135b313a80623012e7449042f5` |
| Source ZIP / annex | `LEAN_SOURCE_piv-v12-fb459343d234.zip` / `LEAN_BOUNDED_GAP_ANNEX_v1.0.zip` | `cb274145…a62e6` / `2847a422…4837d` |
| Historical packages | run_v1.2_r1 / v1.21_r1 / v1.22_r1 / r2 / r3 | `886ed7f0…` / `11659a97…` / `9c74d673…` / `626571be…` / `8ca5a69a1fdbb96823bf415de8de89265d14a8d2897acfed01a86c2a70fd3ddd` |

Full hashes are in `20_EVIDENCE/E0/E0_INITIAL.json`.

## 2. Current E0–E8 verdicts

| Gate | Current verdict | Basis | New check in r4 | Evidence |
|---|---|---|---|---|
| E0 | **PASS** | executed in r4 (initial and final) | complete identity (§1); English, verifier, inventory and figures unchanged from r3 | `20_EVIDENCE/E0/` |
| E1 | **PASS** | inherited and revalidated by identity | impact check | `30_REPORT/CLAIM_MAP_CONSOLIDATED.md` (33 records) |
| E2 | **PASS** | inherited and revalidated by identity | impact check | `E2_RECORD.md` from run_v1.2_r1, run_v1.21_r1 and run_v1.22_r1 |
| E3 | **PASS** | inherited and revalidated by identity | — | `20_EVIDENCE/E3/E3_RECORD.md` |
| E4 | **PASS — reused_verified_external_build** | inherited and revalidated by identity; no build or replay | documentary script rerun (identical result) | console `ef5b01c7…`, records `0f2d8495…`, annex `57ce1895…`; `E4_REUSE_CHECK.json` |
| E5 | **PASS** | inherited and revalidated by identity | — | `20_EVIDENCE/E5/E5_RECORD.md` |
| E6 | **PASS** | executed in r4 (ES delta); English inherited and revalidated by identity | MD/TeX word diff, protected content, PDF tokens, raster, readable pp. 40 and 66 | `20_EVIDENCE/E6/E6_RECORD.md`, `E6_R4_DELTA.json` |
| E7 | **PASS** | inherited and revalidated by identity | identical references | `20_EVIDENCE/E7/E7_RECORD.md` |
| E8 | **PASS** | log reader executed in r4; remainder inherited | verifier rerun: PASS on 1266 (identical to r3) | `20_EVIDENCE/E8/E8_RECORD.md` |

The gate matrix is in `30_REPORT/TRACEABILITY_MATRIX.csv`.

**Label changes relative to r3.**

- E6 changes from PASS_WITH_FINDINGS to PASS because NEW-05, the only finding, is closed.
- E8 changes from PASS_WITH_OBSERVATIONS to PASS. The evidence has not changed; its classification changes under the mandate's criterion: the historical X-28 defect remains recorded as a fact, and the control action has been completed. No observation is deleted.

## 3. New check: NEW-05 (E6)

Both replacements are complete in MD (l.1355, l.2356), TeX (l.1317, l.2159) and PDF (pp. 40 and 66):

- A.2: “**el calendario numérico** de C.3” [the numerical schedule in C.3]. This agrees with l.1599 and the C.3 heading, “Un calendario explícito” [An explicit schedule].
- F.4: “cota adaptada con **muestras con anclajes**” [adapted bound with pinned samples]. This agrees with the F.5 heading and Table 10.

Nothing else changes:

- Formulas, code, labels, headings, bold entries, table rows, images and references are identical.
- The editor's diff agrees with the auditor's.
- The PDF token diff contains only the 2 expected regions.
- Only pages 40 and 66 change in raster. Their page boundaries and line counts do not change, so pagination does not change either.

I inspected them at 130 and 160 dpi. **NEW-05 is CLOSED.**

## 4. Claim map and mathematics (inherited by identity)

The map contains **33 records**. They are the r3 records, with no new rows in r4:

- **21 historical records** from run_v1.2_r1: all MATCH except G.2, recorded in v1.2 as “not re-extracted”.
- **12 new records** from run_v1.22_r3 (N1–N12): all MATCH. They cover:
  - Theorem 5.0, in both interfaces;
  - Corollary 5.4, geometry and density;
  - dichotomy (1.5);
  - quadratic and linear optimality;
  - identity (6.7b);
  - Proposition D.3;
  - G.2 / Proposition G.1, thereby covering historical G.2.

The seven derivations in A.2 are **ACCEPTABLE_SUMMARY**:

- A2-1, A2-2 and A2-7 since v1.2;
- A2-3, A2-5 and A2-6 since v1.21;
- A2-4 since v1.22-r1.

## 5. E4: formal evidence (inherited and revalidated by identity)

**External build** from run_v1.2_r1, 2026-09-30, from 15:09 to 21:33 UTC. Auditor's runner without Lake, Lean 4.28.0, sources extracted from the ZIP.

**Original records:**

- Console: **607** modules with PASS, `EXIT 0`, and **19** targets with PASS.
- `records.jsonl`: 608 rows, all PASS with exit code 0.
- **224** `#check` commands in `ReleaseExportCheck`, with 0 errors.
- Annex: **50/50**.
- The 607 oleans are byte-identical to the author's.

**Axioms** (these are not distinct theorems):

- 461 records, of which 314 are `#print axioms` outputs and the remainder repetitions.
- 18 principal declarations with {propext, Classical.choice, Quot.sound}.
- 50 public cones without nonstandard axioms, without `sorryAx` and without `Erdos81`.

The `SUMMARY.json` overwritten by AuditorChecks is not used.

**Why this remains valid in r4:**

- r4 changes only two Spanish phrases.
- E0 confirms that Lean, the source ZIP, the annex and the run_v1.2_r1 evidence remain intact.
- The documentary script reproduces exactly the same result.

## 6. E5 and E8

**E5:** 59 distinct checks plus 7 negative controls, all rejected. Repetitions are not added. Finite tests and Certo do not replace universal proofs.

**E8:**

- The `verify_frozen_logs.py` verifier remains **mandatory** and identical to r3.
- I reran it with its own output: **PASS on 1266 logs**, comprising 608 + 50 + 422 + 186 files, counted once each.
- The r3 tests are inherited: 15/15 cases, 4/4 corruptions and the case-sensitive error rule (E8-02 closed).
- **History and current compliance of X-28.** The frozen runners retain their insufficient pattern; this is a historical fact, they have not been patched, and this is recorded. The mitigating control is in force and verified, with additional axiom and cone evidence. No action remains open.

## 7. Original verdict history (not rewritten)

| Revision | Run | Original global verdict |
|---|---|---|
| v1.2 | run_v1.2_r1 | **INCONCLUSIVE**: E2 because of A2-3…A2-6 |
| v1.21 | run_v1.21_r1 | **INCONCLUSIVE**: E2 because of A2-4 |
| v1.22-r1 | run_v1.22_r1 | **PASS**, with nonblocking MINOR findings |
| v1.22-r2 | run_v1.22_r2 | **PASS_WITH_OBSERVATIONS** |
| v1.22-r3 | run_v1.22_r3 | **PASS_WITH_FINDINGS**: NEW-05 |
| v1.22-r4 | **run_v1.22_r4** | **PASS** |

## 8. Findings: current status

`FINDINGS.csv` contains 54 rows.

| Class | IDs | Open action |
|---|---|---|
| Closed (30) | X-01…X-16, X-20, X-21, X-23, X-25, X-27, NEW-01…NEW-05, R-02, E8-01, E8-02, E8-03 | none |
| Mitigated, with control in force | X-28: the historical runner defect is preserved | none |
| Accepted observations, limitations or historical facts (7) | X-17 (now also covering N8), X-18, X-19, X-22, X-24, X-29 and R-01 | none |
| Information | X-26 (independence) | none |
| Preserved corrections by the auditor and to the process (15) | AUD-P1, AUD-C1, AUD-C2, C2-01…C2-08, C3-01…C3-03, C4-01…C4-03, C5-01 | none |

C5-01 is an index error in a reporting field of my E6 script. I recalculated it correctly; it does not affect the verdict.

## 9. Disclosed independence and limitations

These limitations are not defects under the contracted scope.

- **Model:** Claude Opus 5.5 (`claude-opus-5-5`), provider Anthropic.
- **Session:** this revalidation is a **continuation of the same session** that produced the five previous runs. **It is not blind, not a new session, and not independent of model family.** The manuscript discloses the use of Claude.
- **Reading:** I read the earlier evidence and the editor's documents, and checked them against my own evidence. They are recorded in `00_CONTROL/INPUT_ACCESS_LOG.csv`.
- **Environment:** the same machine and cache as the historical build.
- **Execution:** no Lean, no build and no kernel replay.
- **Scope of the written check:** summary-level comparison against frozen formal statements.
- **Pages not reinspected:** unchanged ES pages (raster-identical) and all EN pages (byte-identical) inherit the r3 visual inspection.

## 10. Milestones outside this assignment (not conditions of this PASS)

- Human peer review is a future, independent milestone; it is recommended, and this report does not replace it.
- Optionally, an audit by another model family in a separate session, with a clean-room build or kernel replay.
- The publication decision belongs to the owner. This report does not authorize it.

## 11. Final E0, PDF and sealing

- **Final E0:** `20_EVIDENCE/E0/E0_FINAL.json`. Its `checks` object is identical to the initial one (`20_EVIDENCE/logs/E0_final.log`).
- **PDF:** generated with pandoc (Markdown → HTML and standalone TeX) plus PyMuPDF Story (HTML → PDF). **It was not compiled from TeX.** I reviewed it visually (`30_REPORT/PDF_VISUAL_CHECK.csv`).
- **Package:** `40_PACKAGE/EXTERNAL_REVALIDATION_run_v1.22_r4.zip`, with its `RUN_MANIFEST.json`, SHA-256, verified CRC and member list in `PACKAGE_INDEX.json`. Historical ZIPs are linked by path and hash (§1), without duplication.
- **No external effects:** nothing was published, no push was performed, and no data was sent off the machine. Originals and earlier reports were not modified.
