# Paper IV v1.22-r1 — External adversarial revalidation (run_v1.22_r1)

**Overall verdict: PASS.** It comes with two MINOR, non-blocking presentation findings in the Spanish edition (X-15, NEW-01) and an inaccurate author claim about them (NEW-03). No mandatory derivation remains insufficient. This is not human peer review and not permission to publish.

## 1. Target, identity and comparison
- **Target.** `01_manuscript/v1.22_editorial_candidate/`, bound by `AUDIT_TARGET_v1.22.json` (sha256 cbe0fd6e8e8c3f70…, matching its sidecar).
  - `MANUSCRIPT_REVIEW_MANIFEST.json` (d9e559a3…): 223 files.
  - `PAPER_IV_v1.22_REVIEW_PACKAGE_r1.zip` (2b87b746…): 225 members.
  - Lean cut `lean_piv-v12-fb459343d234`: 615/615 entries.
  - The identity was complete and matching at E0 initial. **E0 final (after the review) is identical**, so neither the inputs nor the historical evidence changed.
- **Comparison baseline.** v1.21 and `run_v1.21_r1`.
- **Preservation.** `run_v1.2_r1` (1097 files) and `run_v1.21_r1` (340 files) are unchanged on disk, and their ZIP sidecars match.

## 2. Auditor declaration
- Model and family: Claude Opus 5.5 (`claude-opus-5-5`), Anthropic.
- Session: a **continuation of the same Claude Code session** that produced run_v1.2_r1 and run_v1.21_r1 (with context compaction). This is not a new session.
- Exposure: full prior exposure; **not blind**; not cross-family. The model family is the same as the manuscript's declared AI assistant. The machine and pinned cache are shared.
- Reads: the read restriction is operational, not technical isolation. Every read is listed in `00_CONTROL/INPUT_ACCESS_LOG.csv`, including the pinned Mathlib source read and one incidental out-of-scope path listing that was not opened (C2-07).
- **No Lean, Lake, leanchecker or build was executed.**

## 3. Order executed
E0 initial → E2 (C.3, six checks) → E6 (parity, all 145 pages, zooms) → E1/E3/E7 regressions → E5/E8 → E0 final and documentary E4. The author response was read only after the independent C.3 pass.

## 4. Gate results

| Gate | Verdict | Repeated this cycle | Inherited (and why) |
|---|---|---|---|
| E0 | PASS | E0 initial + final (identical) | – |
| E1 | PASS | diff; tags, displays and headings | – |
| E2 | **PASS** | C.3 rederived against pinned Mathlib `Bound.lean` and frozen `E18/Numeric.lean`, `E19/Main.lean`; A2-4 → ACCEPTABLE_SUMMARY; R-02 checked | A2-1–3, 5–7 (text unchanged per diff) |
| E3 | PASS | new-identifier resolution; X-27 text | probe AuditorASProbe (source identical, 615/615) |
| E4 | **PASS — reused_verified_external_build** | documentary script over records.jsonl, console, module logs, annex records and manifests (not SUMMARY.json): 607 modules, 19 targets, 224 checks, 50 annex modules; identical to the v1.21 result | run_v1.2_r1 build, permitted by 615/615 source identity and unchanged run_v1.2_r1 evidence; **no new build** |
| E5 | PASS | 14 new exact C.3 checks, each with a rejected negative control; 21 v1.21 checks rerun | run_v1.2_r1 T01–T24 (text unchanged) |
| E6 | PASS_WITH_FINDINGS | full parity; 145/145 pages viewed; 10 zooms at 130 dpi | – |
| E7 | PASS | reference diff; NEW-02; spelling | v1.21 literature checks X-06–X-11 (text unchanged) |
| E8 | PASS_WITH_OBSERVATIONS | 1266-log detector rescan (identical); runner hashes; package inventory | – |

## 5. The open item from run_v1.21_r1: A2-4 / X-05 — closed
C.3 now defines the regularity bound as Mathlib's `SzemerediRegularity.initialBound`, `stepBound` and `bound`, and I verified it literally against the pinned source.

At η₀, the following steps are all correct:
- I = k₀, because 100/ε⁵ ≤ 4⁴⁰⁰⁰.
- H = h exactly.
- The two-iteration lower bound R ≥ 2^{2^{k₀}} ≥ G_i holds, and the text explicitly says it is only a lower bound.
- The five terms of (C.1), with their ceilings and the final unit, are bounded by k₀ + αB + G₃ + βG₁B⁵ + 10¹⁸(1+2G₂) + 1. This is the content of `E18.Numeric.NfarE_eta0_le`.
- The absorption B⁶/4 + 7B² ≤ B⁶ and the induction 4t_j ≤ T(j+5) give N_far(η₀) ≤ B⁶ ≤ 2^{30R} ≤ T(h+7), matching `E19.absorb_abstract`, `B6_le_two_pow_two_pow` and `NfarE_eta0_le_tower`.

A.2 now points to C.3, and the account can be reconstructed from the printed text alone. **A2-4: ACCEPTABLE_SUMMARY; X-05: RESOLVED.** All seven A.2 rows are now ACCEPTABLE_SUMMARY. R-02 is resolved. R-01 is kept as a declared expository limit.

## 6. Findings remaining (all non-blocking)

| ID | Severity | Location | Remaining step |
|---|---|---|---|
| X-15 | MINOR | ES prose: MD l.526, 578, 688, 746 (×2), 1892, 1917, 1959, 2177, 2182 (×2), 2184; PDF pp. 16, 18, 20, 21, 55, 56, 61 | Translate 12 occurrences of "matching(s)" and 1 of "packing" in prose (emparejamiento(s)/empaquetamiento). The Figure 3 label "valor base" is already fixed, and cited titles must stay untranslated. |
| NEW-01 | MINOR | ES §7.2: MD l.1203, TeX l.1084, PDF p35 | Set "Model" in "función de ganancia acotada de Model" as code (`` `Model` ``), as in EN and in v1.2 ES. The prior run missed this (C2-08). |
| NEW-03 | MINOR | `RESPONSE_TO_REVALIDATION_v1.22.md`, rows X-15 and NEW-01 | The response claims the X-15 prose translation and the Model restoration; neither happened in ES. |
| R-01, E8-02, X-17, X-18, X-19, X-22, X-24, X-29 | OBSERVATION | as before | kept |
| X-28 | MINOR, MITIGATED | frozen runners | patch not applied; external detector confirmed again |

Resolved this cycle: X-05, X-12, X-10 (spelling), NEW-02, R-02, E8-01 (attribution), E8-03 (single package). X-27 is preserved. The full matrix (45 rows, all historical IDs kept) is in `FINDINGS.csv`.

## 7. Why PASS
No mathematical error was found, and the last mandatory derivation (C.3) is now complete and consistent with the frozen formal statements. Formal reproduction is confirmed by reuse with verified identity. The remaining items concern Spanish typography and terminology and the accuracy of the author's change log; none affects a statement, constant, proof step or formal correspondence. Under §4 of the mandate, non-blocking observations may accompany a PASS.

## 8. Auditor corrections (this cycle)
- C2-01: C3m negative control mis-specified; corrected and supplemented.
- C2-02 to C2-05: during E6, image reads were stripped by a request limit, and provisional page-log rows had been written before the pages were confirmed viewed. Interim progress messages to the owner overstated coverage. All such rows were discarded (the files are kept), and the final log was rebuilt only from sheets displayed at the time of logging.
- C2-06: console encoding error on the first E4 script run; rerun identical.
- C2-07: an over-broad filesystem listing showed an out-of-scope path; it was not opened.
- C2-08: run_v1.21_r1 missed the ES `Model` residual.

## 9. Limitations
- Same session and model as both prior runs, and the same family as the manuscript's assistant. Same machine and cache.
- No kernel replay; E4 is reuse.
- The written-proof check is summary-level.
- Visual inspection used 90 dpi 2-up sheets plus selected 130 dpi zooms.
- Qualified human review remains necessary before any publication decision.

## 10. Deliverables
- `00_CONTROL/`: declaration, access log, corrections.
- `10_LOGS/`.
- `20_EVIDENCE/E0–E8/`: records, scripts, inputs and results.
- `30_REPORT/`: this report and the gate reports in MD, TeX and PDF; `SUMMARY.json`; `FINDINGS.csv`.
- `40_PACKAGE/`: `RUN_MANIFEST.json`, per-gate ZIPs, `EXTERNAL_REVALIDATION_run_v1.22_r1.zip` with sha256 sidecar, `PACKAGE_INDEX.json`.

Nothing was published, pushed, tagged or sent to third parties. The manuscript and its hashes were not modified.
