# Gate E8 report — run_v1.22_r1 (Paper IV v1.22-r1)

Verdict: **PASS_WITH_OBSERVATIONS**. Evidence: `20_EVIDENCE/E8/`. Auditor: Claude Opus 5.5, same session as run_v1.2_r1/run_v1.21_r1; no Lean executed.

---

# E8 — Author evidence, scope attribution and packaging

| Item | Examination | Result |
|---|---|---|
| E8-01: 1266-log scan | The E8-01 row of `RESPONSE_TO_REVALIDATION_v1.22.md` says the author's earlier scan covered 844 logs and the auditor extended it to 1266, with zero alerts, and that this evidence is reused with attribution. This matches the run_v1.21_r1 E8 record. I re-executed the run_v1.21_r1 detector script read-only (`e8_detector_check.py` → `E8_DETECTOR_RERUN.json`): 10/10 cases correct; 608 + 50 + 422 + 186 = **1266** logs, 0 detector hits, 0 broad "sorry" hits. The result is identical to the v1.21 JSON. | **Correctly attributed.** The 1266 scope is the prior auditor's scan, not the old author script. |
| E8-02 / X-28: runner patch | The frozen runners `tools/paperiv_build.py` and `tools/audit_publication.py` still have their SOURCE_MANIFEST hashes. There is no `.patch` file in the v1.22 candidate directory, and the response says the patch is not applied. | **Not applied.** X-28 stays MITIGATED by the external detector, and the limitation stays declared. |
| E8-03: single package | E0: `PAPER_IV_v1.22_REVIEW_PACKAGE_r1.zip`, bound by AUDIT_TARGET and its sidecar, is the only ZIP in `v1.22_editorial_candidate/`. | **RESOLVED** |
| Response claims: X-15 and NEW-01 | X-15 says the prose was translated, but 13 residual occurrences remain. NEW-01 says `Model` was restored, but only the EN text was fixed (E6). | **Inaccurate claims (MINOR)** |
| Response claims: C.3 Lean correspondence | The listed declarations exist and match the prose (E2/E3). | Correct |
| Response claims: R-01 kept, R-02 clarified | Confirmed (E2). | Correct |
| Other author objects (`PROTECTED_BASELINE.json`, `SEMANTIC_CHECKS.json`, `EXACT_CHECKS.json`, `LEAN_IDENTITY_CHECK.json`, `VISUAL_REVIEW_v1.22.md`) | All are bound by the manifest (E0). They were used only as claims to contrast, never as an inherited PASS. `VISUAL_REVIEW` claims "valor base" and the restored [6], which is correct; it does not claim the prose translation. | Noted |
| Historical items | X-19, X-22, X-24, X-26, X-29, AUD-P1, AUD-C1, AUD-C2 and the C-* / C1-* corrections are preserved in their runs, which are unchanged (E0). | Preserved |

**E8 verdict: PASS_WITH_OBSERVATIONS.**
