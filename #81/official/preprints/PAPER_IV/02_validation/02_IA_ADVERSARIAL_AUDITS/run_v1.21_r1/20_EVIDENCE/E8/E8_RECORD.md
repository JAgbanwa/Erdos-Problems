# E8 — Author evidence and packaging revalidation

Author objects examined (manuscript directory, bound by MANUSCRIPT_REVIEW_MANIFEST): `sorry_log_recheck.py`,
`SORRY_RECHECK.json`, `RUNNER_SORRY_FIX_NOT_APPLIED.patch`, `AXIOM_COUNT_RECONCILIATION.json`,
`EVIDENCE_AND_ANNEX_CORRIGENDUM.md`, `LEAN_IDENTITY_CHECK.json`, `EXTERNAL_EVIDENCE_BINDING.json`,
`RESPONSE_TO_AUDIT_v1.21.md`, `EDITORIAL_CHANGE_REPORT_v1.21.md` (grep only). They are not inherited
verdicts. Each was contrasted with the auditor's own checks.

| Item | Examination | Result |
|---|---|---|
| X-28 detector | The pattern was copied literally from `sorry_log_recheck.py` into the auditor's `e8_detector_check.py`, not imported. 10 cases were tested, including the real captured negative log (sha256 58441539…). All 1266 existing logs across the 4 sets were scanned. | Correct: all positives detected, all negatives accepted, 0 hits in the logs. The frozen runners are unchanged (sha256 82479893… / 0a7e66a2… equal the manifest), and the patch is proposed and not applied. **Mitigated; the historical runners keep their insufficient pattern.** OBSERVATION E8-01: the author's rescan omits the 422 logs of author segment 1; the auditor's scan covers them (0 hits). OBSERVATION E8-02: the proposed `audit_publication.py` patch also adds `re.I` to the `error` alternative, which broadens that check (acceptable, but a change of scope). |
| X-20 axiom count | `AXIOM_COUNT_RECONCILIATION.json`: 314 + 147 = 461 | Equals the auditor's recount on the reused auditor logs (E4_REUSE_CHECK). The erratum "313" of the internal report is corrected by a separate note, without rewriting history. **Kept as errata; resolved.** |
| X-25 annex README | The corrigendum reads "§8.2" as "Appendix G.1". The annex ZIP is unchanged (2847a422…). | **Resolved by supplement** (annex file untouched). |
| X-19 lakefile residue | Kept deliberately and documented. | Acceptable; OBSERVATION kept. |
| X-21 / X-29 | The corrigendum and §7 record the auditor's byte-identical reproduction and keep the historical doubt. | Correct. The historical limitation remains recorded. |
| X-22 disagreement | Kept in both the corrigendum and the response. | Correct. |
| X-26 independence | The corrigendum describes the v1.2 run as a separate fresh session. | Correct for run_v1.2_r1. **This v1.21 revalidation ran in the same session as run_v1.2_r1**, as the auditor declares (not blind, not independent of that run). |
| AUD-P1, C-01…C-08 | Preserved in run_v1.2_r1 and unaltered (E0: prior manifest unchanged). | Correct. |
| Evidence binding | `EXTERNAL_EVIDENCE_BINDING.json`: 18 items and the archive; all hashes match. | Correct. |
| Response claims | "No theorem, hypothesis, constant, equation tag or Lean block changed; five declared renamings". | Confirmed by the auditor's own diff (E2). However, the author's header comparison "allowing only monospacing" let a descriptive heading word become a code identifier (NEW-01, E1/E6). |
| Manuscript package | MANUSCRIPT_REVIEW_MANIFEST has 88 files; the r1 ZIP has 90 members (88 + manifest + its sidecar), all hashes equal. The non-r1 `PAPER_IV_v1.21_REVIEW_PACKAGE.zip` also exists in the directory but is not the bound target. | Correct. OBSERVATION E8-03: an earlier unbound package sits next to the bound r1 package. |

**E8 verdict: PASS with observations.**
