# E8 — Internal evidence and packaging (preliminary, after independent first pass)

Independent first-pass records saved before any author verdict/derivation was read:
E1_RECORD.md, E3_STATIC_RECORD.md, E7_FIRST_PASS.md + E7_LEAD_VERIFICATION.md, E2_RECORD.md,
E5_RESULTS.json/E5_RECORD.md, E6_RECORD.md (timestamps in the files). Only then were read:
author build evidence (r2, resume, recovery/provenance/validation JSON), internal-audit final report,
FINDINGS.md, MATHEMATICAL_REVIEW.md §A.2, B01 Certo run. Access logged.

## A. Author two-segment reconstruction (script `e8_author_build_check.py`, output E8_AUTHOR_BUILD_CHECK.json)
- Segment 1 (`full_rebuild_v12_20260929_r2`): 422 PASS rows, status file preserved as
  `RUNNING 423/607 E34.SampleBound` (interruption evidence preserved). All 422 exits 0, logs present,
  no sorry/error; sources equal the manifest.
- Segment 2 (`…_resume`): 607 rows = 421 UP-TO-DATE + 186 PASS; union = 607 distinct, no overlap;
  BUILD.exit 0; no failed/blocked/not-run; sources unchanged.
- Every reused module has a segment-1 PASS with identical source hash and library; run metadata
  (Lean binary/version, options, threads, dependency pins, LEAN_PATH, targets) identical across segments;
  RECOVERY_CHECK olean hashes equal segment-1 RESULTS olean hashes for all 422; `A4S1.IndepAllAudit`
  (a target) passed in segment 1 and was re-executed in segment 2 (the "one re-executed completion").
- All 19 targets PASS with exit 0 in segment 2; no sorryAx/sorry; no non-standard axiom.
- Limitation: reuse validity also depends on the author runner's dependency-olean trace files, which are
  in the author work directory and not in the evidence set; the auditor could verify record consistency,
  not re-hash the reused objects.
- **Axiom-record count reconciled:** the author's regex `(?:depends on axioms:|axioms)\s*\[…\]` yields
  exactly **461** over the 19 target logs; of these **314** are genuine `#print axioms` outputs and **147**
  are axiom lists printed by the custom audit elaborators (ResearchAudit 75, E34 extra, etc.). The internal
  report cites "313 nominal prints over 307 distinct declarations" (1-record difference from the auditor's
  314, OBSERVATION E8-O1). The manuscript correctly says the 461 records are not distinct theorems.
- This is author-build evidence. It does not replace E4.

## B. Internal audit (PASS_INTERNAL_AUTHOR_SIDE) — challenges
| # | Internal position | Auditor challenge | Effect |
|---|---|---|---|
| B1 | All seven A.2 items ACCEPTABLE_SUMMARY "for the paper accompanied by its sources" | The mandate asks for adequacy for a human referee, not with the Lean sources. Internal item 5 itself says normalization is "exposition by contracts with named implementations, not a proof in prose". Internal item 3 (fibres) did not detect that per-edge feasibility needs the two-sided deviation cleanup, absent from the prose. Auditor: A2-3, A2-4, A2-5, A2-6 REQUIRES_EXPANSION. | Disagreement preserved; auditor verdicts stand (E2). |
| B2 | G5/G6 bilingual & visual PASS | Missed E6-01 ("holgura" for margin in ES, contradicting its own l.159 terminology), E6-03 (Spanish subscripts in EN math), E6-04 (A.1 "literal" Lean excerpt rendered `{{v : V}}`). | MINOR/MODERATE findings added. |
| B3 | I-05: '§3.2' in A.2 is an erratum kept outside the sealed manuscript | Confirmed: EN A.2 row "§3.2 and C.2" has no target section. Stays in the audited manuscript. | MINOR finding (F-A2REF). |
| B4 | Certo 0.20.1 certificate for K3∨I3 | Audited by its actual specification: universe = the 12 edges of K3∨I3; 6 parts; each part is the full edge set of a clique; exact cover (auditor's own checker, no Certo import). The certificate proves feasibility (a 6-part partition) only; Certo itself warns it is not optimality. Optimality 6 = kh−C(k,2) comes from the weight argument (6.1). The tamper run lists `cliques`/`exact` as "excused" mutations, so the clique property was not tamper-tested by Certo; the auditor's checker covers it. | E5 T25 updated: Certo item AUDITED (feasibility-only, correct). |
| B5 | "No other build was launched" | Internal G4 relied on recorded author builds; E4 of this run is the first external isolated build. | — |

## C. Packaging
- Internal package ZIP 488 members / 487 manifest entries (PACKAGE_VERIFICATION); hash equals the binding (E0).
- Author evidence ZIP 1239 = 1238 + manifest; all hashes verified (E0).

Status: **preliminary E8 PASS on evidence consistency; disagreements B1–B3 recorded as findings.**
Final E8 after E4 (compare own build outputs with author records).

## Final E8 (after E4)
- The auditor's isolated build reproduces all 607 author olean hashes and all 19 target logs byte for byte
  (apart from the command line), which corroborates the two-segment reuse record (X-21 resolved).
- The author runner's per-module sorry detection uses the pattern `declaration uses 'sorry'`, which Lean 4.28
  does not print (it uses backticks). The internal/author validation therefore relied on it ineffectively,
  though no sorry exists in any log (X-28, MINOR).
- The internal audit did not notice X-27 (cp classification cone on the historical Alon–Shapira route).

**E8 verdict: PASS with findings** (disagreements B1–B3, X-27, X-28 recorded).
