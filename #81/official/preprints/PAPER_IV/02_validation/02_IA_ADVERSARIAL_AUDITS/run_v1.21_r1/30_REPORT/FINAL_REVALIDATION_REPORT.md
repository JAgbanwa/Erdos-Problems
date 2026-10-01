# Paper IV v1.21-r1 — external adversarial revalidation

**Run:** `run_v1.21_r1` (2026-09-30 23:03 UTC – 2026-10-01). **Target:** `AUDIT_TARGET_v1.21.json`
(sha256 574352e8…), editorial candidate `v1.21_editorial_candidate` (manifest abae830f…, ZIP r1 5fc4099a…),
unchanged Lean cut `piv-v12-fb459343d234`. **Auditor:** Claude Opus 5.5, running **in the same session that
produced run_v1.2_r1**. This revalidation is therefore neither blind nor independent of that run. It is not
a cross-family check, and it ran on the same machine and shared dependency cache. **No Lean was run in
this cycle.**

**Overall verdict: INCONCLUSIVE.** v1.21 resolves all MODERATE findings of v1.2 (X-01, X-02, X-03, X-04,
X-27), and six of the seven A.2 derivations are now ACCEPTABLE_SUMMARY. One mandatory E2 item is still
open: **A2-4 / X-05**. C.3 now defines the schedule and derives the selector chain explicitly. However, the
final step is still asserted without proof: the regularity recurrence "iterated h times … dominates these
three quantities after just its first two iterations; absorbing the five terms of (C.1) gives
N_far(η₀) ≤ T(h+7)". The regularity bound B and its recurrence are not defined anywhere in the
manuscript, and A.2 points to a "recurrence in §6.3" that §6.3 does not contain. This affects only the
explicit tower values: T(h+7) and T(h+8) in §6.3, and the c_far/h_iter part of (6.28). It affects neither
the existence of thresholds nor any theorem. No mathematical error, identity defect, attribution blocker
or formal problem was found.

This is an AI review. It is not human peer review and not permission to publish.

## 1. Gate verdicts

| Gate | Verdict | Method | Basis (`20_EVIDENCE/`) |
|---|---|---|---|
| E0 Identity | **PASS** | repeated (start and end identical) | E0/E0_RECORD.md |
| E1 Claims | **PASS** (1 MINOR) | repeated on the diff; v1.2 claim map reused | E1/E1_RECORD.md |
| E2 Mathematics | **INCONCLUSIVE** | repeated: rederivation of every added passage | E2/E2_RECORD.md |
| E3 Conformance | **PASS** | static repetition; v1.2 dynamic results reused (source unchanged) | E3/E3_RECORD.md |
| E4 Formal reproduction | **PASS** — `reused_verified_external_build` | not recompiled; records re-verified | E4/E4_RECORD.md |
| E5 Falsification | **PASS** | 21 new exact checks repeated; v1.2 T01–T24 reused | E5/E5_RECORD.md |
| E6 Bilingual | **PASS with findings** | repeated; 143/143 pages viewed | E6/E6_RECORD.md |
| E7 Attribution | **PASS** | repeated; later-version check 2026-09-30 | E7/E7_RECORD.md |
| E8 Author evidence | **PASS with observations** | repeated (detector re-tested independently) | E8/E8_RECORD.md |

## 2. A.2 rows

| Row | v1.2 | v1.21 |
|---|---|---|
| A2-1 regularization | ACCEPTABLE_SUMMARY | **ACCEPTABLE_SUMMARY** (113/64 sentence added) |
| A2-2 discard counts | ACCEPTABLE_SUMMARY | **ACCEPTABLE_SUMMARY** |
| A2-3 fibres / normalization | REQUIRES_EXPANSION | **ACCEPTABLE_SUMMARY.** Bilateral cleanup, per-edge load ≤ 1 and retention are derived and were rederived. Observation: the second-moment bad-root bounds are cited, not derived. |
| A2-4 Table C.1 / tower | REQUIRES_EXPANSION | **REQUIRES_EXPANSION (narrowed, MINOR):** the regularity recurrence and the final T(h+7) comparison are still missing. |
| A2-5 normalization | REQUIRES_EXPANSION | **ACCEPTABLE_SUMMARY** (counts derived) |
| A2-6 (E.2b)/(E.2d) | REQUIRES_EXPANSION | **ACCEPTABLE_SUMMARY** (joint elimination and the n/9 error derived) |
| A2-7 Bose/Skolem | ACCEPTABLE_SUMMARY | **ACCEPTABLE_SUMMARY** |

## 3. Findings matrix (full list in `FINDINGS.csv`)

- **Resolved:** X-01, X-02, X-03, X-04, X-06, X-07, X-08, X-09, X-10, X-11, X-13, X-14, X-16, X-20,
  X-21, X-23, X-25, X-27.
- **Partial:** X-05 (MINOR, open step above). X-12 (MINOR: `E34.lemma3` and `E34.transfer` are still plain
  text). X-15 (MINOR: "matching(s)" ×12 and "packing" ×1 in ES prose; "baseline" in ES Figure 3).
- **Mitigated:** X-28. The external detector was verified against the real Lean 4.28 warning and against
  variants, and finds 0 hits in all 1266 logs. The frozen runners stay unpatched by design.
- **Kept, as declared:** X-17, X-18, X-19, X-22, X-24, X-26, X-29, AUD-P1, AUD-C1, AUD-C2.
- **New:**
  - NEW-01 (MINOR): descriptive words set as code (`Regularization` in EN §5.1 and A.2; `Nibble` in ES
    Lemma 3.2), with EN/ES heading inconsistency.
  - **NEW-02 (MINOR): the ES reference [6] title is corrupted to «Integer and fractional
    empaquetamientos in dense graphs».**
  - Observations R-01, R-02, E8-01, E8-02, E8-03.

## 4. What was repeated vs reused

- **Repeated in this cycle:**
  - E0 identities (twice).
  - The auditor's own v1.2→v1.21 diff and rederivation of all added mathematics.
  - 21 exact numeric checks with negative controls.
  - Identifier resolution against the frozen source.
  - The X-27 text check against `AuditorASProbe.log`.
  - Later-version literature checks.
  - Independent detector tests and a rescan of all 1266 logs.
  - Re-verification of the E4 records without trusting the overwritten `SUMMARY.json`.
  - A full page-by-page visual inspection.
- **Reused, not repeated:** the E4 build and its cone/axiom/olean evidence, the 24 E5 tests of v1.2, and
  the v1.2 E3 dynamic checks. All are justified by the unchanged sources and by E0.

## 5. Limitations

- Same session and same model as the audited predecessor run. Same family as the manuscript's assistant.
- Same machine and shared pinned Mathlib oleans. No independent kernel replay.
- The E6 automated parity checks were run by a same-family subagent that was stopped twice by rate limits.
  The lead auditor did all the page viewing, on 90 dpi 2-up renders.
- Literature coverage as in run_v1.2_r1. No complete novelty search.

## 6. Recommendation (recommendation only)

1. To close A2-4/X-05, add to C.3:
   - the regularity bound B(δ/8, k₀) used and its recurrence;
   - the two-iteration domination of G₁…G₃;
   - the absorption of the five (C.1) terms into T(h+7).

   Then fix the A.2 sentence that points to "the recurrence in §6.3". Alternatively, state T(h+7) and
   T(h+8) explicitly as formally verified values whose comparison is not reproduced in the text.
2. Correct the ES reference [6] title (NEW-02), the residual X-12 and X-15 items, and NEW-01.
3. Any corrected text needs a new identity. A short revalidation of E0/E2 (C.3 only)/E6 would then suffice.
   No Lean rebuild is needed while the cut stays unchanged.
