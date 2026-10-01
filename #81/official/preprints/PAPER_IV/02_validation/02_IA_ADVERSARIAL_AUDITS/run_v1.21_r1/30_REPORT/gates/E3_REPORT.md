# Gate E3 report — run_v1.21_r1 (Paper IV v1.21)

Verdict: **PASS**. Evidence: `20_EVIDENCE/E3/`.

---

## E3 — Conformance revalidation (no Lean run)

- Lean source cut unchanged: 615/615 manifest entries match (E0; author `LEAN_IDENTITY_CHECK.json` concurs,
  not relied upon). Therefore all static and dynamic E3 results of run_v1.2_r1 carry over for the unchanged
  statements; the diff shows no change to any theorem statement, Lean excerpt or declaration name cited.
- **X-27 (MODERATE in v1.2) — RESOLVED.** v1.21 now states, in §7 (new paragraph after the ASCheck
  paragraph), E.2 (l. after "An earlier existential assembly…"), Table 9 (row "Unrestricted equality
  classification") and reference [23], that `E32.cp_classification_of_theoremCPrimeC` and
  `E32.ref15Theorem11_of_theoremCPrimeC` use the historical assembly through `E32.theoremC_at` and therefore
  include the induced-removal chain of [23], and that the exclusion check must not be extended to them.
  This matches `run_v1.2_r1/20_EVIDENCE/E4/AuditorASProbe.log` (sha256 3a78a44a…, unchanged): the cones of
  both wrappers contain `AlonShapira.lemma_4_2`, `near_chordal_of_induced_cycles_littleO'`,
  `EditRoute.editApproxAt_all`, `EditRoute.fixedL4Localization_unconditional`, `AFKS.strong_regularity`,
  while `rooted_defect_maximum`, `fixed_defect_stability_explicit` and `sequence_arbitrary_orders_stability`
  contain none of them. The text does not extend the exclusion beyond the selected declarations.
- New identifiers typeset in the prose were spot-checked against the source (e.g. `IndepAllBounds`,
  `IndepAllParams`, `E18.NibbleSchedule`, `NibbleOracle`, `NibbleChain`, `RC01DeviationCleanup`,
  `RC01CleanFiber`): see `identifier_check.json`.
- Minor presentation issue (E1/E6 NEW-01): the descriptive word "Regularization" is set as a code identifier in
  the §5.1 heading and the A.2 row; it coincides with the module name `PaperIV.Regularization` but the
  heading is a section title, not a declaration reference.

**E3 verdict: PASS** (X-27 resolved; no conformance defect).
