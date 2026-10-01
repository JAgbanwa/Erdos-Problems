# Gate E3 report — run_v1.22_r1 (Paper IV v1.22-r1)

Verdict: **PASS**. Evidence: `20_EVIDENCE/E3/`. Auditor: Claude Opus 5.5, same session as run_v1.2_r1/run_v1.21_r1; no Lean executed.

---

# E3 — Formal correspondence and dependency disclosure (regression)

- **Lean unchanged.** E0 shows that the cut `lean_piv-v12-fb459343d234` matches all 615 manifest entries, with no extra files, at the start and at the end of the review. The Lean code blocks in the manuscript are identical to v1.21 (E6_PARITY). No Lean was run.
- **New code identifiers** (`identifier_check_v122.py` → `IDENTIFIER_CHECK_V122.json`; tokens new relative to v1.21):
  - EN has 9 new tokens and ES 8.
  - `E18.Numeric`, `E19.Main`, `E34.lemma3` (E34/NearlySimplicial.lean:462), `E34.transfer` (E34/Sampling.lean:190) and `Model` resolve in the cut.
  - `SzemerediRegularity.initialBound`, `stepBound` and `bound` are not in the cut; they resolve in the pinned Mathlib (Bound.lean: namespace `SzemerediRegularity`, l.38; `stepBound` l.42; `initialBound` l.167; `bound` l.190; Mathlib rev 8f9d9cff = lake-manifest).
  - `run_v1.21_r1` is the name of the audit folder, which exists.
  - **No unresolved identifier.**
- **C.3 ↔ Lean.** The prose matches `E18.Numeric.NfarE_eta0_le` and the `E19.Main` statements `absorb_abstract`, `B6_le_two_pow_two_pow`, `four_mul_Tnum_le` and `NfarE_eta0_le_tower`, as read in the frozen sources (E2).
- **X-27 preserved.** §7 (EN/ES p31) still states that `E32.cp_classification_of_theoremCPrimeC` and `E32.ref15Theorem11_of_theoremCPrimeC` use the historical chain through `E32.theoremC_at` (the induced-removal lemmas of [23]), and that the exclusion check is not extended to these wrappers. Table 9 (EN p64 / ES p65) and [23] (EN p72) keep the corresponding statements. The run_v1.2_r1 probe result (AuditorASProbe.log) is inherited because the source is identical.
- X-25 (annex README supplement) is unchanged; the annex ZIP is unchanged (E0).

**E3 verdict: PASS.**
