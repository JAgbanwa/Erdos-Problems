/-
  Contrib/Probes.lean — record of audit step (a): compiler-assisted absence check.

  We stated each candidate contribution and ran `exact?` to ask whether Mathlib
  (v4.28.0) closes it with a single existing lemma. All three failed
  ("`exact?` could not close the goal"), which — together with the structural
  source search (no LP-duality file; algebraic Farkas absent; only `ProperCone`
  geometric Farkas; only convex Carathéodory; no finitely-generated-cone-closed
  lemma) — confirms the three targets are genuine gaps.

  `exact?` failing shows there is no SINGLE-lemma match; it does not prove the
  results are underivable (their ingredients, e.g. `ProperCone.hyperplane_separation`,
  do exist). The contribution value is the packaging plus the nontrivial missing
  piece `fg_cone_isClosed` (Weyl), which is proved in `Contrib/FgConeClosed.lean`.

  The probe statements (kept as documentation; not compiled to avoid the by-design
  `exact?` failures):

  -- PROBE 1 — Weyl (fg cone closed):
  --   {ι E} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  --   (v : ι → E) : IsClosed {x | ∃ c, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v i}   -- exact? FAILED
  --
  -- PROBE 2 — conic Carathéodory:
  --   ... ∃ (t : Finset ι) (d), LinearIndependent ℝ (v ∘ (↑) : t → E) ∧ (∀ i, 0 ≤ d i) ∧
  --       ∑ i, c i • v i = ∑ i ∈ t, d i • v i                                 -- exact? FAILED
  --
  -- PROBE 3 — finite LP strong duality (covering/packing):
  --   IsGreatest {packing values} (sInf {cover values})                        -- exact? FAILED

  Raw run: 2026-07-10, `lake env lean Contrib/Probes.lean` (probe version), all three
  `exact?` calls reported "could not close the goal" (exit 1 by design).
-/

namespace Contrib.Probes
-- (documentation-only file; see FgConeClosed.lean for the drafted contribution)
end Contrib.Probes
