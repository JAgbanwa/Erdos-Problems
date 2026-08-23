/-
# The vortex supplies the level density — and the circularity survives it.

This file answers the two questions that the density-corrected interfaces of
`BKLO/ShellAbsorptionDense.lean` raise.

**(a) Does BKLO's vortex actually supply the level-density hypothesis?**  Yes, with room to spare.
The recursion of `BKLO/CoverDownVortexRecursion.lean` maintains, at every level `W'` of the vortex
down to the bounded core, the invariant

  `(9/10)|W'| - 24 ≤ edeg (F ∩ cliqueEdges W') v`   for every `v ∈ W'`,

and away from the core the stronger `f|W'| · |W'| - 12 ≤ edeg (F ∩ cliqueEdges W') v` of the
schedule.  The clause `(c - 9/10)|W'| ≤ edeg (F ∩ cliqueEdges W') v` demanded by
`BKLO.CoverDownK3DivDense` is *far* weaker: the cover-down is applied at ambient density
`c₀ = 9/10 + ε/8`, so it asks only for `(ε/8)|W'|.

**(b) Is the density-corrected cover-down still of theorem strength?**  Yes.  This is the negative
answer to the hope that the level-density hypothesis breaks the circularity measured in
`BKLO/CoverDownEquivalence.lean`.  The dense recursion below runs the whole cover-down vehicle on
`BKLO.CoverDownK3DivDense` instead of `BKLO.CoverDownK3Div`, and hence

  `BKLO.triDecompDense_of_coverDownK3DivDense`  :  `CoverDownK3DivDense → TriDecompDense`,
  `BKLO.coverDownK3DivDense_iff_triDecompDense` :  `CoverDownK3DivDense ↔ TriDecompDense`,

modulo the same three classical inputs, the schedule and the divisibility fix as before.  Adding the
level-density hypothesis therefore does **not** make the cover-down step weaker than the theorem it
is used to prove: the vortex hands the hypothesis to the step for free, so the step retains its full
strength.  (As in `BKLO/CoverDownEquivalence.lean` the schedule hypothesis `VortexScheduleSlack` is
itself false, so both implications are vacuously conditional; what they measure is the *strength* of
the interface, and that measurement is unaffected.)

The consequence for `BKLO.ShellAbsorptionDense` is exactly the one the equivalence had for
`BKLO.ShellAbsorption`: a proof of it would prove the triangle decomposition theorem for dense
divisible graphs, so no cheap construction can exist.  What the density hypothesis *does* buy is
recorded in `BKLO/ShellAbsorptionDense.lean` and `BKLO/ShellAbsorptionDenseWall.lean`: it removes the
hollow instances, hence the degenerate demand of
`BKLO.shellAbsorption_forces_sparse_selfdecomposition`.

Everything here is `sorry`-free.
-/
import BKLO.ShellAbsorptionDense
import BKLO.CoverDownEquivalence

open Finset

namespace BKLO

/-! ### The ratio-restricted engine is antitone in the density -/

/-- A vortex engine at density `c` is a vortex engine at every larger density: the density constant
occurs only in hypotheses. -/
theorem vortexEngineRatio_antitone {c c' : ℝ} (hcc : c ≤ c') (h : VortexEngineRatio c) :
    VortexEngineRatio c' := by
  obtain ⟨good, n₁, C, n₂, K, hbot, hcov⟩ := h
  have hmono : ∀ {V : Type} [DecidableEq V] (S : Finset V) (E : Finset (Sym2 V)),
      (∀ v ∈ S, c' * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∀ v ∈ S, c * (S.card : ℝ) ≤ (edeg E v : ℝ) := by
    intro V _ S E hdeg v hv
    have h1 : c * (S.card : ℝ) ≤ c' * (S.card : ℝ) :=
      mul_le_mul_of_nonneg_right hcc (by positivity)
    exact le_trans h1 (hdeg v hv)
  refine ⟨good, n₁, C, n₂, K, ?_, ?_⟩
  · intro V _ _ S E hcard hES hdeg
    exact hbot S E hcard hES (hmono S E hdeg)
  · intro V _ _ S U E hES hdeg hdiv hUS hratio hUn hgood
    exact hcov S U E hES (hmono S E hdeg) hdiv hUS hratio hUn hgood

variable {V : Type} [DecidableEq V]

/-! ### One fixed level, with the dense cover-down -/

/-- `BKLO.coverDown_step_fixed`, with the *density-corrected* cover-down step.  The extra hypothesis
of the dense step — that the level `W'` induces a graph of minimum degree at least
`(c₀ - 9/10)|W'|` — is supplied from the invariant `(9/10)|W'| ≤ edeg (F ∩ cliqueEdges W') v` that
the recursion already carries, minus the `12` edges the divisibility fix costs. -/
theorem coverDown_step_fixed_dense {c₀ γ : ℝ} {W W' X Y : Finset V} {F : Finset (Sym2 V)}
    {K n₀ : ℕ} (hFix : LevelDivFixProp)
    (hCD : ∀ (W W' W'' : Finset V) (F : Finset (Sym2 V)),
      n₀ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
      K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
      F ⊆ cliqueEdges W → TriDivisible F →
      TriDivisible (F ∩ cliqueEdges W') → TriDivisible (F ∩ cliqueEdges W'') →
      (∀ v ∈ W, c₀ * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
      (∀ v ∈ W', (c₀ - 9 / 10) * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn F P ∧
        F \ famEdges P ⊆ cliqueEdges W' ∧
        F ∩ cliqueEdges W'' ⊆ F \ famEdges P ∧
        ∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
          ≤ (edeg (F \ famEdges P) v : ℝ) + γ * (W'.card : ℝ))
    (hc₀1 : c₀ ≤ 1)
    (hn₀ : n₀ ≤ W.card) (hW'W : W' ⊆ W) (hXW' : X ⊆ W') (hYX : Y ⊆ X)
    (hr1 : K * W'.card ≤ W.card) (hr2 : W.card ≤ K * K * W'.card) (hXr : K * X.card ≤ W'.card)
    (hK : 2 ≤ K) (h4Y : 4 * Y.card ≤ X.card) (hX100 : 100 ≤ X.card)
    (hFW : F ⊆ cliqueEdges W) (hdiv : TriDivisible F) (hdivW' : TriDivisible (F ∩ cliqueEdges W'))
    (hdegW' : ∀ v ∈ W', (9 / 10 : ℝ) * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ))
    (hdegX : ∀ v ∈ X, (9 / 10 : ℝ) * (X.card : ℝ) ≤ (edeg (F ∩ cliqueEdges X) v : ℝ))
    (hdegW : ∀ v ∈ W, c₀ * (W.card : ℝ) + 12 ≤ (edeg F v : ℝ)) :
    ∃ (R : Finset (Finset V)) (F₁ : Finset (Sym2 V)),
      TriFamilyIn F R ∧ F \ famEdges R = F₁ ∧
      F₁ ⊆ cliqueEdges W' ∧ TriDivisible F₁ ∧ TriDivisible (F₁ ∩ cliqueEdges X) ∧
      F₁ ∩ cliqueEdges Y = F ∩ cliqueEdges Y ∧
      (∀ Z : Finset V, Z ⊆ X → ∀ v : V,
        (edeg (F ∩ cliqueEdges Z) v : ℝ) ≤ (edeg (F₁ ∩ cliqueEdges Z) v : ℝ) + 12) ∧
      ∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
        ≤ (edeg F₁ v : ℝ) + γ * (W'.card : ℝ) + 12 := by
  classical
  have h2X : 2 * X.card ≤ W'.card := le_trans (Nat.mul_le_mul_right _ hK) hXr
  -- the divisibility fix, inside the current level
  obtain ⟨Q, hQfam, hQsub, hQdeg, hQY, hQdiv⟩ :=
    hFix W' X Y (F ∩ cliqueEdges W')
      hXW' hYX h2X h4Y hX100 Finset.inter_subset_right hdegW' (by
        intro v hv
        rw [inter_cliqueEdges_inter hXW']
        exact hdegX v hv)
  set F' : Finset (Sym2 V) := F \ famEdges Q with hF'
  have hQF : TriFamilyIn F Q := triFamilyIn_of_inter hQfam
  have hF'W : F' ⊆ cliqueEdges W := (Finset.sdiff_subset).trans hFW
  have hF'div : TriDivisible F' := triDivisible_sdiff_famEdges hQF hdiv
  have hF'W' : F' ∩ cliqueEdges W' = (F ∩ cliqueEdges W') \ famEdges Q :=
    sdiff_inter_cliqueEdges F (famEdges Q) W'
  have hF'divW' : TriDivisible (F' ∩ cliqueEdges W') := by
    rw [hF'W']
    exact triDivisible_sdiff_famEdges hQfam hdivW'
  have hF'divX : TriDivisible (F' ∩ cliqueEdges X) := by
    have : F' ∩ cliqueEdges X = ((F ∩ cliqueEdges W') \ famEdges Q) ∩ cliqueEdges X := by
      rw [← hF'W', Finset.inter_assoc, Finset.inter_eq_right.2 (cliqueEdges_mono hXW')]
    rw [this]
    exact hQdiv
  -- the degrees, after the fix
  have hdmg : ∀ v : V, edeg F v ≤ edeg F' v + 12 := fun v => edeg_sdiff_ge v 12 (hQdeg v)
  have hdmgR : ∀ v : V, (edeg F v : ℝ) ≤ (edeg F' v : ℝ) + 12 := by
    intro v; exact_mod_cast hdmg v
  have hdegW'' : ∀ v ∈ W, c₀ * (W.card : ℝ) ≤ (edeg F' v : ℝ) := by
    intro v hv
    have := hdegW v hv
    have := hdmgR v
    linarith
  -- the degree inside the level, after the fix: this is the dense step's extra hypothesis
  have hlevel : ∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
      ≤ (edeg (F' ∩ cliqueEdges W') v : ℝ) + 12 := by
    intro v _
    have h2 : edeg (F ∩ cliqueEdges W') v ≤ edeg (F' ∩ cliqueEdges W') v + 12 := by
      have := edeg_sdiff_ge (F := F ∩ cliqueEdges W') v 12 (hQdeg v)
      rwa [← hF'W'] at this
    exact_mod_cast h2
  have hW'15 : (15 : ℝ) ≤ (W'.card : ℝ) := by
    have h : 15 ≤ W'.card := by omega
    exact_mod_cast h
  have hdens : ∀ v ∈ W',
      (c₀ - 9 / 10) * (W'.card : ℝ) ≤ (edeg (F' ∩ cliqueEdges W') v : ℝ) := by
    intro v hv
    have h1 := hlevel v hv
    have h2 := hdegW' v hv
    nlinarith [mul_le_mul_of_nonneg_right hc₀1 (by positivity : (0 : ℝ) ≤ (W'.card : ℝ))]
  -- the cover-down
  obtain ⟨P, hP, hcov, hkeep, hdam⟩ :=
    hCD W W' X F' hn₀ hW'W hXW' hr1 hr2 hXr hF'W hF'div hF'divW' hF'divX hdegW'' hdens
  refine ⟨Q ∪ P, F' \ famEdges P, triFamilyIn_union hQF hP, by rw [sdiff_famEdges_union], hcov,
    triDivisible_sdiff_famEdges hP hF'div, ?_, ?_, ?_, ?_⟩
  · rw [inter_cliqueEdges_eq_of_keep (Finset.Subset.refl X) Finset.sdiff_subset hkeep]
    exact hF'divX
  · have h1 : (F' \ famEdges P) ∩ cliqueEdges Y = F' ∩ cliqueEdges Y :=
      inter_cliqueEdges_eq_of_keep hYX Finset.sdiff_subset hkeep
    rw [h1]
    apply Finset.Subset.antisymm
    · exact Finset.inter_subset_inter_right Finset.sdiff_subset
    · intro e he
      obtain ⟨heF, heY⟩ := Finset.mem_inter.1 he
      refine Finset.mem_inter.2 ⟨Finset.mem_sdiff.2 ⟨heF, fun hmem => ?_⟩, heY⟩
      exact Finset.disjoint_left.1 hQY hmem heY
  · intro Z hZX v
    have h1 : (F' \ famEdges P) ∩ cliqueEdges Z = F' ∩ cliqueEdges Z :=
      inter_cliqueEdges_eq_of_keep hZX Finset.sdiff_subset hkeep
    rw [h1]
    have h2 : edeg (F ∩ cliqueEdges Z) v ≤ edeg (F' ∩ cliqueEdges Z) v + 12 := by
      have h3 : (F ∩ cliqueEdges Z) \ famEdges Q = F' ∩ cliqueEdges Z :=
        (sdiff_inter_cliqueEdges F (famEdges Q) Z).symm
      have := edeg_sdiff_ge (F := F ∩ cliqueEdges Z) v 12 (hQdeg v)
      rwa [h3] at this
    exact_mod_cast h2
  · intro v hv
    have h1 := hdam v hv
    have h2R := hlevel v hv
    linarith

/-! ### The recursion along the vortex, with the dense cover-down -/

/-- **`BKLO.coverDown_vortex_fix`, run on the density-corrected cover-down step.**

The recursion is unchanged except for one extra invariant, `hlevel`:

  `(9/10)|W'| - 24 ≤ edeg (F ∩ cliqueEdges W') v`  for every `v ∈ W'`,

which holds at *every* level, including the bottom set (the schedule invariant `hclean'` is
guarded by `W' ≠ U`, and the last cover-down of the recursion is performed onto `W' = U`).  It is
maintained because each level is chosen with `(9/10)|X| ≤ edeg (F ∩ cliqueEdges X) v` and each
divisibility fix costs at most `12` edges per vertex.

This invariant is what supplies the level-density hypothesis of `BKLO.CoverDownK3DivDense`:
the cover-down is applied at ambient density `c₀ ≤ 1`, so it asks only for
`(c₀ - 9/10)|W'| ≤ (1/10)|W'|`, and `(9/10)|W'| - 24 ≥ (1/10)|W'|` at every level of size at least
`30`. -/
theorem coverDown_vortex_fix_dense {c₀ c₁ γ : ℝ} {f : ℕ → ℝ} {n₂ n₀ K : ℕ} {U : Finset V}
    (hK : 2 ≤ K) (hFix : LevelDivFixProp)
    (hCD : ∀ (W W' W'' : Finset V) (F : Finset (Sym2 V)),
      n₀ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
      K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
      F ⊆ cliqueEdges W → TriDivisible F →
      TriDivisible (F ∩ cliqueEdges W') → TriDivisible (F ∩ cliqueEdges W'') →
      (∀ v ∈ W, c₀ * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
      (∀ v ∈ W', (c₀ - 9 / 10) * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn F P ∧
        F \ famEdges P ⊆ cliqueEdges W' ∧
        F ∩ cliqueEdges W'' ⊆ F \ famEdges P ∧
        ∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
          ≤ (edeg (F \ famEdges P) v : ℝ) + γ * (W'.card : ℝ))
    (hdesc : ∀ (W : Finset V) (E : Finset (Sym2 V)) (m : ℕ),
      U ⊆ W → U.card ≤ m → 2 * m ≤ W.card → E ⊆ cliqueEdges W →
      (∀ v ∈ W, f W.card * (W.card : ℝ) - 12 ≤ (edeg E v : ℝ)) →
      ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ W'.card = m ∧
        ∀ v ∈ W', f m * (m : ℝ) ≤ (edeg (E ∩ cliqueEdges W') v : ℝ))
    (hc₀ : c₀ ≤ c₁) (hc₀1 : c₀ ≤ 1)
    (hS1 : ∀ s : ℕ, n₂ ≤ s → (c₁ + γ) * (s : ℝ) + 36 ≤ f s * (s : ℝ))
    (hS2 : ∀ s : ℕ, n₂ ≤ s → (9 / 10 : ℝ) * (s : ℝ) + 12 ≤ f s * (s : ℝ))
    (hn₀ : n₀ ≤ n₂) (hn₂ : 100 ≤ n₂) (hU : n₂ ≤ U.card) :
    ∀ (fuel : ℕ) (W W' : Finset V) (F : Finset (Sym2 V)),
      W.card ≤ fuel → F ⊆ cliqueEdges W → TriDivisible F →
      (∀ v ∈ W, c₁ * (W.card : ℝ) + 12 ≤ (edeg F v : ℝ)) →
      U ⊆ W' → W' ⊆ W → K * W'.card ≤ W.card → W.card ≤ K * K * W'.card →
      (W' = U ∨ K * U.card ≤ W'.card) →
      TriDivisible (F ∩ cliqueEdges W') →
      (∀ v ∈ W', (9 / 10 : ℝ) * (W'.card : ℝ) - 24 ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
      (W' ≠ U → ∀ v ∈ W',
        f W'.card * (W'.card : ℝ) - 12 ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
      (W' ≠ U → ∀ v ∈ U, f U.card * (U.card : ℝ) - 12 ≤ (edeg (F ∩ cliqueEdges U) v : ℝ)) →
      (K * K * U.card < W'.card → ∀ v ∈ U,
        f U.card * (U.card : ℝ) ≤ (edeg (F ∩ cliqueEdges U) v : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn F P ∧ F \ famEdges P ⊆ cliqueEdges U := by
  classical
  intro fuel
  induction fuel with
  | zero =>
    intro W W' F hfuel _ _ _ hUW' hW'W _ _ _ _ _ _ _ _
    have h1 : U.card ≤ W'.card := Finset.card_le_card hUW'
    have h2 : W'.card ≤ W.card := Finset.card_le_card hW'W
    omega
  | succ fuel ih =>
    intro W W' F hfuel hFW hdiv hdeg hUW' hW'W hr1 hr2 hdisj hdivW' hlevel hclean' hgoodUb hgoodUa
    have hUcard : U.card ≤ W'.card := Finset.card_le_card hUW'
    have hW'card : W'.card ≤ W.card := Finset.card_le_card hW'W
    have hn₂W' : n₂ ≤ W'.card := le_trans hU hUcard
    have hn₀W : n₀ ≤ W.card := le_trans (le_trans hn₀ hn₂W') hW'card
    have hUpos : 1 ≤ U.card := by omega
    have hW'100 : (100 : ℝ) ≤ (W'.card : ℝ) := by
      have h : 100 ≤ W'.card := le_trans hn₂ hn₂W'
      exact_mod_cast h
    -- the ambient density, in the weaker form the cover-down asks for
    have hdeg₀ : ∀ v ∈ W, c₀ * (W.card : ℝ) ≤ (edeg F v : ℝ) := by
      intro v hv
      have h := hdeg v hv
      have hc : c₀ * (W.card : ℝ) ≤ c₁ * (W.card : ℝ) :=
        mul_le_mul_of_nonneg_right hc₀ (by positivity)
      linarith
    -- the level density the dense cover-down asks for
    have hdens : ∀ v ∈ W', (c₀ - 9 / 10) * (W'.card : ℝ)
        ≤ (edeg (F ∩ cliqueEdges W') v : ℝ) := by
      intro v hv
      have h := hlevel v hv
      nlinarith [mul_le_mul_of_nonneg_right hc₀1 (by positivity : (0 : ℝ) ≤ (W'.card : ℝ))]
    by_cases hWU : W' = U
    · -- the bottom set has been reached: one last cover-down, no fix needed
      obtain ⟨P, hP, hcov, -, -⟩ :=
        hCD W W' ∅ F hn₀W hW'W (Finset.empty_subset _) hr1 hr2 (by simp) hFW hdiv hdivW'
          (by rw [inter_cliqueEdges_empty]; exact triDivisible_empty) hdeg₀ hdens
      exact ⟨P, hP, by rw [← hWU]; exact hcov⟩
    · -- otherwise the bottom set is at least `K` times smaller than the current level
      have hKU : K * U.card ≤ W'.card := hdisj.resolve_left hWU
      have hclean := hclean' hWU
      have hgoodU12 := hgoodUb hWU
      have hdegW' : ∀ v ∈ W', (9 / 10 : ℝ) * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ) := by
        intro v hv
        have h := hclean v hv
        have h2 := hS2 W'.card hn₂W'
        linarith
      -- ### choose the level after the next, and the set the fix must avoid
      obtain ⟨X, Y, hUX, hXW', hYX, hXr, hwin, hXdisj, h4Y, hdegX, hcleanX, hcase⟩ :
          ∃ X Y : Finset V, U ⊆ X ∧ X ⊆ W' ∧ Y ⊆ X ∧ K * X.card ≤ W'.card ∧
            W'.card ≤ K * K * X.card ∧ (X = U ∨ K * U.card ≤ X.card) ∧
            4 * Y.card ≤ X.card ∧
            (∀ v ∈ X, (9 / 10 : ℝ) * (X.card : ℝ) ≤ (edeg (F ∩ cliqueEdges X) v : ℝ)) ∧
            (X ≠ U → ∀ v ∈ X, f X.card * (X.card : ℝ) ≤ (edeg (F ∩ cliqueEdges X) v : ℝ)) ∧
            (X = U ∨ (K * K * U.card < W'.card ∧ (K * K * U.card < X.card → Y = U))) := by
        by_cases hsmall : W'.card ≤ K * K * U.card
        · refine ⟨U, ∅, Finset.Subset.refl _, hUW', Finset.empty_subset _, hKU, hsmall,
            Or.inl rfl, by simp, ?_, ?_, Or.inl rfl⟩
          · intro v hv
            have h := hgoodU12 v hv
            have h2 := hS2 U.card hU
            linarith
          · intro hne; exact absurd rfl hne
        · push_neg at hsmall
          obtain ⟨hKa, ham, h2m, hKm, hmm⟩ := vortex_next_level_sizes hK hUpos hsmall
          obtain ⟨X, hUX, hXW', hcardX, hcleanX⟩ :=
            hdesc W' (F ∩ cliqueEdges W') (W'.card / K) hUW' ham h2m Finset.inter_subset_right
              hclean
          have hcleanX' : ∀ v ∈ X, f X.card * (X.card : ℝ)
              ≤ (edeg (F ∩ cliqueEdges X) v : ℝ) := by
            intro v hv
            have h := hcleanX v hv
            rw [inter_cliqueEdges_inter hXW'] at h
            rwa [hcardX]
          have hn₂X : n₂ ≤ X.card := by
            rw [hcardX]; exact le_trans (le_trans hU (Nat.le_mul_of_pos_left _ (by omega))) hKa
          refine ⟨X, if 4 * U.card ≤ X.card then U else ∅, hUX, hXW', ?_,
            by rw [hcardX]; exact hKm, by rw [hcardX]; exact hmm,
            Or.inr (by rw [hcardX]; exact hKa), ?_, ?_, fun _ => hcleanX', Or.inr ⟨hsmall, ?_⟩⟩
          · split_ifs with h
            exacts [hUX, Finset.empty_subset _]
          · split_ifs with h
            exacts [h, by simp]
          · intro v hv
            have h := hcleanX' v hv
            have h2 := hS2 X.card hn₂X
            linarith
          · intro hlt
            have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
            have hmul : 4 * U.card ≤ K * K * U.card := Nat.mul_le_mul_right _ hKK
            rw [if_pos (by omega : 4 * U.card ≤ X.card)]
      have hn₂X : n₂ ≤ X.card := le_trans hU (Finset.card_le_card hUX)
      have hX100 : 100 ≤ X.card := le_trans hn₂ hn₂X
      -- ### the fixed cover-down step, in its dense form
      obtain ⟨R, F₁, hR, hF₁, hF₁W', hF₁div, hF₁divX, hF₁Y, hdmgZ, hdmgW'⟩ :=
        coverDown_step_fixed_dense (c₀ := c₀) (γ := γ) (W := W) (W' := W') (X := X) (Y := Y)
          (F := F) (K := K) (n₀ := n₀) hFix hCD hc₀1 hn₀W hW'W hXW' hYX hr1 hr2 hXr hK h4Y hX100
          hFW hdiv hdivW' hdegW' hdegX (by
            intro v hv
            have h := hdeg v hv
            have hc : c₀ * (W.card : ℝ) ≤ c₁ * (W.card : ℝ) :=
              mul_le_mul_of_nonneg_right hc₀ (by positivity)
            linarith)
      -- ### the invariants at the next state
      have hdeg₁ : ∀ v ∈ W', c₁ * (W'.card : ℝ) + 12 ≤ (edeg F₁ v : ℝ) := by
        intro v hv
        have h1 := hdmgW' v hv
        have h2 := hclean v hv
        have h3 := hS1 W'.card hn₂W'
        linarith
      have hlevel₁ : ∀ v ∈ X, (9 / 10 : ℝ) * (X.card : ℝ) - 24
          ≤ (edeg (F₁ ∩ cliqueEdges X) v : ℝ) := by
        intro v hv
        have h1 := hdmgZ X (Finset.Subset.refl X) v
        have h2 := hdegX v hv
        linarith
      have hclean₁ : X ≠ U → ∀ v ∈ X,
          f X.card * (X.card : ℝ) - 12 ≤ (edeg (F₁ ∩ cliqueEdges X) v : ℝ) := by
        intro hne v hv
        have h1 := hdmgZ X (Finset.Subset.refl X) v
        have h2 := hcleanX hne v hv
        linarith
      have hgoodUb₁ : X ≠ U → ∀ v ∈ U,
          f U.card * (U.card : ℝ) - 12 ≤ (edeg (F₁ ∩ cliqueEdges U) v : ℝ) := by
        intro hne v hv
        rcases hcase with h | ⟨hbig, -⟩
        · exact absurd h hne
        · have h1 := hdmgZ U hUX v
          have h2 := hgoodUa hbig v hv
          linarith
      have hgoodUa₁ : K * K * U.card < X.card → ∀ v ∈ U,
          f U.card * (U.card : ℝ) ≤ (edeg (F₁ ∩ cliqueEdges U) v : ℝ) := by
        intro hlt v hv
        rcases hcase with h | ⟨hbig, hYU⟩
        · exfalso
          rw [h] at hlt
          exact absurd hlt (not_lt.2 (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))))
        · have hYeq : Y = U := hYU hlt
          have h1 : F₁ ∩ cliqueEdges U = F ∩ cliqueEdges U := by rw [← hYeq]; exact hF₁Y
          rw [h1]
          exact hgoodUa hbig v hv
      -- ### recurse
      have hfuel' : W'.card ≤ fuel := by
        have h2 : 2 * W'.card ≤ K * W'.card := Nat.mul_le_mul_right _ hK
        have h3 : 2 * W'.card ≤ W.card := le_trans h2 hr1
        omega
      obtain ⟨P₂, hP₂, hcov₂⟩ :=
        ih W' X F₁ hfuel' hF₁W' hF₁div hdeg₁ hUX hXW' hXr hwin hXdisj hF₁divX hlevel₁ hclean₁
          hgoodUb₁ hgoodUa₁
      refine ⟨R ∪ P₂, triFamilyIn_union hR (by rw [hF₁]; exact hP₂), ?_⟩
      rw [sdiff_famEdges_union, hF₁]
      exact hcov₂

/-! ### The engine, run on the dense cover-down -/

/-- **The ratio-restricted vortex engine, from the *density-corrected* cover-down step.**

Identical to `BKLO.vortexEngineRatio_of_coverDownDiv`, with `BKLO.CoverDownK3DivDense` in place of
`BKLO.CoverDownK3Div`: the level-density hypothesis of the dense step is supplied by the invariant
the recursion already carries (`BKLO.coverDown_vortex_fix_dense`), at no cost.  The density
parameter is capped at `ε ≤ 1/10` so that the ambient density `c₀ = 9/10 + ε/8` at which the step is
applied satisfies `c₀ ≤ 1`; the cap is removed in
`BKLO.vortexEngineRatio_of_coverDownDivDense` by antitonicity. -/
theorem vortexEngineRatio_of_coverDownDivDense_aux (hFix : LevelDivFixProp)
    (hSched : VortexScheduleSlack) (hCoverDown : CoverDownK3DivDense) (ε : ℝ) (hε : 0 < ε)
    (hepsle : ε ≤ 1 / 10) : VortexEngineRatio (9 / 10 + ε) := by
  classical
  obtain ⟨K, n₀, hK, hCD⟩ := hCoverDown (9 / 10 + ε / 8) (ε / 32) (by linarith) (by linarith)
  -- the size threshold: large enough for all the numerical side conditions
  obtain ⟨M, hM⟩ := exists_nat_gt (1152 / (7 * ε))
  obtain ⟨f, n₂, C, hn₀n₂, hn₂C, hn₂pos, hfbd, hbot, hdesc⟩ :=
    hSched ε hε (max (max n₀ 100) M)
  have hn₀le : n₀ ≤ n₂ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn₀n₂
  have h100 : 100 ≤ n₂ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn₀n₂
  have hMn₂ : M ≤ n₂ := le_trans (le_max_right _ _) hn₀n₂
  -- the basic numerical fact: `(7ε/32)·s ≥ 36` for every scale `s ≥ n₂`
  have hbig : ∀ s : ℕ, n₂ ≤ s → (36 : ℝ) ≤ 7 * ε / 32 * (s : ℝ) := by
    intro s hs
    have h1 : (1152 : ℝ) / (7 * ε) < (M : ℝ) := hM
    have h2 : (M : ℝ) ≤ (s : ℝ) := by exact_mod_cast le_trans hMn₂ hs
    have h3 : (0 : ℝ) < 7 * ε := by linarith
    rw [div_lt_iff₀ h3] at h1
    nlinarith
  have hS1 : ∀ s : ℕ, n₂ ≤ s → (9 / 10 + ε / 4 + ε / 32) * (s : ℝ) + 36 ≤ f s * (s : ℝ) := by
    intro s hs
    have h1 := (hfbd s hs).1
    have h2 : (0 : ℝ) ≤ (s : ℝ) := by positivity
    have h3 := hbig s hs
    nlinarith
  have hS2 : ∀ s : ℕ, n₂ ≤ s → (9 / 10 : ℝ) * (s : ℝ) + 12 ≤ f s * (s : ℝ) := by
    intro s hs
    have h1 := (hfbd s hs).1
    have h2 : (0 : ℝ) ≤ (s : ℝ) := by positivity
    have h3 := hbig s hs
    nlinarith
  refine ⟨vortexGood f n₂ C, n₂, C, n₂, K, ?_, ?_⟩
  · -- good bottom sets exist
    intro V _ _ S E hcard hES hdeg
    obtain ⟨U, hUS, hUn₂, hUC, hUdeg⟩ := hbot S E hcard hES hdeg
    exact ⟨U, hUS, hUn₂, hUC, (vortexGood_iff f n₂ C U _).2 ⟨hUC, hUn₂, hUdeg⟩⟩
  · -- the cover-down onto the bottom set
    intro V _ _ S U E hES hdeg hdiv hUS hratio hUn₁ hgood
    obtain ⟨hUC, hUn₂, hUdeg⟩ := (vortexGood_iff f n₂ C U _).1 hgood
    have hUcard : U.card ≤ S.card := Finset.card_le_card hUS
    have hn₂S : n₂ ≤ S.card := le_trans hUn₂ hUcard
    have hUpos : 1 ≤ U.card := by omega
    have hSpos : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
    -- the ambient density, with room for one fix
    have hdegS : ∀ v ∈ S, (9 / 10 : ℝ) * (S.card : ℝ) ≤ (edeg E v : ℝ) := by
      intro v hv
      have h := hdeg v hv
      nlinarith
    have hdescU : ∀ (W : Finset V) (E' : Finset (Sym2 V)) (m : ℕ),
        U ⊆ W → U.card ≤ m → 2 * m ≤ W.card → E' ⊆ cliqueEdges W →
        (∀ v ∈ W, f W.card * (W.card : ℝ) - 12 ≤ (edeg E' v : ℝ)) →
        ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ W'.card = m ∧
          ∀ v ∈ W', f m * (m : ℝ) ≤ (edeg (E' ∩ cliqueEdges W') v : ℝ) :=
      fun W E' m h1 h2 h3 h4 h5 => hdesc W U E' m hUn₂ h1 h2 h3 h4 h5
    -- ### the first level of the vortex
    obtain ⟨W₁, hUW₁, hW₁S, hr1, hr2, hdisj, hcleanW₁, hexact⟩ :
        ∃ W₁ : Finset V, U ⊆ W₁ ∧ W₁ ⊆ S ∧ K * W₁.card ≤ S.card ∧ S.card ≤ K * K * W₁.card ∧
          (W₁ = U ∨ K * U.card ≤ W₁.card) ∧
          (∀ v ∈ W₁, f W₁.card * (W₁.card : ℝ) ≤ (edeg (E ∩ cliqueEdges W₁) v : ℝ)) ∧
          (K * K * U.card < W₁.card → 4 * U.card ≤ W₁.card) := by
      by_cases hsmall : S.card ≤ K * K * U.card
      · exact ⟨U, Finset.Subset.refl _, hUS, hratio, hsmall, Or.inl rfl, hUdeg, fun h => by
          exact absurd h (not_lt.2 (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))))⟩
      · push_neg at hsmall
        obtain ⟨hKa, ham, h2m, hKm, hmm⟩ := vortex_next_level_sizes hK hUpos hsmall
        have hdegf : ∀ v ∈ S, f S.card * (S.card : ℝ) - 12 ≤ (edeg E v : ℝ) := by
          intro v hv
          have h := hdeg v hv
          have hfS := (hfbd S.card hn₂S).2
          nlinarith
        obtain ⟨W₁, hUW₁, hW₁S, hcard₁, hclean₁⟩ :=
          hdescU S E (S.card / K) hUS ham h2m hES hdegf
        refine ⟨W₁, hUW₁, hW₁S, by rw [hcard₁]; exact hKm, by rw [hcard₁]; exact hmm,
          Or.inr (by rw [hcard₁]; exact hKa), ?_, ?_⟩
        · intro v hv; rw [hcard₁]; exact hclean₁ v hv
        · intro hlt
          have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
          have : 4 * U.card ≤ K * K * U.card := Nat.mul_le_mul_right _ hKK
          omega
    have hn₂W₁ : n₂ ≤ W₁.card := le_trans hUn₂ (Finset.card_le_card hUW₁)
    -- ### the initial divisibility fix, on the first level
    set Y : Finset V := if 4 * U.card ≤ W₁.card then U else ∅ with hY
    have hYW₁ : Y ⊆ W₁ := by rw [hY]; split_ifs with h; exacts [hUW₁, Finset.empty_subset _]
    have h4Y : 4 * Y.card ≤ W₁.card := by rw [hY]; split_ifs with h; exacts [h, by simp]
    obtain ⟨Q, hQfam, -, hQdeg, hQY, hQdiv⟩ :=
      hFix S W₁ Y E hW₁S hYW₁
        (le_trans (Nat.mul_le_mul_right _ hK) hr1) h4Y (le_trans h100 hn₂W₁) hES hdegS (by
          intro v hv
          have h := hcleanW₁ v hv
          have h2 := hS2 W₁.card hn₂W₁
          linarith)
    set E₁ : Finset (Sym2 V) := E \ famEdges Q with hE₁
    have hE₁S : E₁ ⊆ cliqueEdges S := Finset.sdiff_subset.trans hES
    have hE₁div : TriDivisible E₁ := triDivisible_sdiff_famEdges hQfam hdiv
    have hE₁deg : ∀ v ∈ S, (9 / 10 + ε / 4) * (S.card : ℝ) + 12 ≤ (edeg E₁ v : ℝ) := by
      intro v hv
      have h1 := hdeg v hv
      have h2 : (edeg E v : ℝ) ≤ (edeg E₁ v : ℝ) + 12 := by
        exact_mod_cast edeg_sdiff_ge (F := E) v 12 (hQdeg v)
      have h3 := hbig S.card hn₂S
      linarith
    have hE₁divW₁ : TriDivisible (E₁ ∩ cliqueEdges W₁) := hQdiv
    have hE₁clean : W₁ ≠ U → ∀ v ∈ W₁,
        f W₁.card * (W₁.card : ℝ) - 12 ≤ (edeg (E₁ ∩ cliqueEdges W₁) v : ℝ) := by
      intro _ v hv
      have h1 := edeg_inter_sdiff_ge E (famEdges Q) W₁ hQdeg v
      have h2 := hcleanW₁ v hv
      linarith
    have hE₁goodb : W₁ ≠ U → ∀ v ∈ U,
        f U.card * (U.card : ℝ) - 12 ≤ (edeg (E₁ ∩ cliqueEdges U) v : ℝ) := by
      intro _ v hv
      have h1 := edeg_inter_sdiff_ge E (famEdges Q) U hQdeg v
      have h2 := hUdeg v hv
      linarith
    have hE₁gooda : K * K * U.card < W₁.card → ∀ v ∈ U,
        f U.card * (U.card : ℝ) ≤ (edeg (E₁ ∩ cliqueEdges U) v : ℝ) := by
      intro hlt v hv
      have hYU : Y = U := by rw [hY, if_pos (hexact hlt)]
      have h1 : E₁ ∩ cliqueEdges U = E ∩ cliqueEdges U := by
        rw [← hYU]
        apply Finset.Subset.antisymm
        · exact Finset.inter_subset_inter_right Finset.sdiff_subset
        · intro e he
          obtain ⟨heE, heY⟩ := Finset.mem_inter.1 he
          exact Finset.mem_inter.2
            ⟨Finset.mem_sdiff.2 ⟨heE, fun hmem => Finset.disjoint_left.1 hQY hmem heY⟩, heY⟩
      rw [h1]
      exact hUdeg v hv
    have hE₁level : ∀ v ∈ W₁, (9 / 10 : ℝ) * (W₁.card : ℝ) - 24
        ≤ (edeg (E₁ ∩ cliqueEdges W₁) v : ℝ) := by
      intro v hv
      have h1 := edeg_inter_sdiff_ge E (famEdges Q) W₁ hQdeg v
      have h2 := hcleanW₁ v hv
      have h3 := hS2 W₁.card hn₂W₁
      rw [← hE₁] at h1
      linarith
    -- ### run the fixed cover-down along the vortex
    obtain ⟨P, hP, hcov⟩ :=
      coverDown_vortex_fix_dense (c₀ := 9 / 10 + ε / 8) (c₁ := 9 / 10 + ε / 4) (γ := ε / 32)
        (U := U) hK hFix (fun W W' W'' F => hCD W W' W'' F) hdescU (by linarith) (by linarith) hS1 hS2 hn₀le
        h100 hUn₂ S.card S W₁ E₁ le_rfl hE₁S hE₁div hE₁deg hUW₁ hW₁S hr1 hr2 hdisj hE₁divW₁
        hE₁level hE₁clean hE₁goodb hE₁gooda
    exact ⟨Q ∪ P, triFamilyIn_union hQfam (by rw [← hE₁]; exact hP), by
      rw [sdiff_famEdges_union, ← hE₁]; exact hcov⟩


/-- **The cap on the density parameter is immaterial.**  The engine is antitone in the density, so
the capped form gives every density above `9/10`. -/
theorem vortexEngineRatio_of_coverDownDivDense (hFix : LevelDivFixProp)
    (hSched : VortexScheduleSlack) (hCoverDown : CoverDownK3DivDense) (ε : ℝ) (hε : 0 < ε) :
    VortexEngineRatio (9 / 10 + ε) := by
  rcases le_or_gt ε (1 / 10) with h | h
  · exact vortexEngineRatio_of_coverDownDivDense_aux hFix hSched hCoverDown ε hε h
  · exact vortexEngineRatio_antitone (by linarith)
      (vortexEngineRatio_of_coverDownDivDense_aux hFix hSched hCoverDown (1 / 10) (by norm_num)
        le_rfl)

/-- **The §10 residual interface, from the density-corrected cover-down vehicle.** -/
theorem vortexEngineRatioFromInputs_of_coverDownDivDense (hFix : LevelDivFixProp)
    (hSched : VortexScheduleSlack) (hCoverDown : CoverDownK3DivDense) :
    VortexEngineRatioFromInputs :=
  fun _ _ _ ε hε => vortexEngineRatio_of_coverDownDivDense hFix hSched hCoverDown ε hε

/-- **The near-optimal decomposition interface, from the density-corrected cover-down vehicle.** -/
theorem nearOptimalDecomp_of_coverDownDivDense (hFix : LevelDivFixProp)
    (hSched : VortexScheduleSlack) (hCoverDown : CoverDownK3DivDense) : NearOptimalDecomp :=
  nearOptimalDecomp_of_vortexRatio
    (vortexEngineRatioFromInputs_of_coverDownDivDense hFix hSched hCoverDown)

/-- **The decomposition theorem for dense divisible graphs follows from the density-corrected
cover-down step.**  The level-density hypothesis does *not* weaken the cover-down interface: the
vortex supplies it at every level, so the dense step still proves the theorem the vehicle uses it
to prove. -/
theorem triDecompDense_of_coverDownK3DivDense
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hFix : LevelDivFixProp) (hSched : VortexScheduleSlack) (hCoverDown : CoverDownK3DivDense) :
    TriDecompDense :=
  triDecompDense_of_inputs hDross (fracToApprox_of_maxDeg hNib) hDirac
    (nearOptimalDecomp_of_coverDownDivDense hFix hSched hCoverDown)

/-- **The circularity is not broken by the level-density hypothesis.**  Modulo the same three
classical inputs, the vortex schedule and the divisibility fix as in
`BKLO.coverDownK3Div_iff_triDecompDense`, the density-corrected cover-down step
`BKLO.CoverDownK3DivDense` is *equivalent* to `BKLO.TriDecompDense`.

So `BKLO.CoverDownK3DivDense` — and hence `BKLO.ShellAbsorptionDense`, which implies it through
`BKLO.coverDownK3DivDense_of_denseNibble_shellAbsorptionDense` — is of theorem strength: proving it
proves the triangle decomposition theorem for dense divisible graphs.  What the level-density
hypothesis achieves is the removal of the *degenerate* hollow instances of
`BKLO/ShellAbsorptionConfinementWall.lean`, not a reduction in strength. -/
theorem coverDownK3DivDense_iff_triDecompDense
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hFix : LevelDivFixProp) (hSched : VortexScheduleSlack) :
    CoverDownK3DivDense ↔ TriDecompDense :=
  ⟨fun hCD => triDecompDense_of_coverDownK3DivDense hDross hNib hDirac hFix hSched hCD,
    fun hT => coverDownK3DivDense_of_coverDownK3Div (coverDownK3Div_of_triDecompDense hT)⟩

end BKLO
