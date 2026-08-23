/-
# The vortex recursion, from the **twice-repaired** interface.

`BKLO.coverDown_vortex_denseR` runs the recursion from a descent clause that is false
(`BKLO.not_vortexDescentClauseR`).  This file redoes it from the repaired descent clause
`BKLO.VortexDescentClauseR2`, whose two extra hypotheses — the bottom set is `K` times smaller
than the level being chosen, and every vertex of the current level is already dense into the
bottom set — are exactly two invariants the recursion has in its hands: the first is the
alternative `W'' = U ∨ K|U| ≤ |W''|` that drives the recursion, the second is the *bottom*
invariant of `BKLO.coverDown_vortex_denseR`.

The cover-down step is unchanged (`BKLO.coverDownStepR_of_reservoirClauseR`), since the reservoir
clause is unchanged.

Everything here is `sorry`-free.
-/
import BKLO.VortexEngineFusedR
import BKLO.ReservoirRepaired2

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The recursion down the vortex -/

/-- **Running the cover-down along the whole vortex, from the twice-repaired descent clause.**  As
carried along the recursion. -/
theorem coverDown_vortex_denseR2 {c₁ γ : ℝ} {f : ℕ → ℝ} {n₂ n₀ K : ℕ} {U : Finset V} (hK : 2 ≤ K)
    (hCD : ∀ (W W' W'' : Finset V) (F : Finset (Sym2 V)),
      n₀ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
      K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
      F ⊆ cliqueEdges W → TriDivisible F → (∀ v ∈ W, c₁ * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
      (∀ v ∈ W', f W'.card * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
      (∀ v ∈ W, c₁ * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn F P ∧
        F \ famEdges P ⊆ cliqueEdges W' ∧
        F ∩ cliqueEdges W'' ⊆ F \ famEdges P ∧
        (∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
          ≤ (edeg (F \ famEdges P) v : ℝ) + γ * (W'.card : ℝ)) ∧
        ∀ v ∈ W', ((resLink F W'' v).card : ℝ)
          ≤ ((resLink (F \ famEdges P) W'' v).card : ℝ) + γ * (W''.card : ℝ))
    (hdesc : ∀ (W : Finset V) (E : Finset (Sym2 V)) (m : ℕ),
      U ⊆ W → K * U.card ≤ m → 2 * m ≤ W.card → W.card ≤ K * K * m → E ⊆ cliqueEdges W →
      (∀ v ∈ W, f W.card * (W.card : ℝ) ≤ (edeg E v : ℝ)) →
      (∀ v ∈ W, f U.card * (U.card : ℝ) ≤ ((resLink E U v).card : ℝ)) →
      ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ W'.card = m ∧
        ∀ v ∈ W, f m * (m : ℝ) ≤ ((resLink E W' v).card : ℝ))
    (hf : ∀ s : ℕ, n₂ ≤ s → c₁ + γ ≤ f s) (hn₀ : n₀ ≤ n₂) (hn₂ : 0 < n₂) (hU : n₂ ≤ U.card) :
    ∀ (fuel : ℕ) (W W' : Finset V) (F : Finset (Sym2 V)),
      W.card ≤ fuel → F ⊆ cliqueEdges W → TriDivisible F →
      (∀ v ∈ W, c₁ * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
      U ⊆ W' → W' ⊆ W → K * W'.card ≤ W.card → W.card ≤ K * K * W'.card →
      (W' = U ∨ K * U.card ≤ W'.card) →
      (∀ v ∈ W', f W'.card * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
      (∀ v ∈ W, c₁ * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ)) →
      (∀ v ∈ W', f U.card * (U.card : ℝ) ≤ ((resLink F U v).card : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn F P ∧ F \ famEdges P ⊆ cliqueEdges U := by
  classical
  intro fuel
  induction fuel with
  | zero =>
    intro W W' F hfuel _ _ _ hUW' hW'W _ _ _ _ _ _
    have h1 : U.card ≤ W'.card := Finset.card_le_card hUW'
    have h2 : W'.card ≤ W.card := Finset.card_le_card hW'W
    omega
  | succ fuel ih =>
    intro W W' F hfuel hFW hdiv hdeg hUW' hW'W hr1 hr2 hdisj hclean hbetween hbottom
    have hUcard : U.card ≤ W'.card := Finset.card_le_card hUW'
    have hW'card : W'.card ≤ W.card := Finset.card_le_card hW'W
    have hn₂W' : n₂ ≤ W'.card := le_trans hU hUcard
    have hn₀W : n₀ ≤ W.card := le_trans (le_trans hn₀ hn₂W') hW'card
    have hnd : ∀ e ∈ F, ¬ e.IsDiag := fun e he => (mem_cliqueEdgesV.1 (hFW he)).2
    by_cases hWU : W' = U
    · -- the bottom set has been reached: one last cover-down
      obtain ⟨P, hP, hcov, -, -, -⟩ :=
        hCD W W' ∅ F hn₀W hW'W (Finset.empty_subset _) hr1 hr2 (by simp) hFW hdiv hdeg hclean
          hbetween
      exact ⟨P, hP, by rw [← hWU]; exact hcov⟩
    · -- otherwise the bottom set is at least `K` times smaller than the current level
      have hKU : K * U.card ≤ W'.card := hdisj.resolve_left hWU
      have hUpos : 1 ≤ U.card := by omega
      have hbottom' : ∀ v ∈ W',
          f U.card * (U.card : ℝ) ≤ ((resLink (F ∩ cliqueEdges W') U v).card : ℝ) := by
        intro v hv
        rw [resLink_inter_cliqueEdges (hUW' : U ⊆ W') hv hnd]
        exact hbottom v hv
      -- choose the level after the next, together with the density of `F` into it seen from `W'`
      obtain ⟨W'', hUW'', hW''W', hW''r1, hW''r2, hW''disj, hres''⟩ :
          ∃ W'' : Finset V, U ⊆ W'' ∧ W'' ⊆ W' ∧ K * W''.card ≤ W'.card ∧
            W'.card ≤ K * K * W''.card ∧ (W'' = U ∨ K * U.card ≤ W''.card) ∧
            ∀ v ∈ W', f W''.card * (W''.card : ℝ) ≤ ((resLink F W'' v).card : ℝ) := by
        by_cases hsmall : W'.card ≤ K * K * U.card
        · exact ⟨U, Finset.Subset.refl _, hUW', hKU, hsmall, Or.inl rfl, hbottom⟩
        · push_neg at hsmall
          obtain ⟨hKa, ham, h2m, hKm, hmm⟩ := vortex_next_level_sizes hK hUpos hsmall
          obtain ⟨W'', hUW'', hW''W', hcard'', hres''⟩ :=
            hdesc W' (F ∩ cliqueEdges W') (W'.card / K) hUW' hKa h2m hmm
              Finset.inter_subset_right hclean hbottom'
          refine ⟨W'', hUW'', hW''W', by rw [hcard'']; exact hKm, by rw [hcard'']; exact hmm,
            Or.inr (by rw [hcard'']; exact hKa), ?_⟩
          intro v hv
          have h := hres'' v hv
          rw [resLink_inter_cliqueEdges hW''W' hv hnd] at h
          rwa [hcard'']
      have hn₂W'' : n₂ ≤ W''.card := le_trans hU (Finset.card_le_card hUW'')
      -- the density of the level after next, in its internal form
      have hclean'' : ∀ v ∈ W'',
          f W''.card * (W''.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W'') v : ℝ) := by
        intro v hv
        rw [edeg_inter_cliqueEdges_eq_card_resLink hv hnd]
        exact hres'' v (hW''W' hv)
      -- cover down one level
      obtain ⟨P₁, hP₁, hcov₁, hkeep₁, hdam₁, hdam₁'⟩ :=
        hCD W W' W'' F hn₀W hW'W hW''W' hr1 hr2 hW''r1 hFW hdiv hdeg hclean hbetween
      set F₁ := F \ famEdges P₁ with hF₁
      have hdiv₁ : TriDivisible F₁ := triDivisible_sdiff_famEdges hP₁ hdiv
      have hdeg₁ : ∀ v ∈ W', c₁ * (W'.card : ℝ) ≤ (edeg F₁ v : ℝ) := fun v hv =>
        edeg_leftover_of_coverDown (hdam₁ v hv) (hclean v hv) (hf _ hn₂W')
      have hclean₁ : ∀ v ∈ W'',
          f W''.card * (W''.card : ℝ) ≤ (edeg (F₁ ∩ cliqueEdges W'') v : ℝ) := by
        intro v hv
        rw [inter_cliqueEdges_eq_of_keep (Finset.Subset.refl W'') Finset.sdiff_subset hkeep₁]
        exact hclean'' v hv
      -- the between-levels density at the next pair, from the density into `W''` minus the damage
      have hbetween₁ : ∀ v ∈ W', c₁ * (W''.card : ℝ) ≤ ((resLink F₁ W'' v).card : ℝ) := by
        intro v hv
        have h1 := hres'' v hv
        have h2 := hdam₁' v hv
        have h3 : c₁ + γ ≤ f W''.card := hf _ hn₂W''
        have h4 : (0 : ℝ) ≤ (W''.card : ℝ) := Nat.cast_nonneg _
        nlinarith only [h1, h2, h3]
      -- the density into the bottom set survives, because the step protects `W''`
      have hbottom₁ : ∀ v ∈ W'', f U.card * (U.card : ℝ) ≤ ((resLink F₁ U v).card : ℝ) := by
        intro v hv
        refine le_trans (hbottom v (hW''W' hv)) ?_
        exact_mod_cast Finset.card_le_card (resLink_subset_of_keep hUW'' hkeep₁ hv hnd)
      -- and recurse on the next level
      have hW'pos : 1 ≤ W'.card := by omega
      have hfuel' : W'.card ≤ fuel := by
        have : 2 * W'.card ≤ K * W'.card := Nat.mul_le_mul_right _ hK
        omega
      obtain ⟨P₂, hP₂, hcov₂⟩ :=
        ih W' W'' F₁ hfuel' hcov₁ hdiv₁ hdeg₁ hUW'' hW''W' hW''r1 hW''r2 hW''disj hclean₁
          hbetween₁ hbottom₁
      refine ⟨P₁ ∪ P₂, triFamilyIn_union hP₁ hP₂, ?_⟩
      rw [sdiff_famEdges_union]
      exact hcov₂
