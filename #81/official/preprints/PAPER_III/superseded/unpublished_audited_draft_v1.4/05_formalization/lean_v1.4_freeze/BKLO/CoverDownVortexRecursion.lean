/-
# The cover-down recursion along the vortex, with divisibility fixing.

This is the faithful BKLO §10 recursion: a vortex `W ⊇ W' ⊇ W'' ⊇ … ⊇ U` is descended one level at
a time, each level being covered down onto the next, the leftover of a level being **absorbed by
the next level** rather than routed anywhere.  The recursion differs from
`BKLO.coverDown_vortex` (`BKLO/VortexEngine.lean`) in exactly one respect: it uses the *repaired*
cover-down `BKLO.CoverDownK3Div`, whose two extra hypotheses demand that the levels induce
triangle-divisible edge sets, and it therefore performs a **divisibility fix**
(`BKLO.LevelDivFixProp`) at every level before covering down onto it.

## The invariants

At a state `(W, W', F)` — ambient set `W`, next level `W'`, current edge set `F` — the recursion
maintains

* `F ⊆ cliqueEdges W` and `TriDivisible F`;
* `c₁|W| + 12 ≤ edeg F v` for `v ∈ W`, the ambient density with the slack one fix costs;
* `TriDivisible (F ∩ cliqueEdges W')` — the level being covered down onto is already fixed;
* `f|W'||W'| - 12 ≤ edeg (F ∩ cliqueEdges W') v` for `v ∈ W'`, *unless* `W' = U`;
* two bottom-set invariants: `f|U||U| - 12 ≤ edeg (F ∩ cliqueEdges U) v` unless `W' = U`, and the
  *exact* `f|U||U| ≤ edeg (F ∩ cliqueEdges U) v` whenever the current level is still more than `K²`
  times the bottom set.

The exact bottom invariant is what makes the fixes non-accumulating at the bottom set: as long as
the level `X` chosen next satisfies `4|U| ≤ |X|`, the fix is made to avoid `cliqueEdges U`
altogether (the `Y` parameter of `BKLO.LevelDivFixProp`), so the bottom set is untouched.  Only in
the final two steps, when the level has come within a factor `K²` of the bottom set, is the bottom
set allowed to lose the `12` edges of one fix — and the invariants are arranged so that this
happens at most once before the recursion terminates.
-/
import BKLO.CoverDownVortexFaithful

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-- **Running the fixed cover-down along the whole vortex.**  Given the repaired cover-down step
`hCD` at ambient density `c₀` with damage tolerance `γ` and size ratio `K`, the divisibility fix
`hFix`, and the one-level descent `hdesc` of the schedule `f`, an edge set `F` spanned by `W` of
minimum degree at least `c₁|W| + 12`, together with an already fixed next level `W'`, is covered by
edge-disjoint triangles down to a remainder inside the bottom set `U`. -/
theorem coverDown_vortex_fix {c₀ c₁ γ : ℝ} {f : ℕ → ℝ} {n₂ n₀ K : ℕ} {U : Finset V}
    (hK : 2 ≤ K) (hFix : LevelDivFixProp)
    (hCD : ∀ (W W' W'' : Finset V) (F : Finset (Sym2 V)),
      n₀ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
      K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
      F ⊆ cliqueEdges W → TriDivisible F →
      TriDivisible (F ∩ cliqueEdges W') → TriDivisible (F ∩ cliqueEdges W'') →
      (∀ v ∈ W, c₀ * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
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
    (hc₀ : c₀ ≤ c₁)
    (hS1 : ∀ s : ℕ, n₂ ≤ s → (c₁ + γ) * (s : ℝ) + 36 ≤ f s * (s : ℝ))
    (hS2 : ∀ s : ℕ, n₂ ≤ s → (9 / 10 : ℝ) * (s : ℝ) + 12 ≤ f s * (s : ℝ))
    (hn₀ : n₀ ≤ n₂) (hn₂ : 100 ≤ n₂) (hU : n₂ ≤ U.card) :
    ∀ (fuel : ℕ) (W W' : Finset V) (F : Finset (Sym2 V)),
      W.card ≤ fuel → F ⊆ cliqueEdges W → TriDivisible F →
      (∀ v ∈ W, c₁ * (W.card : ℝ) + 12 ≤ (edeg F v : ℝ)) →
      U ⊆ W' → W' ⊆ W → K * W'.card ≤ W.card → W.card ≤ K * K * W'.card →
      (W' = U ∨ K * U.card ≤ W'.card) →
      TriDivisible (F ∩ cliqueEdges W') →
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
    intro W W' F hfuel _ _ _ hUW' hW'W _ _ _ _ _ _ _
    have h1 : U.card ≤ W'.card := Finset.card_le_card hUW'
    have h2 : W'.card ≤ W.card := Finset.card_le_card hW'W
    omega
  | succ fuel ih =>
    intro W W' F hfuel hFW hdiv hdeg hUW' hW'W hr1 hr2 hdisj hdivW' hclean' hgoodUb hgoodUa
    have hUcard : U.card ≤ W'.card := Finset.card_le_card hUW'
    have hW'card : W'.card ≤ W.card := Finset.card_le_card hW'W
    have hn₂W' : n₂ ≤ W'.card := le_trans hU hUcard
    have hn₀W : n₀ ≤ W.card := le_trans (le_trans hn₀ hn₂W') hW'card
    have hUpos : 1 ≤ U.card := by omega
    -- the ambient density, in the weaker form the cover-down asks for
    have hdeg₀ : ∀ v ∈ W, c₀ * (W.card : ℝ) ≤ (edeg F v : ℝ) := by
      intro v hv
      have h := hdeg v hv
      have hc : c₀ * (W.card : ℝ) ≤ c₁ * (W.card : ℝ) :=
        mul_le_mul_of_nonneg_right hc₀ (by positivity)
      linarith
    by_cases hWU : W' = U
    · -- the bottom set has been reached: one last cover-down, no fix needed
      obtain ⟨P, hP, hcov, -, -⟩ :=
        hCD W W' ∅ F hn₀W hW'W (Finset.empty_subset _) hr1 hr2 (by simp) hFW hdiv hdivW'
          (by rw [inter_cliqueEdges_empty]; exact triDivisible_empty) hdeg₀
      exact ⟨P, hP, by rw [← hWU]; exact hcov⟩
    · -- otherwise the bottom set is at least `K` times smaller than the current level
      have hKU : K * U.card ≤ W'.card := hdisj.resolve_left hWU
      have hclean := hclean' hWU
      have hgoodU12 := hgoodUb hWU
      -- the density inside `W'` that the fix needs
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
        · -- the bottom set is within reach: descend onto it directly
          refine ⟨U, ∅, Finset.Subset.refl _, hUW', Finset.empty_subset _, hKU, hsmall,
            Or.inl rfl, by simp, ?_, ?_, Or.inl rfl⟩
          · intro v hv
            have h := hgoodU12 v hv
            have h2 := hS2 U.card hU
            linarith
          · intro hne; exact absurd rfl hne
        · -- otherwise one more level of the schedule
          push_neg at hsmall
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
      -- ### the fixed cover-down step
      obtain ⟨R, F₁, hR, hF₁, hF₁W', hF₁div, hF₁divX, hF₁Y, hdmgZ, hdmgW'⟩ :=
        coverDown_step_fixed (c₀ := c₀) (γ := γ) (W := W) (W' := W') (X := X) (Y := Y) (F := F)
          (K := K) (n₀ := n₀) hFix hCD hn₀W hW'W hXW' hYX hr1 hr2 hXr hK h4Y hX100 hFW hdiv hdivW'
          hdegW' hdegX (by
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
        ih W' X F₁ hfuel' hF₁W' hF₁div hdeg₁ hUX hXW' hXr hwin hXdisj hF₁divX hclean₁ hgoodUb₁
          hgoodUa₁
      refine ⟨R ∪ P₂, triFamilyIn_union hR (by rw [hF₁]; exact hP₂), ?_⟩
      rw [sdiff_famEdges_union, hF₁]
      exact hcov₂

end BKLO
