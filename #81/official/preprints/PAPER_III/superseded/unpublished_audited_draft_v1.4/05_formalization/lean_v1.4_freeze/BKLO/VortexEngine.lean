/-
# BKLO §10 — the vortex engine, discharged.

`BKLO/Vortex.lean` reduced §10 to a residual interface: a notion of goodness of a bottom set, the
existence of good bottom sets of bounded size, and the cover-down of a dense triangle-divisible
edge set onto a good bottom set.  This file discharges that residual — in the ratio-restricted form
`VortexEngineRatioFromInputs`, which is the form §10 actually supplies (see the discussion in
`BKLO/Vortex.lean`) — from the two §10 inputs of `BKLO/InputsVortex.lean` (`VortexScheduleExists`,
the probabilistic existence of the vortex, and `CoverDownK3`, BKLO's cover-down lemma for
`F = K₃`).

Two design points are worth recording.

* The *whole* vortex is run inside a single cover-down: the recursion `coverDown_vortex` below
  descends from `S` all the way to `U`.  This is forced, because the density constant demanded of
  every level is the same: restricting an edge set of minimum degree `c|S|` to a subset `W` gives
  minimum degree at best `c|W| - Θ(√|W|)`, and `δ ≥ c|·|` is scale invariant, so there is no slack
  to pay the fluctuation with.  What *is* true — and is what BKLO prove — is that the whole nested
  sequence can be chosen at once, at the cost of a single loss from `9/10 + ε` down to
  `9/10 + ε/2`, because the losses along the vortex are dominated by the loss at the smallest
  level.  This is the content of the schedule `f` in `VortexScheduleExists`.

* The recursion carries a **one-level lookahead**: its state is a pair of consecutive levels
  `W' ⊆ W` together with the current edge set `F`.  The reason is the clause
  `F ∩ cliqueEdges W'' ⊆ F \ famEdges P` of `CoverDownK3`: the cover-down at a level does not touch
  a single edge inside the level *after* the next.  That is what stops the per-level damage from
  accumulating: when the recursion arrives at a level, the edge set inside it is still the original
  one, so its minimum degree is the one supplied by the schedule and only a single level's worth of
  damage (`γ|W'|`) has to be paid.

The levels shrink by a factor between `K` and `K²` at each step, `K` being the ratio supplied by
`CoverDownK3`; the arithmetic of that window is `vortex_next_level_sizes`.

Everything here is `sorry`-free.
-/
import BKLO.InputsVortex
import Mathlib.Data.Int.Star

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Bookkeeping lemmas -/

theorem inter_cliqueEdges_inter {W' W'' : Finset V} (h : W'' ⊆ W') (F : Finset (Sym2 V)) :
    (F ∩ cliqueEdges W') ∩ cliqueEdges W'' = F ∩ cliqueEdges W'' := by
  rw [Finset.inter_assoc, Finset.inter_eq_right.2 (cliqueEdges_mono h)]

/-- If a cover-down step leaves every edge inside `W''` untouched, then it changes nothing inside
any subset `X` of `W''`. -/
theorem inter_cliqueEdges_eq_of_keep {F F₁ : Finset (Sym2 V)} {W'' X : Finset V}
    (hX : X ⊆ W'') (hsub : F₁ ⊆ F) (hkeep : F ∩ cliqueEdges W'' ⊆ F₁) :
    F₁ ∩ cliqueEdges X = F ∩ cliqueEdges X := by
  apply Finset.Subset.antisymm
  · exact Finset.inter_subset_inter_right hsub
  · intro e he
    obtain ⟨he1, he2⟩ := Finset.mem_inter.1 he
    exact Finset.mem_inter.2 ⟨hkeep (Finset.mem_inter.2 ⟨he1, cliqueEdges_mono hX he2⟩), he2⟩

/-- The leftover of a cover-down step still has large minimum degree on the next level. -/
theorem edeg_leftover_of_coverDown {c₁ γ x : ℝ} {W' : Finset V} {F F₁ : Finset (Sym2 V)} {v : V}
    (hdam : (edeg (F ∩ cliqueEdges W') v : ℝ) ≤ (edeg F₁ v : ℝ) + γ * (W'.card : ℝ))
    (hcl : x * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) (hx : c₁ + γ ≤ x) :
    c₁ * (W'.card : ℝ) ≤ (edeg F₁ v : ℝ) := by
  have hcard : (0 : ℝ) ≤ (W'.card : ℝ) := by positivity
  nlinarith only [hdam, hcl, hx]

/-- **The size of the next level.**  If the current level `b` is more than `K²` times the bottom
size `a`, then `m = b / K` is a legitimate next size: it is at least `K` times the bottom size, at
most half of `b`, and it sits in the window `K·m ≤ b ≤ K²·m` demanded by the cover-down. -/
theorem vortex_next_level_sizes {K a b : ℕ} (hK : 2 ≤ K) (ha : 1 ≤ a) (hb : K * K * a < b) :
    K * a ≤ b / K ∧ a ≤ b / K ∧ 2 * (b / K) ≤ b ∧ K * (b / K) ≤ b ∧ b ≤ K * K * (b / K) := by
  have hKpos : 0 < K := by omega
  set m := b / K with hm
  have hdm : K * m + b % K = b := Nat.div_add_mod b K
  have hmod : b % K < K := Nat.mod_lt _ hKpos
  have hKm : K * m ≤ b := Nat.le.intro hdm
  have hlt : b < K * m + K := by omega
  have hKa : K * a ≤ m := by
    rw [hm, Nat.le_div_iff_mul_le hKpos]
    linarith only [hb]
  have ham : a ≤ m := le_trans (Nat.le_mul_of_pos_left a hKpos) hKa
  have hm2 : 2 ≤ m := le_trans (by nlinarith) hKa
  refine ⟨hKa, ham, ?_, hKm, ?_⟩
  · calc 2 * m ≤ K * m := Nat.mul_le_mul_right m hK
      _ ≤ b := hKm
  · nlinarith only [hK, ha, hb, hlt]

/-! ### The recursion down the vortex -/

/-- **Running the cover-down along the whole vortex.**  Given the cover-down step `hCD` at ambient
density `c₁` with damage tolerance `γ` and size ratio `K`, and the one-level descent `hdesc` of the
schedule `f`, an edge set `F` spanned by `W` of minimum degree at least `c₁|W|`, together with an
already chosen next level `W'` on which `F` still has the schedule's density, is covered by
edge-disjoint triangles down to a remainder inside the bottom set `U`. -/
theorem coverDown_vortex {c₁ γ : ℝ} {f : ℕ → ℝ} {n₂ n₀ K : ℕ} {U : Finset V} (hK : 2 ≤ K)
    (hCD : ∀ (W W' W'' : Finset V) (F : Finset (Sym2 V)),
      n₀ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
      K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
      F ⊆ cliqueEdges W → TriDivisible F → (∀ v ∈ W, c₁ * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn F P ∧
        F \ famEdges P ⊆ cliqueEdges W' ∧
        F ∩ cliqueEdges W'' ⊆ F \ famEdges P ∧
        ∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
          ≤ (edeg (F \ famEdges P) v : ℝ) + γ * (W'.card : ℝ))
    (hdesc : ∀ (W : Finset V) (E : Finset (Sym2 V)) (m : ℕ),
      U ⊆ W → U.card ≤ m → 2 * m ≤ W.card → E ⊆ cliqueEdges W →
      (∀ v ∈ W, f W.card * (W.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ W'.card = m ∧
        ∀ v ∈ W', f m * (m : ℝ) ≤ (edeg (E ∩ cliqueEdges W') v : ℝ))
    (hf : ∀ s : ℕ, n₂ ≤ s → c₁ + γ ≤ f s) (hn₀ : n₀ ≤ n₂) (hn₂ : 0 < n₂) (hU : n₂ ≤ U.card) :
    ∀ (fuel : ℕ) (W W' : Finset V) (F : Finset (Sym2 V)),
      W.card ≤ fuel → F ⊆ cliqueEdges W → TriDivisible F →
      (∀ v ∈ W, c₁ * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
      U ⊆ W' → W' ⊆ W → K * W'.card ≤ W.card → W.card ≤ K * K * W'.card →
      (W' = U ∨ K * U.card ≤ W'.card) →
      (∀ v ∈ W', f W'.card * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
      (∀ v ∈ U, f U.card * (U.card : ℝ) ≤ (edeg (F ∩ cliqueEdges U) v : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn F P ∧ F \ famEdges P ⊆ cliqueEdges U := by
  classical
  intro fuel
  induction fuel with
  | zero =>
    intro W W' F hfuel _ _ _ hUW' hW'W _ _ _ _ _
    have h1 : U.card ≤ W'.card := Finset.card_le_card hUW'
    have h2 : W'.card ≤ W.card := Finset.card_le_card hW'W
    omega
  | succ fuel ih =>
    intro W W' F hfuel hFW hdiv hdeg hUW' hW'W hr1 hr2 hdisj hclean hgoodU
    have hUcard : U.card ≤ W'.card := Finset.card_le_card hUW'
    have hW'card : W'.card ≤ W.card := Finset.card_le_card hW'W
    have hn₂W' : n₂ ≤ W'.card := le_trans hU hUcard
    have hn₀W : n₀ ≤ W.card := le_trans (le_trans hn₀ hn₂W') hW'card
    by_cases hWU : W' = U
    · -- the bottom set has been reached: one last cover-down
      obtain ⟨P, hP, hcov, -, -⟩ :=
        hCD W W' ∅ F hn₀W hW'W (Finset.empty_subset _) hr1 hr2 (by simp) hFW hdiv hdeg
      exact ⟨P, hP, by rw [← hWU]; exact hcov⟩
    · -- otherwise the bottom set is at least `K` times smaller than the current level
      have hKU : K * U.card ≤ W'.card := hdisj.resolve_left hWU
      have hUpos : 1 ≤ U.card := by omega
      -- choose the level after the next
      obtain ⟨W'', hUW'', hW''W', hW''r1, hW''r2, hW''disj, hclean''⟩ :
          ∃ W'' : Finset V, U ⊆ W'' ∧ W'' ⊆ W' ∧ K * W''.card ≤ W'.card ∧
            W'.card ≤ K * K * W''.card ∧ (W'' = U ∨ K * U.card ≤ W''.card) ∧
            ∀ v ∈ W'', f W''.card * (W''.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W'') v : ℝ) := by
        by_cases hsmall : W'.card ≤ K * K * U.card
        · exact ⟨U, Finset.Subset.refl _, hUW', hKU, hsmall, Or.inl rfl, hgoodU⟩
        · push_neg at hsmall
          obtain ⟨hKa, ham, h2m, hKm, hmm⟩ := vortex_next_level_sizes hK hUpos hsmall
          obtain ⟨W'', hUW'', hW''W', hcard'', hclean''⟩ :=
            hdesc W' (F ∩ cliqueEdges W') (W'.card / K) hUW' ham h2m Finset.inter_subset_right
              hclean
          refine ⟨W'', hUW'', hW''W', by rw [hcard'']; exact hKm, by rw [hcard'']; exact hmm,
            Or.inr (by rw [hcard'']; exact hKa), ?_⟩
          intro v hv
          have h := hclean'' v hv
          rw [inter_cliqueEdges_inter hW''W'] at h
          rwa [hcard'']
      -- cover down one level
      obtain ⟨P₁, hP₁, hcov₁, hkeep₁, hdam₁⟩ :=
        hCD W W' W'' F hn₀W hW'W hW''W' hr1 hr2 hW''r1 hFW hdiv hdeg
      set F₁ := F \ famEdges P₁ with hF₁
      have hdiv₁ : TriDivisible F₁ := triDivisible_sdiff_famEdges hP₁ hdiv
      have hdeg₁ : ∀ v ∈ W', c₁ * (W'.card : ℝ) ≤ (edeg F₁ v : ℝ) := fun v hv =>
        edeg_leftover_of_coverDown (hdam₁ v hv) (hclean v hv) (hf _ hn₂W')
      have hclean₁ : ∀ v ∈ W'',
          f W''.card * (W''.card : ℝ) ≤ (edeg (F₁ ∩ cliqueEdges W'') v : ℝ) := by
        intro v hv
        rw [inter_cliqueEdges_eq_of_keep (Finset.Subset.refl W'') Finset.sdiff_subset hkeep₁]
        exact hclean'' v hv
      have hgoodU₁ : ∀ v ∈ U, f U.card * (U.card : ℝ) ≤ (edeg (F₁ ∩ cliqueEdges U) v : ℝ) := by
        intro v hv
        rw [inter_cliqueEdges_eq_of_keep hUW'' Finset.sdiff_subset hkeep₁]
        exact hgoodU v hv
      -- and recurse on the next level
      have hW'pos : 1 ≤ W'.card := by omega
      have hfuel' : W'.card ≤ fuel := by
        have : 2 * W'.card ≤ K * W'.card := Nat.mul_le_mul_right _ hK
        omega
      obtain ⟨P₂, hP₂, hcov₂⟩ :=
        ih W' W'' F₁ hfuel' hcov₁ hdiv₁ hdeg₁ hUW'' hW''W' hW''r1 hW''r2 hW''disj hclean₁ hgoodU₁
      refine ⟨P₁ ∪ P₂, triFamilyIn_union hP₁ hP₂, ?_⟩
      rw [sdiff_famEdges_union]
      exact hcov₂

/-! ### The goodness predicate -/

/-- **Goodness of a bottom set** for the vortex engine: a set of bounded size, not too small, on
which the induced edge set already has the density demanded by the schedule.  (The `edeg` is taken
with the classical instance because `GoodPred` quantifies over a bare `Type`.) -/
def vortexGood (f : ℕ → ℝ) (n₂ C : ℕ) : GoodPred :=
  fun V U EU => U.card ≤ C ∧ n₂ ≤ U.card ∧
    ∀ v ∈ U, f U.card * (U.card : ℝ) ≤ (@edeg V (Classical.decEq V) EU v : ℝ)

theorem vortexGood_iff {V : Type} [inst : DecidableEq V] (f : ℕ → ℝ) (n₂ C : ℕ)
    (U : Finset V) (EU : Finset (Sym2 V)) :
    vortexGood f n₂ C V U EU ↔
      (U.card ≤ C ∧ n₂ ≤ U.card ∧ ∀ v ∈ U, f U.card * (U.card : ℝ) ≤ (edeg EU v : ℝ)) := by
  unfold vortexGood
  simp_rw [edeg_inst_irrel (Classical.decEq V) inst]

/-! ### The engine -/

/-- **The vortex engine, from the two §10 inputs.**  For every `ε > 0` the goodness predicate
`vortexGood` supplied by the schedule has bounded good bottom sets, and any sufficiently small
good bottom set can be covered down onto, by running the cover-down along the whole vortex from
`S` down to `U`. -/
theorem vortexEngineRatio_of_inputs (hSched : VortexScheduleExists) (hCoverDown : CoverDownK3)
    (ε : ℝ) (hε : 0 < ε) : VortexEngineRatio (9 / 10 + ε) := by
  classical
  obtain ⟨K, n₀, hK, hCD⟩ := hCoverDown (9 / 10 + ε / 4) (ε / 8) (by linarith) (by linarith)
  obtain ⟨f, n₂, C, hn₀n₂, hn₂C, hn₂pos, hfbd, hbot, hdesc⟩ := hSched ε hε (max n₀ 1)
  have hn₀le : n₀ ≤ n₂ := le_trans (le_max_left _ _) hn₀n₂
  -- the damage budget: `c₁ + γ = 9/10 + 3ε/8 ≤ 9/10 + ε/2 ≤ f s`
  have hf : ∀ s : ℕ, n₂ ≤ s → (9 / 10 + ε / 4) + ε / 8 ≤ f s := by
    intro s hs
    have := (hfbd s hs).1
    linarith
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
    have hn₀S : n₀ ≤ S.card := le_trans hn₀le hn₂S
    have hUpos : 1 ≤ U.card := by omega
    have hdeg₁ : ∀ v ∈ S, (9 / 10 + ε / 4) * (S.card : ℝ) ≤ (edeg E v : ℝ) := by
      intro v hv
      have h := hdeg v hv
      have hS : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
      nlinarith
    have hdescU : ∀ (W : Finset V) (E' : Finset (Sym2 V)) (m : ℕ),
        U ⊆ W → U.card ≤ m → 2 * m ≤ W.card → E' ⊆ cliqueEdges W →
        (∀ v ∈ W, f W.card * (W.card : ℝ) ≤ (edeg E' v : ℝ)) →
        ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ W'.card = m ∧
          ∀ v ∈ W', f m * (m : ℝ) ≤ (edeg (E' ∩ cliqueEdges W') v : ℝ) :=
      fun W E' m h1 h2 h3 h4 h5 => hdesc W U E' m hUn₂ h1 h2 h3 h4 h5
    by_cases hsmall : S.card ≤ K * K * U.card
    · -- the bottom set is already comparable to `S`: a single cover-down
      exact coverDown_vortex (U := U) hK (fun W W' W'' F => hCD W W' W'' F) hdescU hf hn₀le
        hn₂pos hUn₂ S.card S U E le_rfl hES hdiv hdeg₁ (Finset.Subset.refl _) hUS hratio hsmall
        (Or.inl rfl) hUdeg hUdeg
    · -- otherwise start the vortex with one descent from `S`
      push_neg at hsmall
      obtain ⟨hKa, ham, h2m, hKm, hmm⟩ := vortex_next_level_sizes hK hUpos hsmall
      have hdegf : ∀ v ∈ S, f S.card * (S.card : ℝ) ≤ (edeg E v : ℝ) := by
        intro v hv
        have h := hdeg v hv
        have hS : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
        have hfS := (hfbd S.card hn₂S).2
        nlinarith
      obtain ⟨W₁, hUW₁, hW₁S, hcard₁, hclean₁⟩ :=
        hdescU S E (S.card / K) hUS ham h2m hES hdegf
      refine coverDown_vortex (U := U) hK (fun W W' W'' F => hCD W W' W'' F) hdescU hf hn₀le
        hn₂pos hUn₂ S.card S W₁ E le_rfl hES hdiv hdeg₁ hUW₁ hW₁S (by rw [hcard₁]; exact hKm)
        (by rw [hcard₁]; exact hmm) (Or.inr (by rw [hcard₁]; exact hKa)) ?_ hUdeg
      intro v hv
      rw [hcard₁]
      exact hclean₁ v hv

/-- **The residual interface of §10 is discharged.**  From the probabilistic existence of the
vortex and BKLO's cover-down lemma, the ratio-restricted vortex engine holds at every density
above `9/10`. -/
theorem vortexEngineRatioFromInputs_holds (hSched : VortexScheduleExists)
    (hCoverDown : CoverDownK3) : VortexEngineRatioFromInputs :=
  fun _ _ _ ε hε => vortexEngineRatio_of_inputs hSched hCoverDown ε hε

end BKLO
