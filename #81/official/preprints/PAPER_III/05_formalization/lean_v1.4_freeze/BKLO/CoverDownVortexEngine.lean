/-
# The §10 conclusion, the faithful BKLO way: vortex + cover-down.

This file assembles the cover-down vehicle for the AX2 half of Erdős #81.  Nothing here uses the
class-matched routed sweep of `BKLO/AX2*.lean`, no ledger, no reservoir and no routed leftovers:
the vortex's own nested structure absorbs the leftover of each level, exactly as in BKLO §10.

The ingredients are

* `BKLO.CoverDownK3Div` (`BKLO/CoverDownRepaired.lean`) — the repaired cover-down step;
* `BKLO.LevelDivFixProp` (`BKLO/LevelDivFix.lean`) — the divisibility fix that makes the repaired
  cover-down applicable at a level produced by sampling;
* `BKLO.VortexScheduleSlack` (`BKLO/CoverDownVortexFaithful.lean`) — the vortex schedule, with the
  slack one fix costs;
* `BKLO.coverDown_vortex_fix` (`BKLO/CoverDownVortexRecursion.lean`) — the recursion itself;

together with the three classical inputs `BKLO.FracTriangleThreshold`,
`BKLO.FracToApproxMaxDeg` and `BKLO.PerfectMatchingDirac`, which enter through
`BKLO.triangle_decomposition_of_inputs`.

## What is and is not discharged

**Nothing here is unconditional, and two independent obstructions are now proved.**

1. The theorems below are conditional on `CoverDownK3Div`.  That is not an accident of the
   assembly: `BKLO/CoverDownEquivalence.lean` proves that `CoverDownK3Div` is *equivalent* to
   `BKLO.TriDecompDense`, the very statement the vehicle is used to prove.  The cover-down vehicle
   relocates the §10 obstruction into the cover-down step; it does not discharge it.

2. The schedule hypothesis `VortexScheduleSlack` is **false**
   (`BKLO.not_vortexScheduleSlack`, `BKLO/VortexScheduleRefutation.lean`), as is the project's
   original `BKLO.VortexScheduleExists` (`BKLO.not_vortexScheduleExists`) on which
   `BKLO.vortexEngineRatio_of_inputs` rests.  The descent clause of both allows the degenerate
   instance `m = |U|`, which forces the next level to be the bottom set itself and demands a
   density on it that no hypothesis supplies.  Consequently the theorems below, while valid
   implications with genuine content in their proofs, are **vacuously conditional**: they cannot be
   used to derive anything.

A repaired descent clause must require `K|U| ≤ m` together with the density of the vertices of `W`
*into* the bottom set — the `resLink` hypothesis of `BKLO.VortexDescentClauseR2`, which is the form
in which the descent is actually proved in this project
(`BKLO.vortexDescentClauseR3_of_powerSchedule`).  The recursion below cannot maintain that
into-`U` density: every level performs one divisibility fix, each fix costs up to `12` edges at
every vertex — including the edges from a vertex to the bottom set, which are not inside
`cliqueEdges U` and so are not protected by the cover-down's keep clause — and a vortex has
`Θ(log |S|)` levels while `|U| ≤ C` is bounded.  The exact inequality that fails is

  `f |U| * |U| ≤ (resLink F U v).card - 12 * (number of levels)`,

whose right-hand side is eventually negative.  This is the precise obstruction of the cover-down
vehicle, and it is why no repair of the schedule interface alone can close it.
-/
import BKLO.CoverDownVortexRecursion
import BKLO.MainRepaired3

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-- Removing a bounded-degree edge set costs a bounded amount of degree, inside any level. -/
theorem edeg_inter_sdiff_ge (E Z' : Finset (Sym2 V)) (Z : Finset V)
    (hQ : ∀ v : V, edeg Z' v ≤ 12) (v : V) :
    (edeg (E ∩ cliqueEdges Z) v : ℝ) ≤ (edeg ((E \ Z') ∩ cliqueEdges Z) v : ℝ) + 12 := by
  rw [sdiff_inter_cliqueEdges E Z' Z]
  exact_mod_cast edeg_sdiff_ge (F := E ∩ cliqueEdges Z) v 12 (hQ v)

/-- **The ratio-restricted vortex engine, from the repaired cover-down and the divisibility fix.**

For every `ε > 0` the goodness predicate `BKLO.vortexGood` supplied by the schedule has bounded
good bottom sets, and any sufficiently small good bottom set can be covered down onto, by running
the *fixed* cover-down (`BKLO.coverDown_vortex_fix`) along the whole vortex from `S` down to `U`.
The only difference from `BKLO.vortexEngineRatio_of_inputs` is that here the cover-down used is the
repaired one, so a divisibility fix is performed before entering the recursion and once per
level. -/
theorem vortexEngineRatio_of_coverDownDiv (hFix : LevelDivFixProp) (hSched : VortexScheduleSlack)
    (hCoverDown : CoverDownK3Div) (ε : ℝ) (hε : 0 < ε) : VortexEngineRatio (9 / 10 + ε) := by
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
    -- ### run the fixed cover-down along the vortex
    obtain ⟨P, hP, hcov⟩ :=
      coverDown_vortex_fix (c₀ := 9 / 10 + ε / 8) (c₁ := 9 / 10 + ε / 4) (γ := ε / 32)
        (U := U) hK hFix (fun W W' W'' F => hCD W W' W'' F) hdescU (by linarith) hS1 hS2 hn₀le
        h100 hUn₂ S.card S W₁ E₁ le_rfl hE₁S hE₁div hE₁deg hUW₁ hW₁S hr1 hr2 hdisj hE₁divW₁
        hE₁clean hE₁goodb hE₁gooda
    exact ⟨Q ∪ P, triFamilyIn_union hQfam (by rw [← hE₁]; exact hP), by
      rw [sdiff_famEdges_union, ← hE₁]; exact hcov⟩

/-- **The §10 residual interface, discharged by the cover-down vehicle** — conditionally on the
repaired cover-down step, the schedule and the divisibility fix. -/
theorem vortexEngineRatioFromInputs_of_coverDownDiv (hFix : LevelDivFixProp)
    (hSched : VortexScheduleSlack) (hCoverDown : CoverDownK3Div) :
    VortexEngineRatioFromInputs :=
  fun _ _ _ ε hε => vortexEngineRatio_of_coverDownDiv hFix hSched hCoverDown ε hε

/-- **The near-optimal decomposition interface, from the cover-down vehicle.**  This is the
statement `BKLO.triangle_decomposition_of_inputs` consumes. -/
theorem nearOptimalDecomp_of_coverDownDiv (hFix : LevelDivFixProp) (hSched : VortexScheduleSlack)
    (hCoverDown : CoverDownK3Div) : NearOptimalDecomp :=
  nearOptimalDecomp_of_vortexRatio
    (vortexEngineRatioFromInputs_of_coverDownDiv hFix hSched hCoverDown)

/-- **The AX2 §10 conclusion, via cover-down.**  The main theorem of the project, obtained from the
three classical inputs through the faithful BKLO §10 route — a vortex whose levels are covered down
one onto the next — instead of the class-matched routed sweep.

The residual hypotheses are the repaired cover-down step `BKLO.CoverDownK3Div`, the vortex schedule
`BKLO.VortexScheduleSlack` and the divisibility fix `BKLO.LevelDivFixProp`.  See
`BKLO/CoverDownEquivalence.lean` for the exact strength of the first of these. -/
theorem triangle_decomposition_of_inputs_via_coverdown
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hFix : LevelDivFixProp) (hSched : VortexScheduleSlack) (hCoverDown : CoverDownK3Div) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs hDross (fracToApprox_of_maxDeg hNib) hDirac
    (nearOptimalDecomp_of_coverDownDiv hFix hSched hCoverDown)

end BKLO
