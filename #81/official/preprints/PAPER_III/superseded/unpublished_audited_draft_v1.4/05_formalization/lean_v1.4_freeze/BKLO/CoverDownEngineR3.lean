/-
# The FAITHFUL cover-down / nested-vortex route: the §10 engine with the cover-down step as the
only clause left open.

`BKLO/MainR4.lean` derives §10 (`BKLO.NearOptimalConclusion`) from the fused interface
`BKLO.VortexReservoirEngineR4` — the thrice-repaired interface of `BKLO/EngineR3.lean` with the
reservoir clause restricted to a *large* protected level, which is the repair forced by
`BKLO.not_reservoirClauseResidual` — and `BKLO/EngineR4Assembly.lean` reduces that interface to the
*reservoir* clause `BKLO.ReservoirClauseResidual4`: a crossing, vertex-sparse, apex-abundant
reservoir all of whose admissible link systems are coverable.  That is the clause the sparse-cluster
development of this project walls off.

The reservoir clause is used at exactly **one** place in the derivation: through
`BKLO.coverDownStepR_of_reservoirClauseR4`, together with the max-degree nibble, it produces *one
cover-down step*.  Nothing else in §10 sees it.  This file therefore isolates the cover-down step
itself as the interface, and re-runs the whole derivation on it:

* `BKLO.CoverDownStepClauseLarge` — one cover-down step, in exactly the shape the vortex recursion
  `BKLO.coverDown_vortex_denseR2Large` consumes (it is verbatim the conclusion of
  `BKLO.coverDownStepR_of_reservoirClauseR4`);
* `BKLO.VortexCoverDownEngineR3` — the thrice-repaired fused interface with the reservoir clause
  replaced by the cover-down step clause;
* `BKLO.nearOptimalConclusion_of_coverDownEngineR3` — §10 from it.  **No classical input is used
  any more at this stage**: Dross's threshold and the nibble entered `BKLO/MainR4.lean` only
  in order to build the cover-down step out of the reservoir;
* `BKLO.CoverDownStepResidualLarge` — the residual form of the clause (an arbitrary schedule in the
  window, above a threshold depending on `ε` and `K`), and
  `BKLO.vortexCoverDownEngineR3_of_residual`, which supplies all three vortex clauses — the
  schedule window `BKLO.powerSchedule_window`, the bottom clause
  `BKLO.vortexBottomClauseR2_of_schedule_window` and the *proved* descent clause
  `BKLO.vortexDescentClauseR3_of_powerSchedule` — from the explicit power-law schedule;
* `BKLO.coverDownStepResidualLarge_of_reservoir4` — the new residual is no stronger than the old
  one: Dross's threshold, the (dense) max-degree nibble and `BKLO.ReservoirClauseResidual4` imply
  it.

Everything here is `sorry`-free.
-/
import BKLO.EngineR4Assembly
import BKLO.NibbleMaxDegDense

open Finset

namespace BKLO

/-! ### The cover-down step as an interface -/

/-- **One cover-down step of the vortex.**  Verbatim the conclusion of
`BKLO.coverDownStepR_of_reservoirClauseR4`, i.e. what the vortex recursion
`BKLO.coverDown_vortex_denseR2Large` consumes at each level: given the current level `W`, the next
level `W'` and the protected level `W''` (empty, or a genuine level and hence of size at least
`n₂` — without that restriction the clause is false, exactly as in
`BKLO.not_reservoirClauseResidual`), an edge-disjoint triangle family inside `F` whose leftover lies
inside `W'`, which touches no edge inside `W''`, and which damages the degrees at the scale of `W'`
and the links at the scale of `W''` by at most `ε/8` of the respective sizes. -/
def CoverDownStepClauseLarge (ε : ℝ) (f : ℕ → ℝ) (n₂ K : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
    n₂ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
    K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
    (W''.Nonempty → n₂ ≤ W''.card) →
    F ⊆ cliqueEdges W → TriDivisible F →
    (∀ v ∈ W, (9 / 10 + ε / 4) * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
    (∀ v ∈ W', f W'.card * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
    (∀ v ∈ W, (9 / 10 + ε / 4) * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ)) →
    ∃ P : Finset (Finset V), TriFamilyIn F P ∧
      F \ famEdges P ⊆ cliqueEdges W' ∧
      F ∩ cliqueEdges W'' ⊆ F \ famEdges P ∧
      (∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
        ≤ (edeg (F \ famEdges P) v : ℝ) + ε / 8 * (W'.card : ℝ)) ∧
      ∀ v ∈ W', ((resLink F W'' v).card : ℝ)
        ≤ ((resLink (F \ famEdges P) W'' v).card : ℝ) + ε / 8 * (W''.card : ℝ)

/-- **The fused §10 interface of the cover-down route.**  As `BKLO.VortexReservoirEngineR3`, with
the reservoir clause replaced by the cover-down step clause.  The perturbation scale `η` and the
nibble threshold `N` of `BKLO.VortexReservoirEngineR3` disappear with it. -/
def VortexCoverDownEngineR3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ n₀ : ℕ, ∃ (f : ℕ → ℝ) (n₂ C K : ℕ),
    2 ≤ K ∧ (8 : ℝ) / ε ≤ (K : ℝ) ∧
    n₀ ≤ n₂ ∧ n₂ ≤ C ∧ 0 < n₂ ∧
    (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + 3 * ε / 4) ∧
    VortexBottomClauseR2 ε f n₂ C K ∧ VortexDescentClauseR3 f n₂ K ∧
    CoverDownStepClauseLarge ε f n₂ K

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1000000 in
/-- **§10, from the fused interface of the cover-down route.**

This is `BKLO.nearOptimalConclusion_of_fusedR3`, with the cover-down step taken from the interface
instead of being manufactured from the reservoir clause and the nibble.  Since that was the only
use of the two classical inputs in `BKLO/MainRepaired3.lean`, they are gone from the hypotheses. -/
theorem nearOptimalConclusion_of_coverDownEngineR3 (hEng : VortexCoverDownEngineR3) :
    NearOptimalConclusion := by
  classical
  intro ε hε
  -- it is enough to treat a small `ε`
  set e : ℝ := min ε (1 / 100) with hedef
  have he : 0 < e := lt_min hε (by norm_num)
  have he' : e ≤ 1 / 100 := min_le_right _ _
  have hee : e ≤ ε := min_le_left _ _
  obtain ⟨f, n₂, C, K, hK, hKε, -, hn₂C, hn₂pos, hfbd, hbot, hdesc, hCD⟩ :=
    hEng (e / 4) (by linarith) (by linarith) 0
  -- `K` is large: `32/e ≤ K`
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have h2 : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have hKe : (32 : ℝ) ≤ (K : ℝ) * e := by
    have h1 : (8 : ℝ) / (e / 4) ≤ (K : ℝ) := hKε
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < e / 4)] at h1
    linarith
  have hf : ∀ s : ℕ, n₂ ≤ s → (9 / 10 + e / 4 / 4) + e / 4 / 8 ≤ f s := by
    intro s hs
    have := (hfbd s hs).1
    linarith
  refine ⟨C, ?_⟩
  intro Ka
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (2 * (Ka : ℝ) / e)
  refine ⟨max (max n₂ N₁) (16 * (K * K * C) + 16 * (K * K * (2 * Ka)) + 16 * (2 * Ka)
    + 16 * K + 16), ?_⟩
  intro V _ _ G _ hn hδ0
  have hn₂ : n₂ ≤ Fintype.card V := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN : N₁ ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnbig : 16 * (K * K * C) + 16 * (K * K * (2 * Ka)) + 16 * (2 * Ka) + 16 * K + 16
      ≤ Fintype.card V := le_trans (le_max_right _ _) hn
  have hδ : (9 / 10 + e) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) := by
    have hc : (0 : ℝ) ≤ (Fintype.card V : ℝ) := by positivity
    nlinarith
  have hKsmall : (Ka : ℝ) ≤ e / 2 * (Fintype.card V : ℝ) := by
    have h1 : 2 * (Ka : ℝ) / e < (Fintype.card V : ℝ) :=
      lt_of_lt_of_le hN₁ (by exact_mod_cast hnN)
    rw [div_lt_iff₀ he] at h1
    linarith
  -- the ambient edge set
  have hcardu : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
  have hEuniv : G.edgeFinset ⊆ cliqueEdges (Finset.univ : Finset V) := by
    intro e' he'
    refine mem_cliqueEdgesV.2 ⟨fun x _ => Finset.mem_univ x, ?_⟩
    exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.1 he')
  have hnd : ∀ e' ∈ G.edgeFinset, ¬ e'.IsDiag := fun e' he' => (mem_cliqueEdgesV.1 (hEuniv he')).2
  have hdegG : ∀ v, G.degree v = edeg G.edgeFinset v := by
    intro v
    rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter v, edeg]
  have hdegbig : ∀ v ∈ (Finset.univ : Finset V),
      (9 / 10 + e) * ((Finset.univ : Finset V).card : ℝ) ≤ (edeg G.edgeFinset v : ℝ) := by
    intro v _
    rw [hcardu, ← hdegG v]
    refine hδ.trans ?_
    exact_mod_cast G.minDegree_le_degree v
  -- the bottom set and its exceptional set, chosen before the reserved edge set
  obtain ⟨U, B, hUS, -, hUB, hUn₂, hUC, hBcard, hUlink⟩ :=
    hbot (Finset.univ : Finset V) G.edgeFinset (by rw [hcardu]; exact hn₂) hEuniv
      (by
        intro v hv
        refine le_trans ?_ (hdegbig v hv)
        have : (0 : ℝ) ≤ ((Finset.univ : Finset V).card : ℝ) := by positivity
        nlinarith)
  rw [hcardu] at hBcard
  refine ⟨U, hUC, ?_⟩
  intro A hAsub hAcard hAdisj hAdiv
  set F : Finset (Sym2 V) := G.edgeFinset \ A with hF
  have hFuniv : F ⊆ cliqueEdges (Finset.univ : Finset V) := (Finset.sdiff_subset).trans hEuniv
  have hFdeg : ∀ v ∈ (Finset.univ : Finset V),
      (9 / 10 + e / 2) * ((Finset.univ : Finset V).card : ℝ) ≤ (edeg F v : ℝ) := by
    intro v hv
    have h1 := hdegbig v hv
    have h2 : (edeg G.edgeFinset v : ℝ) ≤ (edeg F v : ℝ) + (A.card : ℝ) := by
      exact_mod_cast edeg_le_edeg_sdiff_add (E := G.edgeFinset) (A := A) v
    have h3 : (A.card : ℝ) ≤ (Ka : ℝ) := by exact_mod_cast hAcard
    rw [hcardu] at h1 ⊢
    linarith
  -- the top level of the vortex avoids the exceptional set and the vertices met by `A`
  set Met : Finset V := (Finset.univ : Finset V).filter (fun v => 0 < edeg A v) with hMet
  set D : Finset V := B ∪ (Met \ U) with hD
  have hDcard : D.card ≤ B.card + 2 * Ka := by
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left ?_ _)
    refine le_trans (le_trans (Finset.card_le_card Finset.sdiff_subset)
      (card_vertices_met_le A)) ?_
    omega
  have hbKK : B.card ≤ K * K * B.card := Nat.le_mul_of_pos_left _ (by positivity)
  have hKKd : K * K * D.card ≤ K * K * B.card + K * K * (2 * Ka) := by
    calc K * K * D.card ≤ K * K * (B.card + 2 * Ka) := Nat.mul_le_mul_left _ hDcard
      _ = K * K * B.card + K * K * (2 * Ka) := by ring
  have h4KK : 4 * (K * K * B.card) ≤ Fintype.card V := by
    have : 4 * K * K * B.card = 4 * (K * K * B.card) := by ring
    omega
  have hd1 : 2 * D.card + 2 * K ≤ Fintype.card V := by omega
  have hd2 : K * K * C + D.card + 1 ≤ Fintype.card V := by omega
  have hd3 : K * K * D.card + D.card ≤ Fintype.card V := by omega
  have hUD : Disjoint U D := by
    refine Finset.disjoint_union_right.2 ⟨hUB, ?_⟩
    exact Finset.disjoint_right.2 fun v hv => (Finset.mem_sdiff.1 hv).2
  -- links into the bottom set are undamaged outside `D`
  have hlinkF : ∀ v : V, v ∉ D → resLink G.edgeFinset U v ⊆ resLink F U v := by
    intro v hvD a ha
    obtain ⟨haU, haE⟩ := mem_resLink.1 ha
    refine mem_resLink.2 ⟨haU, Finset.mem_sdiff.2 ⟨haE, fun hA => ?_⟩⟩
    by_cases hvU : v ∈ U
    · refine Finset.disjoint_left.1 hAdisj hA (mem_cliqueEdgesV.2 ⟨?_, hnd _ haE⟩)
      intro z hz
      rcases Sym2.mem_iff.1 hz with rfl | rfl
      exacts [hvU, haU]
    · have hpos : 0 < edeg A v :=
        Finset.card_pos.2 ⟨s(v, a), Finset.mem_filter.2 ⟨hA, by simp⟩⟩
      exact hvD (Finset.mem_union_right _
        (Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ v, hpos⟩, hvU⟩))
  -- the size window of the top level
  obtain ⟨hKm, hmm, hKC, h2m⟩ :=
    vortex_top_level_sizes (K := K) (C := C) (n := Fintype.card V) (d := D.card) hK hd1 hd2
  set m : ℕ := (Fintype.card V - D.card) / K with hm
  have hKD : K * D.card ≤ m := by
    rw [hm, Nat.le_div_iff_mul_le (by omega : 0 < K)]
    have hassoc : K * D.card * K = K * K * D.card := by ring
    omega
  have hUm : U.card ≤ m := le_trans hUC (le_trans (Nat.le_mul_of_pos_left C (by omega)) hKC)
  have hKU : K * U.card ≤ m := le_trans (Nat.mul_le_mul_left K hUC) hKC
  have hmn₂ : n₂ ≤ m := le_trans hUn₂ hUm
  -- the schedule at the top scale, and the surplus of the host graph over it
  have hfuniv : f (Finset.univ : Finset V).card ≤ 9 / 10 + 3 * (e / 4) / 4 :=
    (hfbd (Finset.univ : Finset V).card (by rw [hcardu]; exact hn₂)).2
  have hfa : f (Finset.univ : Finset V).card ≤ 9 / 10 + e / 2 := by linarith
  have ha1 : (9 : ℝ) / 10 + e / 2 ≤ 1 := by linarith
  have hbotD : ∀ v ∈ (Finset.univ : Finset V) \ D,
      f U.card * (U.card : ℝ) ≤ ((resLink F U v).card : ℝ) := by
    intro v hv
    have hvD : v ∉ D := (Finset.mem_sdiff.1 hv).2
    have hvB : v ∉ B := fun h => hvD (Finset.mem_union_left _ h)
    refine le_trans (hUlink v (Finset.mem_sdiff.2 ⟨Finset.mem_univ v, hvB⟩)) ?_
    exact_mod_cast Finset.card_le_card (hlinkF v hvD)
  obtain ⟨W₁, hUW₁, hW₁S, hW₁D, hcard₁, hgrade₁, hweak₁⟩ :=
    hdesc (Finset.univ : Finset V) U D F m (9 / 10 + e / 2) hUn₂ hUS hUD hKU hKD
      (by rw [hcardu]; exact h2m) (by rw [hcardu]; exact hmm) hfa ha1 hFuniv hFdeg hbotD
  -- the surplus of the host graph pays for the avoidance set
  have hlink₁ : ∀ v ∈ (Finset.univ : Finset V) \ D,
      f m * (m : ℝ) ≤ ((resLink F W₁ v).card : ℝ) := by
    intro v hv
    have hg := hgrade₁ v hv
    have hmR : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have huR : (0 : ℝ) ≤ (U.card : ℝ) := Nat.cast_nonneg _
    have hdR : (0 : ℝ) ≤ (D.card : ℝ) := Nat.cast_nonneg _
    have hKU' : (K : ℝ) * (U.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hKU
    have hKD' : (K : ℝ) * (D.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hKD
    have h32u : 32 * (U.card : ℝ) ≤ e * (m : ℝ) := by nlinarith only [hKU', hKe, huR, he]
    have h32d : 32 * (D.card : ℝ) ≤ e * (m : ℝ) := by nlinarith only [hKD', hKe, hdR, he]
    have hsurp : e / 4 ≤ 9 / 10 + e / 2 - f (Finset.univ : Finset V).card := by linarith
    have hmu : (m : ℝ) / 2 ≤ (m : ℝ) - (U.card : ℝ) := by nlinarith only [hKU', huR, hKe, he, he', hmR]
    have hprod : e / 4 * ((m : ℝ) / 2)
        ≤ (9 / 10 + e / 2 - f (Finset.univ : Finset V).card) * ((m : ℝ) - (U.card : ℝ)) :=
      mul_le_mul hsurp hmu (by positivity) (by linarith)
    have hem : (0 : ℝ) ≤ e * (m : ℝ) := by positivity
    nlinarith only [hg, hprod, h32u, h32d, hem, hmR, huR, hdR, hsurp, hmu, he]
  -- the invariants of the recursion at the top level
  have hndF : ∀ e' ∈ F, ¬ e'.IsDiag := fun e' he' => (mem_cliqueEdgesV.1 (hFuniv he')).2
  have hbetween : ∀ v ∈ (Finset.univ : Finset V),
      (9 / 10 + e / 4 / 4) * (W₁.card : ℝ) ≤ ((resLink F W₁ v).card : ℝ) := by
    intro v hv
    have h1 := hweak₁ v hv
    have h2 : (9 / 10 + e / 4 / 2 : ℝ) ≤ f m := (hfbd m hmn₂).1
    have h3 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have h4 : (2 : ℝ) / (K : ℝ) ≤ e / 16 := by
      rw [div_le_iff₀ hKpos]
      linarith only [hKe]
    rw [hcard₁]
    nlinarith only [h1, h2, h3, h4, hKpos, he]
  have hclean : ∀ v ∈ W₁,
      f W₁.card * (W₁.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W₁) v : ℝ) := by
    intro v hv
    rw [edeg_inter_cliqueEdges_eq_card_resLink hv hndF, hcard₁]
    exact hlink₁ v (Finset.mem_sdiff.2 ⟨Finset.mem_univ v, Finset.disjoint_left.1 hW₁D hv⟩)
  have hbottom : ∀ v ∈ W₁, f U.card * (U.card : ℝ) ≤ ((resLink F U v).card : ℝ) := fun v hv =>
    hbotD v (Finset.mem_sdiff.2 ⟨Finset.mem_univ v, Finset.disjoint_left.1 hW₁D hv⟩)
  have hFdeg₁ : ∀ v ∈ (Finset.univ : Finset V),
      (9 / 10 + e / 4 / 4) * ((Finset.univ : Finset V).card : ℝ) ≤ (edeg F v : ℝ) := by
    intro v hv
    have h1 := hFdeg v hv
    have h3 : (0 : ℝ) ≤ ((Finset.univ : Finset V).card : ℝ) := by positivity
    nlinarith only [h1, h3, he]
  -- the descent clause of the recursion (no forbidden vertices below the top level)
  have hdescU : ∀ (W : Finset V) (E' : Finset (Sym2 V)) (mm : ℕ),
      U ⊆ W → K * U.card ≤ mm → 2 * mm ≤ W.card → W.card ≤ K * K * mm → E' ⊆ cliqueEdges W →
      (∀ v ∈ W, f W.card * (W.card : ℝ) ≤ (edeg E' v : ℝ)) →
      (∀ v ∈ W, f U.card * (U.card : ℝ) ≤ ((resLink E' U v).card : ℝ)) →
      ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ W'.card = mm ∧
        ∀ v ∈ W, f mm * (mm : ℝ) ≤ ((resLink E' W' v).card : ℝ) := by
    intro W E' mm h1 h2 h3 h4 h5 h6 h7
    have hUW : U.card ≤ K * U.card := Nat.le_mul_of_pos_left _ (by omega)
    have hn₂W : n₂ ≤ W.card := by omega
    have hf1 : f W.card ≤ 1 := by
      have := (hfbd W.card hn₂W).2
      linarith
    exact descent_of_R3 hdesc W U E' mm hUn₂ h1 h2 h3 h4 hf1 h5 h6 h7
  obtain ⟨P, hP, hcover⟩ :=
    coverDown_vortex_denseR2Large (U := U) (n₀ := n₂) hK (fun W W' W'' F' => hCD W W' W'' F')
      hdescU hf le_rfl hn₂pos hUn₂ (Finset.univ : Finset V).card
      (Finset.univ : Finset V) W₁ F le_rfl hFuniv hAdiv hFdeg₁ hUW₁ hW₁S
      (by rw [hcard₁, hcardu]; exact hKm) (by rw [hcard₁, hcardu]; exact hmm)
      (Or.inr (by rw [hcard₁]; exact hKU))
      hclean hbetween hbottom
  exact ⟨P, hP.1, hP.2.1, hP.2.2, hcover⟩

/-! ### The residual cover-down step, and the assembly of the interface -/

/-- **The residual cover-down step.**  The one clause of `BKLO.VortexCoverDownEngineR3` that is not
proved here: one cover-down step, for every small `ε`, for *some* ratio `K` (large, as the vortex
needs), for every schedule confined to the window `[9/10 + ε/2, 9/10 + 3ε/4]` and every scale above
a threshold that may depend on `ε` and `K`.  As in the classical cover-down input
`BKLO.CoverDownK3Div` the ratio `K` is *provided* by the clause, not demanded of it.  It quantifies
over nothing the engine chooses, so it is not circular: the schedule, the window `C` and the scale
`n₂` are chosen after it, in `BKLO.vortexCoverDownEngineR3_of_residual`. -/
def CoverDownStepResidualLarge : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∃ K n₃ : ℕ, 800 ≤ K ∧ (8 : ℝ) / ε ≤ (K : ℝ) ∧
    ∀ (f : ℕ → ℝ) (n₂ : ℕ), n₃ ≤ n₂ →
      (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + 3 * ε / 4) →
      CoverDownStepClauseLarge ε f n₂ K

set_option maxHeartbeats 1000000 in
/-- **The fused interface of the cover-down route, from the residual cover-down step.**

All three vortex clauses are supplied here, with the explicit power-law schedule of
`BKLO/ScheduleR3.lean`: the window `BKLO.powerSchedule_window`, the bottom clause
`BKLO.vortexBottomClauseR2_of_schedule_window`, and the *proved* thrice-repaired descent clause
`BKLO.vortexDescentClauseR3_of_powerSchedule`.  The window `C := 2n₂` is taken large enough for the
amplitude condition `250√K ≤ (ε/4)C^{1/4}` of the descent clause and for the bottom clause's
requirement `1000k ≤ εn₂`. -/
theorem vortexCoverDownEngineR3_of_residual (h : CoverDownStepResidualLarge) :
    VortexCoverDownEngineR3 := by
  intro ε hε hε' n₀
  -- the constants
  obtain ⟨K, n₃, hK800, hKε, hn₃⟩ := h ε hε hε'
  have hK2 : 2 ≤ K := le_trans (by norm_num) hK800
  have hKR : (800 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK800
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  -- the exponent of the bottom clause
  obtain ⟨k₀, hk₀⟩ :=
    exists_pow_lt_of_lt_one (show (0 : ℝ) < ε / (16 * (K : ℝ) * (K : ℝ)) by positivity)
      (show (1 : ℝ) - ε < 1 by linarith)
  set k : ℕ := max 1 k₀ with hkdef
  have hk1 : 1 ≤ k := le_max_left _ _
  have hkσ : (1 - ε) ^ k ≤ ε / (16 * (K : ℝ) * (K : ℝ)) :=
    le_of_lt (lt_of_le_of_lt
      (pow_le_pow_of_le_one (by linarith) (by linarith) (le_max_right 1 k₀)) hk₀)
  -- the two size thresholds
  obtain ⟨A, hA⟩ := exists_nat_gt ((1000 * Real.sqrt (K : ℝ) / ε) ^ 4)
  obtain ⟨Bn, hBn⟩ := exists_nat_gt ((1000 : ℝ) * (k : ℝ) / ε)
  set n₂ : ℕ := max (max n₀ n₃) (max A (max Bn 1)) with hn₂def
  set C : ℕ := 2 * n₂ with hCdef
  have hn₂1 : 1 ≤ n₂ :=
    le_trans (le_trans (le_max_right Bn 1) (le_max_right _ _)) (le_max_right _ _)
  have hn₂pos : 0 < n₂ := hn₂1
  have hCpos : 0 < C := by omega
  have hn₂R : (1 : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast hn₂1
  have hn₀ : n₀ ≤ n₂ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hn₃le : n₃ ≤ n₂ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hAle : A ≤ n₂ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hBnle : Bn ≤ n₂ :=
    le_trans (le_trans (le_max_left Bn 1) (le_max_right _ _)) (le_max_right _ _)
  -- the schedule window
  have hwin : ∀ s : ℕ, n₂ ≤ s →
      9 / 10 + ε / 2 ≤ powerSchedule ε C s ∧ powerSchedule ε C s ≤ 9 / 10 + 3 * ε / 4 :=
    fun s _ => powerSchedule_window hε hCpos s
  -- the amplitude condition
  have hamp : 250 * Real.sqrt (K : ℝ) ≤ ε / 4 * qrt (C : ℝ) := by
    have hACR : ((1000 : ℝ) * Real.sqrt (K : ℝ) / ε) ^ 4 ≤ (C : ℝ) := by
      have h1 : (A : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast hAle
      have h2 : (n₂ : ℝ) ≤ (C : ℝ) := by
        have : (n₂ : ℕ) ≤ C := by omega
        exact_mod_cast this
      linarith
    have hq : 1000 * Real.sqrt (K : ℝ) / ε ≤ qrt (C : ℝ) :=
      le_qrt_of (by positivity) hACR
    have := mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ ε / 4 by linarith)
    calc 250 * Real.sqrt (K : ℝ) = ε / 4 * (1000 * Real.sqrt (K : ℝ) / ε) := by
          field_simp; ring
      _ ≤ ε / 4 * qrt (C : ℝ) := this
  -- the bottom-clause threshold
  have hkn₂ : (1000 : ℝ) * (k : ℝ) ≤ ε * (n₂ : ℝ) := by
    have h1 : (Bn : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast hBnle
    have h2 : (1000 : ℝ) * (k : ℝ) / ε < (n₂ : ℝ) := lt_of_lt_of_le hBn h1
    rw [div_lt_iff₀ hε] at h2
    linarith
  refine ⟨powerSchedule ε C, n₂, C, K, hK2, hKε, hn₀, by omega, hn₂pos, hwin, ?_, ?_, ?_⟩
  · exact vortexBottomClauseR2_of_schedule_window hε hε' hK2 hk1
      (fun s _ hsC => le_of_eq (powerSchedule_of_le hCpos hsC)) hkσ hkn₂ (by omega)
  · refine vortexDescentClauseR3_of_powerSchedule hε hε' hK800 hn₂pos ?_ hamp
    calc C = 2 * n₂ := hCdef
      _ ≤ K * n₂ := Nat.mul_le_mul_right _ (by omega)
  · exact hn₃ (powerSchedule ε C) n₂ hn₃le hwin

/-! ### The new residual is implied by the old one -/

/-- **The cover-down step residual is no stronger than the reservoir residual.**  Dross's
threshold, the dense max-degree nibble and `BKLO.ReservoirClauseResidual4` — the residual of the
reservoir route — imply `BKLO.CoverDownStepResidualLarge`, through
`BKLO.coverDownStepR_of_reservoirClauseR4`.  So the cover-down route is a genuine relaxation: it
asks only that the step be performed *somehow*, not that it be performed by a vertex-sparse
apex-abundant reservoir. -/
theorem coverDownStepResidualLarge_of_reservoir4 (hDross : FracTriangleThreshold)
    (hNib : FracToApproxMaxDegDense) (hRes : ReservoirClauseResidual4) :
    CoverDownStepResidualLarge := by
  intro ε hε hε'
  set K : ℕ := max 800 ⌈(8 : ℝ) / ε⌉₊ with hKdef
  have hK800 : 800 ≤ K := le_max_left _ _
  have hKε : (8 : ℝ) / ε ≤ (K : ℝ) := by
    have h1 : (8 : ℝ) / ε ≤ (⌈(8 : ℝ) / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(8 : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast Nat.le_max_right 800 ⌈(8 : ℝ) / ε⌉₊
    linarith
  obtain ⟨η, n₃, hη, hn₃⟩ := hRes ε hε hε' K hK800 hKε
  obtain ⟨Nnib, hnib⟩ := nibbleMaxDeg_of_inputs_dense hDross hNib hη
  refine ⟨K, max n₃ Nnib, hK800, hKε, ?_⟩
  intro f n₂ hn₂ hwin
  exact coverDownStepR_of_reservoirClauseR4 hε hKε (le_trans (le_max_right n₃ Nnib) hn₂)
    (fun S E hS hES hdeg => hnib S E hS hES hdeg)
    (hn₃ f n₂ (le_trans (le_max_left n₃ Nnib) hn₂) hwin)

end BKLO
