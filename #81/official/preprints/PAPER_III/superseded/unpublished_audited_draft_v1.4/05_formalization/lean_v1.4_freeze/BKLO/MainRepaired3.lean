/-
# §10 and the main theorem, from the **thrice-repaired** fused interface.

`BKLO/MainRepaired2.lean` derives the main theorem from `BKLO.VortexReservoirEngineR2`; that
interface is false (`BKLO.not_vortexDescentClauseR2`), so that derivation, though proved, is
vacuous.  This file redoes it from the thrice-repaired interface `BKLO.VortexReservoirEngineR3`
of `BKLO/EngineR3.lean`, whose vortex clauses are theorems.

Two things change with respect to `BKLO/MainRepaired2.lean`.

* The interface is only asked for `ε ≤ 1/100`; §10 for a small `ε` implies §10 for every larger
  one, since its hypothesis (a minimum degree of `(9/10 + ε)n`) is monotone in `ε`.  In fact the
  interface is invoked at `ε/4`, so that the loss `2/K` of the second grade of the descent clause
  is still covered by the between-levels density the cover-down step needs.
* The descent clause is now told the *actual* density `a = 9/10 + ε/2` of the host graph, which
  exceeds the density `f n ≤ 9/10 + 3ε/16` the schedule prescribes.  The surplus pays for the
  avoidance set `D` of the top level — the exceptional set of the bottom clause together with the
  vertices met by the reserved edge set — which is what the false clause
  `BKLO.VortexDescentClauseR2` asked for free.  Below the top level the avoidance set is empty and
  the surplus is zero, so the recursion `BKLO.coverDown_vortex_denseR2` is consumed unchanged
  through `BKLO.descent_of_R3`.

Everything here is `sorry`-free.  The assumed inputs are the three classical ones — Dross's
fractional threshold, the maximum-degree nibble, Dirac's theorem — together with the
thrice-repaired §10 interface `BKLO.VortexReservoirEngineR3`.
-/
import BKLO.EngineR3Assembly
import BKLO.MainRepaired2

open Finset

namespace BKLO

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1000000 in
/-- **§10, from the thrice-repaired fused interface and the classical inputs.** -/
theorem nearOptimalConclusion_of_fusedR3 (hDross : FracTriangleThreshold)
    (hNib : FracToApproxMaxDeg) (hEng : VortexReservoirEngineR3) : NearOptimalConclusion := by
  classical
  intro ε hε
  -- it is enough to treat a small `ε`
  set e : ℝ := min ε (1 / 100) with hedef
  have he : 0 < e := lt_min hε (by norm_num)
  have he' : e ≤ 1 / 100 := min_le_right _ _
  have hee : e ≤ ε := min_le_left _ _
  -- the nibble threshold, as a function of its leftover parameter
  have hNex : ∀ η : ℝ, ∃ n : ℕ, 0 < η →
      ∀ {V : Type} [DecidableEq V] (S : Finset V) (E : Finset (Sym2 V)),
        n ≤ S.card → E ⊆ cliqueEdges S → (∀ v ∈ S, (9 / 10 : ℝ) * S.card ≤ edeg E v) →
        ∃ P : Finset (Finset V), TriFamilyIn E P ∧
          ∀ v : V, (edeg (E \ famEdges P) v : ℝ) ≤ η * (S.card : ℝ) := by
    intro η
    by_cases hη : 0 < η
    · obtain ⟨n, hn⟩ := nibbleMaxDeg_of_inputs hDross hNib hη
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => absurd h hη⟩
  choose N hN using hNex
  obtain ⟨f, n₂, C, K, η, hK, hKε, hη, -, hNn₂, hn₂C, hn₂pos, hfbd, hbot, hdesc, hres⟩ :=
    hEng (e / 4) (by linarith) (by linarith) 0 N
  have hnib : ∀ {V : Type} [DecidableEq V] (S : Finset V) (E : Finset (Sym2 V)),
      N η ≤ S.card → E ⊆ cliqueEdges S → (∀ v ∈ S, (9 / 10 : ℝ) * S.card ≤ edeg E v) →
      ∃ P : Finset (Finset V), TriFamilyIn E P ∧
        ∀ v : V, (edeg (E \ famEdges P) v : ℝ) ≤ η * (S.card : ℝ) := hN η hη
  -- `K` is large: `32/e ≤ K`
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have h2 : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have hKe : (32 : ℝ) ≤ (K : ℝ) * e := by
    have h1 : (8 : ℝ) / (e / 4) ≤ (K : ℝ) := hKε
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < e / 4)] at h1
    linarith
  -- one cover-down step
  have hCD : ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
      n₂ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
      K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
      F ⊆ cliqueEdges W → TriDivisible F →
      (∀ v ∈ W, (9 / 10 + e / 4 / 4) * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
      (∀ v ∈ W', f W'.card * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
      (∀ v ∈ W, (9 / 10 + e / 4 / 4) * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn F P ∧
        F \ famEdges P ⊆ cliqueEdges W' ∧
        F ∩ cliqueEdges W'' ⊆ F \ famEdges P ∧
        (∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
          ≤ (edeg (F \ famEdges P) v : ℝ) + e / 4 / 8 * (W'.card : ℝ)) ∧
        ∀ v ∈ W', ((resLink F W'' v).card : ℝ)
          ≤ ((resLink (F \ famEdges P) W'' v).card : ℝ) + e / 4 / 8 * (W''.card : ℝ) :=
    coverDownStepR_of_reservoirClauseR (by linarith) hKε hNn₂ hnib hres
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
    linarith only [hg, hprod, h32u, h32d, hem, hmR, huR, hdR, hsurp, hmu, he]
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
    coverDown_vortex_denseR2 (U := U) (n₀ := n₂) hK (fun W W' W'' F' => hCD W W' W'' F')
      hdescU hf le_rfl hn₂pos hUn₂ (Finset.univ : Finset V).card
      (Finset.univ : Finset V) W₁ F le_rfl hFuniv hAdiv hFdeg₁ hUW₁ hW₁S
      (by rw [hcard₁, hcardu]; exact hKm) (by rw [hcard₁, hcardu]; exact hmm)
      (Or.inr (by rw [hcard₁]; exact hKU))
      hclean hbetween hbottom
  exact ⟨P, hP.1, hP.2.1, hP.2.2, hcover⟩

/-- **§10 (interface), from the thrice-repaired fused interface.** -/
theorem nearOptimalDecomp_of_fusedR3 (hNib : FracToApproxMaxDeg) (hEng : VortexReservoirEngineR3) :
    NearOptimalDecomp :=
  fun hDross _ _ => nearOptimalConclusion_of_fusedR3 hDross hNib hEng

/-- **Main theorem (AX2 half of Erdős #81), from the classical inputs and the thrice-repaired §10
interface.**  For every `ε > 0`, every sufficiently large triangle-divisible graph with
`δ(G) ≥ (9/10 + ε)|V|` has a triangle decomposition. -/
theorem triangle_decomposition_of_inputs_repaired3
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hEng : VortexReservoirEngineR3) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs hDross (fracToApprox_of_maxDeg hNib) hDirac
    (nearOptimalDecomp_of_fusedR3 hNib hEng)

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the residual
reservoir clause.**  All the vortex clauses of the §10 interface — the schedule window, the bottom
clause and the descent clause — are theorems here (`BKLO/BottomClause.lean`,
`BKLO/LevelSampling.lean`, `BKLO/ScheduleR3.lean`); the only remaining hypothesis beyond the three
classical inputs is `BKLO.ReservoirClauseResidual`. -/
theorem triangle_decomposition_of_inputs_and_reservoir
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hRes : ReservoirClauseResidual) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_repaired3 hDross hNib hDirac
    (vortexReservoirEngineR3_of_reservoir hRes)

end BKLO
