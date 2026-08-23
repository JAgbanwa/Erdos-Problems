/-
# §10 and the main theorem, from the **twice-repaired** fused interface.

`BKLO/MainRepaired.lean` derives the main theorem from `BKLO.VortexReservoirEngineR`; that
interface is false as well (`BKLO.not_vortexReservoirEngineR`, whose defect is in the descent
clause), so that derivation, though proved, is vacuous.  This file redoes it from the
twice-repaired interface `BKLO.VortexReservoirEngineR2` of `BKLO/ReservoirRepaired2.lean`.

Two things change with respect to `BKLO/MainRepaired.lean`.

* The avoidance set `D` of the top level — the exceptional set of the bottom clause together with
  the vertices met by the reserved edge set `A` — must now be `K` times smaller than the top
  level, which is why the bottom clause is asked for an exceptional set of density `1/(4K²)` and
  why the size threshold below is larger.
* The descent clause is now told that every vertex outside `D` is dense into the bottom set (which
  is exactly what the bottom clause has just provided), and delivers a *graded* conclusion: full
  density into the new level outside `D`, and density `f(m) - 1/K` at the vertices of `D`.  The
  first grade feeds the internal density of the top level, the second the between-levels density,
  which needs only `9/10 + ε/8`.

Everything here is `sorry`-free.  The assumed inputs are the three classical ones — Dross's
fractional threshold, the maximum-degree nibble, Dirac's theorem — together with the twice-repaired
§10 interface `BKLO.VortexReservoirEngineR2`.
-/
import BKLO.VortexEngineFusedR2
import BKLO.MainRepaired

open Finset

namespace BKLO

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### §10 from the repaired interface -/

set_option maxHeartbeats 1000000 in
/-- **§10, from the repaired fused interface and the classical inputs.**  Dross's threshold and the
maximum-degree nibble supply the bulk of each cover-down; the repaired interface supplies the
levels of the vortex and the reservoir; the greedy cover-down and the link cover finish each step;
`BKLO.coverDown_vortex_denseR2` runs the recursion down the vortex. -/
theorem nearOptimalConclusion_of_fusedR2 (hDross : FracTriangleThreshold)
    (hNib : FracToApproxMaxDeg) (hEng : VortexReservoirEngineR2) : NearOptimalConclusion := by
  classical
  intro ε hε
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
    hEng (ε / 2) (by linarith) 0 N
  have hnib : ∀ {V : Type} [DecidableEq V] (S : Finset V) (E : Finset (Sym2 V)),
      N η ≤ S.card → E ⊆ cliqueEdges S → (∀ v ∈ S, (9 / 10 : ℝ) * S.card ≤ edeg E v) →
      ∃ P : Finset (Finset V), TriFamilyIn E P ∧
        ∀ v : V, (edeg (E \ famEdges P) v : ℝ) ≤ η * (S.card : ℝ) := hN η hη
  -- one cover-down step
  have hCD : ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
      n₂ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
      K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
      F ⊆ cliqueEdges W → TriDivisible F →
      (∀ v ∈ W, (9 / 10 + ε / 2 / 4) * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
      (∀ v ∈ W', f W'.card * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
      (∀ v ∈ W, (9 / 10 + ε / 2 / 4) * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn F P ∧
        F \ famEdges P ⊆ cliqueEdges W' ∧
        F ∩ cliqueEdges W'' ⊆ F \ famEdges P ∧
        (∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
          ≤ (edeg (F \ famEdges P) v : ℝ) + ε / 2 / 8 * (W'.card : ℝ)) ∧
        ∀ v ∈ W', ((resLink F W'' v).card : ℝ)
          ≤ ((resLink (F \ famEdges P) W'' v).card : ℝ) + ε / 2 / 8 * (W''.card : ℝ) :=
    coverDownStepR_of_reservoirClauseR (by linarith) hKε hNn₂ hnib hres
  have hf : ∀ s : ℕ, n₂ ≤ s → (9 / 10 + ε / 2 / 4) + ε / 2 / 8 ≤ f s := by
    intro s hs
    have := (hfbd s hs).1
    linarith
  refine ⟨C, ?_⟩
  intro Ka
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (2 * (Ka : ℝ) / ε)
  refine ⟨max (max n₂ N₁) (16 * (K * K * C) + 16 * (K * K * (2 * Ka)) + 16 * (2 * Ka)
    + 16 * K + 16), ?_⟩
  intro V _ _ G _ hn hδ
  have hn₂ : n₂ ≤ Fintype.card V := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN : N₁ ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnbig : 16 * (K * K * C) + 16 * (K * K * (2 * Ka)) + 16 * (2 * Ka) + 16 * K + 16
      ≤ Fintype.card V := le_trans (le_max_right _ _) hn
  have hKsmall : (Ka : ℝ) ≤ ε / 2 * (Fintype.card V : ℝ) := by
    have h1 : 2 * (Ka : ℝ) / ε < (Fintype.card V : ℝ) :=
      lt_of_lt_of_le hN₁ (by exact_mod_cast hnN)
    rw [div_lt_iff₀ hε] at h1
    linarith
  -- the ambient edge set
  have hcardu : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
  have hEuniv : G.edgeFinset ⊆ cliqueEdges (Finset.univ : Finset V) := by
    intro e he
    refine mem_cliqueEdgesV.2 ⟨fun x _ => Finset.mem_univ x, ?_⟩
    exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.1 he)
  have hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag := fun e he => (mem_cliqueEdgesV.1 (hEuniv he)).2
  have hdegG : ∀ v, G.degree v = edeg G.edgeFinset v := by
    intro v
    rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter v, edeg]
  have hdegbig : ∀ v ∈ (Finset.univ : Finset V),
      (9 / 10 + ε) * ((Finset.univ : Finset V).card : ℝ) ≤ (edeg G.edgeFinset v : ℝ) := by
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
      (9 / 10 + ε / 2) * ((Finset.univ : Finset V).card : ℝ) ≤ (edeg F v : ℝ) := by
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
  have hdegf : ∀ v ∈ (Finset.univ : Finset V),
      f (Finset.univ : Finset V).card * ((Finset.univ : Finset V).card : ℝ) ≤ (edeg F v : ℝ) := by
    intro v hv
    have h1 := hFdeg v hv
    have h2 := (hfbd (Finset.univ : Finset V).card (by rw [hcardu]; exact hn₂)).2
    have h3 : (0 : ℝ) ≤ ((Finset.univ : Finset V).card : ℝ) := by positivity
    nlinarith
  have hKU : K * U.card ≤ m := le_trans (Nat.mul_le_mul_left K hUC) hKC
  have hbotD : ∀ v ∈ (Finset.univ : Finset V) \ D,
      f U.card * (U.card : ℝ) ≤ ((resLink F U v).card : ℝ) := by
    intro v hv
    have hvD : v ∉ D := (Finset.mem_sdiff.1 hv).2
    have hvB : v ∉ B := fun h => hvD (Finset.mem_union_left _ h)
    refine le_trans (hUlink v (Finset.mem_sdiff.2 ⟨Finset.mem_univ v, hvB⟩)) ?_
    exact_mod_cast Finset.card_le_card (hlinkF v hvD)
  obtain ⟨W₁, hUW₁, hW₁S, hW₁D, hcard₁, hlink₁, hweak₁⟩ :=
    hdesc (Finset.univ : Finset V) U D F m hUn₂ hUS hUD hKU hKD
      (by rw [hcardu]; exact h2m) (by rw [hcardu]; exact hmm) hFuniv hdegf hbotD
  -- the invariants of the recursion at the top level
  have hndF : ∀ e ∈ F, ¬ e.IsDiag := fun e he => (mem_cliqueEdgesV.1 (hFuniv he)).2
  have hc₁ : ∀ s : ℕ, n₂ ≤ s → (9 / 10 + ε / 2 / 4 : ℝ) ≤ f s := by
    intro s hs
    have := (hfbd s hs).1
    linarith
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have hKinv : (1 : ℝ) / (K : ℝ) ≤ ε / 2 / 8 := by
    rw [div_le_iff₀ hKpos]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < ε / 2)] at hKε
    nlinarith
  have hbetween : ∀ v ∈ (Finset.univ : Finset V),
      (9 / 10 + ε / 2 / 4) * (W₁.card : ℝ) ≤ ((resLink F W₁ v).card : ℝ) := by
    intro v hv
    have h1 := hweak₁ v hv
    have h2 : (9 / 10 + ε / 2 / 2 : ℝ) ≤ f m := (hfbd m (le_trans hUn₂ hUm)).1
    have h3 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    rw [hcard₁]
    nlinarith
  have hclean : ∀ v ∈ W₁,
      f W₁.card * (W₁.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W₁) v : ℝ) := by
    intro v hv
    rw [edeg_inter_cliqueEdges_eq_card_resLink hv hndF, hcard₁]
    exact hlink₁ v (Finset.mem_sdiff.2 ⟨Finset.mem_univ v, Finset.disjoint_left.1 hW₁D hv⟩)
  have hbottom : ∀ v ∈ W₁, f U.card * (U.card : ℝ) ≤ ((resLink F U v).card : ℝ) := fun v hv =>
    hbotD v (Finset.mem_sdiff.2 ⟨Finset.mem_univ v, Finset.disjoint_left.1 hW₁D hv⟩)
  have hFdeg₁ : ∀ v ∈ (Finset.univ : Finset V),
      (9 / 10 + ε / 2 / 4) * ((Finset.univ : Finset V).card : ℝ) ≤ (edeg F v : ℝ) := by
    intro v hv
    have h1 := hFdeg v hv
    have h3 : (0 : ℝ) ≤ ((Finset.univ : Finset V).card : ℝ) := by positivity
    nlinarith
  -- the descent clause of the recursion (no forbidden vertices below the top level)
  have hdescU : ∀ (W : Finset V) (E' : Finset (Sym2 V)) (mm : ℕ),
      U ⊆ W → K * U.card ≤ mm → 2 * mm ≤ W.card → W.card ≤ K * K * mm → E' ⊆ cliqueEdges W →
      (∀ v ∈ W, f W.card * (W.card : ℝ) ≤ (edeg E' v : ℝ)) →
      (∀ v ∈ W, f U.card * (U.card : ℝ) ≤ ((resLink E' U v).card : ℝ)) →
      ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ W'.card = mm ∧
        ∀ v ∈ W, f mm * (mm : ℝ) ≤ ((resLink E' W' v).card : ℝ) :=
    fun W E' mm h1 h2 h3 h4 h5 h6 h7 => descent_of_R2 hdesc W U E' mm hUn₂ h1 h2 h3 h4 h5 h6 h7
  obtain ⟨P, hP, hcover⟩ :=
    coverDown_vortex_denseR2 (U := U) (n₀ := n₂) hK (fun W W' W'' F' => hCD W W' W'' F')
      hdescU hf le_rfl hn₂pos hUn₂ (Finset.univ : Finset V).card
      (Finset.univ : Finset V) W₁ F le_rfl hFuniv hAdiv hFdeg₁ hUW₁ hW₁S
      (by rw [hcard₁, hcardu]; exact hKm) (by rw [hcard₁, hcardu]; exact hmm)
      (Or.inr (by rw [hcard₁]; exact le_trans (Nat.mul_le_mul_left K hUC) hKC))
      hclean hbetween hbottom
  exact ⟨P, hP.1, hP.2.1, hP.2.2, hcover⟩

/-- **§10 (interface), from the twice-repaired fused interface.** -/
theorem nearOptimalDecomp_of_fusedR2 (hNib : FracToApproxMaxDeg) (hEng : VortexReservoirEngineR2) :
    NearOptimalDecomp :=
  fun hDross _ _ => nearOptimalConclusion_of_fusedR2 hDross hNib hEng

/-- **Main theorem (AX2 half of Erdős #81), from the classical inputs and the twice-repaired §10
interface.**  For every `ε > 0`, every sufficiently large triangle-divisible graph with
`δ(G) ≥ (9/10 + ε)|V|` has a triangle decomposition. -/
theorem triangle_decomposition_of_inputs_repaired2
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hEng : VortexReservoirEngineR2) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs hDross (fracToApprox_of_maxDeg hNib) hDirac
    (nearOptimalDecomp_of_fusedR2 hNib hEng)

end BKLO
