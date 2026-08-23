/-
# §10 and the main theorem, from the **repaired** fused interface.

`BKLO/MainUnconditional.lean` derives the main theorem from `BKLO.VortexReservoirEngine`; that
interface is false (`BKLO.not_vortexReservoirEngine`), so the derivation, though proved, is
vacuous.  This file redoes it from the repaired interface `BKLO.VortexReservoirEngineR` of
`BKLO/ReservoirRepaired.lean`.

The route is *not* through `BKLO.VortexEngineRatio`, and the reason is instructive.  That interface
records the bottom set only through a predicate `good V U (E ∩ cliqueEdges U)` of the edge set
*inside* `U`; the repaired reservoir clause, however, needs to know that every vertex of the
current level is dense *into* the next one, and on the last step the next level is the bottom set
`U`.  That is information about edges **between** `U` and its complement, which `GoodPred` cannot
carry.  So `NearOptimalConclusion` is proved here directly:

* the repaired bottom clause chooses `U` inside the whole vertex set, with every vertex of the
  graph dense into `U`;
* the reserved edge set `A` (bounded, but by a bound chosen *after* the size bound `C` of `U`) can
  destroy the links into `U` of the at most `2|A|` vertices it meets; the top level of the vortex
  is therefore chosen to avoid those vertices, which is what the avoidance set of the repaired
  descent clause `BKLO.VortexDescentClauseR` is for.  Vertices of `U` itself need not be avoided:
  `A` spans no edge inside `U`;
* the recursion `BKLO.coverDown_vortex_denseR` then runs down the vortex.

Everything here is `sorry`-free.  The assumed inputs are the three classical ones — Dross's
fractional threshold, the maximum-degree nibble, Dirac's theorem — together with the repaired §10
interface `BKLO.VortexReservoirEngineR`.
-/
import BKLO.VortexEngineFusedR
import BKLO.VortexMain

open Finset

namespace BKLO

/-! ### Arithmetic of the top level -/

/-- The size window for the top level of the vortex, chosen inside the complement of a set of `d`
forbidden vertices. -/
theorem vortex_top_level_sizes {K C n d : ℕ} (hK : 2 ≤ K) (hd : 2 * d + 2 * K ≤ n)
    (hn : K * K * C + d + 1 ≤ n) :
    K * ((n - d) / K) ≤ n ∧ n ≤ K * K * ((n - d) / K) ∧
      K * C ≤ (n - d) / K ∧ 2 * ((n - d) / K) + d ≤ n := by
  have hKpos : 0 < K := by omega
  set m := (n - d) / K with hm
  have hdm : K * m + (n - d) % K = n - d := Nat.div_add_mod _ _
  have hmod : (n - d) % K < K := Nat.mod_lt _ hKpos
  have h2p : 2 * (K * m) ≤ K * (K * m) := Nat.mul_le_mul_right _ hK
  have hassoc : K * K * m = K * (K * m) := by ring
  have h2m : 2 * m ≤ K * m := Nat.mul_le_mul_right _ hK
  have hKC : K * C ≤ m := by
    rw [hm, Nat.le_div_iff_mul_le hKpos]
    have hcomm : K * C * K = K * K * C := by ring
    omega
  exact ⟨by omega, by omega, hKC, by omega⟩

/-! ### Counting the vertices met by a bounded edge set -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An edge meets at most two vertices. -/
theorem card_filter_mem_le_two (e : Sym2 V) :
    ((Finset.univ : Finset V).filter (fun x => x ∈ e)).card ≤ 2 := by
  classical
  induction e using Sym2.ind with
  | _ a b =>
    have hsub : (Finset.univ : Finset V).filter (fun x => x ∈ s(a, b)) ⊆ {a, b} := by
      intro x hx
      rcases Sym2.mem_iff.1 (Finset.mem_filter.1 hx).2 with rfl | rfl <;> simp
    exact le_trans (Finset.card_le_card hsub)
      (le_trans (Finset.card_insert_le _ _) (by simp))

/-- A set of `k` edges meets at most `2k` vertices. -/
theorem card_vertices_met_le (A : Finset (Sym2 V)) :
    ((Finset.univ : Finset V).filter (fun v => 0 < edeg A v)).card ≤ 2 * A.card := by
  classical
  have hsub : (Finset.univ : Finset V).filter (fun v => 0 < edeg A v) ⊆
      A.biUnion (fun e => (Finset.univ : Finset V).filter (fun x => x ∈ e)) := by
    intro v hv
    obtain ⟨e, he⟩ := Finset.card_pos.1 (Finset.mem_filter.1 hv).2
    obtain ⟨heA, hve⟩ := Finset.mem_filter.1 he
    exact Finset.mem_biUnion.2 ⟨e, heA, Finset.mem_filter.2 ⟨Finset.mem_univ v, hve⟩⟩
  calc ((Finset.univ : Finset V).filter (fun v => 0 < edeg A v)).card
      ≤ (A.biUnion (fun e => (Finset.univ : Finset V).filter (fun x => x ∈ e))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ e ∈ A, ((Finset.univ : Finset V).filter (fun x => x ∈ e)).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ A, 2 := Finset.sum_le_sum fun e _ => card_filter_mem_le_two e
    _ = 2 * A.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-! ### §10 from the repaired interface -/

/-- **§10, from the repaired fused interface and the classical inputs.**  Dross's threshold and the
maximum-degree nibble supply the bulk of each cover-down; the repaired interface supplies the
levels of the vortex and the reservoir; the greedy cover-down and the link cover finish each step;
`BKLO.coverDown_vortex_denseR` runs the recursion down the vortex. -/
theorem nearOptimalConclusion_of_fusedR (hDross : FracTriangleThreshold)
    (hNib : FracToApproxMaxDeg) (hEng : VortexReservoirEngineR) : NearOptimalConclusion := by
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
  refine ⟨max (max n₂ N₁) (8 * (K * K * C + 2 * Ka + K) + 8), ?_⟩
  intro V _ _ G _ hn hδ
  have hn₂ : n₂ ≤ Fintype.card V := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN : N₁ ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnbig : 8 * (K * K * C + 2 * Ka + K) + 8 ≤ Fintype.card V := le_trans (le_max_right _ _) hn
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
  have hd1 : 2 * D.card + 2 * K ≤ Fintype.card V := by omega
  have hd2 : K * K * C + D.card + 1 ≤ Fintype.card V := by omega
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
  have hUm : U.card ≤ m := le_trans hUC (le_trans (Nat.le_mul_of_pos_left C (by omega)) hKC)
  have hdegf : ∀ v ∈ (Finset.univ : Finset V),
      f (Finset.univ : Finset V).card * ((Finset.univ : Finset V).card : ℝ) ≤ (edeg F v : ℝ) := by
    intro v hv
    have h1 := hFdeg v hv
    have h2 := (hfbd (Finset.univ : Finset V).card (by rw [hcardu]; exact hn₂)).2
    have h3 : (0 : ℝ) ≤ ((Finset.univ : Finset V).card : ℝ) := by positivity
    nlinarith
  obtain ⟨W₁, hUW₁, hW₁S, hW₁D, hcard₁, hlink₁⟩ :=
    hdesc (Finset.univ : Finset V) U D F m hUn₂ hUS hUD hUm
      (by rw [hcardu]; exact h2m) (by rw [hcardu]; exact hmm) hFuniv hdegf
  -- the invariants of the recursion at the top level
  have hndF : ∀ e ∈ F, ¬ e.IsDiag := fun e he => (mem_cliqueEdgesV.1 (hFuniv he)).2
  have hc₁ : ∀ s : ℕ, n₂ ≤ s → (9 / 10 + ε / 2 / 4 : ℝ) ≤ f s := by
    intro s hs
    have := (hfbd s hs).1
    linarith
  have hbetween : ∀ v ∈ (Finset.univ : Finset V),
      (9 / 10 + ε / 2 / 4) * (W₁.card : ℝ) ≤ ((resLink F W₁ v).card : ℝ) := by
    intro v hv
    have h1 := hlink₁ v hv
    have h2 : (9 / 10 + ε / 2 / 4 : ℝ) ≤ f m := hc₁ m (le_trans hUn₂ hUm)
    have h3 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    rw [hcard₁]
    nlinarith
  have hclean : ∀ v ∈ W₁,
      f W₁.card * (W₁.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W₁) v : ℝ) := by
    intro v hv
    rw [edeg_inter_cliqueEdges_eq_card_resLink hv hndF, hcard₁]
    exact hlink₁ v (Finset.mem_univ v)
  have hbottom : ∀ v ∈ W₁, f U.card * (U.card : ℝ) ≤ ((resLink F U v).card : ℝ) := by
    intro v hv
    have hvD : v ∉ D := Finset.disjoint_left.1 hW₁D hv
    have hvB : v ∉ B := fun h => hvD (Finset.mem_union_left _ h)
    refine le_trans (hUlink v (Finset.mem_sdiff.2 ⟨Finset.mem_univ v, hvB⟩)) ?_
    exact_mod_cast Finset.card_le_card (hlinkF v hvD)
  have hFdeg₁ : ∀ v ∈ (Finset.univ : Finset V),
      (9 / 10 + ε / 2 / 4) * ((Finset.univ : Finset V).card : ℝ) ≤ (edeg F v : ℝ) := by
    intro v hv
    have h1 := hFdeg v hv
    have h3 : (0 : ℝ) ≤ ((Finset.univ : Finset V).card : ℝ) := by positivity
    nlinarith
  -- the descent clause of the recursion (no forbidden vertices below the top level)
  have hdescU : ∀ (W : Finset V) (E' : Finset (Sym2 V)) (mm : ℕ),
      U ⊆ W → U.card ≤ mm → 2 * mm ≤ W.card → W.card ≤ K * K * mm → E' ⊆ cliqueEdges W →
      (∀ v ∈ W, f W.card * (W.card : ℝ) ≤ (edeg E' v : ℝ)) →
      ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ W'.card = mm ∧
        ∀ v ∈ W, f mm * (mm : ℝ) ≤ ((resLink E' W' v).card : ℝ) := by
    intro W E' mm h1 h2 h3 h4 h5 h6
    obtain ⟨W', hUW', hW'W, -, hcard, hlink⟩ :=
      hdesc W U ∅ E' mm hUn₂ h1 (Finset.disjoint_empty_right _) h2 (by simpa using h3) h4 h5 h6
    exact ⟨W', hUW', hW'W, hcard, hlink⟩
  obtain ⟨P, hP, hcover⟩ :=
    coverDown_vortex_denseR (U := U) (n₀ := n₂) hK (fun W W' W'' F' => hCD W W' W'' F')
      hdescU hf le_rfl hn₂pos hUn₂ (Finset.univ : Finset V).card
      (Finset.univ : Finset V) W₁ F le_rfl hFuniv hAdiv hFdeg₁ hUW₁ hW₁S
      (by rw [hcard₁, hcardu]; exact hKm) (by rw [hcard₁, hcardu]; exact hmm)
      (Or.inr (by rw [hcard₁]; exact le_trans (Nat.mul_le_mul_left K hUC) hKC))
      hclean hbetween hbottom
  exact ⟨P, hP.1, hP.2.1, hP.2.2, hcover⟩

/-- **§10 (interface), from the repaired fused interface.** -/
theorem nearOptimalDecomp_of_fusedR (hNib : FracToApproxMaxDeg) (hEng : VortexReservoirEngineR) :
    NearOptimalDecomp :=
  fun hDross _ _ => nearOptimalConclusion_of_fusedR hDross hNib hEng

/-- **Main theorem (AX2 half of Erdős #81), from the classical inputs and the repaired §10
interface.**  For every `ε > 0`, every sufficiently large triangle-divisible graph with
`δ(G) ≥ (9/10 + ε)|V|` has a triangle decomposition. -/
theorem triangle_decomposition_of_inputs_repaired
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hEng : VortexReservoirEngineR) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs hDross (fracToApprox_of_maxDeg hNib) hDirac
    (nearOptimalDecomp_of_fusedR hNib hEng)

end BKLO
