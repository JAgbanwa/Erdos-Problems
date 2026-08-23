/-
# The two-sided grid design, **re-sized to an eighth**

`BKLO.exists_reservoir_twosided_structured` (`BKLO/ReservoirDesignTwoSided.lean`) equalizes the
reserved link of an outer vertex at `c = q - ⌊q/4⌋` places of every class of its region, because a
quarter is all `IsGridSharpReservoir.classBalancedSharp` gives.  `BKLO/AX2CellStepRepair.lean`
shows that this leaves the quarter condition of `BKLO.exists_cell_balanced_leftovers` no room for a
perturbation, and prescribes the re-sizing: an *eighth*.

This file re-runs the equalization on the eighth-balanced sharp design of
`BKLO.exists_reservoir_sharp_structured_eighth` (`BKLO/ReservoirDesignSharpEighth.lean`), with
`c = q - ⌊q/8⌋`.  Everything the construction used of the quarter gets *better*, so nothing else
changes: the two-sided balance, the apex abundance and the sparsity are exactly as before, and the
reserved link now keeps **seven eighths** of every class of its region.

* `BKLO.IsGridTwoSidedReservoirEighth` — the re-sized design;
* `BKLO.IsGridTwoSidedReservoirEighth.exists_sizes_eighth` — its two sizes, with `7q ≤ 8c`;
* `BKLO.exists_reservoir_twosided_structured_eighth` — the construction.

Everything here is `sorry`-free.
-/
import BKLO.ReservoirDesignTwoSided
import BKLO.ReservoirDesignSharpEighth

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- **A two-sided grid reservoir, re-sized to an eighth.**  A two-sided design in which every
vertex of `W` misses at most an *eighth* of every class, and the reserved link of an outer vertex
keeps *seven eighths* of every class of its region. -/
structure IsGridTwoSidedReservoirEighth (ε : ℝ) (K : ℕ) (W W' W'' : Finset V)
    (F R : Finset (Sym2 V)) (C : ℕ → Finset V) (x y : V → ℕ)
    : Prop extends IsGridTwoSidedReservoir ε K W W' W'' F R C x y where
  /-- **every vertex of `W` misses at most an eighth of each class.** -/
  classBalancedEighth : ∀ v ∈ W, ∀ i < gridSize ε K * gridSize ε K,
    8 * ((nonNbrs F W' v ∩ C i).card) ≤ (C i).card
  /-- **the reserved link keeps seven eighths of every class of its region.** -/
  linkClassGeEighth : ∀ u ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x u) (y u),
    7 * (C i).card ≤ 8 * ((resLink R W' u ∩ C i).card)

variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ}

/-- **The two sizes of a re-sized two-sided design**: the common class size `q` and the common
number `c` of places the reserved links keep in each class of their region, with `7q ≤ 8c ≤ 8q`. -/
theorem IsGridTwoSidedReservoirEighth.exists_sizes_eighth
    (hgrid : IsGridTwoSidedReservoirEighth ε K W W' W'' F R C x y) :
    ∃ q c : ℕ, (∀ i < gridSize ε K * gridSize ε K, (C i).card = q) ∧
      (∀ u ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x u) (y u),
        (resLink R W' u ∩ C i).card = c) ∧ 7 * q ≤ 8 * c ∧ c ≤ q := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hhh : 0 < h * h := Nat.mul_pos hhpos hhpos
  have hqcard : ∀ i < h * h, (C i).card = (C 0).card := fun i hi =>
    hgrid.classCardEq i hi 0 hhh
  by_cases hD : (W \ W').Nonempty
  · obtain ⟨u₀, hu₀⟩ := hD
    have hx₀ : x u₀ < h := hgrid.rowLt u₀ hu₀
    have hy₀ : y u₀ < h := hgrid.colLt u₀ hu₀
    set i₀ : ℕ := x u₀ * h + y u₀ with hi₀def
    have hi₀ : i₀ ∈ gridIdx h (x u₀) (y u₀) := mem_gridIdx.2 (Or.inl ⟨y u₀, hy₀, rfl⟩)
    refine ⟨(C 0).card, (resLink R W' u₀ ∩ C i₀).card, hqcard, ?_, ?_, ?_⟩
    · intro u hu i hi
      exact (hgrid.linkClassEq u hu i hi u₀ hu₀ i₀ hi₀)
    · have h1 := hgrid.linkClassGeEighth u₀ hu₀ i₀ hi₀
      rwa [hqcard i₀ (gridIdx_lt hx₀ hy₀ hi₀)] at h1
    · have h1 : (resLink R W' u₀ ∩ C i₀).card ≤ (C i₀).card :=
        Finset.card_le_card Finset.inter_subset_right
      rwa [hqcard i₀ (gridIdx_lt hx₀ hy₀ hi₀)] at h1
  · refine ⟨(C 0).card, (C 0).card, hqcard, ?_, by omega, le_rfl⟩
    intro u hu
    exact absurd ⟨u, hu⟩ hD

set_option maxHeartbeats 2000000 in
/-- **The re-sized two-sided grid design.**  The eighth-balanced sharp design of
`BKLO.exists_reservoir_sharp_structured_eighth`, with the reserved link of every outer vertex
equalized over the classes of its region: exactly `c = q - ⌊q/8⌋` neighbours are kept in each of
the `2h - 1` classes.  The row part and the column part of every reserved link then have exactly
the same size, and the link keeps seven eighths of every class of its region — which is the room
the cell prescription of `BKLO.exists_cell_balanced_leftovers_of_resized` needs. -/
theorem exists_reservoir_twosided_structured_eighth
    {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 100) {K : ℕ} (hKε : (8 : ℝ) / ε ≤ (K : ℝ))
    {W W' W'' : Finset V} {F : Finset (Sym2 V)}
    (hW''W' : W'' ⊆ W')
    (hKW' : K * W'.card ≤ W.card) (hW'K : W.card ≤ K * K * W'.card)
    (hKW'' : K * W''.card ≤ W'.card)
    (hres : ∀ v ∈ W, (9 / 10 + ε / 4) * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ))
    (hN : reservoirThresholdEighth ε K ≤ W.card) :
    ∃ (R : Finset (Sym2 V)) (C : ℕ → Finset V) (x y : V → ℕ),
      R ⊆ F ∧ IsCrossing W W' R ∧
      (∀ v : V, (edeg R v : ℝ) ≤ ε / 8 * (W.card : ℝ)) ∧
      (∀ u ∈ W \ W', ∀ v ∈ W \ W',
        2 * cleanEta ε K * (W.card : ℝ) ≤ ((apexes R W' u v).card : ℝ)) ∧
      (∀ a ∈ W', (edeg R a : ℝ) ≤ ε / 16 * (W'.card : ℝ)) ∧
      IsGridTwoSidedReservoirEighth ε K W W' W'' F R C x y := by
  classical
  obtain ⟨R₀, C, x, y, hR₀F, _hcross₀, hsparse₀, _hapex₀, hsparse₀', hgrid⟩ :=
    exists_reservoir_sharp_structured_eighth hε hε' hKε hW''W' hKW' hW'K hKW'' hres hN
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hhh : 0 < h * h := Nat.mul_pos hhpos hhpos
  have hKpos : 0 < K := by
    by_contra hcon
    push_neg at hcon
    have hK0 : K = 0 := by omega
    have h1 : (8 : ℝ) / ε ≤ 0 := by rw [hK0] at hKε; simpa using hKε
    have h2 : (0 : ℝ) < 8 / ε := by positivity
    linarith
  -- ## the common class size `q` and the reserved size `c`
  set q : ℕ := (C 0).card with hqdef
  have hqcard : ∀ i < h * h, (C i).card = q := by
    intro i hi
    exact hgrid.classCardEq i (by rw [← hhdef]; exact hi) 0 (by rw [← hhdef]; exact hhh)
  have hq3 : 3 * t ≤ 4 * q := by
    have h1 := hgrid.classCardGe 0 (by rw [← hhdef]; exact hhh)
    rw [← htdef, ← hqdef] at h1
    exact h1
  set c : ℕ := q - q / 8 with hcdef
  have h7q8c : 7 * q ≤ 8 * c := by omega
  have h3q4c : 3 * q ≤ 4 * c := by omega
  have hcq : c ≤ q := by omega
  have hCdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j) := by
    intro i hi j hj hij
    exact hgrid.classDisjoint i (by rw [← hhdef]; exact hi) j (by rw [← hhdef]; exact hj) hij
  -- ## `c` places are available in every class of the region
  have hclass_avail : ∀ u ∈ W \ W', ∀ i ∈ gridIdx h (x u) (y u),
      c ≤ (resLink R₀ W' u ∩ C i).card := by
    intro u hu i hi
    have hxu : x u < h := hgrid.rowLt u hu
    have hyu : y u < h := hgrid.colLt u hu
    have hilt : i < h * h := gridIdx_lt hxu hyu hi
    have hqi : (C i).card = q := hqcard i hilt
    have hbal : 8 * ((nonNbrs F W' u ∩ C i).card) ≤ (C i).card :=
      hgrid.classBalancedEighth u (Finset.mem_sdiff.1 hu).1 i (by rw [← hhdef]; exact hilt)
    have hsplit : (C i \ nonNbrs F W' u).card + (nonNbrs F W' u ∩ C i).card = (C i).card := by
      rw [Finset.inter_comm]
      exact Finset.card_sdiff_add_card_inter _ _
    have hCireg : C i ⊆ gridRegion h C (x u) (y u) := by
      rw [gridRegion_eq_biUnion]
      intro z hz
      exact Finset.mem_biUnion.2 ⟨i, hi, hz⟩
    have hsub : C i \ nonNbrs F W' u ⊆ resLink R₀ W' u ∩ C i := by
      intro z hz
      obtain ⟨hzi, hzn⟩ := Finset.mem_sdiff.1 hz
      have hzW' : z ∈ W' := hgrid.classSubset i (by rw [← hhdef]; exact hilt) hzi
      have hzF : z ∈ resLink F W' u := by
        by_contra hcon
        exact hzn (Finset.mem_sdiff.2 ⟨hzW', hcon⟩)
      refine Finset.mem_inter.2 ⟨?_, hzi⟩
      rw [hgrid.link u hu]
      exact Finset.mem_inter.2 ⟨hzF, hCireg hzi⟩
    have := Finset.card_le_card hsub
    omega
  -- ## the equalized links
  have hAex : ∀ (u : V) (i : ℕ), ∃ A : Finset V, A ⊆ resLink R₀ W' u ∩ C i ∧
      (u ∈ W \ W' → i ∈ gridIdx h (x u) (y u) → A.card = c) := by
    intro u i
    by_cases hcond : u ∈ W \ W' ∧ i ∈ gridIdx h (x u) (y u)
    · obtain ⟨A, hA, hAcard⟩ :=
        Finset.exists_subset_card_eq (hclass_avail u hcond.1 i hcond.2)
      exact ⟨A, hA, fun _ _ => hAcard⟩
    · exact ⟨∅, Finset.empty_subset _, fun h1 h2 => absurd ⟨h1, h2⟩ hcond⟩
  choose A hAsub hAcard using hAex
  set Keep : V → Finset V := fun u => (gridIdx h (x u) (y u)).biUnion (A u) with hKeepdef
  set R : Finset (Sym2 V) := (W \ W').biUnion (fun u => (Keep u).image (fun a => s(u, a)))
    with hRdef
  have hmemR : ∀ e : Sym2 V, e ∈ R ↔ ∃ u ∈ W \ W', ∃ a ∈ Keep u, e = s(u, a) := by
    intro e
    simp only [hRdef, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨u, hu, a, ha, rfl⟩; exact ⟨u, hu, a, ha, rfl⟩
    · rintro ⟨u, hu, a, ha, rfl⟩; exact ⟨u, hu, a, ha, rfl⟩
  have hKeepLink : ∀ u : V, Keep u ⊆ resLink R₀ W' u := by
    intro u a ha
    obtain ⟨i, _, hai⟩ := Finset.mem_biUnion.1 ha
    exact (Finset.mem_inter.1 (hAsub u i hai)).1
  have hKeepW' : ∀ u : V, Keep u ⊆ W' := fun u a ha => (mem_resLink.1 (hKeepLink u ha)).1
  have hRR₀ : R ⊆ R₀ := by
    intro e he
    obtain ⟨u, _, a, ha, rfl⟩ := (hmemR e).1 he
    exact (mem_resLink.1 (hKeepLink u ha)).2
  have hRF : R ⊆ F := hRR₀.trans hR₀F
  have hedeg_mono : ∀ v : V, edeg R v ≤ edeg R₀ v := by
    intro v
    exact Finset.card_le_card (Finset.filter_subset_filter _ hRR₀)
  -- the reserved link of an outer vertex is exactly the equalized set
  have hlink : ∀ u ∈ W \ W', resLink R W' u = Keep u := by
    intro u hu
    have huW' : u ∉ W' := (Finset.mem_sdiff.1 hu).2
    ext a
    rw [mem_resLink]
    constructor
    · rintro ⟨haW', haR⟩
      obtain ⟨u', hu', a', ha', heq⟩ := (hmemR _).1 haR
      have ha'W' : a' ∈ W' := hKeepW' u' ha'
      rcases Sym2.eq_iff.1 heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1; subst h2; exact ha'
      · exact absurd (h1 ▸ ha'W') huW'
    · intro ha
      exact ⟨hKeepW' u ha, (hmemR _).2 ⟨u, hu, a, ha, rfl⟩⟩
  -- the trace of the link on a class of the region
  have htrace : ∀ u ∈ W \ W', ∀ i ∈ gridIdx h (x u) (y u), resLink R W' u ∩ C i = A u i := by
    intro u hu i hi
    have hxu : x u < h := hgrid.rowLt u hu
    have hyu : y u < h := hgrid.colLt u hu
    rw [hlink u hu]
    ext z
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hzK, hzi⟩
      obtain ⟨j, hj, hzj⟩ := Finset.mem_biUnion.1 hzK
      by_cases hij : j = i
      · rwa [hij] at hzj
      · exact absurd hzi (Finset.disjoint_left.1
          (hCdisj j (gridIdx_lt hxu hyu hj) i (gridIdx_lt hxu hyu hi) hij)
          ((Finset.mem_inter.1 (hAsub u j hzj)).2))
    · intro hz
      exact ⟨Finset.mem_biUnion.2 ⟨i, hi, hz⟩, (Finset.mem_inter.1 (hAsub u i hz)).2⟩
  have htracecard : ∀ u ∈ W \ W', ∀ i ∈ gridIdx h (x u) (y u),
      (resLink R W' u ∩ C i).card = c := by
    intro u hu i hi
    rw [htrace u hu i hi, hAcard u i hu hi]
  refine ⟨R, C, x, y, hRF, ?_, ?_, ?_, ?_, ?_⟩
  · -- `R` is crossing
    intro e he
    obtain ⟨u, hu, a, ha, rfl⟩ := (hmemR e).1 he
    exact ⟨u, hu, a, hKeepW' u ha, rfl⟩
  · -- sparsity
    intro v
    exact le_trans (by exact_mod_cast hedeg_mono v) (hsparse₀ v)
  · -- apex abundance
    intro u hu v hv
    have hxu : x u < h := hgrid.rowLt u hu
    have hyv : y v < h := hgrid.colLt v hv
    set i : ℕ := x u * h + y v with hidef
    have hi : i < h * h := grid_idx_lt hxu hyv
    have hiu : i ∈ gridIdx h (x u) (y u) := mem_gridIdx.2 (Or.inl ⟨y v, hyv, rfl⟩)
    have hiv : i ∈ gridIdx h (x v) (y v) := mem_gridIdx.2 (Or.inr ⟨x u, hxu, rfl⟩)
    have hsub : A u i ∩ A v i ⊆ apexes R W' u v := by
      intro z hz
      obtain ⟨hzu, hzv⟩ := Finset.mem_inter.1 hz
      refine mem_apexes.2 ⟨(mem_resLink.1 ((hKeepLink u) (Finset.mem_biUnion.2 ⟨i, hiu, hzu⟩))).1,
        (hmemR _).2 ⟨u, hu, z, Finset.mem_biUnion.2 ⟨i, hiu, hzu⟩, rfl⟩,
        (hmemR _).2 ⟨v, hv, z, Finset.mem_biUnion.2 ⟨i, hiv, hzv⟩, rfl⟩⟩
    -- the two equalized traces are large subsets of one class
    have hAu : (A u i).card = c := hAcard u i hu hiu
    have hAv : (A v i).card = c := hAcard v i hv hiv
    have hAuC : A u i ⊆ C i := (hAsub u i).trans Finset.inter_subset_right
    have hAvC : A v i ⊆ C i := (hAsub v i).trans Finset.inter_subset_right
    have hunion : (A u i ∪ A v i).card ≤ q := by
      have h1 : (A u i ∪ A v i).card ≤ (C i).card :=
        Finset.card_le_card (Finset.union_subset hAuC hAvC)
      rw [hqcard i hi] at h1
      exact h1
    have hinclexcl : (A u i ∪ A v i).card + (A u i ∩ A v i).card = (A u i).card + (A v i).card :=
      Finset.card_union_add_card_inter _ _
    have hI : q ≤ 2 * (A u i ∩ A v i).card := by omega
    have hap : (A u i ∩ A v i).card ≤ (apexes R W' u v).card := Finset.card_le_card hsub
    -- the numerical bound
    have h8 := eight_cleanEta_mul_card_le hgrid.toIsGridSharpReservoir hKpos
    rw [← htdef] at h8
    have hq3r : 3 * (t : ℝ) ≤ 4 * (q : ℝ) := by exact_mod_cast hq3
    have hIr : (q : ℝ) ≤ 2 * ((A u i ∩ A v i).card : ℝ) := by exact_mod_cast hI
    have hapr : ((A u i ∩ A v i).card : ℝ) ≤ ((apexes R W' u v).card : ℝ) := by exact_mod_cast hap
    linarith
  · -- sparsity at the scale of `W'`
    intro a ha
    exact le_trans (by exact_mod_cast hedeg_mono a) (hsparse₀' a ha)
  · -- the two-sided grid structure
    refine
      { classSubset := hgrid.classSubset, classAvoid := hgrid.classAvoid,
        classCardLe := hgrid.classCardLe, classCardGe := hgrid.classCardGe,
        classCardEq := hgrid.classCardEq, classDisjoint := hgrid.classDisjoint,
        classBalancedSharp := hgrid.classBalancedSharp, rowLt := hgrid.rowLt,
        colLt := hgrid.colLt, rowFibre := hgrid.rowFibre, colFibre := hgrid.colFibre,
        cellFibre := hgrid.cellFibre, classPos := hgrid.classPos,
        classVolume := hgrid.classVolume, outerVolume := hgrid.outerVolume,
        classBalancedEighth := hgrid.classBalancedEighth,
        linkSubset := ?_, linkClassGe := ?_, linkClassEq := ?_, rowColBalanced := ?_,
        linkClassGeEighth := ?_ }
    · intro u hu a ha
      rw [hlink u hu] at ha
      obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.1 ha
      obtain ⟨haR₀, haC⟩ := Finset.mem_inter.1 (hAsub u i hai)
      refine Finset.mem_inter.2 ⟨?_, ?_⟩
      · exact mem_resLink.2 ⟨(mem_resLink.1 haR₀).1, hR₀F (mem_resLink.1 haR₀).2⟩
      · rw [gridRegion_eq_biUnion]
        exact Finset.mem_biUnion.2 ⟨i, hi, haC⟩
    · intro u hu i hi
      rw [htracecard u hu i hi,
        hqcard i (gridIdx_lt (hgrid.rowLt u hu) (hgrid.colLt u hu) hi)]
      exact h3q4c
    · intro u hu i hi v hv j hj
      rw [htracecard u hu i hi, htracecard v hv j hj]
    · intro u hu
      have hxu : x u < h := hgrid.rowLt u hu
      have hyu : y u < h := hgrid.colLt u hu
      rw [card_inter_gridRowPart hxu hCdisj, card_inter_gridColPart hyu hCdisj]
      have hrow : ∀ j ∈ Finset.range h, (resLink R W' u ∩ C (x u * h + j)).card = c := by
        intro j hj
        exact htracecard u hu _ (mem_gridIdx.2 (Or.inl ⟨j, Finset.mem_range.1 hj, rfl⟩))
      have hcol : ∀ i ∈ Finset.range h, (resLink R W' u ∩ C (i * h + y u)).card = c := by
        intro i hi
        exact htracecard u hu _ (mem_gridIdx.2 (Or.inr ⟨i, Finset.mem_range.1 hi, rfl⟩))
      rw [Finset.sum_congr rfl hrow, Finset.sum_congr rfl hcol]
    · intro u hu i hi
      rw [htracecard u hu i hi,
        hqcard i (gridIdx_lt (hgrid.rowLt u hu) (hgrid.colLt u hu) hi)]
      exact h7q8c


end BKLO
