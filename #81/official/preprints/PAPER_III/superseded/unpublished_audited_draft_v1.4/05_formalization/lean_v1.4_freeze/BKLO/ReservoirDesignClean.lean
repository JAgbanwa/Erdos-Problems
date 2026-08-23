/-
# The grid design with the protected level removed.

Both refutations of the pairing demand of AX2 §10 exploit the same weakness: the classes of the
grid design may *contain* protected vertices.

* `BKLO.not_gridPairingResidual` takes the protected level to be a whole designed region;
* `BKLO.not_gridPairingResidualFull` puts a fixed number of protected vertices in every class, and
  counts: every outer vertex must then pair each of the `(2h-1)c` protected vertices of its link
  with a partner inside its region, and the classes — a tenth of the pool — cannot carry that load
  inside the `loadInner` budget.

Both disappear if the classes avoid the protected level altogether, and that costs nothing: this
file *derives* such a design from `BKLO.exists_reservoir_full_structured` by deleting `W''`
from every class and deleting from the reservoir every edge that meets `W''`.  What has to be
checked is that the deletion does not destroy the two quantitative exports of the design:

* the classes stay large — `BKLO.IsGridFullReservoir.protectedBalanced` says the protected level
  takes at most a quarter of each class, so at least `3t/4` survives;
* the apexes stay abundant — for two outer vertices `u`, `v` the class of the cell `(x u, y v)`
  lies in the region of `u` *and* in the region of `v`, and it loses at most a quarter to `W''`
  and a quarter to each of the two non-neighbourhoods, so at least `t/4` apexes survive, which is
  exactly what `BKLO.IsGridReservoir.outerVolume` needs for the abundance `η|W|`.

The design so obtained is `BKLO.IsGridCleanReservoir`, and it is what
`BKLO/GridPairingClean.lean` states the remaining residual of AX2 §10 at.

Everything here is `sorry`-free.
-/
import BKLO.ReservoirDesignFull
import BKLO.GridRegionCard

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Two more facts about designed regions -/

/-- A class of the row of a cell lies in its region. -/
theorem class_subset_gridRegion_row {h : ℕ} {C : ℕ → Finset V} {p q j : ℕ} (hj : j < h) :
    C (p * h + j) ⊆ gridRegion h C p q :=
  fun _ ha => Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, ha⟩)

/-- A class of the column of a cell lies in its region. -/
theorem class_subset_gridRegion_col {h : ℕ} {C : ℕ → Finset V} {p q i : ℕ} (hi : i < h) :
    C (i * h + q) ⊆ gridRegion h C p q :=
  fun _ ha => Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 hi, ha⟩)

/-- Deleting a set from every class deletes it from every region. -/
theorem gridRegion_sdiff (h : ℕ) (C : ℕ → Finset V) (B : Finset V) (p q : ℕ) :
    gridRegion h (fun i => C i \ B) p q = gridRegion h C p q \ B := by
  ext a
  simp only [gridRegion, Finset.mem_union, Finset.mem_biUnion, Finset.mem_sdiff,
    Finset.mem_range]
  constructor
  · rintro (⟨j, hj, haj, haB⟩ | ⟨i, hi, hai, haB⟩)
    · exact ⟨Or.inl ⟨j, hj, haj⟩, haB⟩
    · exact ⟨Or.inr ⟨i, hi, hai⟩, haB⟩
  · rintro ⟨hor, haB⟩
    rcases hor with ⟨j, hj, haj⟩ | ⟨i, hi, hai⟩
    · exact Or.inl ⟨j, hj, haj, haB⟩
    · exact Or.inr ⟨i, hi, hai, haB⟩

/-! ### The clean design -/

/-- The perturbation scale of the clean design: half that of the grid design, because half of the
apex abundance is what survives the deletion of the protected level. -/
noncomputable def cleanEta (ε : ℝ) (K : ℕ) : ℝ := reservoirEta ε K / 2

theorem cleanEta_pos {ε : ℝ} {K : ℕ} (hK : 0 < K) : 0 < cleanEta ε K :=
  half_pos (reservoirEta_pos hK)

theorem cleanEta_le {ε : ℝ} {K : ℕ} (hK : 0 < K) : cleanEta ε K ≤ reservoirEta ε K := by
  have := reservoirEta_pos (ε := ε) hK
  unfold cleanEta
  linarith

/-- **A clean grid reservoir**: a grid design whose classes avoid the protected level `W''`, and
whose reservoir touches no protected vertex.  The classes are no longer of one common size — the
deletion of `W''` costs each of them at most a quarter — but they are still large, still disjoint,
still balanced for every vertex of `W`, and the reservoir link of an outer vertex is still exactly
its `F`-link inside its own row and column. -/
structure IsGridCleanReservoir (ε : ℝ) (K : ℕ) (W W' W'' : Finset V) (F R : Finset (Sym2 V))
    (C : ℕ → Finset V) (x y : V → ℕ) : Prop where
  /-- the classes lie in `W'`. -/
  classSubset : ∀ i < gridSize ε K * gridSize ε K, C i ⊆ W'
  /-- **the classes avoid the protected level.** -/
  classAvoid : ∀ i < gridSize ε K * gridSize ε K, Disjoint (C i) W''
  /-- the classes are not larger than the nominal class size `t`. -/
  classCardLe : ∀ i < gridSize ε K * gridSize ε K,
    (C i).card ≤ gridClassSize ε K W'.card
  /-- the classes have at least three quarters of the nominal class size. -/
  classCardGe : ∀ i < gridSize ε K * gridSize ε K,
    3 * gridClassSize ε K W'.card ≤ 4 * (C i).card
  /-- the classes are pairwise disjoint. -/
  classDisjoint : ∀ i < gridSize ε K * gridSize ε K, ∀ j < gridSize ε K * gridSize ε K,
    i ≠ j → Disjoint (C i) (C j)
  /-- every vertex of `W` misses at most a quarter of the nominal class size in each class. -/
  classBalanced : ∀ v ∈ W, ∀ i < gridSize ε K * gridSize ε K,
    4 * ((nonNbrs F W' v ∩ C i).card) ≤ gridClassSize ε K W'.card
  /-- the row label of an outer vertex is a grid coordinate. -/
  rowLt : ∀ u ∈ W \ W', x u < gridSize ε K
  /-- the column label of an outer vertex is a grid coordinate. -/
  colLt : ∀ u ∈ W \ W', y u < gridSize ε K
  /-- the row fibres are small. -/
  rowFibre : ∀ p : ℕ, (((W \ W').filter (fun u => x u = p)).card) * gridSize ε K
    ≤ (W \ W').card + gridSize ε K * gridSize ε K
  /-- the column fibres are small. -/
  colFibre : ∀ q : ℕ, (((W \ W').filter (fun u => y u = q)).card) * gridSize ε K
    ≤ (W \ W').card + gridSize ε K * gridSize ε K
  /-- the cells are small. -/
  cellFibre : ∀ p q : ℕ, (((W \ W').filter (fun u => x u = p ∧ y u = q)).card)
    * (gridSize ε K * gridSize ε K) ≤ (W \ W').card + gridSize ε K * gridSize ε K
  /-- the reservoir link of an outer vertex is its `F`-link inside its row and its column. -/
  link : ∀ u ∈ W \ W', resLink R W' u
    = resLink F W' u ∩ gridRegion (gridSize ε K) C (x u) (y u)
  /-- the nominal class size is positive. -/
  classPos : 0 < gridClassSize ε K W'.card
  /-- the classes take up at most a tenth of `W'`. -/
  classVolume : 10 * ((gridSize ε K * gridSize ε K) * gridClassSize ε K W'.card) ≤ W'.card
  /-- there are at most `20K²h²` outer vertices per place in a class. -/
  outerVolume : W.card
    ≤ 20 * (K * K * gridSize ε K * gridSize ε K) * gridClassSize ε K W'.card

set_option maxHeartbeats 1000000 in
/-- **The clean grid design.**  The design of `BKLO.exists_reservoir_full_structured` with the
protected level deleted from the classes and from the reservoir. -/
theorem exists_reservoir_clean_structured
    {ε : ℝ} (hε : 0 < ε) {K : ℕ} (hKε : (8 : ℝ) / ε ≤ (K : ℝ))
    {W W' W'' : Finset V} {F : Finset (Sym2 V)}
    (hW''W' : W'' ⊆ W')
    (hKW' : K * W'.card ≤ W.card) (hW'K : W.card ≤ K * K * W'.card)
    (hKW'' : K * W''.card ≤ W'.card)
    (hres : ∀ v ∈ W, (9 / 10 + ε / 4) * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ))
    (hN : reservoirThreshold ε K ≤ W.card) :
    ∃ (R : Finset (Sym2 V)) (C : ℕ → Finset V) (x y : V → ℕ),
      R ⊆ F ∧ IsCrossing W W' R ∧
      (∀ v : V, (edeg R v : ℝ) ≤ ε / 8 * (W.card : ℝ)) ∧
      (∀ u ∈ W \ W', ∀ v ∈ W \ W',
        2 * cleanEta ε K * (W.card : ℝ) ≤ ((apexes R W' u v).card : ℝ)) ∧
      (∀ a ∈ W', (edeg R a : ℝ) ≤ ε / 16 * (W'.card : ℝ)) ∧
      IsGridCleanReservoir ε K W W' W'' F R C x y := by
  classical
  obtain ⟨R, C, x, y, hRF, hcross, hsparse, _hapex, hsparse', hgrid⟩ :=
    exists_reservoir_full_structured (W'' := W'') hε hKε hKW' hW'K hKW'' hres hN
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hKpos : 0 < K := by
    by_contra hcon
    push_neg at hcon
    have hK0 : K = 0 := by omega
    have h1 : (8 : ℝ) / ε ≤ 0 := by rw [hK0] at hKε; simpa using hKε
    have h2 : (0 : ℝ) < 8 / ε := by positivity
    linarith
  -- the clean classes and the clean reservoir
  set C' : ℕ → Finset V := fun i => C i \ W'' with hC'def
  set R' : Finset (Sym2 V) := R.filter (fun e => ∀ a ∈ W'', a ∉ e) with hR'def
  have hR'sub : R' ⊆ R := Finset.filter_subset _ _
  have hR'F : R' ⊆ F := hR'sub.trans hRF
  have hcross' : IsCrossing W W' R' := fun e he => hcross e (hR'sub he)
  have hedeg : ∀ v : V, edeg R' v ≤ edeg R v := by
    intro v
    refine Finset.card_le_card ?_
    intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨hR'sub he.1, he.2⟩
  have hsparseR' : ∀ v : V, (edeg R' v : ℝ) ≤ ε / 8 * (W.card : ℝ) := by
    intro v
    have h1 : ((edeg R' v : ℕ) : ℝ) ≤ ((edeg R v : ℕ) : ℝ) := by exact_mod_cast hedeg v
    exact le_trans h1 (hsparse v)
  have hsparseR'' : ∀ a ∈ W', (edeg R' a : ℝ) ≤ ε / 16 * (W'.card : ℝ) := by
    intro a ha
    have h1 : ((edeg R' a : ℕ) : ℝ) ≤ ((edeg R a : ℕ) : ℝ) := by exact_mod_cast hedeg a
    exact le_trans h1 (hsparse' a ha)
  -- the outer vertices are not protected
  have houter : ∀ u ∈ W \ W', u ∉ W'' := by
    intro u hu hcon
    exact (Finset.mem_sdiff.1 hu).2 (hW''W' hcon)
  -- the clean reservoir link
  have hresLink : ∀ u ∈ W \ W', resLink R' W' u = resLink R W' u \ W'' := by
    intro u hu
    ext a
    simp only [mem_resLink, Finset.mem_sdiff, hR'def, Finset.mem_filter]
    constructor
    · rintro ⟨haW', haR, hno⟩
      exact ⟨⟨haW', haR⟩, fun hcon => hno a hcon (by simp)⟩
    · rintro ⟨⟨haW', haR⟩, haW''⟩
      refine ⟨haW', haR, ?_⟩
      intro b hb hbe
      rcases Sym2.mem_iff.1 hbe with hbu | hba
      · exact houter u hu (hbu ▸ hb)
      · exact haW'' (hba ▸ hb)
  have hlink' : ∀ u ∈ W \ W',
      resLink R' W' u = resLink F W' u ∩ gridRegion h C' (x u) (y u) := by
    intro u hu
    have hl := hgrid.link u hu
    rw [← hhdef] at hl
    rw [hresLink u hu, hl, hC'def, gridRegion_sdiff]
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  -- the classes stay large
  have hclassCardLe : ∀ i < h * h, (C' i).card ≤ t := by
    intro i hi
    have := Finset.card_le_card (Finset.sdiff_subset (s := C i) (t := W''))
    rw [hgrid.classCard i (by rw [← hhdef]; exact hi)] at this
    exact this
  have hclassCardGe : ∀ i < h * h, 3 * t ≤ 4 * (C' i).card := by
    intro i hi
    have hi' : i < gridSize ε K * gridSize ε K := by rw [← hhdef]; exact hi
    have hcard : (C i).card = t := hgrid.classCard i hi'
    have hprot : 4 * ((W'' ∩ C i).card) ≤ t := hgrid.protectedBalanced i hi'
    have hsplit : (C i \ W'').card + (C i ∩ W'').card = (C i).card :=
      Finset.card_sdiff_add_card_inter _ _
    have hcomm : (C i ∩ W'').card = (W'' ∩ C i).card := by rw [Finset.inter_comm]
    have : (C' i).card = (C i \ W'').card := rfl
    omega
  -- the apexes stay abundant
  have hapex' : ∀ u ∈ W \ W', ∀ v ∈ W \ W',
      2 * cleanEta ε K * (W.card : ℝ) ≤ ((apexes R' W' u v).card : ℝ) := by
    intro u hu v hv
    have hxu : x u < h := by have := hgrid.rowLt u hu; rwa [← hhdef] at this
    have hyv : y v < h := by have := hgrid.colLt v hv; rwa [← hhdef] at this
    have hxv : x v < h := by have := hgrid.rowLt v hv; rwa [← hhdef] at this
    have hyu : y u < h := by have := hgrid.colLt u hu; rwa [← hhdef] at this
    set i₀ : ℕ := x u * h + y v with hi₀def
    have hi₀ : i₀ < h * h := grid_idx_lt hxu hyv
    have hi₀' : i₀ < gridSize ε K * gridSize ε K := by rw [← hhdef]; exact hi₀
    set S : Finset V := (C i₀ \ W'') \ (nonNbrs F W' u ∪ nonNbrs F W' v) with hSdef
    -- the class of the cell `(x u, y v)` is an apex source
    have hSsub : S ⊆ apexes R' W' u v := by
      intro w hw
      rw [hSdef, Finset.mem_sdiff, Finset.mem_sdiff] at hw
      obtain ⟨⟨hwC, hwW''⟩, hwnon⟩ := hw
      rw [Finset.mem_union] at hwnon
      push_neg at hwnon
      have hwW' : w ∈ W' := hgrid.classSubset i₀ hi₀' hwC
      have hwu : w ∈ resLink F W' u := by
        by_contra hcon
        exact hwnon.1 (Finset.mem_sdiff.2 ⟨hwW', hcon⟩)
      have hwv : w ∈ resLink F W' v := by
        by_contra hcon
        exact hwnon.2 (Finset.mem_sdiff.2 ⟨hwW', hcon⟩)
      have hlu := hgrid.link u hu
      have hlv := hgrid.link v hv
      rw [← hhdef] at hlu hlv
      have hwru : w ∈ resLink R W' u := by
        rw [hlu, Finset.mem_inter]
        exact ⟨hwu, class_subset_gridRegion_row (C := C) (p := x u) (q := y u) hyv hwC⟩
      have hwrv : w ∈ resLink R W' v := by
        rw [hlv, Finset.mem_inter]
        exact ⟨hwv, class_subset_gridRegion_col (C := C) (p := x v) (q := y v) hxu hwC⟩
      refine mem_apexes.2 ⟨hwW', ?_, ?_⟩
      · rw [hR'def, Finset.mem_filter]
        refine ⟨(mem_resLink.1 hwru).2, ?_⟩
        intro b hb hbe
        rcases Sym2.mem_iff.1 hbe with hbu | hbw
        · exact houter u hu (hbu ▸ hb)
        · exact hwW'' (hbw ▸ hb)
      · rw [hR'def, Finset.mem_filter]
        refine ⟨(mem_resLink.1 hwrv).2, ?_⟩
        intro b hb hbe
        rcases Sym2.mem_iff.1 hbe with hbv | hbw
        · exact houter v hv (hbv ▸ hb)
        · exact hwW'' (hbw ▸ hb)
    -- and it keeps at least a quarter of its vertices
    have hcard : (C i₀).card = t := hgrid.classCard i₀ hi₀'
    have hprot : 4 * ((W'' ∩ C i₀).card) ≤ t := hgrid.protectedBalanced i₀ hi₀'
    have hbu : 4 * ((nonNbrs F W' u ∩ C i₀).card) ≤ t :=
      hgrid.classBalanced u (Finset.mem_sdiff.1 hu).1 i₀ hi₀'
    have hbv : 4 * ((nonNbrs F W' v ∩ C i₀).card) ≤ t :=
      hgrid.classBalanced v (Finset.mem_sdiff.1 hv).1 i₀ hi₀'
    have hlow : t ≤ 4 * S.card := by
      have h1 : C i₀ ⊆ S ∪ (W'' ∩ C i₀) ∪ (nonNbrs F W' u ∩ C i₀) ∪ (nonNbrs F W' v ∩ C i₀) := by
        intro w hw
        by_cases hw'' : w ∈ W''
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hw'', hw⟩)))
        · by_cases hwu : w ∈ nonNbrs F W' u
          · exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_inter.2 ⟨hwu, hw⟩))
          · by_cases hwv : w ∈ nonNbrs F W' v
            · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hwv, hw⟩)
            · refine Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_union_left _ ?_))
              rw [hSdef, Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_union]
              exact ⟨⟨hw, hw''⟩, by push_neg; exact ⟨hwu, hwv⟩⟩
      have h2 := Finset.card_le_card h1
      have h3 : (S ∪ (W'' ∩ C i₀) ∪ (nonNbrs F W' u ∩ C i₀) ∪ (nonNbrs F W' v ∩ C i₀)).card
          ≤ S.card + (W'' ∩ C i₀).card + (nonNbrs F W' u ∩ C i₀).card
            + (nonNbrs F W' v ∩ C i₀).card := by
        refine le_trans (Finset.card_union_le _ _) ?_
        have := Finset.card_union_le (S ∪ (W'' ∩ C i₀)) (nonNbrs F W' u ∩ C i₀)
        have h4 := Finset.card_union_le S (W'' ∩ C i₀)
        omega
      omega
    -- the abundance
    have hApex : (t : ℝ) ≤ 4 * ((apexes R' W' u v).card : ℝ) := by
      have h1 : (t : ℝ) ≤ 4 * (S.card : ℝ) := by exact_mod_cast hlow
      have h2 : (S.card : ℝ) ≤ ((apexes R' W' u v).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hSsub
      linarith
    have hvol : (W.card : ℝ) ≤ 20 * ((K : ℝ) * K * h * h) * (t : ℝ) := by
      have := hgrid.outerVolume
      rw [← hhdef, ← htdef] at this
      exact_mod_cast this
    have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
    have hhr : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hhpos
    have heta : cleanEta ε K = 1 / (160 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2) := by
      rw [cleanEta, reservoirEta, ← hhdef]
      field_simp
      ring
    have hpos' : (0 : ℝ) < 80 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2 := by positivity
    have h2 : 2 * (1 / (160 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2)) * (W.card : ℝ)
        = (W.card : ℝ) / (80 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2) := by
      field_simp
      ring
    have h3 : 20 * ((K : ℝ) * K * h * h) * (t : ℝ)
        ≤ 20 * ((K : ℝ) * K * h * h) * (4 * ((apexes R' W' u v).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hApex (by positivity)
    rw [heta, h2, div_le_iff₀ hpos']
    linarith only [hvol, h3]
  -- the packaging
  refine ⟨R', C', x, y, hR'F, hcross', hsparseR', hapex', hsparseR'', ?_⟩
  refine
    { classSubset := ?_, classAvoid := ?_, classCardLe := ?_, classCardGe := ?_,
      classDisjoint := ?_, classBalanced := ?_, rowLt := hgrid.rowLt, colLt := hgrid.colLt,
      rowFibre := hgrid.rowFibre, colFibre := hgrid.colFibre, cellFibre := hgrid.cellFibre,
      link := ?_, classPos := hgrid.classPos, classVolume := hgrid.classVolume,
      outerVolume := hgrid.outerVolume }
  · intro i hi
    exact (Finset.sdiff_subset).trans (hgrid.classSubset i hi)
  · intro i _
    exact Finset.sdiff_disjoint
  · intro i hi
    exact hclassCardLe i (by rw [hhdef]; exact hi)
  · intro i hi
    exact hclassCardGe i (by rw [hhdef]; exact hi)
  · intro i hi j hj hij
    exact Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset (hgrid.classDisjoint i hi j hj hij))
  · intro v hv i hi
    refine le_trans (Nat.mul_le_mul_left 4 (Finset.card_le_card ?_)) (hgrid.classBalanced v hv i hi)
    exact Finset.inter_subset_inter_left Finset.sdiff_subset
  · intro u hu
    have := hlink' u hu
    rw [hhdef] at this
    exact this

end BKLO
