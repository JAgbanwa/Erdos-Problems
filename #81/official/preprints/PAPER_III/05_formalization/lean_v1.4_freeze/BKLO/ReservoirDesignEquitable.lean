/-
# The equitable clean grid design.

`BKLO.IsGridCleanReservoir` removes the protected level from the classes of the grid design, but
it pays for it with classes of *unequal* size: deleting `W''` costs each class up to a quarter, so
the design only exports `3t/4 ≤ |C i| ≤ t`.  `BKLO.not_gridPairingResidualClean`
(`BKLO/GridPairingCleanRefutation.lean`) shows that this is fatal for the pairing demand of
AX2 §10: a design whose classes in the top half of the grid have `3t/4` vertices and whose classes
in the bottom half have `t` vertices makes every link of a bottom row heavier on its row side than
on its column side by `≈ h t / 8`, and a whole row of the grid cannot carry that many pairs.

The repair is to make the design **equitable**: all classes of one common size.  That is free —
after deleting `W''` every class still has at least `⌈3t/4⌉` vertices, so all of them can be
trimmed down to exactly `⌈3t/4⌉`, and the reservoir can be trimmed along with them.  What has to
be rechecked is that the trimming preserves the two quantitative exports:

* the link identity `resLink R W' u = resLink F W' u ∩ gridRegion h C (x u) (y u)` — the trimmed
  reservoir keeps exactly the edges landing in the trimmed classes
  (`BKLO.gridRegion_inter_classUnion`);
* the apex abundance — the class of the cell `(x u, y v)` keeps `⌈3t/4⌉` vertices and loses at
  most a quarter of `t` to each of the two non-neighbourhoods, so at least `t/4` apexes survive,
  which is exactly what the abundance `2·cleanEta·|W|` needs.

With an equitable design the row of a link and its column differ by one class only, so the
imbalance of a link is `t` rather than `Θ(h t)`, and the row-capacity count of the refutation
leaves a factor `Θ(h / K²)` of room.

Everything here is `sorry`-free.
-/
import BKLO.GridPairingCleanCount

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- **An equitable clean grid reservoir**: a clean grid design all of whose classes have one
common size. -/
structure IsGridEquitableReservoir (ε : ℝ) (K : ℕ) (W W' W'' : Finset V) (F R : Finset (Sym2 V))
    (C : ℕ → Finset V) (x y : V → ℕ)
    : Prop extends IsGridCleanReservoir ε K W W' W'' F R C x y where
  /-- **all classes have the same size.** -/
  classCardEq : ∀ i < gridSize ε K * gridSize ε K, ∀ j < gridSize ε K * gridSize ε K,
    (C i).card = (C j).card

set_option maxHeartbeats 1000000 in
/-- **The equitable clean grid design.**  The clean design of
`BKLO.exists_reservoir_clean_structured` with every class trimmed to the common size `⌈3t/4⌉` and
the reservoir trimmed along with it. -/
theorem exists_reservoir_equitable_structured
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
      IsGridEquitableReservoir ε K W W' W'' F R C x y := by
  classical
  obtain ⟨R, C, x, y, hRF, hcross, hsparse, _hapex, hsparse', hgrid⟩ :=
    exists_reservoir_clean_structured (W'' := W'') hε hKε hW''W' hKW' hW'K hKW'' hres hN
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
  -- ## the common class size
  set q : ℕ := (3 * t + 3) / 4 with hqdef
  have hq3 : 3 * t ≤ 4 * q := by omega
  have hqt : q ≤ t := by
    have := hgrid.classPos
    rw [← htdef] at this
    omega
  have hqle : ∀ i < h * h, q ≤ (C i).card := by
    intro i hi
    have h1 : 3 * t ≤ 4 * (C i).card := by
      have := hgrid.classCardGe i (by rw [← hhdef]; exact hi)
      rw [← htdef] at this
      exact this
    omega
  -- ## the trimmed classes
  set C' : ℕ → Finset V := fun i =>
    if hi : q ≤ (C i).card then (Finset.exists_subset_card_eq hi).choose else ∅ with hC'def
  have hC'sub : ∀ i, C' i ⊆ C i := by
    intro i
    rw [hC'def]
    by_cases hi : q ≤ (C i).card
    · simp only [dif_pos hi]
      exact (Finset.exists_subset_card_eq hi).choose_spec.1
    · simp only [dif_neg hi]
      exact Finset.empty_subset _
  have hC'card : ∀ i < h * h, (C' i).card = q := by
    intro i hi
    have hle := hqle i hi
    rw [hC'def]
    simp only [dif_pos hle]
    exact (Finset.exists_subset_card_eq hle).choose_spec.2
  have hCdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j) := by
    intro i hi j hj hij
    exact hgrid.classDisjoint i (by rw [← hhdef]; exact hi) j (by rw [← hhdef]; exact hj) hij
  -- ## the trimmed reservoir
  set Uni : Finset V := (Finset.range (h * h)).biUnion C' with hUnidef
  have hmemUni : ∀ i < h * h, ∀ a ∈ C' i, a ∈ Uni := by
    intro i hi a ha
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 hi, ha⟩
  set R' : Finset (Sym2 V) := R.filter (fun e => ∀ a ∈ W', a ∈ e → a ∈ Uni) with hR'def
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
  have houter : ∀ u ∈ W \ W', u ∉ W' := fun u hu => (Finset.mem_sdiff.1 hu).2
  -- ## the link of the trimmed design
  have hresLink : ∀ u ∈ W \ W', resLink R' W' u = resLink R W' u ∩ Uni := by
    intro u hu
    ext a
    simp only [mem_resLink, Finset.mem_inter, hR'def, Finset.mem_filter]
    constructor
    · rintro ⟨haW', haR, hno⟩
      exact ⟨⟨haW', haR⟩, hno a haW' (by simp)⟩
    · rintro ⟨⟨haW', haR⟩, haU⟩
      refine ⟨haW', haR, ?_⟩
      intro b hb hbe
      rcases Sym2.mem_iff.1 hbe with hbu | hba
      · exact absurd (hbu ▸ hb) (houter u hu)
      · exact hba ▸ haU
  have hlink' : ∀ u ∈ W \ W',
      resLink R' W' u = resLink F W' u ∩ gridRegion h C' (x u) (y u) := by
    intro u hu
    have hxu : x u < h := by have := hgrid.rowLt u hu; rwa [← hhdef] at this
    have hyu : y u < h := by have := hgrid.colLt u hu; rwa [← hhdef] at this
    have hl := hgrid.link u hu
    rw [← hhdef] at hl
    rw [hresLink u hu, hl, Finset.inter_assoc,
      gridRegion_inter_classUnion (C := C) (C' := C') hxu hyu hC'sub hCdisj]
  -- ## the apexes stay abundant
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
    set S : Finset V := C' i₀ \ (nonNbrs F W' u ∪ nonNbrs F W' v) with hSdef
    have hSsub : S ⊆ apexes R' W' u v := by
      intro w hw
      rw [hSdef, Finset.mem_sdiff, Finset.mem_union] at hw
      obtain ⟨hwC', hwnon⟩ := hw
      push_neg at hwnon
      have hwC : w ∈ C i₀ := hC'sub i₀ hwC'
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
      have hwU : w ∈ Uni := hmemUni i₀ hi₀ w hwC'
      refine mem_apexes.2 ⟨hwW', ?_, ?_⟩
      · rw [hR'def, Finset.mem_filter]
        refine ⟨(mem_resLink.1 hwru).2, ?_⟩
        intro b hb hbe
        rcases Sym2.mem_iff.1 hbe with hbu | hbw
        · exact absurd (hbu ▸ hb) (houter u hu)
        · exact hbw ▸ hwU
      · rw [hR'def, Finset.mem_filter]
        refine ⟨(mem_resLink.1 hwrv).2, ?_⟩
        intro b hb hbe
        rcases Sym2.mem_iff.1 hbe with hbv | hbw
        · exact absurd (hbv ▸ hb) (houter v hv)
        · exact hbw ▸ hwU
    have hbu : 4 * ((nonNbrs F W' u ∩ C i₀).card) ≤ t := by
      have := hgrid.classBalanced u (Finset.mem_sdiff.1 hu).1 i₀ hi₀'
      rw [← htdef] at this
      exact this
    have hbv : 4 * ((nonNbrs F W' v ∩ C i₀).card) ≤ t := by
      have := hgrid.classBalanced v (Finset.mem_sdiff.1 hv).1 i₀ hi₀'
      rw [← htdef] at this
      exact this
    have hlow : t ≤ 4 * S.card := by
      have h1 : C' i₀ ⊆ S ∪ (nonNbrs F W' u ∩ C i₀) ∪ (nonNbrs F W' v ∩ C i₀) := by
        intro w hw
        by_cases hwu : w ∈ nonNbrs F W' u
        · exact Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hwu, hC'sub i₀ hw⟩))
        · by_cases hwv : w ∈ nonNbrs F W' v
          · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hwv, hC'sub i₀ hw⟩)
          · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
            rw [hSdef, Finset.mem_sdiff, Finset.mem_union]
            exact ⟨hw, by push_neg; exact ⟨hwu, hwv⟩⟩
      have h2 := Finset.card_le_card h1
      have h3 : (S ∪ (nonNbrs F W' u ∩ C i₀) ∪ (nonNbrs F W' v ∩ C i₀)).card
          ≤ S.card + (nonNbrs F W' u ∩ C i₀).card + (nonNbrs F W' v ∩ C i₀).card := by
        refine le_trans (Finset.card_union_le _ _) ?_
        have := Finset.card_union_le S (nonNbrs F W' u ∩ C i₀)
        omega
      have h4 : (C' i₀).card = q := hC'card i₀ hi₀
      omega
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
    nlinarith only [hvol, h3]
  -- ## the packaging
  refine ⟨R', C', x, y, hR'F, hcross', hsparseR', hapex', hsparseR'', ?_⟩
  refine
    { classSubset := ?_, classAvoid := ?_, classCardLe := ?_, classCardGe := ?_,
      classDisjoint := ?_, classBalanced := ?_, rowLt := hgrid.rowLt, colLt := hgrid.colLt,
      rowFibre := hgrid.rowFibre, colFibre := hgrid.colFibre, cellFibre := hgrid.cellFibre,
      link := ?_, classPos := hgrid.classPos, classVolume := hgrid.classVolume,
      outerVolume := hgrid.outerVolume, classCardEq := ?_ }
  · intro i hi
    exact (hC'sub i).trans (hgrid.classSubset i hi)
  · intro i hi
    exact Finset.disjoint_of_subset_left (hC'sub i) (hgrid.classAvoid i hi)
  · intro i hi
    rw [hC'card i (by rw [hhdef]; exact hi), ← htdef]
    exact hqt
  · intro i hi
    rw [hC'card i (by rw [hhdef]; exact hi), ← htdef]
    exact hq3
  · intro i hi j hj hij
    exact Finset.disjoint_of_subset_left (hC'sub i)
      (Finset.disjoint_of_subset_right (hC'sub j) (hgrid.classDisjoint i hi j hj hij))
  · intro v hv i hi
    refine le_trans (Nat.mul_le_mul_left 4 (Finset.card_le_card ?_)) (hgrid.classBalanced v hv i hi)
    exact Finset.inter_subset_inter_left (hC'sub i)
  · intro u hu
    have := hlink' u hu
    rw [hhdef] at this
    exact this
  · intro i hi j hj
    rw [hC'card i (by rw [hhdef]; exact hi), hC'card j (by rw [hhdef]; exact hj)]

end BKLO
