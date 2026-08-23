/-
# The two-sided (Latin-balanced) grid design.

`BKLO.IsGridSharpReservoir` (`BKLO/ReservoirDesignSharp.lean`) equalizes the sizes of the classes
and measures the balance of a vertex against the size of the class it sits in.  Its balance is
nevertheless **one-sided**: a vertex of `W` may miss up to a quarter of every class of the *column*
of an outer vertex `u` and nothing of its *row*, so the reserved link of `u` is heavier on its row
side than on its column side by `Θ(h t)`.  That is exactly the imbalance the row-capacity count of
`BKLO.not_gridPairingResidualSharp` turns into a refutation of the pairing demand at the sharp
design: a link whose two sides differ by `Θ(h t)` has to place `Θ(h t)` of its pairs *inside* one
side, and the row of the grid — shared by `|W \ W'| / h` outer vertices — has no room for that many
edges.

This file removes the imbalance, **deterministically**.  Instead of reserving for `u` the whole of
its `F`-link inside its region, the design reserves from each of the `2h - 1` classes of the region
the *same number* `c = q - ⌊q/4⌋` of neighbours (`q` is the common class size, and `c` places are
available in every class because a vertex misses at most `⌊q/4⌋` of it — this is precisely
`IsGridSharpReservoir.classBalancedSharp`).  The reserved link then meets every class of the region
in exactly `c` places, so

* its row part and its column part have **exactly the same size** `h·c`
  (`IsGridTwoSidedReservoir.rowColBalanced`), which is the two-sided balance the pairing step needs
  — the row-capacity obstruction disappears, since every pair of a link may now go from its row
  side to its column side;
* it still keeps three quarters of every class of its region
  (`IsGridTwoSidedReservoir.linkClassGe`), so Dirac's threshold is still met with a margin
  proportional to the link (`BKLO/TwoSidedLinkMargin.lean`).

The equalization is a *choice of `c` places per class*, made once and for all; no concentration and
no randomness is involved, in the spirit of the deterministic Latin-square balance of
`BKLO/GridShiftLatin.lean`.

Everything here is `sorry`-free.
-/
import BKLO.SharpSweepBudget

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The two sides of a region -/

/-- The row part of the region of the cell `(p, q)`: the `h` classes of the row `p`. -/
def gridRowPart (h : ℕ) (C : ℕ → Finset V) (p : ℕ) : Finset V :=
  (Finset.range h).biUnion (fun j => C (p * h + j))

/-- The column part of the region of the cell `(p, q)`: the `h` classes of the column `q`. -/
def gridColPart (h : ℕ) (C : ℕ → Finset V) (q : ℕ) : Finset V :=
  (Finset.range h).biUnion (fun i => C (i * h + q))

theorem gridRegion_eq_row_union_col (h : ℕ) (C : ℕ → Finset V) (p q : ℕ) :
    gridRegion h C p q = gridRowPart h C p ∪ gridColPart h C q := rfl

/-- The trace of a set on the row part of a region, class by class. -/
theorem card_inter_gridRowPart {h : ℕ} {C : ℕ → Finset V} {p : ℕ} (hp : p < h)
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j)) (T : Finset V) :
    (T ∩ gridRowPart h C p).card = ∑ j ∈ Finset.range h, (T ∩ C (p * h + j)).card := by
  classical
  have hrw : T ∩ gridRowPart h C p
      = (Finset.range h).biUnion (fun j => T ∩ C (p * h + j)) := by
    ext a
    simp only [gridRowPart, Finset.mem_inter, Finset.mem_biUnion]
    constructor
    · rintro ⟨haT, j, hj, haj⟩; exact ⟨j, hj, haT, haj⟩
    · rintro ⟨j, hj, haT, haj⟩; exact ⟨haT, j, hj, haj⟩
  rw [hrw]
  refine Finset.card_biUnion ?_
  intro i hi j hj hij
  refine Finset.disjoint_of_subset_left Finset.inter_subset_right
    (Finset.disjoint_of_subset_right Finset.inter_subset_right ?_)
  exact hdisj _ (grid_idx_lt hp (Finset.mem_range.1 hi)) _
    (grid_idx_lt hp (Finset.mem_range.1 hj)) (by omega)

/-- The trace of a set on the column part of a region, class by class. -/
theorem card_inter_gridColPart {h : ℕ} {C : ℕ → Finset V} {q : ℕ} (hq : q < h)
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j)) (T : Finset V) :
    (T ∩ gridColPart h C q).card = ∑ i ∈ Finset.range h, (T ∩ C (i * h + q)).card := by
  classical
  have hhpos : 0 < h := lt_of_le_of_lt (Nat.zero_le q) hq
  have hrw : T ∩ gridColPart h C q
      = (Finset.range h).biUnion (fun i => T ∩ C (i * h + q)) := by
    ext a
    simp only [gridColPart, Finset.mem_inter, Finset.mem_biUnion]
    constructor
    · rintro ⟨haT, i, hi, hai⟩; exact ⟨i, hi, haT, hai⟩
    · rintro ⟨i, hi, haT, hai⟩; exact ⟨haT, i, hi, hai⟩
  rw [hrw]
  refine Finset.card_biUnion ?_
  intro i hi j hj hij
  refine Finset.disjoint_of_subset_left Finset.inter_subset_right
    (Finset.disjoint_of_subset_right Finset.inter_subset_right ?_)
  refine hdisj _ (grid_idx_lt (Finset.mem_range.1 hi) hq) _
    (grid_idx_lt (Finset.mem_range.1 hj) hq) ?_
  intro heq
  exact hij (Nat.eq_of_mul_eq_mul_right hhpos (by omega))

/-! ### The design -/

/-- **A two-sided grid reservoir.**  A sharp grid design whose reserved links are *equalized over
the classes of their region*: the link of an outer vertex meets every class of its row and of its
column in the same number of places, and in at least three quarters of the class.  Its row part and
its column part therefore have exactly the same size. -/
structure IsGridTwoSidedReservoir (ε : ℝ) (K : ℕ) (W W' W'' : Finset V) (F R : Finset (Sym2 V))
    (C : ℕ → Finset V) (x y : V → ℕ) : Prop where
  /-- the classes lie in `W'`. -/
  classSubset : ∀ i < gridSize ε K * gridSize ε K, C i ⊆ W'
  /-- the classes avoid the protected level. -/
  classAvoid : ∀ i < gridSize ε K * gridSize ε K, Disjoint (C i) W''
  /-- the classes are not larger than the nominal class size `t`. -/
  classCardLe : ∀ i < gridSize ε K * gridSize ε K,
    (C i).card ≤ gridClassSize ε K W'.card
  /-- the classes have at least three quarters of the nominal class size. -/
  classCardGe : ∀ i < gridSize ε K * gridSize ε K,
    3 * gridClassSize ε K W'.card ≤ 4 * (C i).card
  /-- all classes have the same size. -/
  classCardEq : ∀ i < gridSize ε K * gridSize ε K, ∀ j < gridSize ε K * gridSize ε K,
    (C i).card = (C j).card
  /-- the classes are pairwise disjoint. -/
  classDisjoint : ∀ i < gridSize ε K * gridSize ε K, ∀ j < gridSize ε K * gridSize ε K,
    i ≠ j → Disjoint (C i) (C j)
  /-- every vertex of `W` misses at most a quarter of each class. -/
  classBalancedSharp : ∀ v ∈ W, ∀ i < gridSize ε K * gridSize ε K,
    4 * ((nonNbrs F W' v ∩ C i).card) ≤ (C i).card
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
  /-- the reserved link of an outer vertex lies in its `F`-link inside its region. -/
  linkSubset : ∀ u ∈ W \ W', resLink R W' u
    ⊆ resLink F W' u ∩ gridRegion (gridSize ε K) C (x u) (y u)
  /-- **the reserved link keeps three quarters of every class of its region.** -/
  linkClassGe : ∀ u ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x u) (y u),
    3 * (C i).card ≤ 4 * ((resLink R W' u ∩ C i).card)
  /-- **the reserved link meets every class of its region in the same number of places** — and
  that number is the same for every outer vertex. -/
  linkClassEq : ∀ u ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x u) (y u),
    ∀ v ∈ W \ W', ∀ j ∈ gridIdx (gridSize ε K) (x v) (y v),
    (resLink R W' u ∩ C i).card = (resLink R W' v ∩ C j).card
  /-- **two-sided balance**: the row part and the column part of a reserved link have exactly the
  same size. -/
  rowColBalanced : ∀ u ∈ W \ W',
    (resLink R W' u ∩ gridRowPart (gridSize ε K) C (x u)).card
      = (resLink R W' u ∩ gridColPart (gridSize ε K) C (y u)).card
  /-- the nominal class size is positive. -/
  classPos : 0 < gridClassSize ε K W'.card
  /-- the classes take up at most a tenth of `W'`. -/
  classVolume : 10 * ((gridSize ε K * gridSize ε K) * gridClassSize ε K W'.card) ≤ W'.card
  /-- there are at most `20K²h²` outer vertices per place in a class. -/
  outerVolume : W.card
    ≤ 20 * (K * K * gridSize ε K * gridSize ε K) * gridClassSize ε K W'.card

/-! ### Elementary consequences -/

variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ}

/-- The classes of the region of an outer vertex are pairwise disjoint. -/
theorem IsGridTwoSidedReservoir.region_disjoint
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) {u : V} (hu : u ∈ W \ W')
    {i : ℕ} (hi : i ∈ gridIdx (gridSize ε K) (x u) (y u))
    {j : ℕ} (hj : j ∈ gridIdx (gridSize ε K) (x u) (y u)) (hij : i ≠ j) :
    Disjoint (C i) (C j) :=
  hgrid.classDisjoint i (gridIdx_lt (hgrid.rowLt u hu) (hgrid.colLt u hu) hi) j
    (gridIdx_lt (hgrid.rowLt u hu) (hgrid.colLt u hu) hj) hij

/-- The reserved link of an outer vertex is the disjoint union of its traces on the classes of its
region, so it has exactly `(2h - 1)c` vertices. -/
theorem IsGridTwoSidedReservoir.card_resLink
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) {u : V} (hu : u ∈ W \ W')
    {c : ℕ} (hc : ∀ i ∈ gridIdx (gridSize ε K) (x u) (y u),
      (resLink R W' u ∩ C i).card = c) :
    (resLink R W' u).card = (2 * gridSize ε K - 1) * c := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set I : Finset ℕ := gridIdx h (x u) (y u) with hIdef
  have hxu : x u < h := hgrid.rowLt u hu
  have hyu : y u < h := hgrid.colLt u hu
  have hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (C i) (C j) := fun i hi j hj hij =>
    hgrid.region_disjoint hu hi hj hij
  have hsub : resLink R W' u ⊆ I.biUnion C := by
    intro a ha
    have h1 := (hgrid.linkSubset u hu) ha
    rw [Finset.mem_inter] at h1
    have h2 : a ∈ gridRegion h C (x u) (y u) := h1.2
    rw [gridRegion_eq_biUnion] at h2
    exact h2
  have hself : resLink R W' u ∩ I.biUnion C = resLink R W' u := Finset.inter_eq_left.2 hsub
  have hcard := card_inter_biUnion_eq_sum (I := I) (C := C) (resLink R W' u) hdisj
  rw [hself] at hcard
  rw [hcard, Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, card_gridIdx hxu hyu]

/-! ### The construction -/

set_option maxHeartbeats 2000000 in
/-- **The two-sided grid design.**  The sharp design of
`BKLO.exists_reservoir_sharp_structured`, with the reserved link of every outer vertex equalized
over the classes of its region: exactly `c = q - ⌊q/4⌋` neighbours are kept in each of the `2h - 1`
classes.  The row part and the column part of every reserved link then have exactly the same size,
which is the two-sided balance the pairing step of AX2 §10 needs. -/
theorem exists_reservoir_twosided_structured
    {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 100) {K : ℕ} (hKε : (8 : ℝ) / ε ≤ (K : ℝ))
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
      IsGridTwoSidedReservoir ε K W W' W'' F R C x y := by
  classical
  obtain ⟨R₀, C, x, y, hR₀F, _hcross₀, hsparse₀, _hapex₀, hsparse₀', hgrid⟩ :=
    exists_reservoir_sharp_structured hε hε' hKε hW''W' hKW' hW'K hKW'' hres hN
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
  set c : ℕ := q - q / 4 with hcdef
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
    have hbal : 4 * ((nonNbrs F W' u ∩ C i).card) ≤ (C i).card :=
      hgrid.classBalancedSharp u (Finset.mem_sdiff.1 hu).1 i (by rw [← hhdef]; exact hilt)
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
    have h8 := eight_cleanEta_mul_card_le hgrid hKpos
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
        linkSubset := ?_, linkClassGe := ?_, linkClassEq := ?_, rowColBalanced := ?_ }
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

end BKLO
