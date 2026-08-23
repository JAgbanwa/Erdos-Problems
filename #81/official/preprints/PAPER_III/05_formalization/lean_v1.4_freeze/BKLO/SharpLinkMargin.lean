/-
# The links of the sharp design meet Dirac's threshold with a margin.

At the sharp grid design (`BKLO.IsGridSharpReservoir`, `BKLO/ReservoirDesignSharp.lean`) the
reserved link of an outer vertex `u` is its `F`-link inside its designed region, and the region is
the union of the `2h-1` classes of the row and the column of `u`, each of the one common size `q`
and each *balanced against its own size*: every vertex of `W` misses at most a quarter of it.

Two counts follow, and they are the reason the sharp design is the right one for the pairing step
of AX2 §10:

* `BKLO.card_resLink_sharp_ge` — the link keeps three quarters of its region:
  `3(2h-1)q ≤ 4|link|`;
* `BKLO.card_nonNbrs_inter_resLink_sharp_le` — every vertex misses at most a quarter of the region
  inside the link: `4|nonNbrs a ∩ link| ≤ (2h-1)q`.

Together they give `BKLO.sharp_link_dirac_margin`:

  `4|link| + (2h-1)q ≤ 8·deg_F(a; link)`  for every `a` in the link,

that is, every vertex of the link has `|link|/2 + (2h-1)q/8` neighbours inside it — Dirac's
threshold with a margin proportional to the link itself.  (At the clean and at the equitable
designs the same count gives exactly `|link|/2`, with no margin, because there the balance is
measured against the nominal class size `t` and a class may be as small as `3t/4`.)

Everything here is `sorry`-free.
-/
import BKLO.ReservoirDesignSharp

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The index set of a designed region -/

/-- The indices of the classes of the region of the cell `(p, q)`: the row `p` and the column
`q`. -/
def gridIdx (h p q : ℕ) : Finset ℕ :=
  ((Finset.range h).image (fun j => p * h + j)) ∪ ((Finset.range h).image (fun i => i * h + q))

theorem mem_gridIdx {h p q i : ℕ} :
    i ∈ gridIdx h p q ↔ (∃ j < h, i = p * h + j) ∨ (∃ l < h, i = l * h + q) := by
  simp only [gridIdx, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact Or.inl ⟨j, hj, rfl⟩
    · exact Or.inr ⟨l, hl, rfl⟩
  · rintro (⟨j, hj, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact Or.inl ⟨j, hj, rfl⟩
    · exact Or.inr ⟨l, hl, rfl⟩

theorem gridIdx_lt {h p q i : ℕ} (hp : p < h) (hq : q < h) (hi : i ∈ gridIdx h p q) :
    i < h * h := by
  rcases mem_gridIdx.1 hi with ⟨j, hj, rfl⟩ | ⟨l, hl, rfl⟩
  · exact grid_idx_lt hp hj
  · exact grid_idx_lt hl hq

/-- The region of a cell is the union of the classes of its row and of its column. -/
theorem gridRegion_eq_biUnion (h : ℕ) (C : ℕ → Finset V) (p q : ℕ) :
    gridRegion h C p q = (gridIdx h p q).biUnion C := by
  ext a
  simp only [gridRegion, gridIdx, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro (⟨j, hj, haj⟩ | ⟨l, hl, hal⟩)
    · exact ⟨p * h + j, Or.inl ⟨j, hj, rfl⟩, haj⟩
    · exact ⟨l * h + q, Or.inr ⟨l, hl, rfl⟩, hal⟩
  · rintro ⟨i, hi, hai⟩
    rcases hi with ⟨j, hj, rfl⟩ | ⟨l, hl, rfl⟩
    · exact Or.inl ⟨j, hj, hai⟩
    · exact Or.inr ⟨l, hl, hai⟩

/-- A region is made of `2h-1` classes. -/
theorem card_gridIdx {h p q : ℕ} (hp : p < h) (hq : q < h) :
    (gridIdx h p q).card = 2 * h - 1 := by
  classical
  have hhpos : 0 < h := lt_of_le_of_lt (Nat.zero_le p) hp
  set A : Finset ℕ := (Finset.range h).image (fun j => p * h + j) with hAdef
  set B : Finset ℕ := (Finset.range h).image (fun i => i * h + q) with hBdef
  have hAcard : A.card = h := by
    rw [hAdef, Finset.card_image_of_injective _ (fun a b hab => by omega), Finset.card_range]
  have hBcard : B.card = h := by
    rw [hBdef, Finset.card_image_of_injOn ?_, Finset.card_range]
    intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_range] at hi hj
    simp only at hij
    exact Nat.eq_of_mul_eq_mul_right hhpos (by omega)
  have hinter : A ∩ B = {p * h + q} := by
    ext i
    simp only [hAdef, hBdef, Finset.mem_inter, Finset.mem_image, Finset.mem_range,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, l, hl, hl'⟩
      have hlp : l = p := by
        have h1 : (p * h + j) / h = p := grid_row_of_idx hj
        have h2 : (l * h + q) / h = l := grid_row_of_idx hq
        rw [← hl'] at h1
        omega
      subst hlp
      omega
    · rintro rfl
      exact ⟨⟨q, hq, rfl⟩, p, hp, rfl⟩
  have hsum : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter _ _
  rw [hinter, Finset.card_singleton, hAcard, hBcard] at hsum
  simp only [gridIdx, ← hAdef, ← hBdef]
  omega

/-! ### Counting inside a region -/

/-- The trace of a set on the classes of a region adds up. -/
theorem card_inter_biUnion_eq_sum {I : Finset ℕ} {C : ℕ → Finset V} (T : Finset V)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (C i) (C j)) :
    (T ∩ I.biUnion C).card = ∑ i ∈ I, (T ∩ C i).card := by
  classical
  have hrw : T ∩ I.biUnion C = I.biUnion (fun i => T ∩ C i) := by
    ext a
    simp only [Finset.mem_inter, Finset.mem_biUnion]
    constructor
    · rintro ⟨haT, i, hi, hai⟩; exact ⟨i, hi, haT, hai⟩
    · rintro ⟨i, hi, haT, hai⟩; exact ⟨haT, i, hi, hai⟩
  rw [hrw]
  refine Finset.card_biUnion ?_
  intro i hi j hj hij
  exact Finset.disjoint_of_subset_left Finset.inter_subset_right
    (Finset.disjoint_of_subset_right Finset.inter_subset_right (hdisj i hi j hj hij))

/-! ### The two counts at a sharp design -/

variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ} {q : ℕ}

/-- Every vertex of `W` misses at most a quarter of the region of an outer vertex. -/
theorem card_nonNbrs_inter_gridRegion_sharp_le
    (hgrid : IsGridSharpReservoir ε K W W' W'' F R C x y)
    (hq : ∀ i < gridSize ε K * gridSize ε K, (C i).card = q)
    {u : V} (hu : u ∈ W \ W') {a : V} (ha : a ∈ W) :
    4 * ((nonNbrs F W' a ∩ gridRegion (gridSize ε K) C (x u) (y u)).card)
      ≤ (2 * gridSize ε K - 1) * q := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hxu : x u < h := hgrid.rowLt u hu
  have hyu : y u < h := hgrid.colLt u hu
  set I : Finset ℕ := gridIdx h (x u) (y u) with hIdef
  have hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (C i) (C j) := by
    intro i hi j hj hij
    exact hgrid.classDisjoint i (gridIdx_lt hxu hyu hi) j (gridIdx_lt hxu hyu hj) hij
  rw [gridRegion_eq_biUnion, ← hIdef, card_inter_biUnion_eq_sum _ hdisj, Finset.mul_sum]
  calc ∑ i ∈ I, 4 * ((nonNbrs F W' a ∩ C i).card)
      ≤ ∑ _i ∈ I, q := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact hgrid.classBalancedSharp a ha i (gridIdx_lt hxu hyu hi) |>.trans_eq
          (hq i (gridIdx_lt hxu hyu hi))
    _ = I.card * q := by rw [Finset.sum_const, smul_eq_mul]
    _ = (2 * h - 1) * q := by rw [card_gridIdx hxu hyu]

/-- The reserved link of an outer vertex keeps three quarters of its region. -/
theorem card_resLink_sharp_ge
    (hgrid : IsGridSharpReservoir ε K W W' W'' F R C x y)
    (hq : ∀ i < gridSize ε K * gridSize ε K, (C i).card = q)
    {u : V} (hu : u ∈ W \ W') :
    3 * ((2 * gridSize ε K - 1) * q) ≤ 4 * (resLink R W' u).card := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hxu : x u < h := hgrid.rowLt u hu
  have hyu : y u < h := hgrid.colLt u hu
  set I : Finset ℕ := gridIdx h (x u) (y u) with hIdef
  have hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (C i) (C j) := by
    intro i hi j hj hij
    exact hgrid.classDisjoint i (gridIdx_lt hxu hyu hi) j (gridIdx_lt hxu hyu hj) hij
  have hlink := hgrid.link u hu
  have hsub : resLink R W' u ⊆ gridRegion h C (x u) (y u) := by
    rw [hlink]
    exact Finset.inter_subset_right
  have hself : resLink R W' u ∩ gridRegion h C (x u) (y u) = resLink R W' u :=
    Finset.inter_eq_left.2 hsub
  have hcard : (resLink R W' u).card = ∑ i ∈ I, ((resLink R W' u) ∩ C i).card := by
    have h1 : ((resLink R W' u) ∩ I.biUnion C).card = ∑ i ∈ I, ((resLink R W' u) ∩ C i).card :=
      card_inter_biUnion_eq_sum _ hdisj
    have h2 : I.biUnion C = gridRegion h C (x u) (y u) := by
      rw [hIdef, gridRegion_eq_biUnion]
    rw [h2, hself] at h1
    exact h1
  -- each class keeps three quarters of itself
  have hclass : ∀ i ∈ I, 3 * q ≤ 4 * ((resLink R W' u) ∩ C i).card := by
    intro i hi
    have hilt : i < h * h := gridIdx_lt hxu hyu hi
    have hiW' : C i ⊆ W' := hgrid.classSubset i hilt
    have hireg : C i ⊆ gridRegion h C (x u) (y u) := by
      rw [gridRegion_eq_biUnion]
      intro z hz
      exact Finset.mem_biUnion.2 ⟨i, hi, hz⟩
    have hnn : nonNbrs F W' u = W' \ resLink F W' u := rfl
    have heq : (resLink R W' u) ∩ C i = C i \ nonNbrs F W' u := by
      rw [hlink, hnn]
      ext z
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨hz1, -⟩, hz3⟩
        exact ⟨hz3, fun hcon => hcon.2 hz1⟩
      · rintro ⟨hz1, hz2⟩
        refine ⟨⟨?_, hireg hz1⟩, hz1⟩
        by_contra hcon
        exact hz2 ⟨hiW' hz1, hcon⟩
    have hsplit : (C i \ nonNbrs F W' u).card + (nonNbrs F W' u ∩ C i).card = (C i).card := by
      rw [Finset.inter_comm]
      exact Finset.card_sdiff_add_card_inter _ _
    have hbal : 4 * ((nonNbrs F W' u ∩ C i).card) ≤ q := by
      have := hgrid.classBalancedSharp u (Finset.mem_sdiff.1 hu).1 i hilt
      rwa [hq i hilt] at this
    have hqi : (C i).card = q := hq i hilt
    rw [heq]
    omega
  have hsum : ∑ i ∈ I, 3 * q ≤ ∑ i ∈ I, 4 * ((resLink R W' u) ∩ C i).card :=
    Finset.sum_le_sum hclass
  have hleft : ∑ _i ∈ I, 3 * q = 3 * ((2 * h - 1) * q) := by
    rw [Finset.sum_const, smul_eq_mul, card_gridIdx hxu hyu]
    ring
  have hright : ∑ i ∈ I, 4 * ((resLink R W' u) ∩ C i).card
      = 4 * (resLink R W' u).card := by
    rw [hcard, Finset.mul_sum]
  rw [hleft, hright] at hsum
  omega

/-- **Dirac's threshold with a margin.**  At a sharp grid design every vertex of the reserved link
of an outer vertex has at least `|link|/2 + (2h-1)q/8` neighbours inside the link. -/
theorem sharp_link_dirac_margin
    (hgrid : IsGridSharpReservoir ε K W W' W'' F R C x y)
    (hnd : ∀ e ∈ F, ¬ e.IsDiag) (hW'W : W' ⊆ W)
    (hq : ∀ i < gridSize ε K * gridSize ε K, (C i).card = q)
    {u : V} (hu : u ∈ W \ W') {a : V} (ha : a ∈ resLink R W' u) :
    4 * (resLink R W' u).card + (2 * gridSize ε K - 1) * q
      ≤ 8 * edeg (F ∩ cliqueEdges (resLink R W' u)) a := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set S : Finset V := resLink R W' u with hSdef
  have hSW' : S ⊆ W' := fun z hz => (mem_resLink.1 hz).1
  have haW : a ∈ W := hW'W (hSW' ha)
  have hSreg : S ⊆ gridRegion h C (x u) (y u) := by
    rw [hSdef, hgrid.link u hu]
    exact Finset.inter_subset_right
  -- the degree inside the link
  have hdeg : edeg (F ∩ cliqueEdges S) a = (S \ nonNbrs F W' a).card := by
    rw [edeg_inter_cliqueEdges_eq_card_resLink ha hnd, resLink_eq_sdiff_nonNbrs hSW' a]
  have hsplit : (S \ nonNbrs F W' a).card + (nonNbrs F W' a ∩ S).card = S.card := by
    rw [Finset.inter_comm]
    exact Finset.card_sdiff_add_card_inter _ _
  -- the two counts
  have hupper : 4 * ((nonNbrs F W' a ∩ S).card) ≤ (2 * h - 1) * q := by
    refine le_trans (Nat.mul_le_mul_left 4 (Finset.card_le_card ?_))
      (card_nonNbrs_inter_gridRegion_sharp_le hgrid hq hu haW)
    exact Finset.inter_subset_inter_left hSreg
  have hlower : 3 * ((2 * h - 1) * q) ≤ 4 * S.card := card_resLink_sharp_ge hgrid hq hu
  rw [hdeg]
  omega

/-! ### The perturbed link -/

/-- The adversary's perturbation is small against the margin of a sharp design: at most a twelfth
of it. -/
theorem sharp_perturbation_small
    (hgrid : IsGridSharpReservoir ε K W W' W'' F R C x y)
    (hK : 0 < K) (hh3 : 3 ≤ gridSize ε K)
    (hq : ∀ i < gridSize ε K * gridSize ε K, (C i).card = q)
    {n : ℕ} (hn : (n : ℝ) ≤ 2 * cleanEta ε K * (W.card : ℝ)) :
    12 * n ≤ (2 * gridSize ε K - 1) * q := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have hhpos : 0 < h := by omega
  have hhh : 0 < h * h := Nat.mul_pos hhpos hhpos
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hhr : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hhpos
  -- the outer volume, in the reals
  have hvol : (W.card : ℝ) ≤ 20 * ((K : ℝ) * K * h * h) * (t : ℝ) := by
    have := hgrid.outerVolume
    rw [← hhdef, ← htdef] at this
    exact_mod_cast this
  have heta : cleanEta ε K = 1 / (160 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2) := by
    rw [cleanEta, reservoirEta, ← hhdef]
    field_simp
    ring
  have hden : (0 : ℝ) < 80 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2 := by positivity
  have h4n : 4 * (n : ℝ) ≤ (t : ℝ) := by
    rw [heta] at hn
    have h1 : 2 * (1 / (160 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2)) * (W.card : ℝ)
        = (W.card : ℝ) / (80 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2) := by
      field_simp; ring
    rw [h1, le_div_iff₀ hden] at hn
    have h2 : (n : ℝ) * (80 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2) ≤ 20 * ((K : ℝ) * K * h * h) * (t : ℝ) :=
      le_trans hn hvol
    have hpos : (0 : ℝ) < 20 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2 := by positivity
    nlinarith only [h2, hpos]
  have h4n' : 4 * n ≤ t := by exact_mod_cast h4n
  -- the classes are at least three quarters of the nominal size
  have h3t : 3 * t ≤ 4 * q := by
    have h1 := hgrid.classCardGe 0 hhh
    rw [← htdef, hq 0 hhh] at h1
    exact h1
  have hstep : 4 * q ≤ (2 * h - 1) * q := Nat.mul_le_mul_right q (by omega)
  omega

/-- **Dirac's hypothesis for the perturbed link.**  At a sharp grid design, an admissible
perturbation `X` of the reserved link of an outer vertex still has every vertex joined to at least
half of it. -/
theorem sharp_perturbed_link_dirac
    (hgrid : IsGridSharpReservoir ε K W W' W'' F R C x y)
    (hnd : ∀ e ∈ F, ¬ e.IsDiag) (hW'W : W' ⊆ W)
    (hq : ∀ i < gridSize ε K * gridSize ε K, (C i).card = q)
    {u : V} (hu : u ∈ W \ W') {X : Finset V} (hXW' : X ⊆ W')
    {n : ℕ} (hadd : (X \ resLink R W' u).card ≤ n) (hdel : (resLink R W' u \ X).card ≤ n)
    (hmargin : 12 * n ≤ (2 * gridSize ε K - 1) * q)
    {a : V} (ha : a ∈ X) :
    X.card ≤ 2 * edeg (F ∩ cliqueEdges X) a := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set S : Finset V := resLink R W' u with hSdef
  have haW : a ∈ W := hW'W (hXW' ha)
  have hSW' : S ⊆ W' := fun z hz => (mem_resLink.1 hz).1
  have hSreg : S ⊆ gridRegion h C (x u) (y u) := by
    rw [hSdef, hgrid.link u hu]
    exact Finset.inter_subset_right
  -- the degree inside the perturbed link
  have hdeg : edeg (F ∩ cliqueEdges X) a = (X \ nonNbrs F W' a).card := by
    rw [edeg_inter_cliqueEdges_eq_card_resLink ha hnd, resLink_eq_sdiff_nonNbrs hXW' a]
  have hsplit : (X \ nonNbrs F W' a).card + (nonNbrs F W' a ∩ X).card = X.card := by
    rw [Finset.inter_comm]
    exact Finset.card_sdiff_add_card_inter _ _
  -- the non-neighbours inside `X` are those inside the link, plus the perturbation
  have hsub : nonNbrs F W' a ∩ X ⊆ (nonNbrs F W' a ∩ S) ∪ (X \ S) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_inter.1 hz
    by_cases hzS : z ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hz1, hzS⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hz2, hzS⟩)
  have hnon : (nonNbrs F W' a ∩ X).card ≤ (nonNbrs F W' a ∩ S).card + (X \ S).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  -- the two counts at the sharp design
  have hupper : 4 * ((nonNbrs F W' a ∩ S).card) ≤ (2 * h - 1) * q := by
    refine le_trans (Nat.mul_le_mul_left 4 (Finset.card_le_card ?_))
      (card_nonNbrs_inter_gridRegion_sharp_le hgrid hq hu haW)
    exact Finset.inter_subset_inter_left hSreg
  have hlower : 3 * ((2 * h - 1) * q) ≤ 4 * S.card := card_resLink_sharp_ge hgrid hq hu
  -- the link is not much larger than its perturbation
  have hSX : S.card ≤ X.card + n := by
    have h1 : S.card ≤ (S ∩ X).card + (S \ X).card := by
      rw [Finset.card_inter_add_card_sdiff]
    have h2 : (S ∩ X).card ≤ X.card := Finset.card_le_card Finset.inter_subset_right
    omega
  rw [hdeg]
  omega

/-! ### One pairing per link -/

section Dirac

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Every link of a sharp design is paired up.**  Given Dirac's theorem, an admissible
perturbation of even size of the reserved link of an outer vertex of a sharp grid design carries a
fixed-point-free involution all of whose pairs are edges of `F`. -/
theorem exists_pairing_of_sharp_link (hDirac : PerfectMatchingDirac)
    {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
    {x y : V → ℕ} {q : ℕ}
    (hgrid : IsGridSharpReservoir ε K W W' W'' F R C x y)
    (hnd : ∀ e ∈ F, ¬ e.IsDiag) (hW'W : W' ⊆ W)
    (hq : ∀ i < gridSize ε K * gridSize ε K, (C i).card = q)
    {u : V} (hu : u ∈ W \ W') {X : Finset V} (hXW' : X ⊆ W') (hXeven : Even X.card)
    {n : ℕ} (hadd : (X \ resLink R W' u).card ≤ n) (hdel : (resLink R W' u \ X).card ≤ n)
    (hmargin : 12 * n ≤ (2 * gridSize ε K - 1) * q) :
    ∃ g : V → V, (∀ a ∈ X, g a ∈ X) ∧ (∀ a ∈ X, g (g a) = a) ∧ (∀ a ∈ X, g a ≠ a) ∧
      ∀ a ∈ X, s(a, g a) ∈ F :=
  exists_pairing_of_dirac hDirac hXeven
    (fun _ ha => sharp_perturbed_link_dirac hgrid hnd hW'W hq hu hXW' hadd hdel hmargin ha)

end Dirac

end BKLO
