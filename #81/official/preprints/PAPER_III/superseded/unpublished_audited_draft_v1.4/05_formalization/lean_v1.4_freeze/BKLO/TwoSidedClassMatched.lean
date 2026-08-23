/-
# The ledger of a sweep that follows *any* class matching with small fibres.

The cross-side rule of `BKLO/TwoSidedCrossSideSweep.lean` fixes the class matching of a link to be
the shift `canonShift`.  That choice keeps the ledger spread, but it is **not feasible**: all the
outer vertices of one cell `(p, Q)` of the grid have the same canonical shift, hence prescribe the
*same* target class for a given vertex `a`, and a cell holds about `20K²t` outer vertices while a
class holds only about `t` vertices — a vertex cannot be paired into one class that often, since
the partners are distinct.  What a feasible rule needs is a class matching whose target *varies
inside a cell*, and that is compatible with everything the ledger uses, because the ledger only
ever needs the **fibres** of the matching to be small.

This file states the rule in that generality:

* `BKLO.IsClassMatchedSweep` — a family `ρ w β` (the column class the row class `β` of the link of
  `w` is matched with) and `σ w α` (the row class the column class `α` is matched with); outside a
  per-link exceptional set, every vertex of the reserved part of a link went to the class the
  family prescribes on the other side of the region;
* `BKLO.ClassMatchingFibres` — the only thing the ledger asks of the family: every fibre
  `{w : x w = p, ρ w β = P}` of a row line, and every fibre `{w : y w = q, σ w α = Q}` of a column
  line, is as small as a cell fibre of the design;
* `BKLO.ledgerSpread_of_classMatchedSweep` — **the ledger of such a sweep is spread.**

The canonical shift is the special case `ρ w β = (β + canonShift h x y w) % h`, whose fibres are
cell fibres; a shift balanced inside every cell (`BKLO.exists_cell_balanced_shift`) has fibres of
the same order and is feasible.

Everything here is `sorry`-free.
-/
import BKLO.TwoSidedCrossSideExc
import BKLO.BipartiteMatching

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **The canonical shift is constant on a cell**, and so is the class it matches a given class
with.  This is the capacity obstruction to the rule of `BKLO.IsCrossSideSweep`: all the outer
vertices of one cell — about `20K²t` of them — prescribe the *same* target class for a given
vertex `a`, while a class holds only about `t` vertices and the partners of `a` are distinct.  A
feasible class matching has to vary inside a cell; `BKLO.ClassMatchingFibres` is what the ledger
asks of it instead. -/
theorem canonShift_const_on_cell {h : ℕ} {x y : V → ℕ} {w w' : V} (hx : x w = x w')
    (hy : y w = y w') (β : ℕ) :
    crossShift h (canonShift h x y) β w = crossShift h (canonShift h x y) β w' := by
  simp only [crossShift, canonShift, hx, hy]

/-- **A sweep following a class matching.**  Outside the exceptional set `Exc w`, every vertex of
the reserved part of the link of `w` went to the class the family `(ρ, σ)` prescribes on the other
side of the region. -/
def IsClassMatchedSweep (h : ℕ) (C : ℕ → Finset V) (R : Finset (Sym2 V)) (W' : Finset V)
    (X : V → Finset V) (x y : V → ℕ) (ρ σ : V → ℕ → ℕ) (S : Finset V) (g : V → V → V)
    (Exc : V → Finset V) : Prop :=
  ∀ (a : V) (α β : ℕ), α < h → β < h → a ∈ C (α * h + β) →
    ∀ w ∈ S, a ∈ X w → a ∈ resLink R W' w → a ∉ Exc w →
      IsCrossSideAt h C x y α β w (g w a) (ρ w β) (σ w α)

variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ}

/-- **The fibres of a class matching are small**: a row line of the design carries at most as many
outer vertices matching a given row class to a given column class as a cell of the design carries
outer vertices, and likewise for the columns. -/
def ClassMatchingFibres (ε : ℝ) (K : ℕ) (W W' : Finset V) (x y : V → ℕ) (ρ σ : V → ℕ → ℕ) :
    Prop :=
  (∀ p β P : ℕ, (((W \ W').filter (fun w => x w = p ∧ ρ w β = P)).card)
      ≤ 20 * (K * K) * gridClassSize ε K W'.card + 1 + gridSize ε K) ∧
  (∀ q α Q : ℕ, (((W \ W').filter (fun w => y w = q ∧ σ w α = Q)).card)
      ≤ 20 * (K * K) * gridClassSize ε K W'.card + 1 + gridSize ε K)

/-- The class matching of the canonical shift has small fibres: its fibres are cell fibres. -/
theorem classMatchingFibres_canonShift
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) :
    ClassMatchingFibres ε K W W' x y
      (fun w β => crossShift (gridSize ε K) (canonShift (gridSize ε K) x y) β w)
      (fun w α => crossShiftInv (gridSize ε K) (canonShift (gridSize ε K) x y) α w) := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  set φ : V → ℕ := canonShift h x y with hφdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hφlt : ∀ w, φ w < h := fun w => canonShift_lt hhpos x y w
  have hxlt : ∀ w ∈ W \ W', x w < h := fun w hw => hgrid.rowLt w hw
  have hylt : ∀ w ∈ W \ W', y w < h := fun w hw => hgrid.colLt w hw
  constructor
  · intro p β P
    show ((W \ W').filter (fun w => x w = p ∧ crossShift h φ β w = P)).card
      ≤ 20 * (K * K) * t + 1 + h
    rcases Finset.eq_empty_or_nonempty
      ((W \ W').filter (fun w => x w = p ∧ crossShift h φ β w = P)) with he | ⟨w₀, hw₀⟩
    · rw [he]; simp
    · obtain ⟨hw₀D, hw₀x, hw₀P⟩ := Finset.mem_filter.1 hw₀
      have hsub : (W \ W').filter (fun w => x w = p ∧ crossShift h φ β w = P)
          ⊆ (W \ W').filter (fun w => x w = p ∧ y w = y w₀) := by
        intro w hw
        obtain ⟨hwD, hwx, hwP⟩ := Finset.mem_filter.1 hw
        have hφeq : φ w = φ w₀ := crossShift_inj (hφlt w) (hφlt w₀) (by rw [hwP, hw₀P])
        exact Finset.mem_filter.2 ⟨hwD, hwx, canonShift_inj_row (x := x) (y := y) (hylt w hwD)
          (hylt w₀ hw₀D) (by rw [hwx, hw₀x]) (by simpa only [← hφdef] using hφeq)⟩
      have hcell := twoSided_cell_card_le hgrid (x := x) (y := y) p (y w₀)
      rw [← htdef] at hcell
      have h2 := Finset.card_le_card hsub
      omega
  · intro q α Q
    show ((W \ W').filter (fun w => y w = q ∧ crossShiftInv h φ α w = Q)).card
      ≤ 20 * (K * K) * t + 1 + h
    rcases Finset.eq_empty_or_nonempty
      ((W \ W').filter (fun w => y w = q ∧ crossShiftInv h φ α w = Q)) with he | ⟨w₀, hw₀⟩
    · rw [he]; simp
    · obtain ⟨hw₀D, hw₀y, hw₀Q⟩ := Finset.mem_filter.1 hw₀
      have hsub : (W \ W').filter (fun w => y w = q ∧ crossShiftInv h φ α w = Q)
          ⊆ (W \ W').filter (fun w => x w = x w₀ ∧ y w = q) := by
        intro w hw
        obtain ⟨hwD, hwy, hwQ⟩ := Finset.mem_filter.1 hw
        have hφeq : φ w = φ w₀ := crossShiftInv_inj (hφlt w) (hφlt w₀) (by rw [hwQ, hw₀Q])
        exact Finset.mem_filter.2 ⟨hwD, canonShift_inj_col (x := x) (y := y) (hxlt w hwD)
          (hxlt w₀ hw₀D) (by rw [hwy, hw₀y]) (by simpa only [← hφdef] using hφeq), hwy⟩
      have hcell := twoSided_cell_card_le hgrid (x := x) (y := y) (x w₀) q
      rw [← htdef] at hcell
      have h2 := Finset.card_le_card hsub
      omega

/-! ### A class matching with small fibres exists, and it varies inside every cell -/

/-- A line fibre of a shift balanced on every cell is as small as a cell fibre of the design.  This
is what makes the balanced shift of `BKLO.exists_cell_balanced_shift` — which, unlike the canonical
shift, does vary inside a cell — an admissible class matching. -/
theorem card_row_fibre_of_cell_balanced
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) {φ : V → ℕ}
    (hφcell : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    (p j : ℕ) :
    (((W \ W').filter (fun w => x w = p ∧ φ w = j)).card)
      ≤ 20 * (K * K) * gridClassSize ε K W'.card + 1 + gridSize ε K := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hhpos : 0 < h := gridSize_pos ε K
  set D : Finset V := W \ W' with hDdef
  set A : Finset V := D.filter (fun w => x w = p ∧ φ w = j) with hAdef
  have hyA : ∀ w ∈ A, y w ∈ Finset.range h := by
    intro w hw
    exact Finset.mem_range.2 (hgrid.colLt w (Finset.mem_filter.1 hw).1)
  have hyD : ∀ w ∈ D.filter (fun w => x w = p), y w ∈ Finset.range h := by
    intro w hw
    exact Finset.mem_range.2 (hgrid.colLt w (Finset.mem_filter.1 hw).1)
  have hcardA : A.card = ∑ q ∈ Finset.range h, (A.filter (fun w => y w = q)).card :=
    Finset.card_eq_sum_card_fiberwise hyA
  have hcardR : (D.filter (fun w => x w = p)).card
      = ∑ q ∈ Finset.range h, ((D.filter (fun w => x w = p)).filter (fun w => y w = q)).card :=
    Finset.card_eq_sum_card_fiberwise hyD
  have hstep : ∀ q ∈ Finset.range h, (A.filter (fun w => y w = q)).card
      ≤ ((D.filter (fun w => x w = p ∧ y w = q)).card) / h + 1 := by
    intro q _
    refine le_trans (Finset.card_le_card ?_) (hφcell p q j)
    intro w hw
    obtain ⟨hwA, hwy⟩ := Finset.mem_filter.1 hw
    obtain ⟨hwD, hwx, hwφ⟩ := Finset.mem_filter.1 hwA
    exact Finset.mem_filter.2 ⟨hwD, hwx, hwy, hwφ⟩
  have hfib : ∀ q ∈ Finset.range h,
      ((D.filter (fun w => x w = p)).filter (fun w => y w = q)).card
        = (D.filter (fun w => x w = p ∧ y w = q)).card := by
    intro q _
    congr 1
    ext w
    simp only [Finset.mem_filter]
    tauto
  set S1 : ℕ := ∑ q ∈ Finset.range h, ((D.filter (fun w => x w = p ∧ y w = q)).card) / h with hS1
  have hA1 : A.card ≤ S1 + h := by
    calc A.card = ∑ q ∈ Finset.range h, (A.filter (fun w => y w = q)).card := hcardA
      _ ≤ ∑ q ∈ Finset.range h, (((D.filter (fun w => x w = p ∧ y w = q)).card) / h + 1) :=
          Finset.sum_le_sum hstep
      _ = S1 + h := by rw [Finset.sum_add_distrib]; simp [hS1]
  have hmul : h * S1 ≤ (D.filter (fun w => x w = p)).card := by
    calc h * S1 = ∑ q ∈ Finset.range h, h * (((D.filter (fun w => x w = p ∧ y w = q)).card) / h) :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ q ∈ Finset.range h, ((D.filter (fun w => x w = p ∧ y w = q)).card) :=
          Finset.sum_le_sum (fun q _ => Nat.mul_div_le _ _)
      _ = (D.filter (fun w => x w = p)).card := by
          rw [hcardR]; exact (Finset.sum_congr rfl hfib).symm
  have hS1le : S1 ≤ (D.filter (fun w => x w = p)).card / h :=
    (Nat.le_div_iff_mul_le hhpos).2 (by rw [Nat.mul_comm]; exact hmul)
  have hrow : ((D.filter (fun w => x w = p)).card) / h
      ≤ 20 * (K * K) * gridClassSize ε K W'.card + 1 := twoSided_row_card_le hgrid p
  omega

/-- The column form of `BKLO.card_row_fibre_of_cell_balanced`. -/
theorem card_col_fibre_of_cell_balanced
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) {φ : V → ℕ}
    (hφcell : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    (q j : ℕ) :
    (((W \ W').filter (fun w => y w = q ∧ φ w = j)).card)
      ≤ 20 * (K * K) * gridClassSize ε K W'.card + 1 + gridSize ε K := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hhpos : 0 < h := gridSize_pos ε K
  set D : Finset V := W \ W' with hDdef
  set A : Finset V := D.filter (fun w => y w = q ∧ φ w = j) with hAdef
  have hxA : ∀ w ∈ A, x w ∈ Finset.range h := by
    intro w hw
    exact Finset.mem_range.2 (hgrid.rowLt w (Finset.mem_filter.1 hw).1)
  have hxD : ∀ w ∈ D.filter (fun w => y w = q), x w ∈ Finset.range h := by
    intro w hw
    exact Finset.mem_range.2 (hgrid.rowLt w (Finset.mem_filter.1 hw).1)
  have hcardA : A.card = ∑ p ∈ Finset.range h, (A.filter (fun w => x w = p)).card :=
    Finset.card_eq_sum_card_fiberwise hxA
  have hcardR : (D.filter (fun w => y w = q)).card
      = ∑ p ∈ Finset.range h, ((D.filter (fun w => y w = q)).filter (fun w => x w = p)).card :=
    Finset.card_eq_sum_card_fiberwise hxD
  have hstep : ∀ p ∈ Finset.range h, (A.filter (fun w => x w = p)).card
      ≤ ((D.filter (fun w => x w = p ∧ y w = q)).card) / h + 1 := by
    intro p _
    refine le_trans (Finset.card_le_card ?_) (hφcell p q j)
    intro w hw
    obtain ⟨hwA, hwx⟩ := Finset.mem_filter.1 hw
    obtain ⟨hwD, hwy, hwφ⟩ := Finset.mem_filter.1 hwA
    exact Finset.mem_filter.2 ⟨hwD, hwx, hwy, hwφ⟩
  have hfib : ∀ p ∈ Finset.range h,
      ((D.filter (fun w => y w = q)).filter (fun w => x w = p)).card
        = (D.filter (fun w => x w = p ∧ y w = q)).card := by
    intro p _
    congr 1
    ext w
    simp only [Finset.mem_filter]
    tauto
  set S1 : ℕ := ∑ p ∈ Finset.range h, ((D.filter (fun w => x w = p ∧ y w = q)).card) / h with hS1
  have hA1 : A.card ≤ S1 + h := by
    calc A.card = ∑ p ∈ Finset.range h, (A.filter (fun w => x w = p)).card := hcardA
      _ ≤ ∑ p ∈ Finset.range h, (((D.filter (fun w => x w = p ∧ y w = q)).card) / h + 1) :=
          Finset.sum_le_sum hstep
      _ = S1 + h := by rw [Finset.sum_add_distrib]; simp [hS1]
  have hmul : h * S1 ≤ (D.filter (fun w => y w = q)).card := by
    calc h * S1 = ∑ p ∈ Finset.range h, h * (((D.filter (fun w => x w = p ∧ y w = q)).card) / h) :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ p ∈ Finset.range h, ((D.filter (fun w => x w = p ∧ y w = q)).card) :=
          Finset.sum_le_sum (fun p _ => Nat.mul_div_le _ _)
      _ = (D.filter (fun w => y w = q)).card := by
          rw [hcardR]; exact (Finset.sum_congr rfl hfib).symm
  have hS1le : S1 ≤ (D.filter (fun w => y w = q)).card / h :=
    (Nat.le_div_iff_mul_le hhpos).2 (by rw [Nat.mul_comm]; exact hmul)
  have hcol : ((D.filter (fun w => y w = q)).card) / h
      ≤ 20 * (K * K) * gridClassSize ε K W'.card + 1 := twoSided_col_card_le hgrid q
  omega

/-- **A class matching with small fibres exists** — and, unlike the canonical shift, it varies
inside every cell, which is what feasibility needs.  It is the shift balanced on every cell of the
labelling (`BKLO.exists_cell_balanced_shift`), and it is an involution of the classes:
`σ w (ρ w β) = β`. -/
theorem exists_classMatching_fibres
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) :
    ∃ ρ σ : V → ℕ → ℕ,
      (∀ w β, ρ w β < gridSize ε K) ∧ (∀ w α, σ w α < gridSize ε K) ∧
      (∀ w β, β < gridSize ε K → σ w (ρ w β) = β) ∧
      ClassMatchingFibres ε K W W' x y ρ σ := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hhpos : 0 < h := gridSize_pos ε K
  obtain ⟨φ, hφlt, hφcell⟩ := exists_cell_balanced_shift (W \ W') x y hhpos
  refine ⟨fun w β => crossShift h φ β w, fun w α => crossShiftInv h φ α w,
    fun w β => crossShift_lt hhpos φ β w, fun w α => crossShiftInv_lt hhpos φ α w,
    fun w β hβ => crossShiftInv_crossShift hβ (hφlt w), ?_, ?_⟩
  · intro p β P
    show ((W \ W').filter (fun w => x w = p ∧ crossShift h φ β w = P)).card
      ≤ 20 * (K * K) * gridClassSize ε K W'.card + 1 + h
    rcases Finset.eq_empty_or_nonempty
      ((W \ W').filter (fun w => x w = p ∧ crossShift h φ β w = P)) with he | ⟨w₀, hw₀⟩
    · rw [he]; simp
    · obtain ⟨-, -, hw₀P⟩ := Finset.mem_filter.1 hw₀
      have hsub : (W \ W').filter (fun w => x w = p ∧ crossShift h φ β w = P)
          ⊆ (W \ W').filter (fun w => x w = p ∧ φ w = φ w₀) := by
        intro w hw
        obtain ⟨hwD, hwx, hwP⟩ := Finset.mem_filter.1 hw
        exact Finset.mem_filter.2 ⟨hwD, hwx,
          crossShift_inj (hφlt w) (hφlt w₀) (by rw [hwP, hw₀P])⟩
      exact le_trans (Finset.card_le_card hsub)
        (card_row_fibre_of_cell_balanced hgrid hφcell p (φ w₀))
  · intro q α Q
    show ((W \ W').filter (fun w => y w = q ∧ crossShiftInv h φ α w = Q)).card
      ≤ 20 * (K * K) * gridClassSize ε K W'.card + 1 + h
    rcases Finset.eq_empty_or_nonempty
      ((W \ W').filter (fun w => y w = q ∧ crossShiftInv h φ α w = Q)) with he | ⟨w₀, hw₀⟩
    · rw [he]; simp
    · obtain ⟨-, -, hw₀Q⟩ := Finset.mem_filter.1 hw₀
      have hsub : (W \ W').filter (fun w => y w = q ∧ crossShiftInv h φ α w = Q)
          ⊆ (W \ W').filter (fun w => y w = q ∧ φ w = φ w₀) := by
        intro w hw
        obtain ⟨hwD, hwy, hwQ⟩ := Finset.mem_filter.1 hw
        exact Finset.mem_filter.2 ⟨hwD, hwy,
          crossShiftInv_inj (hφlt w) (hφlt w₀) (by rw [hwQ, hw₀Q])⟩
      exact le_trans (Finset.card_le_card hsub)
        (card_col_fibre_of_cell_balanced hgrid hφcell q (φ w₀))

/-! ### Two classes of a region are matched -/

/-- **Two classes of a region carry a class-respecting matching.**  Every vertex of `W` misses at
most a quarter of every class (`IsGridTwoSidedReservoir.classBalancedSharp`), so as soon as the two
classes have the same number of places in the perturbed link, and the edges already used inside the
pair are few at every vertex, the two are matched by unused edges of `F`.  This is the step the
class-respecting part of a link is made of. -/
theorem exists_class_matching_avoiding
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (hW'W : W' ⊆ W)
    {i j : ℕ} (hi : i < gridSize ε K * gridSize ε K) (hj : j < gridSize ε K * gridSize ε K)
    {Xu : Finset V} (hXW' : Xu ⊆ W') {U : Finset (Sym2 V)} {m q : ℕ}
    (hq : ∀ k < gridSize ε K * gridSize ε K, (C k).card = q)
    (hcard : (C i ∩ Xu).card = (C j ∩ Xu).card)
    (hUA : ∀ a ∈ C i ∩ Xu, ((C j ∩ Xu).filter (fun b => s(a, b) ∈ U)).card ≤ m)
    (hUB : ∀ b ∈ C j ∩ Xu, ((C i ∩ Xu).filter (fun a => s(a, b) ∈ U)).card ≤ m)
    (hsize : q + 4 * m < 2 * (C i ∩ Xu).card) :
    ∃ f : V → V, (∀ a ∈ C i ∩ Xu, f a ∈ C j ∩ Xu) ∧
      (∀ a ∈ C i ∩ Xu, s(a, f a) ∈ F ∧ s(a, f a) ∉ U) ∧
      Set.InjOn f ((C i ∩ Xu : Finset V) : Set V) := by
  classical
  -- the half-degree count, at one vertex against one class
  have hmain : ∀ (a : V) (k : ℕ) (T : Finset V), a ∈ W' → k < gridSize ε K * gridSize ε K →
      T ⊆ C k → T ⊆ W' → (T.filter (fun b => s(a, b) ∈ U)).card ≤ m →
      q + 4 * m < 2 * T.card →
      T.card < 2 * (T.filter (fun b => s(a, b) ∈ F ∧ s(a, b) ∉ U)).card := by
    intro a k T haW' hk hTC hTW' hU hsz
    have hbal := hgrid.classBalancedSharp a (hW'W haW') k hk
    rw [hq k hk] at hbal
    have hsub : T.filter (fun b => ¬ (s(a, b) ∈ F ∧ s(a, b) ∉ U))
        ⊆ (nonNbrs F W' a ∩ C k) ∪ T.filter (fun b => s(a, b) ∈ U) := by
      intro b hb
      obtain ⟨hbT, hbr⟩ := Finset.mem_filter.1 hb
      by_cases hU' : s(a, b) ∈ U
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hbT, hU'⟩)
      · refine Finset.mem_union_left _ (Finset.mem_inter.2 ⟨?_, hTC hbT⟩)
        refine Finset.mem_sdiff.2 ⟨hTW' hbT, ?_⟩
        intro hmem
        exact hbr ⟨(mem_resLink.1 hmem).2, hU'⟩
    have hcards : (T.filter (fun b => ¬ (s(a, b) ∈ F ∧ s(a, b) ∉ U))).card
        ≤ (nonNbrs F W' a ∩ C k).card + (T.filter (fun b => s(a, b) ∈ U)).card :=
      le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have hsplit : (T.filter (fun b => s(a, b) ∈ F ∧ s(a, b) ∉ U)).card
        + (T.filter (fun b => ¬ (s(a, b) ∈ F ∧ s(a, b) ∉ U))).card = T.card :=
      Finset.card_filter_add_card_filter_not _
    omega
  -- the two sides
  have hA : ∀ a ∈ C i ∩ Xu, (C j ∩ Xu).card
      < 2 * ((C j ∩ Xu).filter (fun b => s(a, b) ∈ F ∧ s(a, b) ∉ U)).card := by
    intro a ha
    refine hmain a j (C j ∩ Xu) (hXW' (Finset.mem_inter.1 ha).2) hj Finset.inter_subset_left
      (fun z hz => hXW' (Finset.mem_inter.1 hz).2) (hUA a ha) ?_
    omega
  have hB : ∀ b ∈ C j ∩ Xu, (C i ∩ Xu).card
      < 2 * ((C i ∩ Xu).filter (fun a => s(a, b) ∈ F ∧ s(a, b) ∉ U)).card := by
    intro b hb
    have hswapU : ((C i ∩ Xu).filter (fun a => s(b, a) ∈ U))
        = ((C i ∩ Xu).filter (fun a => s(a, b) ∈ U)) := by
      refine Finset.filter_congr fun a _ => ?_
      rw [Sym2.eq_swap]
    have hswap : ((C i ∩ Xu).filter (fun a => s(b, a) ∈ F ∧ s(b, a) ∉ U))
        = ((C i ∩ Xu).filter (fun a => s(a, b) ∈ F ∧ s(a, b) ∉ U)) := by
      refine Finset.filter_congr fun a _ => ?_
      rw [Sym2.eq_swap]
    have := hmain b i (C i ∩ Xu) (hXW' (Finset.mem_inter.1 hb).2) hi Finset.inter_subset_left
      (fun z hz => hXW' (Finset.mem_inter.1 hz).2) (by rw [hswapU]; exact hUB b hb) (by omega)
    rwa [hswap] at this
  exact exists_matching_of_half_degree (r := fun a b => s(a, b) ∈ F ∧ s(a, b) ∉ U) hcard hA hB

/-- **The ledger of a sweep following a class matching with small fibres is spread**, as soon as
the leftovers of the sweep are spread.  Only three facts about the design enter: a vertex is seen
only through the row line and the column line of its own class, a cell holds few outer vertices,
and the matching has small fibres. -/
theorem ledgerSpread_of_classMatchedSweep
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 0 < K)
    (hbig : 512 ≤ gridClassSize ε K W'.card)
    {X : V → Finset V} {Exc : V → Finset V} {ρ σ : V → ℕ → ℕ}
    (hρlt : ∀ w β, ρ w β < gridSize ε K) (hσlt : ∀ w α, σ w α < gridSize ε K)
    (hfib : ClassMatchingFibres ε K W W' x y ρ σ)
    {S : Finset V} (hSD : S ⊆ W \ W') {g : V → V → V}
    (hXmult : ∀ a ∈ W', ((((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℕ) : ℝ)
      ≤ 2 * cleanEta ε K * (W.card : ℝ))
    (hcross : IsClassMatchedSweep (gridSize ε K) C R W' X x y ρ σ S g Exc)
    (hexc : ExcLedgerSpread ε K W' C g S Exc) :
    LedgerSpread ε K W' C X x y S g := by
  classical
  obtain ⟨hρfib, hσfib⟩ := hfib
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hwide : 6400 * (K * K) ≤ h := gridSize_ge_of_eps_small hε hε' K
  have hKK : 1 ≤ K * K := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hK.ne' hK.ne')
  have ht1 : 1 ≤ t := by omega
  have hxlt : ∀ w ∈ W \ W', x w < h := fun w hw => hgrid.rowLt w hw
  have hylt : ∀ w ∈ W \ W', y w < h := fun w hw => hgrid.colLt w hw
  have hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j) := fun i hi j hj hij =>
    hgrid.classDisjoint i hi j hj hij
  intro a ha P hP Q hQ
  set E₀ : Finset V := (W \ W').filter (fun u => a ∈ X u \ resLink R W' u) with hE₀def
  set E₁ : Finset V := S.filter (fun w => a ∈ Exc w ∧ g w a ∈ gridRegion h C P Q) with hE₁def
  set E : Finset V := E₀ ∪ E₁ with hEdef
  have hE₀bud : 256 * E₀.card ≤ h * t := by
    have h4 : 4 * E₀.card ≤ t := twoSided_perturbation_quarter hgrid hK (hXmult a ha)
    have h64 : 64 * t ≤ h * t := Nat.mul_le_mul_right t (by omega)
    omega
  have hEbud : 8 * E.card ≤ h * t / 16 := by
    have h0 : 16 * E₀.card ≤ h * t / 16 := by
      have := eight_le_div_sixteen (x := h * t) (F := 2 * E₀.card) (by omega)
      omega
    have h1 : 16 * E₁.card ≤ h * t / 16 := hexc a ha P hP Q hQ
    have hu : E.card ≤ E₀.card + E₁.card := Finset.card_union_le _ _
    omega
  obtain ⟨α, β, hα, hβ, hrule⟩ : ∃ α β : ℕ, α < h ∧ β < h ∧
      ∀ w ∈ S, a ∈ X w → g w a ∈ gridRegion h C P Q → w ∈ E ∨
        IsCrossSideAt h C x y α β w (g w a) (ρ w β) (σ w α) := by
    by_cases hcls : ∃ i, i < h * h ∧ a ∈ C i
    · obtain ⟨i, hi, hai⟩ := hcls
      refine ⟨i / h, i % h, Nat.div_lt_of_lt_mul (by omega), Nat.mod_lt _ hhpos, ?_⟩
      have hid : i / h * h + i % h = i := by
        have hdm := Nat.div_add_mod i h
        rw [Nat.mul_comm h (i / h)] at hdm
        exact hdm
      intro w hwS haX hreg
      by_cases hres : a ∈ resLink R W' w
      · by_cases hexcw : a ∈ Exc w
        · exact Or.inl (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hwS, hexcw, hreg⟩))
        · exact Or.inr (hcross a (i / h) (i % h) (Nat.div_lt_of_lt_mul (by omega))
            (Nat.mod_lt _ hhpos) (by rw [hid]; exact hai) w hwS haX hres hexcw)
      · exact Or.inl (Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨hSD hwS, Finset.mem_sdiff.2 ⟨haX, hres⟩⟩))
    · refine ⟨0, 0, hhpos, hhpos, ?_⟩
      intro w hwS haX _
      refine Or.inl (Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨hSD hwS, Finset.mem_sdiff.2 ⟨haX, ?_⟩⟩))
      intro hres
      have h1 := (Finset.mem_inter.1 (hgrid.linkSubset w (hSD hwS) hres)).2
      rw [gridRegion_eq_biUnion] at h1
      obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.1 h1
      exact hcls ⟨i, gridIdx_lt (hxlt w (hSD hwS)) (hylt w (hSD hwS)) hi, hai⟩
  have hcellbud : ∀ p q : ℕ, 128 * (((W \ W').filter (fun u => x u = p ∧ y u = q)).card)
      ≤ h * t := fun p q =>
    crossSide_cell_budget hKK ht1 hwide (twoSided_cell_card_le hgrid p q)
  have hF2 : 8 * (S.filter (fun w => x w = α ∧ y w = Q)).card ≤ h * t / 16 := by
    refine eight_le_div_sixteen (le_trans (Nat.mul_le_mul_left 128 ?_) (hcellbud α Q))
    exact Finset.card_le_card fun w hw => by
      obtain ⟨hwS, hwx, hwy⟩ := Finset.mem_filter.1 hw
      exact Finset.mem_filter.2 ⟨hSD hwS, hwx, hwy⟩
  have hF3 : 8 * (S.filter (fun w => y w = β ∧ x w = P)).card ≤ h * t / 16 := by
    refine eight_le_div_sixteen (le_trans (Nat.mul_le_mul_left 128 ?_) (hcellbud P β))
    exact Finset.card_le_card fun w hw => by
      obtain ⟨hwS, hwy, hwx⟩ := Finset.mem_filter.1 hw
      exact Finset.mem_filter.2 ⟨hSD hwS, hwx, hwy⟩
  have hF1 : 8 * (S.filter (fun w => x w = α ∧ ρ w β = P)).card ≤ h * t / 16 := by
    refine eight_le_div_sixteen ?_
    have hsub : (S.filter (fun w => x w = α ∧ ρ w β = P))
        ⊆ (W \ W').filter (fun w => x w = α ∧ ρ w β = P) := by
      intro w hw
      obtain ⟨hwS, hwx, hwP⟩ := Finset.mem_filter.1 hw
      exact Finset.mem_filter.2 ⟨hSD hwS, hwx, hwP⟩
    refine le_trans (Nat.mul_le_mul_left 128 (Finset.card_le_card hsub)) ?_
    exact crossSide_shift_budget hKK hbig hwide (hρfib α β P)
  have hF4 : 8 * (S.filter (fun w => y w = β ∧ σ w α = Q)).card ≤ h * t / 16 := by
    refine eight_le_div_sixteen ?_
    have hsub : (S.filter (fun w => y w = β ∧ σ w α = Q))
        ⊆ (W \ W').filter (fun w => y w = β ∧ σ w α = Q) := by
      intro w hw
      obtain ⟨hwS, hwy, hwQ⟩ := Finset.mem_filter.1 hw
      exact Finset.mem_filter.2 ⟨hSD hwS, hwy, hwQ⟩
    refine le_trans (Nat.mul_le_mul_left 128 (Finset.card_le_card hsub)) ?_
    exact crossSide_shift_budget hKK hbig hwide (hσfib β α Q)
  exact regionLoad_le_of_crossSide_bounds_region (C := C) (X := X) (g := g) (S := S) (E := E)
    (x := x) (y := y) (a := a) (α := α) (β := β)
    (ρ := fun w => ρ w β) (σ := fun w => σ w α)
    hdisj (fun w hw => hxlt w (hSD hw)) (fun w hw => hylt w (hSD hw))
    (fun w _ => hρlt w β) (fun w _ => hσlt w α) hP hQ
    hrule hF1 hF2 hF3 hF4 hEbud

end BKLO
