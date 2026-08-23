/-
# The class-matched part of the partner-class load is a cell-shift fibre

`BKLO/AX2PartnerClassLedger.lean` splits the partner-class load of a place into five terms, and
`BKLO/AX2PartnerClassSpread.lean` observes that the two *routed* terms are capped by the counted
invariant.  This file caps the two terms that no cap of the invariant touches — the class-matched
term `BKLO.prescribedClassLoad` and the cycle term `BKLO.cycleClassLoad` — and it caps them by a
quantity of order `|cell| / h`, far below a class fibre.

The mechanism is the **cell-balanced shift** `φ` of `BKLO.exists_cell_balanced_shift`.  At a link
`w` the class matching is the shift by `φ w`: a place `a` of the class `C (α h + β)` is paired into
`C (crossShift h φ β w · h + y w)` or into `C (x w · h + crossShiftInv h φ α w)`.  Asking that the
partner land in one *fixed* class `C i` therefore pins the cell of `w` — `(α, i % h)` on the first
side, `(i / h, β)` on the second — **and** pins the shift value `φ w`
(`BKLO.crossShift_determines_shift`).  So the links that pair `a` into `C i` by the class matching
form at most two cell-shift fibres, and the balance hypothesis on `φ` bounds each of them by
`|cell| / h + 1`.

The only links that escape the argument are those at which `a` lies in the link system but *outside*
the reserved link, where `BKLO.IsClassMatchedSweep` says nothing; the sweep-wide perturbation
multiplicity bounds their number.

* `BKLO.crossShift_determines_shift` — a shift value is determined by one of its images;
* `BKLO.card_cell_shift_fibre_le` — a cell-shift fibre of the design is small;
* `BKLO.prescribedClassLoad_le_cellShift`, `BKLO.cycleClassLoad_le_cellShift` — the two bounds.

Everything here is `sorry`-free.
-/
import BKLO.AX2PartnerClassLedger

open Finset

namespace BKLO

/-! ### A shift value is pinned by one of its images -/

/-- The two digits of a grid class index. -/
theorem grid_div_mod {h A b : ℕ} (hb : b < h) :
    (A * h + b) / h = A ∧ (A * h + b) % h = b := by
  have hh : 0 < h := lt_of_le_of_lt (Nat.zero_le b) hb
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hh, Nat.div_eq_of_lt hb, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-- **The shift is determined by one image.**  If the class matching of the link `w` sends the
column digit `β` to the row digit `P`, the shift `φ w` is `(P + (h - β)) % h`. -/
theorem crossShift_determines_shift {V : Type} {h β P : ℕ} {φ : V → ℕ} {w : V} (hβ : β < h)
    (hφ : φ w < h) (hP : crossShift h φ β w = P) : φ w = (P + (h - β)) % h := by
  have hh : 0 < h := lt_of_le_of_lt (Nat.zero_le β) hβ
  subst hP
  rw [crossShift, Nat.mod_add_mod]
  have he : β + φ w + (h - β) = φ w + h := by omega
  rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hφ]

variable {V : Type} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ}

/-! ### A cell-shift fibre of the design is small -/

/-- **A cell of the design carrying one value of the shift is small.**  The cell-balance hypothesis
on `φ` divides the cell of `BKLO.twoSided_cell_card_le` into `h` pieces of the average size. -/
theorem card_cell_shift_fibre_le (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {φ : V → ℕ}
    (hφcell : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    (p q j : ℕ) :
    (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (20 * (K * K) * gridClassSize ε K W'.card + 1) / gridSize ε K + 1 := by
  have h1 := hφcell p q j
  have h2 := twoSided_cell_card_le hgrid p q
  have h3 : (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K
      ≤ (20 * (K * K) * gridClassSize ε K W'.card + 1) / gridSize ε K :=
    Nat.div_le_div_right h2
  omega

/-! ### The class-matched term -/

/-- **The class-matched part of the partner-class load is two cell-shift fibres and the
perturbation.**  At a link at which `a` lies in the reserved link, the class matching pins both the
cell and the shift of the link, so the class-matched links pairing `a` into `C i` fall into two
cell-shift fibres; the remaining links are those at which `a` lies outside the reserved link, whose
number the sweep-wide perturbation multiplicity `N` bounds. -/
theorem prescribedClassLoad_le_cellShift
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hφcell : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    {X : V → Finset V} {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    (hSD : S ⊆ W \ W')
    (hsweep : IsClassMatchedSweep (gridSize ε K) C R W' X x y
      (fun w β => crossShift (gridSize ε K) φ β w)
      (fun w α => crossShiftInv (gridSize ε K) φ α w) S g Exc)
    {a : V} {N : ℕ}
    (hmult : (((W \ W').filter (fun w => a ∈ X w ∧ a ∉ resLink R W' w)).card) ≤ N)
    {i : ℕ} (hi : i < gridSize ε K * gridSize ε K) :
    prescribedClassLoad C X S g Exc a i
      ≤ N + 2 * ((20 * (K * K) * gridClassSize ε K W'.card + 1) / gridSize ε K + 1) := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hhpos : 0 < h := gridSize_pos ε K
  set B : ℕ := (20 * (K * K) * gridClassSize ε K W'.card + 1) / h + 1 with hBdef
  set P0 : Finset V := (W \ W').filter (fun w => a ∈ X w ∧ a ∉ resLink R W' w) with hP0
  -- every class-matched link at which `a` lies in the reserved link puts `a` in a class
  by_cases hex : ∃ k, k < h * h ∧ a ∈ C k
  · obtain ⟨k, hk, hak⟩ := hex
    set α : ℕ := k / h with hα
    set β : ℕ := k % h with hβ
    have hβlt : β < h := Nat.mod_lt _ hhpos
    have hαlt : α < h := by
      rw [hα]
      exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)
    have hkeq : k = α * h + β := by
      rw [hα, hβ, Nat.div_add_mod']
    have haC : a ∈ C (α * h + β) := by rwa [← hkeq]
    set j₁ : ℕ := (i / h + (h - β)) % h with hj₁
    set j₂ : ℕ := (α + (h - i % h)) % h with hj₂
    set F₁ : Finset V := (W \ W').filter (fun w => x w = α ∧ y w = i % h ∧ φ w = j₁) with hF₁
    set F₂ : Finset V := (W \ W').filter (fun w => x w = i / h ∧ y w = β ∧ φ w = j₂) with hF₂
    have hsub : S.filter (fun w => a ∈ X w ∧ a ∉ Exc w ∧ g w a ∈ C i) ⊆ (P0 ∪ F₁) ∪ F₂ := by
      intro w hw
      obtain ⟨hwS, hwX, hwE, hwC⟩ : w ∈ S ∧ a ∈ X w ∧ a ∉ Exc w ∧ g w a ∈ C i := by
        obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hw
        exact ⟨h1, h2.1, h2.2.1, h2.2.2⟩
      have hwD : w ∈ W \ W' := hSD hwS
      by_cases hres : a ∈ resLink R W' w
      · have hxw : x w < h := hgrid.rowLt w hwD
        have hyw : y w < h := hgrid.colLt w hwD
        have hφw : φ w < h := hφlt w
        have hcross := hsweep a α β hαlt hβlt haC w hwS hwX hres hwE
        have hidx : ∀ l : ℕ, l < h * h → g w a ∈ C l → l = i := by
          intro l hl hmem
          by_contra hne
          exact (Finset.disjoint_left.1 (hgrid.classDisjoint l hl i hi hne)) hmem hwC
        rcases hcross with ⟨hxa, hmem⟩ | ⟨hyb, hmem⟩
        · -- the row side: the partner lies in `C (crossShift β · h + y w)`
          have hlt : crossShift h φ β w < h := crossShift_lt hhpos φ β w
          have heq : crossShift h φ β w * h + y w = i := hidx _ (grid_idx_lt hlt hyw) hmem
          have hdig : crossShift h φ β w = i / h ∧ y w = i % h := by
            rw [← heq]
            exact ⟨(grid_div_mod hyw).1.symm, (grid_div_mod hyw).2.symm⟩
          have hφeq : φ w = j₁ :=
            crossShift_determines_shift (φ := φ) (w := w) hβlt hφw hdig.1
          exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.2 ⟨hwD, hxa, hdig.2, hφeq⟩))
        · -- the column side: the partner lies in `C (x w · h + crossShiftInv α)`
          have hlt : crossShiftInv h φ α w < h := crossShiftInv_lt hhpos φ α w
          have heq : x w * h + crossShiftInv h φ α w = i := hidx _ (grid_idx_lt hxw hlt) hmem
          have hdig : x w = i / h ∧ crossShiftInv h φ α w = i % h := by
            rw [← heq]
            exact ⟨(grid_div_mod hlt).1.symm, (grid_div_mod hlt).2.symm⟩
          have hback : crossShift h φ (i % h) w = α := by
            rw [← hdig.2]
            exact crossShift_crossShiftInv hαlt hφw
          have hφeq : φ w = j₂ :=
            crossShift_determines_shift (φ := φ) (w := w) (Nat.mod_lt _ hhpos) hφw hback
          exact Finset.mem_union_right _
            (Finset.mem_filter.2 ⟨hwD, hdig.1, hyb, hφeq⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨hwD, hwX, hres⟩))
    have hc1 : F₁.card ≤ B := card_cell_shift_fibre_le hgrid hφcell _ _ _
    have hc2 : F₂.card ≤ B := card_cell_shift_fibre_le hgrid hφcell _ _ _
    have hcard : prescribedClassLoad C X S g Exc a i ≤ (P0.card + F₁.card) + F₂.card := by
      refine le_trans (Finset.card_le_card hsub) ?_
      exact le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    omega
  · -- `a` lies in no class: every class-matched link is a perturbation link
    push_neg at hex
    have hsub : S.filter (fun w => a ∈ X w ∧ a ∉ Exc w ∧ g w a ∈ C i) ⊆ P0 := by
      intro w hw
      obtain ⟨hwS, hwX⟩ : w ∈ S ∧ a ∈ X w := by
        obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hw
        exact ⟨h1, h2.1⟩
      have hwD : w ∈ W \ W' := hSD hwS
      refine Finset.mem_filter.2 ⟨hwD, hwX, ?_⟩
      intro hres
      have hreg : a ∈ gridRegion h C (x w) (y w) :=
        (Finset.mem_inter.1 (hgrid.linkSubset w hwD hres)).2
      rw [gridRegion_eq_biUnion] at hreg
      obtain ⟨l, hl, hal⟩ := Finset.mem_biUnion.1 hreg
      exact hex l (gridIdx_lt (hgrid.rowLt w hwD) (hgrid.colLt w hwD) hl) hal
    have := Finset.card_le_card hsub
    have : prescribedClassLoad C X S g Exc a i ≤ N := le_trans this hmult
    omega

/-! ### The cycle term -/

/-- **The cycle part of the partner-class load is two cell-shift fibres.**  A cycle leftover lies in
one of the two classes of the three-class cycle of its link, and both the class it lies in and the
class it is paired into are shifts of the cell of the link: asking for a fixed place and a fixed
partner class pins the cell and the shift. -/
theorem cycleClassLoad_le_cellShift
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hφcell : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    {S : Finset V} {g : V → V → V} {Cc Cr : V → Finset V} (hSD : S ⊆ W \ W')
    (hcyc : IsCycleRoutedLeftover (gridSize ε K) C x y φ S g Cc Cr)
    (a : V) {i : ℕ} (hi : i < gridSize ε K * gridSize ε K) :
    cycleClassLoad C S g Cc Cr a i
      ≤ 2 * ((20 * (K * K) * gridClassSize ε K W'.card + 1) / gridSize ε K + 1) := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hhpos : 0 < h := gridSize_pos ε K
  set B : ℕ := (20 * (K * K) * gridClassSize ε K W'.card + 1) / h + 1 with hBdef
  by_cases hex : ∃ k, k < h * h ∧ a ∈ C k
  · obtain ⟨k, hk, hak⟩ := hex
    set α : ℕ := k / h with hα
    set β : ℕ := k % h with hβ
    have hβlt : β < h := Nat.mod_lt _ hhpos
    have hαlt : α < h := by
      rw [hα]
      exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hk)
    have hkeq : k = α * h + β := by rw [hα, hβ, Nat.div_add_mod']
    have haC : a ∈ C (α * h + β) := by rwa [← hkeq]
    -- the two fibres
    set j₁ : ℕ := (α + (h - β)) % h with hj₁
    set j₂ : ℕ := (i / h + (h - i % h)) % h with hj₂
    set F₁ : Finset V := (W \ W').filter (fun w => x w = α ∧ y w = i % h ∧ φ w = j₁) with hF₁
    set F₂ : Finset V := (W \ W').filter (fun w => x w = i / h ∧ y w = β ∧ φ w = j₂) with hF₂
    have hsub : S.filter (fun w => (a ∈ Cc w ∨ a ∈ Cr w) ∧ g w a ∈ C i) ⊆ F₁ ∪ F₂ := by
      intro w hw
      obtain ⟨hwS, hwmem, hwC⟩ : w ∈ S ∧ (a ∈ Cc w ∨ a ∈ Cr w) ∧ g w a ∈ C i := by
        obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hw
        exact ⟨h1, h2.1, h2.2⟩
      have hwD : w ∈ W \ W' := hSD hwS
      have hxw : x w < h := hgrid.rowLt w hwD
      have hyw : y w < h := hgrid.colLt w hwD
      have hφw : φ w < h := hφlt w
      have hidx : ∀ l : ℕ, l < h * h → g w a ∈ C l → l = i := by
        intro l hl hmem
        by_contra hne
        exact (Finset.disjoint_left.1 (hgrid.classDisjoint l hl i hi hne)) hmem hwC
      have hself : ∀ l : ℕ, l < h * h → a ∈ C l → l = α * h + β := by
        intro l hl hmem
        by_contra hne
        exact (Finset.disjoint_left.1
          (hgrid.classDisjoint l hl (α * h + β) (by rw [← hkeq]; exact hk) hne)) hmem haC
      rcases hwmem with hcc | hcr
      · -- a column-cycle leftover: `a` sits in the row class of the cycle
        obtain ⟨hain, hgin⟩ := (hcyc w hwS).1 a hcc
        have hσlt : crossShiftInv h φ (x w) w < h := crossShiftInv_lt hhpos φ (x w) w
        have hρlt : crossShift h φ (y w) w < h := crossShift_lt hhpos φ (y w) w
        have h1 : x w * h + crossShiftInv h φ (x w) w = α * h + β :=
          hself _ (grid_idx_lt hxw hσlt) hain
        have hdig1 : x w = α ∧ crossShiftInv h φ (x w) w = β :=
          gridDigits_inj hσlt hβlt h1
        have h2 : crossShift h φ (y w) w * h + y w = i := hidx _ (grid_idx_lt hρlt hyw) hgin
        have hdig2 : y w = i % h := by rw [← h2]; exact (grid_div_mod hyw).2.symm
        have hback : crossShift h φ β w = α := by
          rw [← hdig1.2, ← hdig1.1]
          exact crossShift_crossShiftInv hxw hφw
        have hφeq : φ w = j₁ := crossShift_determines_shift (φ := φ) (w := w) hβlt hφw hback
        exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hwD, hdig1.1, hdig2, hφeq⟩)
      · -- a row-cycle leftover: `a` sits in the column class of the cycle
        obtain ⟨hain, hgin⟩ := (hcyc w hwS).2 a hcr
        have hρlt : crossShift h φ (y w) w < h := crossShift_lt hhpos φ (y w) w
        have hσlt : crossShiftInv h φ (x w) w < h := crossShiftInv_lt hhpos φ (x w) w
        have h1 : crossShift h φ (y w) w * h + y w = α * h + β :=
          hself _ (grid_idx_lt hρlt hyw) hain
        have hdig1 : crossShift h φ (y w) w = α ∧ y w = β := gridDigits_inj hyw hβlt h1
        have h2 : x w * h + crossShiftInv h φ (x w) w = i := hidx _ (grid_idx_lt hxw hσlt) hgin
        have hdig2 : x w = i / h ∧ crossShiftInv h φ (x w) w = i % h := by
          rw [← h2]
          exact ⟨(grid_div_mod hσlt).1.symm, (grid_div_mod hσlt).2.symm⟩
        have hback : crossShift h φ (i % h) w = x w := by
          rw [← hdig2.2]
          exact crossShift_crossShiftInv hxw hφw
        have hφeq : φ w = (x w + (h - i % h)) % h :=
          crossShift_determines_shift (φ := φ) (w := w) (Nat.mod_lt _ hhpos) hφw hback
        refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hwD, hdig2.1, hdig1.2, ?_⟩)
        rw [hφeq, hj₂, hdig2.1]
    have hc1 : F₁.card ≤ B := card_cell_shift_fibre_le hgrid hφcell _ _ _
    have hc2 : F₂.card ≤ B := card_cell_shift_fibre_le hgrid hφcell _ _ _
    have hcard : cycleClassLoad C S g Cc Cr a i ≤ F₁.card + F₂.card :=
      le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    omega
  · -- `a` lies in no class: it is no cycle leftover at all
    push_neg at hex
    have hsub : S.filter (fun w => (a ∈ Cc w ∨ a ∈ Cr w) ∧ g w a ∈ C i) ⊆ (∅ : Finset V) := by
      intro w hw
      obtain ⟨hwS, hwmem, -⟩ : w ∈ S ∧ (a ∈ Cc w ∨ a ∈ Cr w) ∧ g w a ∈ C i := by
        obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hw
        exact ⟨h1, h2.1, h2.2⟩
      have hwD : w ∈ W \ W' := hSD hwS
      have hxw : x w < h := hgrid.rowLt w hwD
      have hyw : y w < h := hgrid.colLt w hwD
      exfalso
      rcases hwmem with hcc | hcr
      · obtain ⟨hain, -⟩ := (hcyc w hwS).1 a hcc
        exact hex _ (grid_idx_lt hxw (crossShiftInv_lt hhpos φ (x w) w)) hain
      · obtain ⟨hain, -⟩ := (hcyc w hwS).2 a hcr
        exact hex _ (grid_idx_lt (crossShift_lt hhpos φ (y w) w) hyw) hain
    have := Finset.card_le_card hsub
    simp only [Finset.card_empty, Nat.le_zero] at this
    have : cycleClassLoad C S g Cc Cr a i = 0 := this
    omega

end BKLO
