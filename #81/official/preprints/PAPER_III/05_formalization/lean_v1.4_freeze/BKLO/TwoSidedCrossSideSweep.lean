/-
# The cross-side sweep: the ledger of AX2 §10 is a theorem, not an invariant.

`BKLO.regionLoad_le_crossSide` (`BKLO/TwoSidedCrossSide.lean`) bounds a ledger entry of a sweep
that obeys the cross-side rule by two cell fibres and the two free coordinates of the rule.  This
file fixes the free coordinates once and for all — a **shift** `φ` of the outer vertices, balanced
on every cell, which exists by enumeration (`BKLO.exists_cell_balanced_shift`) — and proves that
the resulting discipline keeps the ledger inside the budget of the sweep:

* `BKLO.crossShift`, `BKLO.crossShiftInv` — the class matching of a link: the row class
  `(x u, s)` is paired with the column class `((s + φ u) % h, y u)`, and back.  They are mutually
  inverse, so the rule is consistent with an involution.
* `BKLO.IsCrossSideSweep` — the discipline: every pairing already chosen sent each vertex of the
  reserved part of its link to the class the shift prescribes, on the *other* side of the region.
* `BKLO.ledgerSpread_of_crossSideSweep` — **the ledger is then automatically spread**: every entry
  is at most `h t / 16`, with no bookkeeping and no invariant to maintain.  Only three design
  facts enter: a vertex of a class is seen only through its own row line and column line, a cell
  holds few outer vertices (`cellFibre`), and a row line holds few outer vertices per value of the
  shift (`rowFibre` plus the balance of `φ`).

This is what the least-loaded bookkeeping was supposed to achieve.  The reason no bookkeeping is
needed is the confinement of a class: a vertex `a` of the class `C (α h + β)` belongs to the
reserved link of `w` only if `x w = α` or `y w = β`, so the outer vertices that can ever pair `a`
lie on the two lines of the grid through `a`'s class — and the cross-side rule sends the partner
to the *other* line, where the load is spread by the shift.

What is left of AX2 §10 at the two-sided design is therefore the one-link matching demand: pair up
the link of one outer vertex, class by class, following the shift — a bipartite matching between
the row part and the column part of a region, which have exactly the same size by
`IsGridTwoSidedReservoir.rowColBalanced`.

Everything here is `sorry`-free.
-/
import BKLO.TwoSidedCrossSide

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The class matching of a link -/

/-- The column class the row class `s` of a link is paired with: the shift by `φ w`. -/
def crossShift (h : ℕ) (φ : V → ℕ) (s : ℕ) (w : V) : ℕ := (s + φ w) % h

/-- The row class the column class `r` of a link is paired with: the inverse shift. -/
def crossShiftInv (h : ℕ) (φ : V → ℕ) (r : ℕ) (w : V) : ℕ := (r + (h - φ w)) % h

omit [DecidableEq V] in
theorem crossShift_lt {h : ℕ} (hh : 0 < h) (φ : V → ℕ) (s : ℕ) (w : V) :
    crossShift h φ s w < h := Nat.mod_lt _ hh

omit [DecidableEq V] in
theorem crossShiftInv_lt {h : ℕ} (hh : 0 < h) (φ : V → ℕ) (r : ℕ) (w : V) :
    crossShiftInv h φ r w < h := Nat.mod_lt _ hh

omit [DecidableEq V] in
/-- The two shifts are mutually inverse, so a cross-side rule can be an involution. -/
theorem crossShiftInv_crossShift {h : ℕ} {φ : V → ℕ} {s : ℕ} {w : V} (hs : s < h)
    (hφ : φ w < h) : crossShiftInv h φ (crossShift h φ s w) w = s := by
  have hle : φ w ≤ h := hφ.le
  have h1 : (s + φ w) % h ≡ s + φ w [MOD h] := Nat.mod_modEq _ _
  have h2 : (s + φ w) % h + (h - φ w) ≡ (s + φ w) + (h - φ w) [MOD h] :=
    Nat.ModEq.add_right _ h1
  have h3 : (s + φ w) + (h - φ w) = s + h := by omega
  rw [h3] at h2
  have h4 : ((s + φ w) % h + (h - φ w)) % h = (s + h) % h := h2
  rw [crossShiftInv, crossShift, h4, Nat.add_mod_right, Nat.mod_eq_of_lt hs]

omit [DecidableEq V] in
/-- Two outer vertices that send the class `s` to the same class have the same shift. -/
theorem crossShift_inj {h : ℕ} {φ : V → ℕ} {s : ℕ} {w w' : V} (hφ : φ w < h) (hφ' : φ w' < h)
    (heq : crossShift h φ s w = crossShift h φ s w') : φ w = φ w' := by
  have h1 : s + φ w ≡ s + φ w' [MOD h] := heq
  have h2 : φ w ≡ φ w' [MOD h] := Nat.ModEq.add_left_cancel' s h1
  have h3 : φ w % h = φ w' % h := h2
  rwa [Nat.mod_eq_of_lt hφ, Nat.mod_eq_of_lt hφ'] at h3

omit [DecidableEq V] in
/-- The same, for the inverse shift. -/
theorem crossShiftInv_inj {h : ℕ} {φ : V → ℕ} {r : ℕ} {w w' : V} (hφ : φ w < h) (hφ' : φ w' < h)
    (heq : crossShiftInv h φ r w = crossShiftInv h φ r w') : φ w = φ w' := by
  have h1 : r + (h - φ w) ≡ r + (h - φ w') [MOD h] := heq
  have h2 : (h - φ w) ≡ (h - φ w') [MOD h] := Nat.ModEq.add_left_cancel' r h1
  have h3 : (h - φ w) + (φ w + φ w') ≡ (h - φ w') + (φ w + φ w') [MOD h] :=
    Nat.ModEq.add_right _ h2
  have e1 : (h - φ w) + (φ w + φ w') = h + φ w' := by omega
  have e2 : (h - φ w') + (φ w + φ w') = h + φ w := by omega
  rw [e1, e2] at h3
  have h4 : φ w' ≡ φ w [MOD h] := Nat.ModEq.add_left_cancel' h h3
  have h5 : φ w' % h = φ w % h := h4
  rw [Nat.mod_eq_of_lt hφ', Nat.mod_eq_of_lt hφ] at h5
  exact h5.symm

/-! ### The discipline -/

/-- **The cross-side sweep.**  Every pairing already chosen sent each vertex `a` of the *reserved*
part of its link to the class prescribed by the shift on the other side of the region: a vertex of
the row class `(x w, β)` goes to the column class `(crossShift h φ β w, y w)`, and a vertex of the
column class `(α, y w)` goes to the row class `(x w, crossShiftInv h φ α w)`. -/
def IsCrossSideSweep (h : ℕ) (C : ℕ → Finset V) (R : Finset (Sym2 V)) (W' : Finset V)
    (X : V → Finset V) (x y φ : V → ℕ) (S : Finset V) (g : V → V → V) : Prop :=
  ∀ (a : V) (α β : ℕ), α < h → β < h → a ∈ C (α * h + β) →
    ∀ w ∈ S, a ∈ X w → a ∈ resLink R W' w →
      IsCrossSideAt h C x y α β w (g w a) (crossShift h φ β w) (crossShiftInv h φ α w)

/-! ### The arithmetic of the budget -/

/-- The budget of a cell fibre. -/
theorem crossSide_cell_budget {K h t n : ℕ} (hK : 1 ≤ K * K) (ht : 1 ≤ t)
    (hh : 6400 * (K * K) ≤ h) (hn : n ≤ 20 * (K * K) * t + 1) : 128 * n ≤ h * t := by
  have h1 : 1 ≤ K * K * t := Nat.mul_le_mul hK ht
  calc 128 * n ≤ 128 * (20 * (K * K) * t + 1) := Nat.mul_le_mul_left _ hn
    _ = 2560 * (K * K * t) + 128 := by ring
    _ ≤ 2560 * (K * K * t) + 128 * (K * K * t) := by
        have := Nat.mul_le_mul_left 128 h1; omega
    _ = 2688 * (K * K) * t := by ring
    _ ≤ 6400 * (K * K) * t := Nat.mul_le_mul_right _ (by omega)
    _ ≤ h * t := Nat.mul_le_mul_right _ hh

/-- The budget of a line fibre of the shift. -/
theorem crossSide_shift_budget {K h t b : ℕ} (hK : 1 ≤ K * K) (ht : 512 ≤ t)
    (hh : 6400 * (K * K) ≤ h) (hb : b ≤ 20 * (K * K) * t + 1 + h) : 128 * b ≤ h * t := by
  have hh1 : 1 ≤ h := le_trans (by omega) hh
  have hstep : 10 * (2560 * (K * K * t) + 256 * h) ≤ 10 * (h * t) := by
    have e1 : 25600 * (K * K * t) ≤ 4 * (h * t) := by
      have : 4 * (6400 * (K * K)) * t ≤ 4 * h * t :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hh)
      calc 25600 * (K * K * t) = 4 * (6400 * (K * K)) * t := by ring
        _ ≤ 4 * h * t := this
        _ = 4 * (h * t) := by ring
    have e2 : 2560 * h ≤ 5 * (h * t) := by
      have : h * 2560 ≤ h * (5 * t) := Nat.mul_le_mul_left h (by omega)
      calc 2560 * h = h * 2560 := by ring
        _ ≤ h * (5 * t) := this
        _ = 5 * (h * t) := by ring
    calc 10 * (2560 * (K * K * t) + 256 * h) = 25600 * (K * K * t) + 2560 * h := by ring
      _ ≤ 4 * (h * t) + 5 * (h * t) := Nat.add_le_add e1 e2
      _ ≤ 10 * (h * t) := by omega
  have hmain : 2560 * (K * K * t) + 256 * h ≤ h * t := Nat.le_of_mul_le_mul_left hstep (by omega)
  calc 128 * b ≤ 128 * (20 * (K * K) * t + 1 + h) := Nat.mul_le_mul_left _ hb
    _ = 2560 * (K * K * t) + 128 + 128 * h := by ring
    _ ≤ 2560 * (K * K * t) + 128 * h + 128 * h := by omega
    _ = 2560 * (K * K * t) + 256 * h := by ring
    _ ≤ h * t := hmain

/-- From a budget in the form `128 F ≤ h t` to the form the ledger needs. -/
theorem eight_le_div_sixteen {x F : ℕ} (h : 128 * F ≤ x) : 8 * F ≤ x / 16 := by
  have h1 : F ≤ x / 128 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  have h2 : x / 128 = x / 16 / 8 := by rw [Nat.div_div_eq_div_mul]
  calc 8 * F ≤ 8 * (x / 16 / 8) := by omega
    _ ≤ x / 16 := Nat.mul_div_le _ _

variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ}

/-- A cell of a two-sided design holds at most `20K²t + 1` outer vertices. -/
theorem twoSided_cell_card_le (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (p q : ℕ) : (((W \ W').filter (fun u => x u = p ∧ y u = q)).card)
      ≤ 20 * (K * K) * gridClassSize ε K W'.card + 1 := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hhh : 0 < h * h := Nat.mul_pos hhpos hhpos
  have hcell : (((W \ W').filter (fun u => x u = p ∧ y u = q)).card) * (h * h)
      ≤ (W \ W').card + h * h := hgrid.cellFibre p q
  have hDW : (W \ W').card ≤ W.card := Finset.card_le_card Finset.sdiff_subset
  have hvol : W.card ≤ 20 * (K * K * h * h) * t := hgrid.outerVolume
  have hstep : (((W \ W').filter (fun u => x u = p ∧ y u = q)).card) * (h * h)
      ≤ (20 * (K * K) * t + 1) * (h * h) := by
    calc (((W \ W').filter (fun u => x u = p ∧ y u = q)).card) * (h * h)
        ≤ (W \ W').card + h * h := hcell
      _ ≤ 20 * (K * K * h * h) * t + h * h := Nat.add_le_add_right (le_trans hDW hvol) _
      _ = (20 * (K * K) * t + 1) * (h * h) := by ring
  exact Nat.le_of_mul_le_mul_right hstep hhh

/-- A row line of a two-sided design holds at most `(20K²t + 1) h` outer vertices. -/
theorem twoSided_row_card_le (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (p : ℕ) :
    (((W \ W').filter (fun u => x u = p)).card) / gridSize ε K
      ≤ 20 * (K * K) * gridClassSize ε K W'.card + 1 := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hrow : (((W \ W').filter (fun u => x u = p)).card) * h ≤ (W \ W').card + h * h :=
    hgrid.rowFibre p
  have hDW : (W \ W').card ≤ W.card := Finset.card_le_card Finset.sdiff_subset
  have hvol : W.card ≤ 20 * (K * K * h * h) * t := hgrid.outerVolume
  have hstep : (((W \ W').filter (fun u => x u = p)).card) * h
      ≤ ((20 * (K * K) * t + 1) * h) * h := by
    calc (((W \ W').filter (fun u => x u = p)).card) * h ≤ (W \ W').card + h * h := hrow
      _ ≤ 20 * (K * K * h * h) * t + h * h := Nat.add_le_add_right (le_trans hDW hvol) _
      _ = ((20 * (K * K) * t + 1) * h) * h := by ring
  have hle : (((W \ W').filter (fun u => x u = p)).card) ≤ (20 * (K * K) * t + 1) * h :=
    Nat.le_of_mul_le_mul_right hstep hhpos
  calc (((W \ W').filter (fun u => x u = p)).card) / h ≤ ((20 * (K * K) * t + 1) * h) / h :=
        Nat.div_le_div_right hle
    _ = 20 * (K * K) * t + 1 := Nat.mul_div_cancel _ hhpos

/-- A column line of a two-sided design holds at most `(20K²t + 1) h` outer vertices. -/
theorem twoSided_col_card_le (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (q : ℕ) :
    (((W \ W').filter (fun u => y u = q)).card) / gridSize ε K
      ≤ 20 * (K * K) * gridClassSize ε K W'.card + 1 := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hcol : (((W \ W').filter (fun u => y u = q)).card) * h ≤ (W \ W').card + h * h :=
    hgrid.colFibre q
  have hDW : (W \ W').card ≤ W.card := Finset.card_le_card Finset.sdiff_subset
  have hvol : W.card ≤ 20 * (K * K * h * h) * t := hgrid.outerVolume
  have hstep : (((W \ W').filter (fun u => y u = q)).card) * h
      ≤ ((20 * (K * K) * t + 1) * h) * h := by
    calc (((W \ W').filter (fun u => y u = q)).card) * h ≤ (W \ W').card + h * h := hcol
      _ ≤ 20 * (K * K * h * h) * t + h * h := Nat.add_le_add_right (le_trans hDW hvol) _
      _ = ((20 * (K * K) * t + 1) * h) * h := by ring
  have hle : (((W \ W').filter (fun u => y u = q)).card) ≤ (20 * (K * K) * t + 1) * h :=
    Nat.le_of_mul_le_mul_right hstep hhpos
  calc (((W \ W').filter (fun u => y u = q)).card) / h ≤ ((20 * (K * K) * t + 1) * h) / h :=
        Nat.div_le_div_right hle
    _ = 20 * (K * K) * t + 1 := Nat.mul_div_cancel _ hhpos

/-! ### The ledger of a cross-side sweep is spread -/

/-- **The cross-side rule keeps the ledger of the sweep inside its budget.**  No invariant is
maintained: the bound holds for whatever set of earlier links, as soon as each of them obeyed the
rule, and it uses only the cell fibres and the row and column fibres of the design together with
the balance of the shift. -/
theorem ledgerSpread_of_crossSideSweep
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 0 < K)
    (hbig : 512 ≤ gridClassSize ε K W'.card)
    {X : V → Finset V} {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hφrow : ∀ p j : ℕ, (((W \ W').filter (fun w => x w = p ∧ φ w = j)).card)
      ≤ 20 * (K * K) * gridClassSize ε K W'.card + 1 + gridSize ε K)
    (hφcol : ∀ q j : ℕ, (((W \ W').filter (fun w => y w = q ∧ φ w = j)).card)
      ≤ 20 * (K * K) * gridClassSize ε K W'.card + 1 + gridSize ε K)
    {S : Finset V} (hSD : S ⊆ W \ W') {g : V → V → V}
    (hXmult : ∀ a ∈ W', ((((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℕ) : ℝ)
      ≤ 2 * cleanEta ε K * (W.card : ℝ))
    (hcross : IsCrossSideSweep (gridSize ε K) C R W' X x y φ S g) :
    LedgerSpread ε K W' C X x y S g := by
  classical
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
  -- the exceptional links: those where `a` sits in the perturbation
  set E : Finset V := (W \ W').filter (fun u => a ∈ X u \ resLink R W' u) with hEdef
  have hEbud : 128 * E.card ≤ h * t := by
    have h4 : 4 * E.card ≤ t := twoSided_perturbation_quarter hgrid hK (hXmult a ha)
    have h32 : 32 * t ≤ h * t := Nat.mul_le_mul_right t (by omega)
    omega
  -- the class coordinates of `a`
  obtain ⟨α, β, hα, hβ, hrule⟩ : ∃ α β : ℕ, α < h ∧ β < h ∧
      ∀ w ∈ S, a ∈ X w → w ∈ E ∨
        IsCrossSideAt h C x y α β w (g w a) (crossShift h φ β w) (crossShiftInv h φ α w) := by
    by_cases hcls : ∃ i, i < h * h ∧ a ∈ C i
    · obtain ⟨i, hi, hai⟩ := hcls
      refine ⟨i / h, i % h, Nat.div_lt_of_lt_mul (by omega), Nat.mod_lt _ hhpos, ?_⟩
      have hid : i / h * h + i % h = i := by
        have hdm := Nat.div_add_mod i h
        rw [Nat.mul_comm h (i / h)] at hdm
        exact hdm
      intro w hwS haX
      by_cases hres : a ∈ resLink R W' w
      · exact Or.inr (hcross a (i / h) (i % h) (Nat.div_lt_of_lt_mul (by omega))
          (Nat.mod_lt _ hhpos) (by rw [hid]; exact hai) w hwS haX hres)
      · exact Or.inl (Finset.mem_filter.2 ⟨hSD hwS, Finset.mem_sdiff.2 ⟨haX, hres⟩⟩)
    · refine ⟨0, 0, hhpos, hhpos, ?_⟩
      intro w hwS haX
      refine Or.inl (Finset.mem_filter.2 ⟨hSD hwS, Finset.mem_sdiff.2 ⟨haX, ?_⟩⟩)
      intro hres
      have h1 := (Finset.mem_inter.1 (hgrid.linkSubset w (hSD hwS) hres)).2
      rw [gridRegion_eq_biUnion] at h1
      obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.1 h1
      exact hcls ⟨i, gridIdx_lt (hxlt w (hSD hwS)) (hylt w (hSD hwS)) hi, hai⟩
  -- the four counts of the rule
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
  have hF1 : 8 * (S.filter (fun w => x w = α ∧ crossShift h φ β w = P)).card ≤ h * t / 16 := by
    refine eight_le_div_sixteen ?_
    rcases Finset.eq_empty_or_nonempty (S.filter (fun w => x w = α ∧ crossShift h φ β w = P))
      with he | ⟨w₀, hw₀⟩
    · rw [he]; simp
    · obtain ⟨hw₀S, hw₀x, hw₀P⟩ := Finset.mem_filter.1 hw₀
      have hsub : (S.filter (fun w => x w = α ∧ crossShift h φ β w = P))
          ⊆ (W \ W').filter (fun w => x w = α ∧ φ w = φ w₀) := by
        intro w hw
        obtain ⟨hwS, hwx, hwP⟩ := Finset.mem_filter.1 hw
        refine Finset.mem_filter.2 ⟨hSD hwS, hwx, ?_⟩
        exact crossShift_inj (hφlt w) (hφlt w₀) (by rw [hwP, hw₀P])
      refine le_trans (Nat.mul_le_mul_left 128 (Finset.card_le_card hsub)) ?_
      refine crossSide_shift_budget hKK hbig hwide ?_
      exact hφrow α (φ w₀)
  have hF4 : 8 * (S.filter (fun w => y w = β ∧ crossShiftInv h φ α w = Q)).card
      ≤ h * t / 16 := by
    refine eight_le_div_sixteen ?_
    rcases Finset.eq_empty_or_nonempty (S.filter (fun w => y w = β ∧ crossShiftInv h φ α w = Q))
      with he | ⟨w₀, hw₀⟩
    · rw [he]; simp
    · obtain ⟨hw₀S, hw₀y, hw₀Q⟩ := Finset.mem_filter.1 hw₀
      have hsub : (S.filter (fun w => y w = β ∧ crossShiftInv h φ α w = Q))
          ⊆ (W \ W').filter (fun w => y w = β ∧ φ w = φ w₀) := by
        intro w hw
        obtain ⟨hwS, hwy, hwQ⟩ := Finset.mem_filter.1 hw
        refine Finset.mem_filter.2 ⟨hSD hwS, hwy, ?_⟩
        exact crossShiftInv_inj (hφlt w) (hφlt w₀) (by rw [hwQ, hw₀Q])
      refine le_trans (Nat.mul_le_mul_left 128 (Finset.card_le_card hsub)) ?_
      refine crossSide_shift_budget hKK hbig hwide ?_
      exact hφcol β (φ w₀)
  have hE : 8 * E.card ≤ h * t / 16 := eight_le_div_sixteen hEbud
  exact regionLoad_le_of_crossSide_bounds (C := C) (X := X) (g := g) (S := S) (E := E)
    (x := x) (y := y) (a := a) (α := α) (β := β)
    (ρ := fun w => crossShift h φ β w) (σ := fun w => crossShiftInv h φ α w)
    hdisj (fun w hw => hxlt w (hSD hw)) (fun w hw => hylt w (hSD hw))
    (fun w _ => crossShift_lt hhpos φ β w) (fun w _ => crossShiftInv_lt hhpos φ α w) hP hQ
    hrule hF1 hF2 hF3 hF4 hE

/-! ### The canonical shift of a two-sided design

The class matching of a link has to send the class `(x u, y u)`, which lies on *both* sides of the
region, to itself — otherwise it would have to supply twice as many partners as it has vertices.
That pins the shift down: `φ u = x u - y u` modulo `h`.  Its line fibres are then cell fibres, so
the ledger of a cross-side sweep with this shift is spread. -/

/-- **The canonical shift**: `x u - y u` modulo `h`.  It sends the class of `u`'s own cell to
itself, so the class matching of a link is an involution. -/
def canonShift (h : ℕ) (x y : V → ℕ) (w : V) : ℕ := (x w + (h - y w)) % h

omit [DecidableEq V] in
theorem canonShift_lt {h : ℕ} (hh : 0 < h) (x y : V → ℕ) (w : V) :
    canonShift h x y w < h := Nat.mod_lt _ hh

omit [DecidableEq V] in
/-- The canonical shift sends the class of `u`'s own cell to itself. -/
theorem crossShift_canonShift {h : ℕ} {x y : V → ℕ} {w : V} (hx : x w < h) (hy : y w < h) :
    crossShift h (canonShift h x y) (y w) w = x w := by
  have hle : y w ≤ h := hy.le
  have h1 : (x w + (h - y w)) % h ≡ x w + (h - y w) [MOD h] := Nat.mod_modEq _ _
  have h2 : y w + (x w + (h - y w)) % h ≡ y w + (x w + (h - y w)) [MOD h] :=
    Nat.ModEq.add_left _ h1
  have h3 : y w + (x w + (h - y w)) = x w + h := by omega
  rw [h3] at h2
  have h4 : (y w + (x w + (h - y w)) % h) % h = (x w + h) % h := h2
  rw [crossShift, canonShift, h4, Nat.add_mod_right, Nat.mod_eq_of_lt hx]

omit [DecidableEq V] in
/-- Two outer vertices of the same row line with the same canonical shift lie in the same cell. -/
theorem canonShift_inj_row {h : ℕ} {x y : V → ℕ} {w w' : V} (hy : y w < h) (hy' : y w' < h)
    (hx : x w = x w') (heq : canonShift h x y w = canonShift h x y w') : y w = y w' := by
  have h1 : crossShiftInv h y (x w) w = crossShiftInv h y (x w) w' := by
    simp only [crossShiftInv]
    simp only [canonShift] at heq
    rw [heq, hx]
  exact crossShiftInv_inj hy hy' h1

omit [DecidableEq V] in
/-- Two outer vertices of the same column line with the same canonical shift lie in the same
cell. -/
theorem canonShift_inj_col {h : ℕ} {x y : V → ℕ} {w w' : V} (hx : x w < h) (hx' : x w' < h)
    (hy : y w = y w') (heq : canonShift h x y w = canonShift h x y w') : x w = x w' := by
  have h1 : crossShift h x (h - y w) w = crossShift h x (h - y w) w' := by
    simp only [crossShift]
    have e1 : h - y w + x w = x w + (h - y w) := by omega
    have e2 : h - y w + x w' = x w' + (h - y w') := by rw [hy]; omega
    rw [e1, e2]
    simpa [canonShift] using heq
  exact crossShift_inj hx hx' h1

/-- **The ledger of a cross-side sweep with the canonical shift is spread.** -/
theorem ledgerSpread_of_crossSideSweep_canon
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 0 < K)
    (hbig : 512 ≤ gridClassSize ε K W'.card)
    {X : V → Finset V}
    {S : Finset V} (hSD : S ⊆ W \ W') {g : V → V → V}
    (hXmult : ∀ a ∈ W', ((((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℕ) : ℝ)
      ≤ 2 * cleanEta ε K * (W.card : ℝ))
    (hcross : IsCrossSideSweep (gridSize ε K) C R W' X x y
      (canonShift (gridSize ε K) x y) S g) :
    LedgerSpread ε K W' C X x y S g := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hxlt : ∀ w ∈ W \ W', x w < h := fun w hw => hgrid.rowLt w hw
  have hylt : ∀ w ∈ W \ W', y w < h := fun w hw => hgrid.colLt w hw
  refine ledgerSpread_of_crossSideSweep hgrid hε hε' hK hbig
    (fun w => canonShift_lt hhpos x y w) ?_ ?_ hSD hXmult hcross
  · intro p j
    rcases Finset.eq_empty_or_nonempty
      ((W \ W').filter (fun w => x w = p ∧ canonShift h x y w = j)) with he | ⟨w₀, hw₀⟩
    · rw [he]; simp
    · obtain ⟨hw₀D, hw₀x, hw₀j⟩ := Finset.mem_filter.1 hw₀
      have hsub : (W \ W').filter (fun w => x w = p ∧ canonShift h x y w = j)
          ⊆ (W \ W').filter (fun w => x w = p ∧ y w = y w₀) := by
        intro w hw
        obtain ⟨hwD, hwx, hwj⟩ := Finset.mem_filter.1 hw
        exact Finset.mem_filter.2 ⟨hwD, hwx, canonShift_inj_row (x := x) (y := y) (hylt w hwD) (hylt w₀ hw₀D)
          (by rw [hwx, hw₀x]) (by rw [hwj, hw₀j])⟩
      have := twoSided_cell_card_le hgrid (x := x) (y := y) p (y w₀)
      have h2 := Finset.card_le_card hsub
      omega
  · intro q j
    rcases Finset.eq_empty_or_nonempty
      ((W \ W').filter (fun w => y w = q ∧ canonShift h x y w = j)) with he | ⟨w₀, hw₀⟩
    · rw [he]; simp
    · obtain ⟨hw₀D, hw₀y, hw₀j⟩ := Finset.mem_filter.1 hw₀
      have hsub : (W \ W').filter (fun w => y w = q ∧ canonShift h x y w = j)
          ⊆ (W \ W').filter (fun w => x w = x w₀ ∧ y w = q) := by
        intro w hw
        obtain ⟨hwD, hwy, hwj⟩ := Finset.mem_filter.1 hw
        exact Finset.mem_filter.2 ⟨hwD, canonShift_inj_col (x := x) (y := y) (hxlt w hwD) (hxlt w₀ hw₀D)
          (by rw [hwy, hw₀y]) (by rw [hwj, hw₀j]), hwy⟩
      have := twoSided_cell_card_le hgrid (x := x) (y := y) (x w₀) q
      have h2 := Finset.card_le_card hsub
      omega

end BKLO
