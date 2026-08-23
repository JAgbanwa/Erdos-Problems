/-
# The three-class cycle discipline, and the ledger it costs

A region of the two-sided grid design has `2h - 1` classes, an odd number, so a class matching
`ρ, σ` of the region — a permutation of the `h` classes of the row line of the link onto the `h`
classes of its column line — always double-books one class: the **corner** class
`C (x u · h + y u)`, which lies on both lines.  Its `q` places have to serve as the partners both
of the column class `A = C (ρ u (y u) · h + y u)` and of the row class
`B = C (x u · h + σ u (x u))`, and they cannot: one class' worth of places is left over at every
link, whatever the matching.

`BKLO/ClassPairingOrphan.lean` pays that debt by *orphaning* a class — the places of `A` are paired
inside `A` and recorded as leftovers.  `BKLO.not_excLedgerSpread_of_orphan_and_attacked`
(`BKLO/AX2RoutedLedgerLower.lean`) shows that this is too expensive: the partner of an orphaned
place lies in its own class, so a single cell of the grid catches **all** `20 K² t` of the links at
which a given place is orphaned, and the `5 K² t` of slack that leaves does not cover the leftovers
the perturbation forces.

This file formalises the discipline that pays the debt *cross-side* instead — the **three-class
cycle**.  The corner class splits: some of its places take partners in `A` and the rest take
partners in `B`, and the places of `A` and of `B` that are then left over are paired **with each
other**.  A leftover of `A` — a column class of the link — is therefore paired into `B`, a **row**
class of the link, and conversely; the index of the partner's class is not an index of the
leftover's own class but a coordinate of the *link*, shifted:

```
a ∈ A = C (ρ u (y u) · h + y u)   ↦   partner in  C (x u · h + σ u (x u))
a ∈ B = C (x u · h + σ u (x u))   ↦   partner in  C (ρ u (y u) · h + y u)
```

* `BKLO.IsCycleRoutedLeftover` — the discipline.
* `BKLO.excLedgerSpread_of_cycleRouted` — **the ledger it costs**, for the class matching of a
  shift `φ` that is *balanced on every cell* (`BKLO.exists_cell_balanced_shift`).  Each of the four
  lines and fibres of `BKLO.excLoad_le_routed` is then a **single cell fibre** of the shift, of
  size at most `(20 K² t + 1)/h + 1 ≤ t + 1`, so the load of a vertex on a cell is at most
  `4 (t + 1)` — smaller than the orphan's `20 K² t` by about the factor `h ≥ 6400 K²`.

The alignment is what does the work: at a link `w` at which `a` can be a cycle leftover at all,
*both* indices of `a`'s class are coordinates of `w`, one of them shifted, so the shift of `w` is
determined by `a`; a query at a cell `(P, Q)` then pins the remaining coordinate of `w` as well.
The links a query catches are the outer vertices of **one cell** carrying **one value** of the
shift, and a cell-balanced shift spreads those over the `h` values.

Everything here is `sorry`-free.
-/
import BKLO.AX2RoutedLedger

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The discipline -/

/-- **The three-class cycle leftover discipline.**  At the link of `w` the leftovers split into

* `Ecol w`, places of the **row** class `C (x w · h + σ w (x w))` of the cycle, which are paired
  into the **column** class `C (ρ w (y w) · h + y w)`, and
* `Erow w`, places of that column class, which are paired into the row class

— where `ρ w β = crossShift h φ β w` and `σ w α = crossShiftInv h φ α w` is the class matching of
the shift `φ`.  No leftover is paired inside its own class, and no index of a leftover's partner is
an index of the leftover's own class. -/
def IsCycleRoutedLeftover (h : ℕ) (C : ℕ → Finset V) (x y φ : V → ℕ)
    (S : Finset V) (g : V → V → V) (Ecol Erow : V → Finset V) : Prop :=
  ∀ w ∈ S,
    (∀ a ∈ Ecol w, a ∈ C (x w * h + crossShiftInv h φ (x w) w) ∧
        g w a ∈ C (crossShift h φ (y w) w * h + y w)) ∧
    (∀ a ∈ Erow w, a ∈ C (crossShift h φ (y w) w * h + y w) ∧
        g w a ∈ C (x w * h + crossShiftInv h φ (x w) w))

/-! ### Cancellation modulo the number of classes -/

/-- Cancellation of a common summand modulo `h`. -/
theorem add_mod_right_inj {h a b d : ℕ} (ha : a < h) (hb : b < h)
    (heq : (a + d) % h = (b + d) % h) : a = b := by
  have h1 : a + d ≡ b + d [MOD h] := heq
  have h2 : a ≡ b [MOD h] := Nat.ModEq.add_right_cancel' d h1
  have h3 : a % h = b % h := h2
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h3

/-! ### The ledger of the cycle discipline -/

variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ}

/-- A set of links pinned to one cell and one value of a cell-balanced shift is small. -/
theorem card_le_cell_shift_fibre
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) {φ : V → ℕ}
    (hbal : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    {T : Finset V} {p q j : ℕ}
    (hT : ∀ w ∈ T, w ∈ W \ W' ∧ x w = p ∧ y w = q ∧ φ w = j) :
    T.card ≤ (20 * (K * K) * gridClassSize ε K W'.card + 1) / gridSize ε K + 1 := by
  classical
  have hsub : T ⊆ (W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j) := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hT w hw
    exact Finset.mem_filter.2 ⟨h1, h2, h3, h4⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans (hbal p q j) ?_)
  exact Nat.add_le_add_right (Nat.div_le_div_right (twoSided_cell_card_le hgrid p q)) 1
omit [DecidableEq V] in
/-- The cell fibre of a cell-balanced shift is at most `t + 1`: the `20 K² t + 1` outer vertices of
a cell are spread over the `h ≥ 6400 K²` values of the shift. -/
theorem cell_shift_fibre_le_succ_class
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 2 ≤ K) (ht : 512 ≤ gridClassSize ε K W'.card) :
    (20 * (K * K) * gridClassSize ε K W'.card + 1) / gridSize ε K + 1
      ≤ gridClassSize ε K W'.card + 1 := by
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have hwide : 6400 * (K * K) ≤ gridSize ε K := gridSize_ge_of_eps_small hε hε' K
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have hstep : 20 * (K * K) * t + 1 ≤ gridSize ε K * t := by
    have h1 : (6400 * (K * K)) * t ≤ gridSize ε K * t := Nat.mul_le_mul_right t hwide
    have h3 : 21 * ((K * K) * t) ≤ 6400 * ((K * K) * t) := Nat.mul_le_mul_right _ (by omega)
    have h4 : 1 ≤ (K * K) * t := Nat.one_le_iff_ne_zero.2 (by positivity)
    have e1 : 20 * (K * K) * t = 20 * ((K * K) * t) := by ring
    have e2 : (6400 * (K * K)) * t = 6400 * ((K * K) * t) := by ring
    omega
  have hfib : (20 * (K * K) * t + 1) / gridSize ε K ≤ t := Nat.div_le_of_le_mul hstep
  omega

/-! ### The load of the cycle discipline on a cell -/

/-- **The load of a three-class cycle discipline on a cell of the ledger**, for a class matching
whose shift is balanced on every cell.

Each of the four lines and fibres of `BKLO.excLoad_le_routed` is a single cell fibre of the shift:
the class of a cycle leftover `a` pins the shift of its link — both indices of `a`'s class are
coordinates of the link, one of them shifted — and the query `(P, Q)` then pins the cell.  So a
vertex loads a cell of the ledger at most `4 ((20 K² t + 1)/h + 1) ≤ 4 (t + 1)` times, against the
`20 K² t` of an orphan-confined discipline. -/
theorem excLoad_le_of_cycleRouted_fibre
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K) {B : ℕ}
    (hfib : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card) ≤ B)
    {S : Finset V} (hSD : S ⊆ W \ W') {g : V → V → V} {Exc Ecol Erow : V → Finset V}
    (hdisjE : ∀ w ∈ S, ∀ a ∈ Erow w, a ∉ Ecol w)
    (hsplit : ∀ w ∈ S, Exc w ⊆ Ecol w ∪ Erow w)
    (hcyc : IsCycleRoutedLeftover (gridSize ε K) C x y φ S g Ecol Erow)
    (a : V) {P Q : ℕ} (hP : P < gridSize ε K) (hQ : Q < gridSize ε K) :
    excLoad (gridSize ε K) C g S Exc a P Q ≤ 4 * B := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hcard : ∀ (T : Finset V) (p q' j : ℕ),
      (∀ w ∈ T, w ∈ W \ W' ∧ x w = p ∧ y w = q' ∧ φ w = j) → T.card ≤ B := by
    intro T p q' j hT
    refine le_trans (Finset.card_le_card ?_) (hfib p q' j)
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hT w hw
    exact Finset.mem_filter.2 ⟨h1, h2, h3, h4⟩
  have hxlt : ∀ w ∈ S, x w < h := fun w hw => hgrid.rowLt w (hSD hw)
  have hylt : ∀ w ∈ S, y w < h := fun w hw => hgrid.colLt w (hSD hw)
  -- the routing index of a leftover
  set rt : V → V → ℕ := fun w a =>
    if a ∈ Ecol w then crossShift h φ (y w) w else crossShiftInv h φ (x w) w with hrtdef
  have hrtlt : ∀ w ∈ S, ∀ b : V, rt w b < h := by
    intro w _ b
    by_cases hmem : b ∈ Ecol w
    · simp only [hrtdef, if_pos hmem]; exact crossShift_lt hhpos _ _ _
    · simp only [hrtdef, if_neg hmem]; exact crossShiftInv_lt hhpos _ _ _
  have hroute : IsCrossRoutedLeftover h C x y rt S g Ecol Erow := by
    intro w hw
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · simp only [hrtdef, if_pos hb]
      exact ((hcyc w hw).1 b hb).2
    · simp only [hrtdef, if_neg (hdisjE w hw b hb)]
      exact ((hcyc w hw).2 b hb).2
  -- the class of a vertex is determined
  have hclass : ∀ {i j : ℕ} {b : V}, i < h * h → j < h * h → b ∈ C i → b ∈ C j → i = j := by
    intro i j b hi hj hmi hmj
    by_contra hne
    exact (Finset.disjoint_left.1 (hgrid.classDisjoint i hi j hj hne)) hmi hmj
  -- the two indices of the class of a `Ecol`-leftover pin the row and the shift of its link
  have hEcol : ∀ w ∈ S, ∀ w₀ ∈ S, a ∈ Ecol w → a ∈ Ecol w₀ → x w = x w₀ ∧ φ w = φ w₀ := by
    intro w hw w₀ hw₀ ha ha₀
    have h1 := ((hcyc w hw).1 a ha).1
    have h2 := ((hcyc w₀ hw₀).1 a ha₀).1
    have hlt1 : x w * h + crossShiftInv h φ (x w) w < h * h :=
      grid_idx_lt (hxlt w hw) (crossShiftInv_lt hhpos _ _ _)
    have hlt2 : x w₀ * h + crossShiftInv h φ (x w₀) w₀ < h * h :=
      grid_idx_lt (hxlt w₀ hw₀) (crossShiftInv_lt hhpos _ _ _)
    obtain ⟨hx, hinv⟩ := gridDigits_inj (crossShiftInv_lt hhpos φ (x w) w)
      (crossShiftInv_lt hhpos φ (x w₀) w₀) (hclass hlt1 hlt2 h1 h2)
    refine ⟨hx, ?_⟩
    refine crossShiftInv_inj (r := x w₀) (hφlt w) (hφlt w₀) ?_
    rw [hx] at hinv
    exact hinv
  -- the two indices of the class of a `Erow`-leftover pin the column and the shift of its link
  have hErow : ∀ w ∈ S, ∀ w₀ ∈ S, a ∈ Erow w → a ∈ Erow w₀ → y w = y w₀ ∧ φ w = φ w₀ := by
    intro w hw w₀ hw₀ ha ha₀
    have h1 := ((hcyc w hw).2 a ha).1
    have h2 := ((hcyc w₀ hw₀).2 a ha₀).1
    have hlt1 : crossShift h φ (y w) w * h + y w < h * h :=
      grid_idx_lt (crossShift_lt hhpos _ _ _) (hylt w hw)
    have hlt2 : crossShift h φ (y w₀) w₀ * h + y w₀ < h * h :=
      grid_idx_lt (crossShift_lt hhpos _ _ _) (hylt w₀ hw₀)
    obtain ⟨hsh, hy⟩ := gridDigits_inj (hylt w hw) (hylt w₀ hw₀) (hclass hlt1 hlt2 h1 h2)
    refine ⟨hy, ?_⟩
    refine crossShift_inj (s := y w₀) (hφlt w) (hφlt w₀) ?_
    rw [hy] at hsh
    exact hsh
  -- the four lines and fibres
  have hc1 : excRouteCount S Ecol a (fun w => rt w a) P ≤ B := by
    simp only [excRouteCount]
    rcases (S.filter (fun w => a ∈ Ecol w ∧ rt w a = P)).eq_empty_or_nonempty with he | ⟨w₀, hw₀⟩
    · rw [he]; simp
    obtain ⟨hw₀S, hw₀E, hw₀P⟩ := Finset.mem_filter.1 hw₀
    refine hcard _ (x w₀) (y w₀) (φ w₀) ?_
    intro w hw
    obtain ⟨hwS, hwE, hwP⟩ := Finset.mem_filter.1 hw
    obtain ⟨hx, hφ⟩ := hEcol w hwS w₀ hw₀S hwE hw₀E
    refine ⟨hSD hwS, hx, ?_, hφ⟩
    have e1 : crossShift h φ (y w) w = crossShift h φ (y w₀) w₀ := by
      have q1 : rt w a = crossShift h φ (y w) w := by simp only [hrtdef, if_pos hwE]
      have q2 : rt w₀ a = crossShift h φ (y w₀) w₀ := by simp only [hrtdef, if_pos hw₀E]
      rw [← q1, ← q2, hwP, hw₀P]
    have e2 : (y w + φ w) % h = (y w₀ + φ w₀) % h := e1
    rw [hφ] at e2
    exact add_mod_right_inj (hylt w hwS) (hylt w₀ hw₀S) e2
  have hc2 : excRouteCount S Ecol a y Q ≤ B := by
    simp only [excRouteCount]
    rcases (S.filter (fun w => a ∈ Ecol w ∧ y w = Q)).eq_empty_or_nonempty with he | ⟨w₀, hw₀⟩
    · rw [he]; simp
    obtain ⟨hw₀S, hw₀E, hw₀Q⟩ := Finset.mem_filter.1 hw₀
    refine hcard _ (x w₀) (y w₀) (φ w₀) ?_
    intro w hw
    obtain ⟨hwS, hwE, hwQ⟩ := Finset.mem_filter.1 hw
    obtain ⟨hx, hφ⟩ := hEcol w hwS w₀ hw₀S hwE hw₀E
    exact ⟨hSD hwS, hx, by rw [hwQ, hw₀Q], hφ⟩
  have hc3 : excRouteCount S Erow a x P ≤ B := by
    simp only [excRouteCount]
    rcases (S.filter (fun w => a ∈ Erow w ∧ x w = P)).eq_empty_or_nonempty with he | ⟨w₀, hw₀⟩
    · rw [he]; simp
    obtain ⟨hw₀S, hw₀E, hw₀P⟩ := Finset.mem_filter.1 hw₀
    refine hcard _ (x w₀) (y w₀) (φ w₀) ?_
    intro w hw
    obtain ⟨hwS, hwE, hwP⟩ := Finset.mem_filter.1 hw
    obtain ⟨hy, hφ⟩ := hErow w hwS w₀ hw₀S hwE hw₀E
    exact ⟨hSD hwS, by rw [hwP, hw₀P], hy, hφ⟩
  have hc4 : excRouteCount S Erow a (fun w => rt w a) Q ≤ B := by
    simp only [excRouteCount]
    rcases (S.filter (fun w => a ∈ Erow w ∧ rt w a = Q)).eq_empty_or_nonempty with he | ⟨w₀, hw₀⟩
    · rw [he]; simp
    obtain ⟨hw₀S, hw₀E, hw₀Q⟩ := Finset.mem_filter.1 hw₀
    refine hcard _ (x w₀) (y w₀) (φ w₀) ?_
    intro w hw
    obtain ⟨hwS, hwE, hwQ⟩ := Finset.mem_filter.1 hw
    obtain ⟨hy, hφ⟩ := hErow w hwS w₀ hw₀S hwE hw₀E
    refine ⟨hSD hwS, ?_, hy, hφ⟩
    have e1 : crossShiftInv h φ (x w) w = crossShiftInv h φ (x w₀) w₀ := by
      have q1 : rt w a = crossShiftInv h φ (x w) w := by
        simp only [hrtdef, if_neg (hdisjE w hwS a hwE)]
      have q2 : rt w₀ a = crossShiftInv h φ (x w₀) w₀ := by
        simp only [hrtdef, if_neg (hdisjE w₀ hw₀S a hw₀E)]
      rw [← q1, ← q2, hwQ, hw₀Q]
    have e2 : (x w + (h - φ w)) % h = (x w₀ + (h - φ w₀)) % h := e1
    rw [hφ] at e2
    exact add_mod_right_inj (hxlt w hwS) (hxlt w₀ hw₀S) e2
  have hmain := excLoad_le_routed (C := C) (x := x) (y := y) (rt := rt) (S := S) (g := g)
    (Exc := Exc) (Ecol := Ecol) (Erow := Erow) (a := a) (P := P) (Q := Q)
    (fun i hi j hj hij => hgrid.classDisjoint i hi j hj hij) hxlt hylt
    (fun w hw => hrtlt w hw a) hP hQ hsplit hroute
  rw [← hhdef] at hmain
  show excLoad h C g S Exc a P Q ≤ 4 * B
  omega

/-- **The load of a three-class cycle discipline on a cell of the ledger**, for a class matching
whose shift is balanced on every cell: the cell fibre of a balanced shift is
`(20 K² t + 1)/h + 1`. -/
theorem excLoad_le_of_cycleRouted
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hbal : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    {S : Finset V} (hSD : S ⊆ W \ W') {g : V → V → V} {Exc Ecol Erow : V → Finset V}
    (hdisjE : ∀ w ∈ S, ∀ a ∈ Erow w, a ∉ Ecol w)
    (hsplit : ∀ w ∈ S, Exc w ⊆ Ecol w ∪ Erow w)
    (hcyc : IsCycleRoutedLeftover (gridSize ε K) C x y φ S g Ecol Erow)
    (a : V) {P Q : ℕ} (hP : P < gridSize ε K) (hQ : Q < gridSize ε K) :
    excLoad (gridSize ε K) C g S Exc a P Q
      ≤ 4 * ((20 * (K * K) * gridClassSize ε K W'.card + 1) / gridSize ε K + 1) :=
  excLoad_le_of_cycleRouted_fibre hgrid hφlt
    (fun _ _ _ => card_le_cell_shift_fibre hgrid hbal
      (fun _ hw => ⟨(Finset.mem_filter.1 hw).1, (Finset.mem_filter.1 hw).2.1,
        (Finset.mem_filter.1 hw).2.2.1, (Finset.mem_filter.1 hw).2.2.2⟩))
    hSD hdisjE hsplit hcyc a hP hQ

/-! ### The ledger of the cycle discipline -/

/-- **The ledger of a three-class cycle discipline is spread.**  A vertex loads a cell at most
`4 (t + 1)` times, and the budget is `25 K² t`. -/
theorem excLedgerSpread_of_cycleRouted
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 2 ≤ K)
    (ht : 512 ≤ gridClassSize ε K W'.card)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hbal : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    {S : Finset V} (hSD : S ⊆ W \ W') {g : V → V → V} {Exc Ecol Erow : V → Finset V}
    (hdisjE : ∀ w ∈ S, ∀ a ∈ Erow w, a ∉ Ecol w)
    (hsplit : ∀ w ∈ S, Exc w ⊆ Ecol w ∪ Erow w)
    (hcyc : IsCycleRoutedLeftover (gridSize ε K) C x y φ S g Ecol Erow) :
    ExcLedgerSpread ε K W' C g S Exc := by
  refine excLedgerSpread_of_load_le (C := C) (W' := W') hε hε' ?_
  intro a P hP Q hQ
  have h1 := excLoad_le_of_cycleRouted hgrid hφlt hbal hSD hdisjE hsplit hcyc a hP hQ
  have h2 := cell_shift_fibre_le_succ_class (W' := W') hε hε' hK ht
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have h3 : 25 * (K * K) * gridClassSize ε K W'.card
      = 25 * ((K * K) * gridClassSize ε K W'.card) := by ring
  have h4 : 4 * gridClassSize ε K W'.card ≤ (K * K) * gridClassSize ε K W'.card :=
    Nat.mul_le_mul_right _ hKK
  have h5 : 1 ≤ (K * K) * gridClassSize ε K W'.card :=
    Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

/-- **The ledger of a three-class cycle discipline, with the leftovers the perturbation forces.**

The cycle costs `4 (t + 1)` on a cell, so the whole budget `25 K² t` is left for the forced
leftovers, of which the ledger sees, at a given cell, at most the number of links at which the
vertex is a forced leftover at all.  A perturbation that deletes the permitted quarter `t / 4` from
the partner class of `a` at every link of a cell forces `a` to be a leftover at a `(t/4)/q ≤ 1/3`
fraction of the `20 K² t + 1` links of the cell, and `a` lies in the region of two lines of cells,
so `18 K² t` is a bound with room to spare. -/
theorem excLedgerSpread_of_cycleRouted_and_forced
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 2 ≤ K)
    (ht : 512 ≤ gridClassSize ε K W'.card)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hbal : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    {S : Finset V} (hSD : S ⊆ W \ W') {g : V → V → V} {Exc Ecol Erow Efor : V → Finset V}
    (hdisjE : ∀ w ∈ S, ∀ a ∈ Erow w, a ∉ Ecol w)
    (hsplit : ∀ w ∈ S, Exc w ⊆ (Ecol w ∪ Erow w) ∪ Efor w)
    (hcyc : IsCycleRoutedLeftover (gridSize ε K) C x y φ S g Ecol Erow)
    (hforced : ∀ a : V, (S.filter (fun w => a ∈ Efor w)).card
      ≤ 18 * (K * K) * gridClassSize ε K W'.card) :
    ExcLedgerSpread ε K W' C g S Exc := by
  classical
  refine excLedgerSpread_of_load_le (C := C) (W' := W') hε hε' ?_
  intro a P hP Q hQ
  set h : ℕ := gridSize ε K with hhdef
  -- the load splits into the cycle part and the forced part
  have hsub : S.filter (fun w => a ∈ Exc w ∧ g w a ∈ gridRegion h C P Q)
      ⊆ (S.filter (fun w => a ∈ (Ecol w ∪ Erow w) ∧ g w a ∈ gridRegion h C P Q))
        ∪ (S.filter (fun w => a ∈ Efor w)) := by
    intro w hw
    obtain ⟨hwS, hwE, hwreg⟩ := Finset.mem_filter.1 hw
    rcases Finset.mem_union.1 (hsplit w hwS hwE) with hcase | hcase
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hwS, hcase, hwreg⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hwS, hcase⟩)
  have hsplit' : ∀ w ∈ S, (fun w => Ecol w ∪ Erow w) w ⊆ Ecol w ∪ Erow w := fun w _ => Finset.Subset.refl _
  have h1 := excLoad_le_of_cycleRouted hgrid hφlt hbal hSD hdisjE hsplit' hcyc a hP hQ
  have h2 := cell_shift_fibre_le_succ_class (W' := W') hε hε' hK ht
  have h6 : excLoad h C g S Exc a P Q
      ≤ excLoad h C g S (fun w => Ecol w ∪ Erow w) a P Q + (S.filter (fun w => a ∈ Efor w)).card := by
    simp only [excLoad]
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  rw [← hhdef] at h1 h2
  have h7 := hforced a
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have e1 : 25 * (K * K) * gridClassSize ε K W'.card
      = 25 * ((K * K) * gridClassSize ε K W'.card) := by ring
  have e2 : 18 * (K * K) * gridClassSize ε K W'.card
      = 18 * ((K * K) * gridClassSize ε K W'.card) := by ring
  have h4 : 4 * gridClassSize ε K W'.card ≤ (K * K) * gridClassSize ε K W'.card :=
    Nat.mul_le_mul_right _ hKK
  have h5 : 1 ≤ (K * K) * gridClassSize ε K W'.card :=
    Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

end BKLO
