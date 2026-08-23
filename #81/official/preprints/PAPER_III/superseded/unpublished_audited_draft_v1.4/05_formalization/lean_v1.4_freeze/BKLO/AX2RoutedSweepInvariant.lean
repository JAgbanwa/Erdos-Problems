/-
# The routed invariant of a class-matched sweep

`BKLO.TwoSidedUsedClassMatchedQuarterPairing` (`BKLO/TwoSidedUsedClassMatchedQuarter.lean`) asks
for a class matching `ρ, σ`, an invariant `Inv` of the sweep implying the leftover ledger
`BKLO.ExcLedgerSpread`, and a one-link step maintaining it.  This file supplies the **invariant**
and the two easy halves of the demand — that the empty sweep satisfies it, and that it implies the
ledger.

The invariant records that the leftovers of every earlier link split into

* the leftovers of the **three-class cycle** of the link (`BKLO.IsCycleRoutedLeftover`), whose
  ledger `BKLO.excLoad_le_of_cycleRouted` bounds by `4 (t + 1)` on every cell — the class of such a
  leftover pins both the cell and the shift of its link; and
* the leftovers the **perturbation** forces, which are routed the same way — into the column class
  `C (ρ w (y w) · h + y w)` or the row class `C (x w · h + σ w (x w))` of the link — and for which
  the invariant carries the four **routed counts** of `BKLO.excLoad_le_routed`, one per line and
  per routing fibre, each inside `5 K² t + 1` — a quarter of the links of a cell, which is what
  the balanced prescription `BKLO.exists_cell_balanced_leftovers` supplies and what
  `BKLO.routed_quarter_counters_fit_ledger_budget` shows the ledger can afford.

`BKLO.excLedgerSpread_of_routedSweepInv` is the resulting ledger: `4 (t + 1) + 4 (5 K² t + 1)`,
inside the `25 K² t` that `BKLO.excLedgerSpread_of_load_le` allows.

Everything in this file is `sorry`-free.
-/
import BKLO.AX2CycleRouted

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ}

/-- **The routed invariant of a class-matched sweep.**  The leftovers of every link of `S` split
into the leftovers of the three-class cycle of the link and the leftovers the perturbation forces;
both are routed cross-side, into the column class `C (ρ w (y w) · h + y w)` or the row class
`C (x w · h + σ w (x w))` of the link, and the forced ones carry the four routed counts of
`BKLO.excLoad_le_routed`. -/
def RoutedSweepInv (ε : ℝ) (K : ℕ) (W W' : Finset V) (C : ℕ → Finset V) (x y φ : V → ℕ)
    (S : Finset V) (g : V → V → V) (Exc : V → Finset V) : Prop :=
  S ⊆ W \ W' ∧
  ∃ Cc Cr Pc Pr : V → Finset V,
    -- the leftovers split into the cycle part and the forced part
    (∀ w ∈ S, Exc w ⊆ (Cc w ∪ Cr w) ∪ (Pc w ∪ Pr w)) ∧
    (∀ w ∈ S, ∀ a ∈ Cr w, a ∉ Cc w) ∧
    (∀ w ∈ S, ∀ a ∈ Pr w, a ∉ Pc w) ∧
    -- the cycle part obeys the three-class cycle discipline
    IsCycleRoutedLeftover (gridSize ε K) C x y φ S g Cc Cr ∧
    -- the forced part is routed the same way
    (∀ w ∈ S, ∀ a ∈ Pc w,
      g w a ∈ C (crossShift (gridSize ε K) φ (y w) w * gridSize ε K + y w)) ∧
    (∀ w ∈ S, ∀ a ∈ Pr w,
      g w a ∈ C (x w * gridSize ε K + crossShiftInv (gridSize ε K) φ (x w) w)) ∧
    -- and its four routed counts stay inside a fifth of the budget
    (∀ a : V, ∀ P : ℕ, (S.filter (fun w => a ∈ Pc w ∧
        crossShift (gridSize ε K) φ (y w) w = P)).card
      ≤ 5 * (K * K) * gridClassSize ε K W'.card + 1) ∧
    (∀ a : V, ∀ Q : ℕ, (S.filter (fun w => a ∈ Pc w ∧ y w = Q)).card
      ≤ 5 * (K * K) * gridClassSize ε K W'.card + 1) ∧
    (∀ a : V, ∀ P : ℕ, (S.filter (fun w => a ∈ Pr w ∧ x w = P)).card
      ≤ 5 * (K * K) * gridClassSize ε K W'.card + 1) ∧
    (∀ a : V, ∀ Q : ℕ, (S.filter (fun w => a ∈ Pr w ∧
        crossShiftInv (gridSize ε K) φ (x w) w = Q)).card
      ≤ 5 * (K * K) * gridClassSize ε K W'.card + 1)

/-- The empty sweep satisfies the routed invariant. -/
theorem routedSweepInv_empty (φ : V → ℕ) :
    RoutedSweepInv ε K W W' C x y φ (∅ : Finset V) (fun _ a => a) (fun _ => ∅) := by
  classical
  refine ⟨Finset.empty_subset _, (fun _ => ∅), (fun _ => ∅), (fun _ => ∅), (fun _ => ∅),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro a ha <;> simp_all

/-! ### The invariant implies the ledger -/

/-- **The routed invariant keeps the leftover ledger spread.**  The cycle part costs `4 (t + 1)` on
a cell (`BKLO.excLoad_le_of_cycleRouted`) and the forced part costs its four routed counts
(`BKLO.excLoad_le_routed`), `4 (5 K² t + 1)`; the budget is `25 K² t`. -/
theorem excLedgerSpread_of_routedSweepInv
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 2 ≤ K)
    (ht : 512 ≤ gridClassSize ε K W'.card)
    {φ : V → ℕ} (hφlt : ∀ w, φ w < gridSize ε K)
    (hbal : ∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1)
    {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    (hInv : RoutedSweepInv ε K W W' C x y φ S g Exc) :
    ExcLedgerSpread ε K W' C g S Exc := by
  classical
  obtain ⟨hSD, Cc, Cr, Pc, Pr, hsplit, hdisjC, hdisjP, hcyc, hPc, hPr,
    hc1, hc2, hc3, hc4⟩ := hInv
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  refine excLedgerSpread_of_load_le (C := C) (W' := W') hε hε' ?_
  intro a P hP Q hQ
  -- the load splits into the cycle part and the forced part
  have hsub : S.filter (fun w => a ∈ Exc w ∧ g w a ∈ gridRegion h C P Q)
      ⊆ (S.filter (fun w => a ∈ (Cc w ∪ Cr w) ∧ g w a ∈ gridRegion h C P Q))
        ∪ (S.filter (fun w => a ∈ (Pc w ∪ Pr w) ∧ g w a ∈ gridRegion h C P Q)) := by
    intro w hw
    obtain ⟨hwS, hwE, hwreg⟩ := Finset.mem_filter.1 hw
    rcases Finset.mem_union.1 (hsplit w hwS hwE) with hcase | hcase
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hwS, hcase, hwreg⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hwS, hcase, hwreg⟩)
  have hload : excLoad h C g S Exc a P Q
      ≤ excLoad h C g S (fun w => Cc w ∪ Cr w) a P Q
        + excLoad h C g S (fun w => Pc w ∪ Pr w) a P Q := by
    simp only [excLoad]
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  -- the cycle part
  have hcycload := excLoad_le_of_cycleRouted (W'' := W'') (F := F) (R := R) hgrid hφlt hbal hSD
    hdisjC (fun w _ => Finset.Subset.refl _) hcyc a hP hQ
  have hcycbound := cell_shift_fibre_le_succ_class (W' := W') hε hε' hK ht
  -- the forced part
  set rt : V → V → ℕ := fun w b =>
    if b ∈ Pc w then crossShift h φ (y w) w else crossShiftInv h φ (x w) w with hrtdef
  have hrtlt : ∀ w ∈ S, ∀ b : V, rt w b < h := by
    intro w _ b
    by_cases hmem : b ∈ Pc w
    · simp only [hrtdef, if_pos hmem]; exact crossShift_lt (gridSize_pos ε K) _ _ _
    · simp only [hrtdef, if_neg hmem]; exact crossShiftInv_lt (gridSize_pos ε K) _ _ _
  have hroute : IsCrossRoutedLeftover h C x y rt S g Pc Pr := by
    intro w hw
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · simp only [hrtdef, if_pos hb]
      exact hPc w hw b hb
    · simp only [hrtdef, if_neg (hdisjP w hw b hb)]
      exact hPr w hw b hb
  have hperload := excLoad_le_routed (C := C) (x := x) (y := y) (rt := rt) (S := S) (g := g)
    (Exc := fun w => Pc w ∪ Pr w) (Ecol := Pc) (Erow := Pr) (a := a) (P := P) (Q := Q)
    (fun i hi j hj hij => hgrid.classDisjoint i hi j hj hij)
    (fun w hw => hgrid.rowLt w (hSD hw)) (fun w hw => hgrid.colLt w (hSD hw))
    (fun w hw => hrtlt w hw a) hP hQ (fun w _ => Finset.Subset.refl _) hroute
  -- the four routed counts
  have he1 : excRouteCount S Pc a (fun w => rt w a) P
      = (S.filter (fun w => a ∈ Pc w ∧ crossShift h φ (y w) w = P)).card := by
    simp only [excRouteCount]
    congr 1
    apply Finset.filter_congr
    intro w _
    constructor
    · rintro ⟨hwa, hwP⟩
      exact ⟨hwa, by simpa only [hrtdef, if_pos hwa] using hwP⟩
    · rintro ⟨hwa, hwP⟩
      exact ⟨hwa, by simpa only [hrtdef, if_pos hwa] using hwP⟩
  have he4 : excRouteCount S Pr a (fun w => rt w a) Q
      ≤ (S.filter (fun w => a ∈ Pr w ∧ crossShiftInv h φ (x w) w = Q)).card := by
    simp only [excRouteCount]
    refine Finset.card_le_card ?_
    intro w hw
    obtain ⟨hwS, hwa, hwQ⟩ := Finset.mem_filter.1 hw
    refine Finset.mem_filter.2 ⟨hwS, hwa, ?_⟩
    simpa only [hrtdef, if_neg (hdisjP w hwS a hwa)] using hwQ
  have hcycload' : excLoad h C g S (fun w => Cc w ∪ Cr w) a P Q
      ≤ 4 * ((20 * (K * K) * t + 1) / h + 1) := hcycload
  have hcycbound' : (20 * (K * K) * t + 1) / h + 1 ≤ t + 1 := hcycbound
  have hperload' : excLoad h C g S (fun w => Pc w ∪ Pr w) a P Q
      ≤ excRouteCount S Pc a (fun w => rt w a) P + excRouteCount S Pc a y Q
        + excRouteCount S Pr a x P + excRouteCount S Pr a (fun w => rt w a) Q := hperload
  have hb1 := hc1 a P
  have hb2 := hc2 a Q
  have hb3 := hc3 a P
  have hb4 := hc4 a Q
  rw [← he1] at hb1
  have hb2' : excRouteCount S Pc a y Q ≤ 5 * (K * K) * t + 1 := hb2
  have hb3' : excRouteCount S Pr a x P ≤ 5 * (K * K) * t + 1 := hb3
  have hb4' : excRouteCount S Pr a (fun w => rt w a) Q ≤ 5 * (K * K) * t + 1 :=
    le_trans he4 hb4
  -- the arithmetic
  show excLoad h C g S Exc a P Q ≤ 25 * (K * K) * t
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have e1 : 25 * (K * K) * t = 25 * ((K * K) * t) := by ring
  have e2 : 5 * (K * K) * t = 5 * ((K * K) * t) := by ring
  have h4 : 4 * t ≤ (K * K) * t := Nat.mul_le_mul_right _ hKK
  have h5 : 1 ≤ (K * K) * t := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

end BKLO
