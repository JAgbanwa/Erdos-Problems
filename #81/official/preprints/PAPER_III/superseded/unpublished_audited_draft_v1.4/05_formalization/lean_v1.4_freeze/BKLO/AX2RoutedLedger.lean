/-
# Cross-side **routed** leftovers, and the ledger budget they buy

`BKLO.orphan_plus_forced_exceeds_ledger_budget` (`BKLO/AX2QuarterLedgerBudget.lean`) shows that the
*count* of leftovers is not the quantity a class-matched sweep can afford to bound: an
orphan-confined discipline already spends `20 K² t` of the budget `h t / 256 ≥ 25 K² t`, and the
leftovers the perturbation forces cost a further `10 K² t` on the count.

The ledger `BKLO.ExcLedgerSpread` is however not a bound on the count: it bounds `BKLO.excLoad`,
which filters the leftovers of a vertex `a` by the **cell the partner of `a` lies in**.  This file
isolates what a sweep has to do to profit from that filter, and verifies the arithmetic of the
profit.

* `BKLO.IsCrossRoutedLeftover` — the routing discipline.  The leftovers of the link of `w` are
  split into those routed into a **column** class `C (rt w a · h + y w)` of the region of `w` and
  those routed into a **row** class `C (x w · h + rt w a)`; in both cases one index is the link's
  own coordinate and the other, the *routing index* `rt w a`, is free to vary with the link.
* `BKLO.excLoad_le_routed`, `BKLO.excLoad_le_routed_counts` — **the decomposition**: a query at the
  cell `(P, Q)` catches a column-routed leftover link only if `rt w a = P` or `y w = Q`, and a
  row-routed one only if `x w = P` or `rt w a = Q`.  Each of the four counts is a *line* or a
  *fibre* of the leftover links of `a`, never the whole leftover set: this is the factor `h` a
  routed discipline buys over a count, and it is exactly what
  `BKLO.orphan_plus_forced_exceeds_ledger_budget` shows a count cannot buy.
* `BKLO.excLedgerSpread_of_load_le` — the budget in its sharpest form: a per-cell load of
  `25 K² t` is affordable (`BKLO.excLedgerSpread_of_leftover_count` is the special case in which
  the leftover *count* is at most `20 K² t + 1`).
* `BKLO.excLedgerSpread_of_crossRouted` — the two together: a cross-routed sweep whose four lines
  and fibres are each at most `6 K² t` meets the ledger.
* `BKLO.orphan_plus_routed_fits_ledger_budget`,
  `BKLO.orphan_plus_routed_lines_exceeds_ledger_budget` — the sharp threshold for a discipline that
  keeps an orphan class: the routed part may cost `5 K² t - 1` on a cell and no more.

Everything here is `sorry`-free.
-/
import BKLO.ClassLeftoverBudget

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The routing discipline -/

/-- **A cross-routed leftover discipline.**  The leftovers of the link of `w` are split into two
families: `Ecol w`, whose members are paired into the **column** class `C (rt w a · h + y w)` of the
region of `w`, and `Erow w`, whose members are paired into the **row** class
`C (x w · h + rt w a)`.

In both cases one index of the partner's class is a coordinate of the link itself and the other is
the *routing index* `rt w a`, which is free to vary with the link.  A leftover of a class that `w`
sees through its row part is meant to be routed into a column class and conversely — the partner
then shares no index with the class of the leftover, and a query at one cell of the grid catches
only a line or a fibre of the leftover links of a vertex. -/
def IsCrossRoutedLeftover (h : ℕ) (C : ℕ → Finset V) (x y : V → ℕ) (rt : V → V → ℕ)
    (S : Finset V) (g : V → V → V) (Ecol Erow : V → Finset V) : Prop :=
  ∀ w ∈ S, (∀ a ∈ Ecol w, g w a ∈ C (rt w a * h + y w)) ∧
    (∀ a ∈ Erow w, g w a ∈ C (x w * h + rt w a))

/-- The links of `S` at which `a` is a leftover of the family `E` and the index `p` takes the value
`P`.  With `p = x`, `p = y` this is a *line* of the grid, with `p = rt · a` a *fibre* of the
routing. -/
def excRouteCount (S : Finset V) (E : V → Finset V) (a : V) (p : V → ℕ) (P : ℕ) : ℕ :=
  (S.filter (fun w => a ∈ E w ∧ p w = P)).card

/-! ### The decomposition -/

/-- **The load of a routed leftover discipline splits into two lines and two fibres.**

A query at the cell `(P, Q)` catches a column-routed leftover link `w` of `a` only if the routing
index `rt w a` is `P` or the link lies in the grid line `y w = Q`, and it catches a row-routed one
only if the link lies in the line `x w = P` or the routing index is `Q`.

This is what a bound on the leftover *count* cannot see.  If `a` lies in the class `C (α h + β)`,
then the links at which `a` can be a leftover at all lie in the two lines `x w = α`, `y w = β`; a
row-routed leftover of the first kind and a column-routed leftover of the second kind therefore
cost, per query, one *cell* of links and one *fibre* of the routing, instead of the whole line. -/
theorem excLoad_le_routed {h : ℕ} {C : ℕ → Finset V} {x y : V → ℕ} {rt : V → V → ℕ}
    {S : Finset V} {g : V → V → V} {Exc Ecol Erow : V → Finset V} {a : V} {P Q : ℕ}
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j))
    (hxlt : ∀ w ∈ S, x w < h) (hylt : ∀ w ∈ S, y w < h)
    (hrt : ∀ w ∈ S, rt w a < h) (hP : P < h) (hQ : Q < h)
    (hsplit : ∀ w ∈ S, Exc w ⊆ Ecol w ∪ Erow w)
    (hroute : IsCrossRoutedLeftover h C x y rt S g Ecol Erow) :
    excLoad h C g S Exc a P Q
      ≤ excRouteCount S Ecol a (fun w => rt w a) P + excRouteCount S Ecol a y Q
        + excRouteCount S Erow a x P + excRouteCount S Erow a (fun w => rt w a) Q := by
  classical
  set F1 : Finset V := S.filter (fun w => a ∈ Ecol w ∧ rt w a = P) with hF1
  set F2 : Finset V := S.filter (fun w => a ∈ Ecol w ∧ y w = Q) with hF2
  set F3 : Finset V := S.filter (fun w => a ∈ Erow w ∧ x w = P) with hF3
  set F4 : Finset V := S.filter (fun w => a ∈ Erow w ∧ rt w a = Q) with hF4
  have hsub : S.filter (fun w => a ∈ Exc w ∧ g w a ∈ gridRegion h C P Q)
      ⊆ (F1 ∪ F2) ∪ (F3 ∪ F4) := by
    intro w hw
    obtain ⟨hwS, hwa, hwreg⟩ := Finset.mem_filter.1 hw
    have hxw : x w < h := hxlt w hwS
    have hyw : y w < h := hylt w hwS
    have hrtw : rt w a < h := hrt w hwS
    -- the class of the partner, as the region prescribes it
    rw [gridRegion_eq_biUnion] at hwreg
    obtain ⟨k, hk, hmem⟩ := Finset.mem_biUnion.1 hwreg
    have hklt : k < h * h := gridIdx_lt hP hQ hk
    -- the class of the partner, as the routing prescribes it
    have hkey : ∀ i j : ℕ, i < h → j < h → g w a ∈ C (i * h + j) → i = P ∨ j = Q := by
      intro i j hi hj hij
      have hlt : i * h + j < h * h := grid_idx_lt hi hj
      have heq : i * h + j = k := by
        by_contra hne
        exact (Finset.disjoint_left.1 (hdisj _ hlt _ hklt hne)) hij hmem
      rcases mem_gridIdx.1 hk with ⟨j', hj', rfl⟩ | ⟨l, hl, rfl⟩
      · exact Or.inl (gridDigits_inj hj hj' heq).1
      · exact Or.inr (gridDigits_inj hj hQ heq).2
    rcases Finset.mem_union.1 (hsplit w hwS hwa) with hcolmem | hrowmem
    · rcases hkey _ _ hrtw hyw ((hroute w hwS).1 a hcolmem) with h1 | h1
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨hwS, hcolmem, h1⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨hwS, hcolmem, h1⟩))
    · rcases hkey _ _ hxw hrtw ((hroute w hwS).2 a hrowmem) with h1 | h1
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨hwS, hrowmem, h1⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨hwS, hrowmem, h1⟩))
  calc excLoad h C g S Exc a P Q ≤ ((F1 ∪ F2) ∪ (F3 ∪ F4)).card := Finset.card_le_card hsub
    _ ≤ (F1 ∪ F2).card + (F3 ∪ F4).card := Finset.card_union_le _ _
    _ ≤ (F1.card + F2.card) + (F3.card + F4.card) :=
        Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _)
    _ = excRouteCount S Ecol a (fun w => rt w a) P + excRouteCount S Ecol a y Q
          + excRouteCount S Erow a x P + excRouteCount S Erow a (fun w => rt w a) Q := by
        simp only [excRouteCount, hF1, hF2, hF3, hF4]
        ring

/-- The budget form of `BKLO.excLoad_le_routed`: four bounds, one per line and per fibre. -/
theorem excLoad_le_routed_counts {h : ℕ} {C : ℕ → Finset V} {x y : V → ℕ} {rt : V → V → ℕ}
    {S : Finset V} {g : V → V → V} {Exc Ecol Erow : V → Finset V} {a : V} {P Q B : ℕ}
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j))
    (hxlt : ∀ w ∈ S, x w < h) (hylt : ∀ w ∈ S, y w < h)
    (hrt : ∀ w ∈ S, rt w a < h) (hP : P < h) (hQ : Q < h)
    (hsplit : ∀ w ∈ S, Exc w ⊆ Ecol w ∪ Erow w)
    (hroute : IsCrossRoutedLeftover h C x y rt S g Ecol Erow)
    (h1 : 4 * excRouteCount S Ecol a (fun w => rt w a) P ≤ B)
    (h2 : 4 * excRouteCount S Ecol a y Q ≤ B)
    (h3 : 4 * excRouteCount S Erow a x P ≤ B)
    (h4 : 4 * excRouteCount S Erow a (fun w => rt w a) Q ≤ B) :
    excLoad h C g S Exc a P Q ≤ B := by
  have := excLoad_le_routed (C := C) (x := x) (y := y) (rt := rt) (S := S) (g := g) (Exc := Exc)
    (Ecol := Ecol) (Erow := Erow) (a := a) (P := P) (Q := Q) hdisj hxlt hylt hrt hP hQ hsplit
    hroute
  omega

/-! ### The budget -/

variable {ε : ℝ} {K : ℕ} {W' : Finset V} {C : ℕ → Finset V}

/-- **The ledger budget, in its sharpest form.**  In the regime `ε ≤ 1/100` the grid has
`h ≥ 6400 K²` classes per line, so the budget `h t / 16` of `BKLO.ExcLedgerSpread` allows a load of
`25 K² t` on every cell.  `BKLO.excLedgerSpread_of_leftover_count` is the special case in which the
whole leftover *count* is bounded by `20 K² t + 1`. -/
theorem excLedgerSpread_of_load_le (hε : 0 < ε) (hε' : ε ≤ 1 / 100)
    {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    (hload : ∀ a : V, ∀ P < gridSize ε K, ∀ Q < gridSize ε K,
      excLoad (gridSize ε K) C g S Exc a P Q
        ≤ 25 * (K * K) * gridClassSize ε K W'.card) :
    ExcLedgerSpread ε K W' C g S Exc := by
  classical
  have hwide : 6400 * (K * K) ≤ gridSize ε K := gridSize_ge_of_eps_small hε hε' K
  have hbud : 400 * (K * K) * gridClassSize ε K W'.card
      ≤ gridSize ε K * gridClassSize ε K W'.card / 16 := by
    refine (Nat.le_div_iff_mul_le (by norm_num)).2 ?_
    calc 400 * (K * K) * gridClassSize ε K W'.card * 16
        = (6400 * (K * K)) * gridClassSize ε K W'.card := by ring
      _ ≤ gridSize ε K * gridClassSize ε K W'.card := Nat.mul_le_mul_right _ hwide
  intro a _ P hP Q hQ
  have h1 := hload a P hP Q hQ
  have key : ∀ n : ℕ, n * (K * K) * gridClassSize ε K W'.card
      = n * ((K * K) * gridClassSize ε K W'.card) := fun n => by ring
  rw [key 25] at h1
  rw [key 400] at hbud
  omega

/-- **A cross-routed sweep meets the ledger**, as soon as each of its two lines and each of its two
routing fibres stays inside a quarter of the budget.  Compare
`BKLO.orphan_plus_forced_exceeds_ledger_budget`: what a routed discipline has to control is four
*lines and fibres* of the leftovers of a vertex, each of them smaller than the leftover set itself
by about the number `h` of classes per line. -/
theorem excLedgerSpread_of_crossRouted (hε : 0 < ε) (hε' : ε ≤ 1 / 100)
    {x y : V → ℕ} {rt : V → V → ℕ} {S : Finset V} {g : V → V → V} {Exc Ecol Erow : V → Finset V}
    (hdisj : ∀ i < gridSize ε K * gridSize ε K, ∀ j < gridSize ε K * gridSize ε K,
      i ≠ j → Disjoint (C i) (C j))
    (hxlt : ∀ w ∈ S, x w < gridSize ε K) (hylt : ∀ w ∈ S, y w < gridSize ε K)
    (hrt : ∀ w ∈ S, ∀ a : V, rt w a < gridSize ε K)
    (hsplit : ∀ w ∈ S, Exc w ⊆ Ecol w ∪ Erow w)
    (hroute : IsCrossRoutedLeftover (gridSize ε K) C x y rt S g Ecol Erow)
    (hcolfib : ∀ a : V, ∀ P, excRouteCount S Ecol a (fun w => rt w a) P
      ≤ 6 * (K * K) * gridClassSize ε K W'.card)
    (hcolline : ∀ a : V, ∀ Q, excRouteCount S Ecol a y Q
      ≤ 6 * (K * K) * gridClassSize ε K W'.card)
    (hrowline : ∀ a : V, ∀ P, excRouteCount S Erow a x P
      ≤ 6 * (K * K) * gridClassSize ε K W'.card)
    (hrowfib : ∀ a : V, ∀ Q, excRouteCount S Erow a (fun w => rt w a) Q
      ≤ 6 * (K * K) * gridClassSize ε K W'.card) :
    ExcLedgerSpread ε K W' C g S Exc := by
  refine excLedgerSpread_of_load_le (C := C) (W' := W') hε hε' ?_
  intro a P hP Q hQ
  have h1 := excLoad_le_routed (C := C) (x := x) (y := y) (rt := rt) (S := S) (g := g)
    (Exc := Exc) (Ecol := Ecol) (Erow := Erow) (a := a) (P := P) (Q := Q) hdisj hxlt hylt
    (fun w hw => hrt w hw a) hP hQ hsplit hroute
  have h2 := hcolfib a P
  have h3 := hcolline a Q
  have h4 := hrowline a P
  have h5 := hrowfib a Q
  have key : ∀ n : ℕ, n * (K * K) * gridClassSize ε K W'.card
      = n * ((K * K) * gridClassSize ε K W'.card) := fun n => by ring
  rw [key 6] at h2 h3 h4 h5
  rw [key 25]
  omega

/-! ### The threshold for a discipline that keeps the orphan class -/

/-- **What a routed discipline may spend, on top of an orphan class.**  A sweep whose leftovers are
the orphan class of the link — `20 K² t + 1` links for any one vertex,
`BKLO.card_leftover_of_orphanConfined` — together with a routed part of load at most `5 K² t - 1`
on every cell still meets the ledger.  This is the exact slack left by
`BKLO.orphan_plus_forced_exceeds_ledger_budget`, which shows that a *further* `10 K² t` on the
count is not affordable. -/
theorem orphan_plus_routed_fits_ledger_budget {K t h Orph B : ℕ}
    (hh : 6400 * (K * K) ≤ h) (horph : Orph ≤ 20 * (K * K) * t + 1)
    (hB : B + 1 ≤ 5 * (K * K) * t) :
    16 * (Orph + B) ≤ h * t / 16 := by
  have hbud : 400 * (K * K) * t ≤ h * t / 16 := by
    refine (Nat.le_div_iff_mul_le (by norm_num)).2 ?_
    calc 400 * (K * K) * t * 16 = (6400 * (K * K)) * t := by ring
      _ ≤ h * t := Nat.mul_le_mul_right t hh
  have e1 : 20 * (K * K) * t = 20 * (K * K * t) := by ring
  have e2 : 5 * (K * K) * t = 5 * (K * K * t) := by ring
  have e3 : 400 * (K * K) * t = 400 * (K * K * t) := by ring
  omega

/-- **And what it may not spend.**  The slack above an orphan class is `5 K² t` and no more: at the
narrowest grid `h ≤ 6401 K²` the budget is `h t / 256 ≤ 25.004 K² t`, so a routed part costing a
further `K² t` — a sixth of one of the four counts of `BKLO.excLedgerSpread_of_crossRouted` —
already overruns the ledger.  This is the sharp form of
`BKLO.orphan_plus_forced_exceeds_ledger_budget`, whose forced part costs `10 K² t`. -/
theorem orphan_plus_routed_lines_exceeds_ledger_budget {K t h Orph B : ℕ} (hK : 2 ≤ K) (ht : 0 < t)
    (hh : h ≤ 6401 * (K * K)) (horph : 20 * (K * K) * t ≤ Orph) (hB : 6 * (K * K) * t ≤ B) :
    ¬ (16 * (Orph + B) ≤ h * t / 16) := by
  intro hcon
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have e1 : 20 * (K * K) * t = 20 * (K * K * t) := by ring
  have e2 : 6 * (K * K) * t = 6 * (K * K * t) := by ring
  rw [e1] at horph
  rw [e2] at hB
  have h1 : 16 * (h * t / 16) ≤ h * t := Nat.mul_div_le _ _
  have h2 : 16 * (16 * (Orph + B)) ≤ 16 * (h * t / 16) := Nat.mul_le_mul_left _ hcon
  have h3 : h * t ≤ 6401 * (K * K) * t := Nat.mul_le_mul_right _ hh
  have h7 : 6401 * (K * K) * t = 6401 * (K * K * t) := by ring
  rw [h7] at h3
  have h4 : 256 * (26 * (K * K * t)) ≤ 16 * (16 * (Orph + B)) := by
    have hsum : 26 * (K * K * t) ≤ Orph + B := by omega
    calc 256 * (26 * (K * K * t)) ≤ 256 * (Orph + B) := Nat.mul_le_mul_left _ hsum
      _ = 16 * (16 * (Orph + B)) := by ring
  have h5 : 0 < K * K * t := Nat.mul_pos (by omega) ht
  have h6 : 256 * (26 * (K * K * t)) = 6656 * (K * K * t) := by ring
  omega

end BKLO
