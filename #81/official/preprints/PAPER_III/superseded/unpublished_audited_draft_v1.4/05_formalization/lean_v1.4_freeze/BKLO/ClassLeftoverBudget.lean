/-
# The leftover budget of a class-matched sweep, from a count of leftovers.

`BKLO.ExcLedgerSpread` — the hypothesis `BKLO.ledgerSpread_of_classMatchedSweep` asks of the
leftovers of a class-matched sweep — is a bound on the *cell load* of the leftovers of one vertex.
This file reduces it to a much cruder quantity: the **number of links in which a given vertex is a
leftover at all**.  As soon as that number is at most one cell's worth of outer vertices,
`20 K² t + 1`, the leftover budget holds — with a factor `5/4` to spare, because the budget is
`h t / 256 ≥ 25 K² t` in the regime `h ≥ 6400 K²` of `BKLO.gridSize_ge_of_eps_small`.

* `BKLO.excLedgerSpread_of_leftover_count` — the reduction.
* `BKLO.card_leftover_of_cornerConfined` — leftovers confined to the **corner class** of the region
  of their link, `C (x w · h + y w)`, are automatically that rare: a vertex `a` lies in the corner
  class of the region of `w` only for the outer vertices `w` of one single cell of the grid, and a
  cell holds at most `20 K² t + 1` outer vertices.
* `BKLO.excLedgerSpread_of_cornerConfined` — the two together: **a sweep whose leftovers are the
  corner classes of the links stays inside the leftover budget.**

This is the leftover half of the class-matched one-link step: whatever the pairing does with the
corner class of a region — the one class of the `2h - 1` classes of a region that no matching of
row classes with column classes can reach — it costs nothing on the ledger.

Everything here is `sorry`-free.
-/
import BKLO.TwoSidedClassMatched

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ}

/-- **The leftover budget, from a count of leftovers.**  If every vertex is a leftover in at most
one cell's worth of links, the leftovers of the sweep are spread. -/
theorem excLedgerSpread_of_leftover_count
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 2 ≤ K)
    (hbig : 512 ≤ gridClassSize ε K W'.card)
    {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    (hcount : ∀ a : V, (S.filter (fun w => a ∈ Exc w)).card
      ≤ 20 * (K * K) * gridClassSize ε K W'.card + 1) :
    ExcLedgerSpread ε K W' C g S Exc := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have hwide : 6400 * (K * K) ≤ h := gridSize_ge_of_eps_small hε hε' K
  have hKK : 4 ≤ K * K := by nlinarith only [hK]
  -- the budget
  have hbud : 400 * (K * K) * t ≤ h * t / 16 := by
    refine (Nat.le_div_iff_mul_le (by norm_num)).2 ?_
    calc 400 * (K * K) * t * 16 = (6400 * (K * K)) * t := by ring
      _ ≤ h * t := Nat.mul_le_mul_right t hwide
  intro a _ P _ Q _
  have h1 : excLoad h C g S Exc a P Q ≤ (S.filter (fun w => a ∈ Exc w)).card := by
    refine Finset.card_le_card ?_
    intro w hw
    obtain ⟨hwS, hw1, -⟩ := Finset.mem_filter.1 hw
    exact Finset.mem_filter.2 ⟨hwS, hw1⟩
  have h2 := hcount a
  have h3 : 16 * (20 * (K * K) * t + 1) ≤ 400 * (K * K) * t := by nlinarith only [hK, hbig]
  have : 16 * excLoad h C g S Exc a P Q ≤ h * t / 16 := by omega
  exact this

/-- **Leftovers confined to the corner class of a region are rare.**  The corner class
`C (x w · h + y w)` of the region of an outer vertex `w` determines the cell of `w`, so a vertex
`a` can be a corner leftover only for the outer vertices of one cell of the grid — at most
`20 K² t + 1` of them. -/
theorem card_leftover_of_cornerConfined
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {S : Finset V} (hSD : S ⊆ W \ W') {Exc : V → Finset V}
    (hcorner : ∀ w ∈ S, Exc w ⊆ C (x w * gridSize ε K + y w)) (a : V) :
    (S.filter (fun w => a ∈ Exc w)).card
      ≤ 20 * (K * K) * gridClassSize ε K W'.card + 1 := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  rcases Finset.eq_empty_or_nonempty (S.filter (fun w => a ∈ Exc w)) with he | ⟨w₀, hw₀⟩
  · rw [he]; simp
  obtain ⟨hw₀S, hw₀a⟩ := Finset.mem_filter.1 hw₀
  have hw₀D : w₀ ∈ W \ W' := hSD hw₀S
  have hx₀ : x w₀ < h := hgrid.rowLt w₀ hw₀D
  have hy₀ : y w₀ < h := hgrid.colLt w₀ hw₀D
  have hmem₀ : a ∈ C (x w₀ * h + y w₀) := hcorner w₀ hw₀S hw₀a
  have hsub : S.filter (fun w => a ∈ Exc w)
      ⊆ (W \ W').filter (fun w => x w = x w₀ ∧ y w = y w₀) := by
    intro w hw
    obtain ⟨hwS, hwa⟩ := Finset.mem_filter.1 hw
    have hwD : w ∈ W \ W' := hSD hwS
    have hx : x w < h := hgrid.rowLt w hwD
    have hy : y w < h := hgrid.colLt w hwD
    have hmem : a ∈ C (x w * h + y w) := hcorner w hwS hwa
    have hlt : x w * h + y w < h * h := by
      calc x w * h + y w < x w * h + h := by omega
        _ = (x w + 1) * h := by ring
        _ ≤ h * h := Nat.mul_le_mul_right h (by omega)
    have hlt₀ : x w₀ * h + y w₀ < h * h := by
      calc x w₀ * h + y w₀ < x w₀ * h + h := by omega
        _ = (x w₀ + 1) * h := by ring
        _ ≤ h * h := Nat.mul_le_mul_right h (by omega)
    have hidx : x w * h + y w = x w₀ * h + y w₀ := by
      by_contra hne
      exact (Finset.disjoint_left.1 (hgrid.classDisjoint _ hlt _ hlt₀ hne)) hmem hmem₀
    obtain ⟨h1, h2⟩ := gridDigits_inj hy hy₀ hidx
    exact Finset.mem_filter.2 ⟨hwD, h1, h2⟩
  exact le_trans (Finset.card_le_card hsub) (twoSided_cell_card_le hgrid (x w₀) (y w₀))

/-- **A sweep whose leftovers are the corner classes of the links stays inside the leftover
budget.**  This is what makes the corner class of a region — the one class of the `2h - 1` classes
of a region that no matching of the row classes with the column classes can reach — affordable:
declaring it exceptional at *every* link costs nothing on the ledger. -/
theorem excLedgerSpread_of_cornerConfined
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 2 ≤ K)
    (hbig : 512 ≤ gridClassSize ε K W'.card)
    {S : Finset V} (hSD : S ⊆ W \ W') {g : V → V → V} {Exc : V → Finset V}
    (hcorner : ∀ w ∈ S, Exc w ⊆ C (x w * gridSize ε K + y w)) :
    ExcLedgerSpread ε K W' C g S Exc :=
  excLedgerSpread_of_leftover_count hε hε' hK hbig
    (card_leftover_of_cornerConfined hgrid hSD hcorner)

end BKLO
