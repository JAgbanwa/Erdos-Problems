/-
# BKLO §11, cells route: the reservation is placed

`BKLO/Section11CellsWire.lean` reduced `BKLO.TriDecompDense` (given the dense nibble) to the pure
placement statement `BKLO.CellsChainReservation`.  This file discharges it.

The bottom cells of the vortex are enumerated as `cell 0, …, cell (N-1)` and the greedy chain
`BKLO.exists_cellsChain_percell` places, edge-disjointly inside the host,

* one bounded core absorbing structure per cell, for the core `cell i ∪ Tv (i-1)`, and
* two connectors — vertex-disjoint `4`-cycles on eight vertices `Tv i` of cell `i` — per boundary,

with the **per-cell** degree bound: every vertex sends at most `60` reserved edges into any single
bottom cell.  Since the bottom cells have at least `m - 1 ≥ 60/ε` vertices, this constant bound is
a genuine `ε`-spread at the scale of a cell, and `BKLO.spreadAlong_of_percell` propagates it to
every part of every level of the partition sequence, which is exactly `BKLO.SpreadAlong`.

* `BKLO.cellsChainReservation_holds` — the placement statement;
* `BKLO.triDecompDense_of_nibble_faithful_uncond` — hence `BKLO.TriDecompDense` from the dense
  nibble alone.

Everything here is `sorry`-free.
-/
import BKLO.Section11CellsWire
import BKLO.CellsGreedy
import BKLO.CellsSpreadLevels

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### The reserved chain, as a union over the cells -/

/-- With empty remainders and no connectors past the end of the chain, the chain of `N` cells is
just the union of the reserved pieces of its cells. -/
theorem chainSet_eq_biUnion (Aa c₁ c₂ : ℕ → Finset (Sym2 V)) (N : ℕ)
    (hc : ∀ i, N ≤ i + 1 → c₁ i = ∅ ∧ c₂ i = ∅) :
    chainSet Aa (fun _ => ∅) c₁ c₂ 0 N
      = (Finset.range N).biUnion (fun i => Aa i ∪ c₁ i ∪ c₂ i) := by
  classical
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨i, -, hi, hmem⟩ := chainSet_subset_cellPiece Aa (fun _ => ∅) c₁ c₂ N 0 e he
    refine Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 (by omega), ?_⟩
    simpa [cellPiece] using hmem
  · intro e he
    obtain ⟨i, hi, hmem⟩ := Finset.mem_biUnion.1 he
    rw [Finset.mem_range] at hi
    have habs : Aa i ⊆ chainSet Aa (fun _ => ∅) c₁ c₂ 0 N :=
      subset_chainSet_absorber Aa (fun _ => ∅) c₁ c₂ N 0 i (Nat.zero_le _) (by omega)
    by_cases hi1 : i + 1 < N
    · have hconn : c₁ i ∪ c₂ i ⊆ chainSet Aa (fun _ => ∅) c₁ c₂ 0 N :=
        subset_chainSet_conn Aa (fun _ => ∅) c₁ c₂ N 0 i (Nat.zero_le _) (by omega)
      rcases Finset.mem_union.1 hmem with h | h
      · rcases Finset.mem_union.1 h with h' | h'
        · exact habs h'
        · exact hconn (Finset.mem_union_left _ h')
      · exact hconn (Finset.mem_union_right _ h)
    · obtain ⟨he₁, he₂⟩ := hc i (by omega)
      rw [he₁, he₂] at hmem
      simp only [Finset.union_empty] at hmem
      exact habs hmem

/-! ### Placing the reservation -/

set_option maxHeartbeats 1000000 in
/-- **The cells reservation can be placed.**

This is `BKLO.CellsChainReservation`: in every large dense host carrying a vortex with bottom cells
of size at least `max 3000 (⌈60/ε⌉ + 2)`, one reserves a bounded core absorber per bottom cell and
two connectors per boundary, all edge-disjoint, and the reservation is `ε`-spread along the whole
partition sequence. -/
theorem cellsChainReservation_holds : CellsChainReservation := by
  classical
  intro ε hε hε1 k m₀ hk
  refine ⟨max 3000 (⌈(60 : ℝ) / ε⌉₊ + 2), fun mmax => ?_⟩
  obtain ⟨n₀, hchain⟩ := exists_cellsChain_percell mmax
  refine ⟨max n₀ 1, ?_⟩
  intro V _ E S m L Pl hcard hES hdiv hdeg _hm hm1 hmmax hseq hPS hPdisj hPcover hPcard hPdeg
  -- enumerate the bottom cells
  set Cells : Finset (Finset V) := restrictParts Pl S with hCells
  set N : ℕ := Cells.card with hNdef
  set cell : ℕ → Finset V := fun i =>
    if h : i < N then ((Cells.equivFin.symm ⟨i, h⟩ : {x // x ∈ Cells}) : Finset V) else ∅
    with hcelldef
  have hcellmem : ∀ i, i < N → cell i ∈ Cells := by
    intro i hi
    simp only [hcelldef, dif_pos hi]
    exact (Cells.equivFin.symm ⟨i, hi⟩).2
  have hcellsurj : ∀ P ∈ Cells, ∃ i, i < N ∧ cell i = P := by
    intro P hP
    refine ⟨(Cells.equivFin ⟨P, hP⟩ : Fin N).1, (Cells.equivFin ⟨P, hP⟩ : Fin N).2, ?_⟩
    show (if h : ((Cells.equivFin ⟨P, hP⟩ : Fin N) : ℕ) < N then
      ((Cells.equivFin.symm ⟨_, h⟩ : {x // x ∈ Cells}) : Finset V) else ∅) = P
    rw [dif_pos (Cells.equivFin ⟨P, hP⟩ : Fin N).2, Fin.eta, Equiv.symm_apply_apply]
  have hcellinj : ∀ i, i < N → ∀ j, j < N → i ≠ j → cell i ≠ cell j := by
    intro i hi j hj hij heq
    simp only [hcelldef, dif_pos hi, dif_pos hj] at heq
    have h1 : (Cells.equivFin.symm ⟨i, hi⟩) = (Cells.equivFin.symm ⟨j, hj⟩) := Subtype.ext heq
    have h2 : (⟨i, hi⟩ : Fin N) = ⟨j, hj⟩ := Cells.equivFin.symm.injective h1
    exact hij (by simpa using congrArg Fin.val h2)
  have hcelldisj : ∀ i, i < N → ∀ j, j < N → i ≠ j → Disjoint (cell i) (cell j) :=
    fun i hi j hj hij => hPdisj _ (hcellmem i hi) _ (hcellmem j hj) (hcellinj i hi j hj hij)
  -- there is at least one cell
  have hScard : 1 ≤ S.card := le_trans (le_max_right _ _) hcard
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with hN0 | h; swap; · exact h
    exfalso
    have hCempty : Cells = ∅ := Finset.card_eq_zero.1 hN0
    rw [hCempty, Finset.biUnion_empty] at hPcover
    have : S = ∅ := Finset.subset_empty.1 hPcover
    rw [this] at hScard
    simp at hScard
  -- the numeric hypotheses of the greedy chain
  have hmindeg : ∀ q ∈ S, 9 * S.card ≤ 10 * edeg E q := by
    intro q hq
    have h := hdeg q hq
    have h0 : (0 : ℝ) ≤ ε * (S.card : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg _)
    have h9 : (9 : ℝ) * (S.card : ℝ) ≤ 10 * (edeg E q : ℝ) := by nlinarith
    exact_mod_cast h9
  have h3000 : 3000 ≤ m := le_trans (le_max_left _ _) hm1
  have hcellS : ∀ i, i < N → cell i ⊆ S := fun i hi => hPS _ (hcellmem i hi)
  have hcellcard : ∀ i, i < N → m - 1 ≤ (cell i).card ∧ (cell i).card ≤ m :=
    fun i hi => hPcard _ (hcellmem i hi)
  have hedegle : ∀ (P : Finset V) (v : V), v ∈ P → edeg (E ∩ cliqueEdges P) v ≤ degTo E v P := by
    intro P v _
    have hsupp : ∀ e ∈ E ∩ cliqueEdges P, ∀ x ∈ e, x ∈ P := by
      intro e he x hx
      exact (mem_cliqueEdgesV.1 (Finset.mem_inter.1 he).2).1 x hx
    rw [edeg_eq_degTo_of_supp hsupp v]
    exact degTo_mono_left Finset.inter_subset_left v P
  have hinternal : ∀ i, i < N → ∀ v ∈ cell i,
      9 * (cell i).card ≤ 10 * degTo E v (cell i) := by
    intro i hi v hv
    have h := hPdeg _ (hcellmem i hi) v hv
    have h2 : (edeg (E ∩ cliqueEdges (cell i)) v : ℝ) ≤ (degTo E v (cell i) : ℝ) := by
      exact_mod_cast hedegle (cell i) v hv
    have h0 : (0 : ℝ) ≤ ε * ((cell i).card : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg _)
    have h9 : (9 : ℝ) * ((cell i).card : ℝ) ≤ 10 * (degTo E v (cell i) : ℝ) := by nlinarith
    exact_mod_cast h9
  -- run the greedy chain
  obtain ⟨Tv, Aa, c₁, c₂, hTv, habs, hcTv, hcprop, hcempty, hpieces, hAac, hsubE, hpercell⟩ :=
    hchain E S cell N m (le_trans (le_max_left _ _) hcard) hES hmindeg h3000 hmmax hNpos
      hcellS hcellcard hcelldisj hinternal
  -- the reservation
  set A : Finset (Sym2 V) := (Finset.range N).biUnion (fun i => Aa i ∪ c₁ i ∪ c₂ i) with hAdef
  have hchainEq : chainSet Aa (fun _ => ∅) c₁ c₂ 0 N = A :=
    chainSet_eq_biUnion Aa c₁ c₂ N hcempty
  -- the parts of a piece are even and disjoint
  have hc₁ev : ∀ i, EvenDegrees (c₁ i) := by
    intro i
    by_cases h : i + 1 < N
    · exact (hcprop i h).1
    · rw [(hcempty i (by omega)).1]; intro v; simp
  have hc₂ev : ∀ i, EvenDegrees (c₂ i) := by
    intro i
    by_cases h : i + 1 < N
    · exact (hcprop i h).2.1
    · rw [(hcempty i (by omega)).2]; intro v; simp
  have hc₁₂ : ∀ i, Disjoint (c₁ i) (c₂ i) := by
    intro i
    by_cases h : i + 1 < N
    · exact (hcprop i h).2.2.2.2
    · rw [(hcempty i (by omega)).1]; exact Finset.disjoint_empty_left _
  have hpieceEven : ∀ i, i < N → EvenDegrees (Aa i ∪ c₁ i ∪ c₂ i) := by
    intro i hi
    have hAev : EvenDegrees (Aa i) := evenDegrees_of_triDecomp (habs i hi).triDecomp
    have hd := hAac i hi
    have hd₁ : Disjoint (Aa i) (c₁ i) := hd.mono_right Finset.subset_union_left
    have hd₂ : Disjoint (Aa i) (c₂ i) := hd.mono_right Finset.subset_union_right
    refine evenDegrees_union_of_disjoint ?_ (evenDegrees_union_of_disjoint hd₁ hAev (hc₁ev i))
      (hc₂ev i)
    exact Finset.disjoint_union_left.2 ⟨hd₂, hc₁₂ i⟩
  have hAev : EvenDegrees A := by
    rw [hAdef]
    refine evenDegrees_biUnion _ _ ?_ ?_
    · intro i hi j hj hij
      exact hpieces i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hij
    · intro i hi
      exact hpieceEven i (Finset.mem_range.1 hi)
  have hAE : A ⊆ E := by
    rw [hAdef]
    exact Finset.biUnion_subset.2 fun i hi => hsubE i (Finset.mem_range.1 hi)
  -- the per-cell bound is an `ε`-spread
  have hceil : (60 : ℝ) / ε ≤ (⌈(60 : ℝ) / ε⌉₊ : ℝ) := Nat.le_ceil _
  have hspreadbd : ∀ x : V, ∀ R ∈ Cells, (degTo A x R : ℝ) ≤ ε * (R.card : ℝ) := by
    intro x R hR
    obtain ⟨j, hj, rfl⟩ := hcellsurj R hR
    have hb : degTo A x (cell j) ≤ 60 := hpercell x j hj
    have hb' : (degTo A x (cell j) : ℝ) ≤ 60 := by exact_mod_cast hb
    have hmge : ⌈(60 : ℝ) / ε⌉₊ + 2 ≤ m := le_trans (le_max_right _ _) hm1
    have hcge : ⌈(60 : ℝ) / ε⌉₊ ≤ (cell j).card := by
      have := (hcellcard j hj).1
      omega
    have hcge' : ((⌈(60 : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ ((cell j).card : ℝ) := by exact_mod_cast hcge
    have h60 : (60 : ℝ) = ε * ((60 : ℝ) / ε) := by field_simp
    have : (60 : ℝ) ≤ ε * ((cell j).card : ℝ) := by
      rw [h60]
      exact mul_le_mul_of_nonneg_left (le_trans hceil hcge') hε.le
    linarith
  have hAsp : SpreadAlong ε L Pl A S :=
    spreadAlong_of_percell L (9 / 10 + 2 * ε) Pl E S hseq hPdisj hspreadbd
  -- assemble
  refine ⟨N, cell, coreOf cell Tv, Aa, c₁, c₂, hNpos, hcellmem, hcellsurj, hPdisj, hcelldisj,
    fun i _ => cell_subset_coreOf cell Tv i, habs, ?_, ?_, ?_, ?_,
    fun i hi => hc₁ev i, fun i hi => hc₂ev i, ?_, ?_, hpieces, hAac, fun i _ => hc₁₂ i, hcempty,
    ?_, ?_, ?_⟩
  · exact fun i hi => (hcTv i hi).1.trans (cliqueEdges_subset_of_subset
      ((hTv i (by omega)).trans (cell_subset_coreOf cell Tv i)))
  · refine fun i hi => (hcTv i hi).1.trans (cliqueEdges_subset_of_subset ?_)
    unfold coreOf
    rw [if_neg (Nat.succ_ne_zero i)]
    simp
  · exact fun i hi => (hcTv i hi).2.trans (cliqueEdges_subset_of_subset
      ((hTv i (by omega)).trans (cell_subset_coreOf cell Tv i)))
  · refine fun i hi => (hcTv i hi).2.trans (cliqueEdges_subset_of_subset ?_)
    unfold coreOf
    rw [if_neg (Nat.succ_ne_zero i)]
    simp
  · intro i hi; rw [(hcprop i hi).2.2.1]
  · intro i hi; rw [(hcprop i hi).2.2.2.1]
  · rw [hchainEq]; exact hAE
  · rw [hchainEq]; exact hAev
  · rw [hchainEq]; exact hAsp

/-! ### The dense theorem, unconditionally on the nibble -/

/-- **The dense triangle-decomposition theorem from the dense nibble alone.**

Every large triangle-divisible graph of minimum degree at least `9/10` of its order has a triangle
decomposition, given the approximate (nibble) decomposition at the same density. -/
theorem triDecompDense_of_nibble_faithful_uncond (happ : ApproxTriDecompMinDeg (9 / 10)) :
    TriDecompDense :=
  triDecompDense_of_nibble_chainReservation cellsChainReservation_holds happ

end BKLO
