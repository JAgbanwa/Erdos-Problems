/-
# BKLO §11, cells route: the reservation interface is a pure placement statement

`BKLO/Section11CellsSeq.lean` reduced the §11 interface to the reservation `CellsAbsorberSpread`,
and `BKLO/Section11CellsChain.lean` showed how a chain of per-cell absorbers with connectors on the
boundaries absorbs a remainder that is only *globally* divisible.  This file joins the two: it
states the reservation as the **existence of the chain** — per bottom cell of the vortex a bounded
core absorber, per boundary two connectors, all edge-disjoint and spread at the scale of a cell —
and derives `BKLO.CellsAbsorberSpread` from it.

* `BKLO.CellsChainReservation` — the placement statement;
* `BKLO.cellsAbsorberSpread_of_chainReservation` — it implies the reservation interface;
* `BKLO.triDecompDense_of_nibble_chainReservation` — hence, with the dense nibble, `TriDecompDense`.

After this file the only thing between the proved §10 core and `BKLO.TriDecompDense` is
`BKLO.CellsChainReservation`, which mentions no partition sequence, no divisibility and no
absorption: it asks only that the absorbers and connectors can be *placed*.

Everything here is `sorry`-free.
-/
import BKLO.Section11CellsSeq
import BKLO.Section11CellsChain

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### Two elementary facts about clique edges of cells -/

theorem cliqueEdges_subset_of_subset {U W : Finset V} (h : U ⊆ W) :
    cliqueEdges U ⊆ cliqueEdges W := by
  intro e he
  obtain ⟨hmem, hdiag⟩ := mem_cliqueEdgesV.1 he
  exact mem_cliqueEdgesV.2 ⟨fun x hx => h (hmem x hx), hdiag⟩

theorem disjoint_cliqueEdges_of_disjoint {U W : Finset V} (h : Disjoint U W) :
    Disjoint (cliqueEdges U) (cliqueEdges W) := by
  refine Finset.disjoint_left.2 fun e heU heW => ?_
  obtain ⟨hU, hdiag⟩ := mem_cliqueEdgesV.1 heU
  obtain ⟨hW, -⟩ := mem_cliqueEdgesV.1 heW
  obtain ⟨x, hx⟩ : ∃ x, x ∈ e := ⟨e.out.1, by simp [Sym2.out_fst_mem]⟩
  exact (Finset.disjoint_left.1 h) (hU x hx) (hW x hx)

/-! ### The placement interface -/

/-- **The §8 reservation on the vortex, as a placement statement.**

For every `ε ∈ (0, 1]`, every `k ≥ 16` and every prescribed bottom-cell size `m₀`, in every large
dense triangle-divisible host `E` carrying a partition sequence with bottom cells of size at least
`m₀`, the bottom cells can be enumerated as `cell 0, …, cell (N-1)` and one can reserve

* for each cell a bounded **core absorbing structure** `Aa i` for a core `core i ⊇ cell i`
  (`BKLO.CoreAbsorbers`), and
* for each boundary two **connectors** `c₁ i`, `c₂ i`: even-degree edge sets with `1` edge mod `3`
  lying inside the cores of both cell `i` and cell `i+1`,

all pairwise edge-disjoint, with the whole reservation `A*` contained in `E`, of even degrees, and
**spread along the partition sequence** (`BKLO.SpreadAlong`), i.e. every vertex sends at most `ε|W|`
reserved edges into every part `W` of every level.

This asks only that the absorbers and the connectors can be *placed*; the divisibility and the
absorption are supplied by `BKLO.triDecomp_chainSet`. -/
def CellsChainReservation : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ k m₀ : ℕ, 16 ≤ k → ∃ m₁ : ℕ, ∀ mmax : ℕ, ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V) (m : ℕ)
      (L : List (Finset (Finset V))) (Pl : Finset (Finset V)),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → TriDivisible E →
      (∀ v ∈ S, (9 / 10 + 4 * ε) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      m₀ ≤ m → m₁ ≤ m → m ≤ mmax →
      PartSeq k (9 / 10 + 2 * ε) (9 / 10 + ε) ε m L Pl E S →
      (∀ P ∈ restrictParts Pl S, P ⊆ S) →
      (∀ P ∈ restrictParts Pl S, ∀ Q ∈ restrictParts Pl S, P ≠ Q → Disjoint P Q) →
      S ⊆ (restrictParts Pl S).biUnion id →
      (∀ P ∈ restrictParts Pl S, m - 1 ≤ P.card ∧ P.card ≤ m) →
      (∀ P ∈ restrictParts Pl S, ∀ v ∈ P,
        (9 / 10 + 3 * ε) * (P.card : ℝ) ≤ (edeg (E ∩ cliqueEdges P) v : ℝ)) →
      ∃ (N : ℕ) (cell core : ℕ → Finset V) (Aa c₁ c₂ : ℕ → Finset (Sym2 V)),
        0 < N ∧
        -- the cells are exactly the bottom cells of the partition sequence
        (∀ i, i < N → cell i ∈ restrictParts Pl S) ∧
        (∀ P ∈ restrictParts Pl S, ∃ i, i < N ∧ cell i = P) ∧
        (∀ P ∈ restrictParts Pl S, ∀ Q ∈ restrictParts Pl S, P ≠ Q → Disjoint P Q) ∧
        (∀ i, i < N → ∀ j, j < N → i ≠ j → Disjoint (cell i) (cell j)) ∧
        -- each core contains its cell
        (∀ i, i < N → cell i ⊆ core i) ∧
        -- the per-cell absorbers
        (∀ i, i < N → CoreAbsorbers (core i) (Aa i)) ∧
        -- the connectors
        (∀ i, i + 1 < N → c₁ i ⊆ cliqueEdges (core i)) ∧
        (∀ i, i + 1 < N → c₁ i ⊆ cliqueEdges (core (i + 1))) ∧
        (∀ i, i + 1 < N → c₂ i ⊆ cliqueEdges (core i)) ∧
        (∀ i, i + 1 < N → c₂ i ⊆ cliqueEdges (core (i + 1))) ∧
        (∀ i, i + 1 < N → EvenDegrees (c₁ i)) ∧
        (∀ i, i + 1 < N → EvenDegrees (c₂ i)) ∧
        (∀ i, i + 1 < N → (c₁ i).card % 3 = 1) ∧
        (∀ i, i + 1 < N → (c₂ i).card % 3 = 1) ∧
        -- the reserved pieces are pairwise edge-disjoint
        (∀ i, i < N → ∀ j, j < N → i ≠ j →
          Disjoint (Aa i ∪ c₁ i ∪ c₂ i) (Aa j ∪ c₁ j ∪ c₂ j)) ∧
        (∀ i, i < N → Disjoint (Aa i) (c₁ i ∪ c₂ i)) ∧
        (∀ i, i + 1 < N → Disjoint (c₁ i) (c₂ i)) ∧
        -- nothing is reserved outside the chain
        (∀ i, N ≤ i + 1 → c₁ i = ∅ ∧ c₂ i = ∅) ∧
        -- the reservation itself
        chainSet Aa (fun _ => ∅) c₁ c₂ 0 N ⊆ E ∧
        EvenDegrees (chainSet Aa (fun _ => ∅) c₁ c₂ 0 N) ∧
        SpreadAlong ε L Pl (chainSet Aa (fun _ => ∅) c₁ c₂ 0 N) S

/-- **The placement statement implies the reservation interface.**

Given the chain of per-cell absorbers and connectors, the remainder `H` left by §10 inside the
bottom cells is split into its per-cell parts `H ∩ K_{cell i}`, which are even
(`BKLO.evenDegrees_inter_cliqueEdges`) and cover `H` (`BKLO.eq_biUnion_inter_cliqueEdges`);
`BKLO.triDecomp_chainSet` then absorbs them all under the single global divisibility hypothesis. -/
theorem cellsAbsorberSpread_of_chainReservation (h : CellsChainReservation) :
    CellsAbsorberSpread := by
  classical
  intro ε hε hε1 k m₀ hk
  obtain ⟨m₁, hres0⟩ := h ε hε hε1 k m₀ hk
  refine ⟨m₁, fun mmax => ?_⟩
  obtain ⟨n₀, hres⟩ := hres0 mmax
  refine ⟨n₀, ?_⟩
  intro V _ E S m L Pl hcard hES hdiv hdeg hm hm1 hmmax hseq hPS hPdisj' hPcover hPcard hPdeg
  obtain ⟨N, cell, core, Aa, c₁, c₂, hN, hcellmem, hcellsurj, hPldisj, hcelldisj, hcellcore,
    habs, hc₁l, hc₁r, hc₂l, hc₂r, hc₁ev, hc₂ev, hc₁card, hc₂card, hpieces, hAac, hc₁₂, hcempty,
    hAE, hAev, hAsp⟩ := hres E S m L Pl hcard hES hdiv hdeg hm hm1 hmmax hseq hPS hPdisj'
      hPcover hPcard hPdeg
  set A : Finset (Sym2 V) := chainSet Aa (fun _ => ∅) c₁ c₂ 0 N with hAdef
  refine ⟨A, hAE, hAev, hAsp, ?_⟩
  intro H hHin hHev hHdvd
  -- the remainder is confined to the cells and avoids the reservation
  have hHEA : H ⊆ E \ A := hHin.trans (insideParts_subset _ _)
  have hHE : H ⊆ E := fun e he => (Finset.mem_sdiff.1 (hHEA he)).1
  have hHA : Disjoint H A :=
    Finset.disjoint_left.2 fun e he heA => (Finset.mem_sdiff.1 (hHEA he)).2 heA
  have hloop : ∀ e ∈ H, ¬ e.IsDiag := fun e he => (mem_cliqueEdgesV.1 (hES (hHE he))).2
  -- the per-cell remainders
  set Y : ℕ → Finset (Sym2 V) := fun i => H ∩ cliqueEdges (cell i) with hYdef
  have hYsub : ∀ i, Y i ⊆ H := fun i => Finset.inter_subset_left
  have hYA : ∀ i, Disjoint (Y i) A := fun i => hHA.mono_left (hYsub i)
  -- the reserved material of a cell is part of the reservation
  have hAasub : ∀ i, i < N → Aa i ⊆ A :=
    fun i hi => subset_chainSet_absorber Aa (fun _ => ∅) c₁ c₂ N 0 i (by omega) (by omega)
  have hconnsub : ∀ i, i + 1 < N → c₁ i ∪ c₂ i ⊆ A :=
    fun i hi => subset_chainSet_conn Aa (fun _ => ∅) c₁ c₂ N 0 i (by omega) (by omega)
  have hRsub : ∀ i, i < N → Aa i ∪ c₁ i ∪ c₂ i ⊆ A := by
    intro i hi
    by_cases hi1 : i + 1 < N
    · exact Finset.union_subset (Finset.union_subset (hAasub i hi)
        (Finset.subset_union_left.trans (hconnsub i hi1)))
        (Finset.subset_union_right.trans (hconnsub i hi1))
    · obtain ⟨he₁, he₂⟩ := hcempty i (by omega)
      rw [he₁, he₂]
      simpa using hAasub i hi
  -- `H` is the union of its per-cell parts
  have hHunion : H = (Finset.range N).biUnion Y := by
    have h1 : H = (restrictParts Pl S).biUnion (fun P => H ∩ cliqueEdges P) :=
      eq_biUnion_inter_cliqueEdges hHin hloop
    rw [h1]
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨P, hP, heP⟩
      obtain ⟨i, hi, rfl⟩ := hcellsurj P hP
      exact ⟨i, hi, heP⟩
    · rintro ⟨i, hi, hei⟩
      exact ⟨cell i, hcellmem i hi, hei⟩
  -- the chain data
  have hchain : ChainData Aa Y c₁ c₂ (fun i => cliqueEdges (core i)) N := by
    refine ⟨?_, ?_, ?_, hc₁l, hc₁r, hc₂l, hc₂r, hc₁ev, hc₂ev, hc₁card, hc₂card, ?_, ?_, ?_, hc₁₂⟩
    · intro i hi Z hZ hZev hZdisj hZdvd
      exact (habs i hi).absorbs_even hZ hZev hZdisj hZdvd
    · intro i hi
      exact Finset.inter_subset_right.trans (cliqueEdges_subset_of_subset (hcellcore i hi))
    · intro i hi
      exact evenDegrees_inter_cliqueEdges hHin hloop hHev (hcellmem i hi) hPldisj
    · -- distinct cells carry disjoint material
      intro i hi j hj hij
      have hYY : Disjoint (Y i) (Y j) :=
        (disjoint_cliqueEdges_of_disjoint (hcelldisj i hi j hj hij)).mono
          Finset.inter_subset_right Finset.inter_subset_right
      refine Finset.disjoint_left.2 fun e hei hej => ?_
      simp only [cellPiece, Finset.mem_union] at hei hej
      have hsplit : ∀ a : ℕ, (((e ∈ Aa a ∨ e ∈ Y a) ∨ e ∈ c₁ a) ∨ e ∈ c₂ a) →
          e ∈ Y a ∨ e ∈ Aa a ∪ c₁ a ∪ c₂ a := by
        intro a ha
        rcases ha with ((h' | h') | h') | h'
        · exact Or.inr (by simp [Finset.mem_union, h'])
        · exact Or.inl h'
        · exact Or.inr (by simp [Finset.mem_union, h'])
        · exact Or.inr (by simp [Finset.mem_union, h'])
      rcases hsplit i hei with h1 | h1 <;> rcases hsplit j hej with h2 | h2
      · exact (Finset.disjoint_left.1 hYY) h1 h2
      · exact (Finset.disjoint_left.1 (hYA i)) h1 (hRsub j hj h2)
      · exact (Finset.disjoint_left.1 (hYA j)) h2 (hRsub i hi h1)
      · exact (Finset.disjoint_left.1 (hpieces i hi j hj hij)) h1 h2
    · intro i hi
      exact ((hYA i).mono_right (hAasub i hi)).symm
    · intro i hi
      refine Finset.disjoint_union_left.2 ⟨hAac i (by omega), ?_⟩
      exact (hYA i).mono_right (hconnsub i hi)
  -- absorb
  have hsplitA : A ∪ H = chainSet Aa Y c₁ c₂ 0 N := by
    have hsp := chainSet_split Aa Y c₁ c₂ N 0
    rw [zero_add, ← Finset.range_eq_Ico] at hsp
    rw [hsp, hHunion]
  rw [hsplitA]
  rw [hsplitA] at hHdvd
  exact triDecomp_chainSet hchain hN hHdvd

/-- **The dense theorem from the nibble and the placement statement.** -/
theorem triDecompDense_of_nibble_chainReservation (hplace : CellsChainReservation)
    (happ : ApproxTriDecompMinDeg (9 / 10)) : TriDecompDense :=
  triDecompDense_of_nibble_cellsAbsorberSpread
    (cellsAbsorberSpread_of_chainReservation hplace) happ

end BKLO
