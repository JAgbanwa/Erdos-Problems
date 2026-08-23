/-
# One step of the cells reservation: a bounded absorber and two connectors, placed at cell scale

This file contains the single step of BKLO §8's placement of the absorbing structure, run over the
bottom cells of the vortex: given what has already been reserved (`A`), it reserves, inside the
still unused part of the host,

* two vertex-disjoint `4`-cycles inside the current cell (the **connectors** of the chain), and
* a bounded **core absorbing structure** for the current core `U` (BKLO §8.1 through §5).

The point of the step is the *placement*: the fresh vertices of the absorber are chosen with the
conflict relation `BKLO.confRel`, which forbids two of them to lie in the same cell and forbids a
fresh vertex to lie on an edge already reserved into the cell of another vertex of the structure.
With that, the whole new piece adds at most `20` edges at any vertex *into any single cell*, and a
fresh vertex which receives new edges into a cell had none there before.  This is what makes the
reservation spread at the scale of a single cell, which is what the vortex needs
(`BKLO.spreadAlong_of_percell`).

* `BKLO.CoreAbsConf` — the §5/§8.1 placement statement with a conflict relation, as a predicate;
* `BKLO.cellOf`, `BKLO.confRel` — the cell of a vertex and the conflict relation;
* `BKLO.cells_chain_step` — one step of the reservation.

Everything here is `sorry`-free.
-/
import BKLO.CoreAbsorberConf
import BKLO.CellGadgets
import BKLO.Section9Greedy
import BKLO.Section11CellsSeq

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### Two elementary degree bounds -/

/-- The degree into a set is at most the number of edges. -/
theorem degTo_le_card_edges (F : Finset (Sym2 V)) (x : V) (W : Finset V) : degTo F x W ≤ F.card :=
  le_trans (degTo_le_edeg F x W) (Finset.card_filter_le _ _)

/-! ### The §5/§8.1 placement statement with a conflict relation -/

/-- **`BKLO.coreAbsorberExistence_conf` as a predicate.**  For a core of size `C`, a bounded core
absorbing structure of at most `M` edges can be placed on `C + Kt` vertices of the host, avoiding a
forbidden set `F` and pairwise non-conflicting for an arbitrary reflexive symmetric relation
`conf`, provided the host has enough room. -/
def CoreAbsConf (V : Type) [DecidableEq V] (C M Kt : ℕ) : Prop :=
  ∀ (T : Finset (Sym2 V)) (S U F Z : Finset V) (conf : V → V → Prop),
    T ⊆ cliqueEdges S → U ⊆ S → U.card = C → S.Nonempty → U ⊆ F → Z ⊆ S →
    (∀ x, conf x x) → (∀ x y, conf x y → conf y x) →
    (∀ Q : Finset V, Q ⊆ S → Q.card ≤ 9 → ∀ Bad : Finset V, Bad.card ≤ Z.card + Kt →
      ∃ y ∈ S, y ∉ F ∧ (∀ z ∈ Bad, ¬ conf y z) ∧ ∀ q ∈ Q, s(q, y) ∈ T) →
    ∃ (R₂ : Finset (Sym2 V)) (Fr : Finset V),
      R₂ ⊆ T ∧ R₂.card ≤ M ∧ CoreAbsorbers U R₂ ∧
      R₂ ⊆ cliqueEdges (U ∪ Fr) ∧ Fr ⊆ S ∧ Fr.card ≤ Kt ∧
      (∀ v ∈ Fr, v ∉ F) ∧
      (∀ v ∈ Fr, ∀ z ∈ Z, ¬ conf v z) ∧
      (∀ v ∈ Fr, ∀ z ∈ U, ¬ conf v z) ∧
      (∀ v ∈ Fr, ∀ w ∈ Fr, v ≠ w → ¬ conf v w) ∧
      (∀ x : V, degTo R₂ x U ≤ 9)

/-- The placement statement holds, with constants depending only on the size of the core. -/
theorem coreAbsConf_holds (C : ℕ) : ∃ M Kt : ℕ, ∀ (V : Type) [DecidableEq V],
    CoreAbsConf V C M Kt := by
  obtain ⟨M, Kt, h⟩ := coreAbsorberExistence_conf C
  exact ⟨M, Kt, fun V _ => h⟩

/-- Weakening the two constants. -/
theorem CoreAbsConf.mono {C M Kt M' Kt' : ℕ} (h : CoreAbsConf V C M Kt) (hM : M ≤ M')
    (hKt : Kt ≤ Kt') : CoreAbsConf V C M' Kt' := by
  intro T S U F Z conf hTS hUS hUC hSne hUF hZS hrefl hsymm hroom
  obtain ⟨R₂, Fr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    h T S U F Z conf hTS hUS hUC hSne hUF hZS hrefl hsymm
      (fun Q hQ hQc Bad hBad => hroom Q hQ hQc Bad (by omega))
  exact ⟨R₂, Fr, h1, by omega, h3, h4, h5, by omega, h7, h8, h9, h10, h11⟩

/-! ### The cell of a vertex, and the conflict relation -/

/-- The cell of `v` among the cells `cell 0, …, cell (N-1)`, or `{v}` if `v` lies in none of
them. -/
def cellOf (cell : ℕ → Finset V) (N : ℕ) (v : V) : Finset V :=
  ((Finset.range N).filter (fun i => v ∈ cell i)).biUnion cell ∪ {v}

theorem mem_cellOf_self (cell : ℕ → Finset V) (N : ℕ) (v : V) : v ∈ cellOf cell N v := by
  simp [cellOf]

variable {cell : ℕ → Finset V} {N : ℕ}

theorem cellOf_eq_cell (hdisj : ∀ i, i < N → ∀ j, j < N → i ≠ j → Disjoint (cell i) (cell j))
    {j : ℕ} {v : V} (hj : j < N) (hv : v ∈ cell j) : cellOf cell N v = cell j := by
  classical
  have hfilter : (Finset.range N).filter (fun i => v ∈ cell i) = {j} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hi, hvi⟩
      by_contra hne
      exact (Finset.disjoint_left.1 (hdisj i hi j hj hne)) hvi hv
    · rintro rfl
      exact ⟨hj, hv⟩
  rw [cellOf, hfilter, Finset.singleton_biUnion]
  exact Finset.union_eq_left.2 (Finset.singleton_subset_iff.2 hv)

theorem cellOf_eq_singleton {v : V} (h : ∀ i, i < N → v ∉ cell i) : cellOf cell N v = {v} := by
  classical
  have hfilter : (Finset.range N).filter (fun i => v ∈ cell i) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
    exact h i
  rw [cellOf, hfilter]
  simp

theorem cellOf_card_le (hdisj : ∀ i, i < N → ∀ j, j < N → i ≠ j → Disjoint (cell i) (cell j))
    {m : ℕ} (hcard : ∀ i, i < N → (cell i).card ≤ m) (hm : 1 ≤ m) (v : V) :
    (cellOf cell N v).card ≤ m := by
  by_cases h : ∃ j, j < N ∧ v ∈ cell j
  · obtain ⟨j, hj, hv⟩ := h
    rw [cellOf_eq_cell hdisj hj hv]
    exact hcard j hj
  · push_neg at h
    rw [cellOf_eq_singleton h]
    simpa using hm

theorem cellOf_subset (hdisj : ∀ i, i < N → ∀ j, j < N → i ≠ j → Disjoint (cell i) (cell j))
    {S : Finset V} (hcellS : ∀ i, i < N → cell i ⊆ S) {v : V} (hv : v ∈ S) :
    cellOf cell N v ⊆ S := by
  by_cases h : ∃ j, j < N ∧ v ∈ cell j
  · obtain ⟨j, hj, hvj⟩ := h
    rw [cellOf_eq_cell hdisj hj hvj]
    exact hcellS j hj
  · push_neg at h
    rw [cellOf_eq_singleton h]
    simpa using hv

theorem cellOf_congr (hdisj : ∀ i, i < N → ∀ j, j < N → i ≠ j → Disjoint (cell i) (cell j))
    {v w : V} (hw : w ∈ cellOf cell N v) : cellOf cell N w = cellOf cell N v := by
  by_cases h : ∃ j, j < N ∧ v ∈ cell j
  · obtain ⟨j, hj, hvj⟩ := h
    rw [cellOf_eq_cell hdisj hj hvj] at hw ⊢
    exact cellOf_eq_cell hdisj hj hw
  · push_neg at h
    rw [cellOf_eq_singleton h] at hw ⊢
    rw [Finset.mem_singleton] at hw
    rw [hw]
    exact cellOf_eq_singleton h

/-- **The conflict relation of the placement.**  Two vertices conflict if they lie in the same
cell, or if one of them already carries a reserved edge into the cell of the other. -/
def confRel (cell : ℕ → Finset V) (N : ℕ) (A : Finset (Sym2 V)) (y z : V) : Prop :=
  cellOf cell N y = cellOf cell N z ∨ 0 < degTo A y (cellOf cell N z) ∨
    0 < degTo A z (cellOf cell N y)

theorem confRel_refl (A : Finset (Sym2 V)) (y : V) : confRel cell N A y y := Or.inl rfl

theorem confRel_symm (A : Finset (Sym2 V)) (y z : V) :
    confRel cell N A y z → confRel cell N A z y := by
  rintro (h | h | h)
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)



/-! ### One step of the reservation -/

set_option maxHeartbeats 1000000 in
/-- **One step of the cells reservation.**

Inside the host `E` on `S`, with `A` already reserved, the current cell `cell t` and the current
core `U ⊇ cell t`, one can reserve

* two vertex-disjoint `4`-cycles `c1`, `c2` on eight vertices `Tv` of the cell, and
* a bounded core absorbing structure `R` for `U`,

all edge-disjoint from `A` and from each other, so that the new piece `R ∪ c1 ∪ c2`

* adds at most `20` edges at any vertex into any single cell, and
* at a *fresh* vertex only adds edges into cells where that vertex had no reserved edge at all.

The hypotheses are: the host is dense (`hmindeg`), the cell is dense inside itself (`hinternal`)
and large (`hm`), what is already reserved has bounded degree (`hAdeg`), bounded degree into each
cell (`hAcell`) and few edges (`hAcard`), and the host is large compared to the constants
(`hconst`). -/
theorem cells_chain_step {E A : Finset (Sym2 V)} {S : Finset V} {cell : ℕ → Finset V}
    {U : Finset V} {N m M Kt D₀ Δ t : ℕ}
    (hbase : CoreAbsConf V U.card M Kt)
    (hES : E ⊆ cliqueEdges S) (hAE : A ⊆ E)
    (hmindeg : ∀ q ∈ S, 9 * S.card ≤ 10 * edeg E q)
    (htN : t < N)
    (hcellS : ∀ i, i < N → cell i ⊆ S)
    (hcellcard : ∀ i, i < N → (cell i).card ≤ m)
    (hcelllow : m - 1 ≤ (cell t).card)
    (hcelldisj : ∀ i, i < N → ∀ j, j < N → i ≠ j → Disjoint (cell i) (cell j))
    (hinternal : ∀ v ∈ cell t, 9 * (cell t).card ≤ 10 * degTo E v (cell t))
    (hm : 3000 ≤ m)
    (hAdeg : ∀ x : V, edeg A x ≤ Δ)
    (hAcell : ∀ x : V, ∀ j, j < N → degTo A x (cell j) ≤ 60)
    (hUS : U ⊆ S) (hcellU : cell t ⊆ U)
    (hAcard : 40 * (A.card + 8) ≤ (D₀ + 1) * S.card)
    (hconst : 20 * ((Kt + 1) * (9 * (Δ + 8) + U.card + m + 2 * (m * (Δ + 8)) + 1) + 1)
      ≤ S.card) :
    ∃ (Tv : Finset V) (c1 c2 R : Finset (Sym2 V)) (Fr : Finset V),
      Tv ⊆ cell t ∧ Tv.card = 8 ∧
      c1 ⊆ cliqueEdges Tv ∧ c2 ⊆ cliqueEdges Tv ∧
      EvenDegrees c1 ∧ EvenDegrees c2 ∧ c1.card = 4 ∧ c2.card = 4 ∧ Disjoint c1 c2 ∧
      CoreAbsorbers U R ∧ Disjoint R (c1 ∪ c2) ∧
      R ∪ c1 ∪ c2 ⊆ E \ A ∧ (R ∪ c1 ∪ c2).card ≤ M + 8 ∧
      (∀ x : V, x ∉ U ∪ Fr → edeg (R ∪ c1 ∪ c2) x = 0) ∧
      (∀ x ∈ Fr, edeg A x ≤ D₀) ∧
      (∀ x : V, ∀ j, j < N → degTo (R ∪ c1 ∪ c2) x (cell j) ≤ 20) ∧
      (∀ x ∈ Fr, ∀ j, j < N → 0 < degTo (R ∪ c1 ∪ c2) x (cell j) →
        degTo A x (cell j) = 0) := by
  classical
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos]
    omega
  -- ### 1. the two connectors inside the current cell
  have hcelltS : cell t ⊆ S := hcellS t htN
  have hcellcardt : (cell t).card ≤ m := hcellcard t htN
  have hconnDeg : ∀ v ∈ cell t,
      (cell t).card ≤ degTo (E \ A) v (cell t) + ((cell t).card / 10 + 61) := by
    intro v hv
    have h1 := hinternal v hv
    have h2 : degTo E v (cell t) ≤ degTo (E \ A) v (cell t) + degTo A v (cell t) :=
      degTo_sdiff_add_degTo_ge E A v (cell t)
    have h3 := hAcell v t htN
    omega
  have hlargeP : (∅ : Finset V).card + 8 + 8 * ((cell t).card / 10 + 61) < (cell t).card := by
    simp only [Finset.card_empty]
    omega
  obtain ⟨Tv, c1, c2, hTvP, -, hTvcard, hc1F, hc2F, hc1cl, hc2cl, hc12, hc1ev, hc2ev,
    hc1card, hc2card⟩ := exists_two_fourCycles hconnDeg ∅ hlargeP
  -- ### 2. the reservation so far, extended by the connectors
  have hcsub : c1 ∪ c2 ⊆ E \ A := Finset.union_subset hc1F hc2F
  have hccard : (c1 ∪ c2).card ≤ 8 := le_trans (Finset.card_union_le _ _) (by omega)
  set A' : Finset (Sym2 V) := A ∪ (c1 ∪ c2) with hA'def
  have hA'E : A' ⊆ E := Finset.union_subset hAE (fun e he => (Finset.mem_sdiff.1 (hcsub he)).1)
  have hAA' : A ⊆ A' := Finset.subset_union_left
  have hA'deg : ∀ x : V, edeg A' x ≤ Δ + 8 := by
    intro x
    have h1 : edeg A' x ≤ edeg A x + edeg (c1 ∪ c2) x := by
      rw [hA'def]; exact edeg_union_le A (c1 ∪ c2) x
    have h2 : edeg (c1 ∪ c2) x ≤ (c1 ∪ c2).card := by
      unfold edeg; exact Finset.card_filter_le _ _
    have h3 := hAdeg x
    omega
  have hA'card : A'.card ≤ A.card + 8 := le_trans (Finset.card_union_le _ _) (by omega)
  have hDp : ∀ w : V, degTo A' w S ≤ Δ + 8 := fun w =>
    le_trans (degTo_le_edeg A' w S) (hA'deg w)
  -- ### 3. the forbidden set: the core and the vertices already carrying many reserved edges
  set High : Finset V := S.filter (fun v => ¬ edeg A' v ≤ D₀) with hHighdef
  set Fset : Finset V := U ∪ High with hFsetdef
  have hUF : U ⊆ Fset := Finset.subset_union_left
  have hHighcard : 20 * High.card ≤ S.card := by
    have h1 : High.card ≤ 2 * A'.card / (D₀ + 1) := card_high_deg_le A' S D₀
    have h2 : High.card * (D₀ + 1) ≤ 2 * A'.card :=
      le_trans (Nat.mul_le_mul_right _ h1) (Nat.div_mul_le_self _ _)
    have h4 : 40 * (A.card + 8) ≤ (D₀ + 1) * S.card := hAcard
    have h5 : (20 * High.card) * (D₀ + 1) ≤ S.card * (D₀ + 1) := by
      calc (20 * High.card) * (D₀ + 1) = 20 * (High.card * (D₀ + 1)) := by ring
        _ ≤ 20 * (2 * A'.card) := Nat.mul_le_mul_left _ h2
        _ ≤ 40 * (A.card + 8) := by omega
        _ ≤ (D₀ + 1) * S.card := h4
        _ = S.card * (D₀ + 1) := by ring
    exact Nat.le_of_mul_le_mul_right h5 (Nat.succ_pos _)
  -- ### 4. the room for a fresh vertex
  have hcellcardOf : ∀ v : V, (cellOf cell N v).card ≤ m :=
    cellOf_card_le hcelldisj hcellcard (by omega)
  have hroom : ∀ Q : Finset V, Q ⊆ S → Q.card ≤ 9 → ∀ Bad : Finset V,
      Bad.card ≤ (∅ : Finset V).card + Kt →
      ∃ y ∈ S, y ∉ Fset ∧ (∀ z ∈ Bad, ¬ confRel cell N A' y z) ∧
        ∀ q ∈ Q, s(q, y) ∈ E \ A' := by
    intro Q hQS hQcard Bad hBadcard
    simp only [Finset.card_empty, Nat.zero_add] at hBadcard
    set ConfSet : V → Finset V := fun z =>
      (cellOf cell N z ∪ (cellOf cell N z).biUnion (fun w => nbhdIn A' w S)) ∪
        (nbhdIn A' z S).biUnion (fun w => cellOf cell N w) with hConfdef
    set BadV : Finset V :=
      (Q.biUnion (fun q => S \ nbhdIn (E \ A') q S) ∪ Fset) ∪ Bad.biUnion ConfSet with hBadVdef
    have hConfcard : ∀ z : V, (ConfSet z).card ≤ m + 2 * (m * (Δ + 8)) := by
      intro z
      have h1 : ((cellOf cell N z).biUnion (fun w => nbhdIn A' w S)).card ≤ m * (Δ + 8) := by
        refine le_trans Finset.card_biUnion_le ?_
        calc ∑ w ∈ cellOf cell N z, (nbhdIn A' w S).card
            ≤ ∑ _w ∈ cellOf cell N z, (Δ + 8) := Finset.sum_le_sum fun w _ => hDp w
          _ = (cellOf cell N z).card * (Δ + 8) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ m * (Δ + 8) := Nat.mul_le_mul_right _ (hcellcardOf z)
      have h2 : ((nbhdIn A' z S).biUnion (fun w => cellOf cell N w)).card ≤ m * (Δ + 8) := by
        refine le_trans Finset.card_biUnion_le ?_
        calc ∑ w ∈ nbhdIn A' z S, (cellOf cell N w).card
            ≤ ∑ _w ∈ nbhdIn A' z S, m := Finset.sum_le_sum fun w _ => hcellcardOf w
          _ = (nbhdIn A' z S).card * m := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ (Δ + 8) * m := Nat.mul_le_mul_right _ (hDp z)
          _ = m * (Δ + 8) := by ring
      have h3 := hcellcardOf z
      have h4 : (ConfSet z).card ≤ (cellOf cell N z).card
          + ((cellOf cell N z).biUnion (fun w => nbhdIn A' w S)).card
          + ((nbhdIn A' z S).biUnion (fun w => cellOf cell N w)).card :=
        le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      omega
    have hsumQ : 10 * (∑ q ∈ Q, (S \ nbhdIn (E \ A') q S).card)
        ≤ 9 * (S.card + 10 * (Δ + 8)) := by
      have hper : ∀ q ∈ Q, 10 * (S \ nbhdIn (E \ A') q S).card ≤ S.card + 10 * (Δ + 8) := by
        intro q hq
        have hqS : q ∈ S := hQS hq
        have h1 : (S \ nbhdIn (E \ A') q S).card + (nbhdIn (E \ A') q S).card = S.card :=
          Finset.card_sdiff_add_card_eq_card (nbhdIn_subset _ _ _)
        have h2 : degTo E q S ≤ degTo (E \ A') q S + degTo A' q S :=
          degTo_sdiff_add_degTo_ge E A' q S
        have h3 : degTo A' q S ≤ Δ + 8 := hDp q
        have h4 : edeg E q = degTo E q S :=
          edeg_eq_degTo_of_supp (fun e he x hx => (mem_cliqueEdgesV.1 (hES he)).1 x hx) q
        have h5 := hmindeg q hqS
        unfold degTo at h2 h3 h4
        omega
      calc 10 * (∑ q ∈ Q, (S \ nbhdIn (E \ A') q S).card)
          = ∑ q ∈ Q, 10 * (S \ nbhdIn (E \ A') q S).card := by rw [Finset.mul_sum]
        _ ≤ ∑ _q ∈ Q, (S.card + 10 * (Δ + 8)) := Finset.sum_le_sum hper
        _ = Q.card * (S.card + 10 * (Δ + 8)) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 9 * (S.card + 10 * (Δ + 8)) := Nat.mul_le_mul_right _ hQcard
    have hBadsum : (Bad.biUnion ConfSet).card ≤ Kt * (m + 2 * (m * (Δ + 8))) := by
      refine le_trans Finset.card_biUnion_le ?_
      calc ∑ z ∈ Bad, (ConfSet z).card ≤ ∑ _z ∈ Bad, (m + 2 * (m * (Δ + 8))) :=
            Finset.sum_le_sum fun z _ => hConfcard z
        _ = Bad.card * (m + 2 * (m * (Δ + 8))) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ Kt * (m + 2 * (m * (Δ + 8))) := Nat.mul_le_mul_right _ hBadcard
    have hkey : 9 * (Δ + 8) + U.card + Kt * (m + 2 * (m * (Δ + 8)))
        ≤ (Kt + 1) * (9 * (Δ + 8) + U.card + m + 2 * (m * (Δ + 8)) + 1) := by
      have hb : m + 2 * (m * (Δ + 8))
          ≤ 9 * (Δ + 8) + U.card + m + 2 * (m * (Δ + 8)) + 1 := by omega
      have hc : Kt * (m + 2 * (m * (Δ + 8)))
          ≤ Kt * (9 * (Δ + 8) + U.card + m + 2 * (m * (Δ + 8)) + 1) :=
        Nat.mul_le_mul_left _ hb
      have hd : (Kt + 1) * (9 * (Δ + 8) + U.card + m + 2 * (m * (Δ + 8)) + 1)
          = Kt * (9 * (Δ + 8) + U.card + m + 2 * (m * (Δ + 8)) + 1)
            + (9 * (Δ + 8) + U.card + m + 2 * (m * (Δ + 8)) + 1) := by ring
      omega
    have hFcard : Fset.card ≤ U.card + High.card := Finset.card_union_le _ _
    have hBadV : BadV.card ≤ (∑ q ∈ Q, (S \ nbhdIn (E \ A') q S).card) + Fset.card
        + (Bad.biUnion ConfSet).card := by
      refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
      exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right Finset.card_biUnion_le _)
    have hcount : BadV.card < S.card := by omega
    have hne : (S \ BadV).Nonempty := by
      rw [← Finset.card_pos]
      have h := Finset.le_card_sdiff BadV S
      omega
    obtain ⟨y, hy⟩ := hne
    rw [Finset.mem_sdiff] at hy
    obtain ⟨hyS, hyBad⟩ := hy
    have hyQ : ∀ q ∈ Q, s(q, y) ∈ E \ A' := by
      intro q hq
      by_contra hcon
      exact hyBad (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_biUnion.2 ⟨q, hq, Finset.mem_sdiff.2 ⟨hyS, fun hmem =>
          hcon (mem_nbhdIn.1 hmem).2⟩⟩)))
    have hyF : y ∉ Fset := fun h => hyBad (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    refine ⟨y, hyS, hyF, ?_, hyQ⟩
    intro z hz hconf
    refine hyBad (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨z, hz, ?_⟩))
    rcases hconf with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (h ▸ mem_cellOf_self cell N y))
    · obtain ⟨w, hw⟩ := Finset.card_pos.1 h
      rw [mem_nbhdIn] at hw
      refine Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨w, hw.1, ?_⟩))
      exact mem_nbhdIn.2 ⟨hyS, by rw [Sym2.eq_swap]; exact hw.2⟩
    · obtain ⟨w, hw⟩ := Finset.card_pos.1 h
      rw [mem_nbhdIn] at hw
      have hwS : w ∈ S := cellOf_subset hcelldisj hcellS hyS hw.1
      refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨w, mem_nbhdIn.2 ⟨hwS, hw.2⟩, ?_⟩)
      rw [cellOf_congr hcelldisj hw.1]
      exact mem_cellOf_self _ _ _
  -- ### 5. the bounded absorber for the core, placed conflict-free
  have hTS : (E \ A') ⊆ cliqueEdges S := fun e he => hES (Finset.mem_sdiff.1 he).1
  obtain ⟨R, Fr, hRT, hRcard, hRabs, hRcl, hFrS, hFrcard, hFrF, -, hFrU, hFrFr, hRdeg⟩ :=
    hbase (E \ A') S U Fset ∅ (confRel cell N A') hTS hUS rfl hSne hUF
      (Finset.empty_subset _) (fun x => confRel_refl A' x) (fun x y => confRel_symm A' x y) hroom
  -- ### 6. the new piece
  have hcU : c1 ∪ c2 ⊆ cliqueEdges U :=
    Finset.union_subset (hc1cl.trans (cliqueEdges_mono (hTvP.trans hcellU)))
      (hc2cl.trans (cliqueEdges_mono (hTvP.trans hcellU)))
  have hRc : Disjoint R (c1 ∪ c2) := by
    refine Finset.disjoint_left.2 fun e heR hec => ?_
    exact (Finset.mem_sdiff.1 (hRT heR)).2 (Finset.mem_union_right _ hec)
  have hpieceEA : R ∪ c1 ∪ c2 ⊆ E \ A := by
    intro e he
    have he' : e ∈ R ∪ (c1 ∪ c2) := by rwa [Finset.union_assoc] at he
    rcases Finset.mem_union.1 he' with h | h
    · obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 (hRT h)
      exact Finset.mem_sdiff.2 ⟨h1, fun hA => h2 (hAA' hA)⟩
    · exact hcsub h
  have hpiececard : (R ∪ c1 ∪ c2).card ≤ M + 8 := by
    have h1 : (R ∪ c1 ∪ c2).card ≤ (R ∪ c1).card + c2.card := Finset.card_union_le _ _
    have h2 : (R ∪ c1).card ≤ R.card + c1.card := Finset.card_union_le _ _
    omega
  have hpiececl : R ∪ c1 ∪ c2 ⊆ cliqueEdges (U ∪ Fr) := by
    intro e he
    have he' : e ∈ R ∪ (c1 ∪ c2) := by rwa [Finset.union_assoc] at he
    rcases Finset.mem_union.1 he' with h | h
    · exact hRcl h
    · exact cliqueEdges_mono Finset.subset_union_left (hcU h)
  have hzero : ∀ x : V, x ∉ U ∪ Fr → edeg (R ∪ c1 ∪ c2) x = 0 := by
    intro x hx
    unfold edeg
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun e he hxe => hx ((mem_cliqueEdgesV.1 (hpiececl he)).1 x hxe)
  have hFrnotU : ∀ x ∈ Fr, x ∉ U := fun x hx hxU => hFrF x hx (Finset.mem_union_left _ hxU)
  have hFrdeg : ∀ x ∈ Fr, edeg A x ≤ D₀ := by
    intro x hx
    have h1 : x ∉ Fset := hFrF x hx
    have h2 : x ∈ S := hFrS hx
    have h3 : edeg A' x ≤ D₀ := by
      by_contra hcon
      exact h1 (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨h2, hcon⟩))
    exact le_trans (edeg_mono hAA' x) h3
  have hFrcell : ∀ j, j < N → (Fr ∩ cell j).card ≤ 1 := by
    intro j hj
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    rw [Finset.mem_inter] at ha hb
    by_contra hne
    exact hFrFr a ha.1 b hb.1 hne
      (Or.inl (by rw [cellOf_eq_cell hcelldisj hj ha.2, cellOf_eq_cell hcelldisj hj hb.2]))
  have hdegpiece : ∀ x : V, ∀ j, j < N → degTo (R ∪ c1 ∪ c2) x (cell j) ≤ 20 := by
    intro x j hj
    have hsub : nbhdIn (R ∪ c1 ∪ c2) x (cell j) ⊆
        (nbhdIn R x U ∪ (Fr ∩ cell j)) ∪ nbhdIn (c1 ∪ c2) x (cell j) := by
      intro y hy
      rw [mem_nbhdIn] at hy
      obtain ⟨hyj, hye⟩ := hy
      have hye' : s(x, y) ∈ R ∪ (c1 ∪ c2) := by rwa [Finset.union_assoc] at hye
      rcases Finset.mem_union.1 hye' with h | h
      · have hyUF : y ∈ U ∪ Fr := (mem_cliqueEdgesV.1 (hRcl h)).1 y (by simp)
        rcases Finset.mem_union.1 hyUF with hU | hF
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (mem_nbhdIn.2 ⟨hU, h⟩))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_inter.2 ⟨hF, hyj⟩))
      · exact Finset.mem_union_right _ (mem_nbhdIn.2 ⟨hyj, h⟩)
    have h1 : degTo R x U ≤ 9 := hRdeg x
    have h2 : (Fr ∩ cell j).card ≤ 1 := hFrcell j hj
    have h3 : degTo (c1 ∪ c2) x (cell j) ≤ 8 := le_trans (degTo_le_card_edges _ _ _) hccard
    have h4 : ((nbhdIn R x U ∪ (Fr ∩ cell j)) ∪ nbhdIn (c1 ∪ c2) x (cell j)).card
        ≤ (nbhdIn R x U).card + (Fr ∩ cell j).card + (nbhdIn (c1 ∪ c2) x (cell j)).card :=
      le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have h5 : degTo (R ∪ c1 ∪ c2) x (cell j)
        ≤ ((nbhdIn R x U ∪ (Fr ∩ cell j)) ∪ nbhdIn (c1 ∪ c2) x (cell j)).card :=
      Finset.card_le_card hsub
    unfold degTo at h1 h3 h5 ⊢
    omega
  have hfresh : ∀ x ∈ Fr, ∀ j, j < N → 0 < degTo (R ∪ c1 ∪ c2) x (cell j) →
      degTo A x (cell j) = 0 := by
    intro x hx j hj hpos
    obtain ⟨y, hy⟩ := Finset.card_pos.1 hpos
    rw [mem_nbhdIn] at hy
    obtain ⟨hyj, hye⟩ := hy
    have hxU : x ∉ U := hFrnotU x hx
    have hye' : s(x, y) ∈ R ∪ (c1 ∪ c2) := by rwa [Finset.union_assoc] at hye
    have hyR : s(x, y) ∈ R := by
      rcases Finset.mem_union.1 hye' with h | h
      · exact h
      · exact absurd ((mem_cliqueEdgesV.1 (hcU h)).1 x (by simp)) hxU
    have hyUF : y ∈ U ∪ Fr := (mem_cliqueEdgesV.1 (hRcl hyR)).1 y (by simp)
    have hnoconf : ¬ confRel cell N A' x y := by
      rcases Finset.mem_union.1 hyUF with hU | hF
      · exact hFrU x hx y hU
      · have hne : x ≠ y := by
          rintro rfl
          have hdiag : ¬ (s(x, x) : Sym2 V).IsDiag :=
            (mem_cliqueEdgesV.1 (hES (Finset.mem_sdiff.1 (hRT hyR)).1)).2
          exact hdiag (by simp)
        exact hFrFr x hx y hF hne
    have hcy : cellOf cell N y = cell j := cellOf_eq_cell hcelldisj hj hyj
    have h0 : degTo A' x (cell j) = 0 := by
      by_contra hcon
      exact hnoconf (Or.inr (Or.inl (by rw [hcy]; omega)))
    have h1 : degTo A x (cell j) ≤ degTo A' x (cell j) := degTo_mono_left hAA' x (cell j)
    omega
  exact ⟨Tv, c1, c2, R, Fr, hTvP, hTvcard, hc1cl, hc2cl, hc1ev, hc2ev, hc1card, hc2card, hc12,
    hRabs, hRc, hpieceEA, hpiececard, hzero, hFrdeg, hdegpiece, hfresh⟩

end BKLO
