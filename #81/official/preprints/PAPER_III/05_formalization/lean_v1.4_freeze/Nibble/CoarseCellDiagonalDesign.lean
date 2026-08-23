/-
# Nibble — the **diagonal cell design**: three independent per-pair densities, exactly

`Nibble.CoarseCellShapeGate` shows why the naive coarse-cell route to
`Nibble.AX1.BlockCoverResidualCoupled` stops: a cluster triple `(U,W,X)` whose cells are tiled into
`p`, `q`, `s` blocks per axis needs to occupy its three cluster pairs at *three different rates*
(`p·q`, `p·s`, `q·s` block rectangles per cell), while a box built from **one cell per pair** offers
the same rate at all three.  Equalising the rates forces `p = q = s`, i.e.
`C_U/d(W,X) = C_W/d(U,X) = C_X/d(U,W)` for cluster-attached cell lengths `C`, a system that is
over-determined from four clusters on.

This file supplies the mechanism that removes that obstruction, deterministically and with **no
loss at all**.  The coarse cells of a cluster are indexed not by an interval but by a finite abelian
group

    CellIdx Z = (Z × Z) × (Z × Z) × (Z × Z),

one `Z × Z` block per *role* a cluster pair can play in the triple (`ST`, `SY`, `TY`).  Ownership of
a cell of the pair `(S,T)` is decided by the **sum rule** `(gS + gT).1 ∈ A₀` — a union of diagonals,
in the first block only.  Three consequences:

* `Nibble.AX1.diagonalOwnership_disjoint` — cluster triples with disjoint value sets `A₀` own
  disjoint sets of cells of the pair, so the disjointness clause of the residual is free;
* `Nibble.AX1.diagonalOwnership_fibre_card` — the ownership is *exactly* of density `#A₀/#(Z × Z)`
  in every row of the pair grid: the LP value is realised with no rounding loss, and the three
  densities `#A₀`, `#B₀`, `#C₀` of the three pairs of one triple are **independent** — which is what
  the shape gate says is needed;
* the three maps `Nibble.AX1.psiS`, `Nibble.AX1.psiT`, `Nibble.AX1.psiY` assign to a coherent cell
  triangle `(gS, gT, gY)` a *block group* inside each of its three cells, and
  `Nibble.AX1.psi_ST_bijective`, `Nibble.AX1.psi_SY_bijective`, `Nibble.AX1.psi_TY_bijective` say
  that fixing any one face of the triangle, the remaining freedom maps **bijectively** onto the pairs
  of block groups of that face.  In other words every cell of every pair is filled *exactly*, with
  each block rectangle used once, and the shares of the triangles through a face are a partition.

The three face fibres have cardinalities `#C₀·#B₀·|Z|²`, `#C₀·#A₀·|Z|²`, `#B₀·#A₀·|Z|²`
(`Nibble.AX1.faceST_fibre_card` and companions), i.e. the multiplicities `κ` with which a cell of
each pair is shared; the block-group sets have sizes `#C₀·|Z|`, `#B₀·|Z|`, `#A₀·|Z|`.  Their ratios
are exactly the ratios `p : q : s` prescribed by the opposite densities, so the *three separately
sized cell families* of one cluster triple coexist without waste — this is the degree condition
`deg_UW(g)·n_W = deg_UX(g)·n_X` in exact form.

What this file does **not** do is assemble the construction into
`Nibble.AX1.BlockCoverResidualCoupled`; see `AX1_COARSE_CELL_REPORT.md` for the exact remaining
step, and `Nibble.CoarseCellLatinFill` for the Latin filling of a single box.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

open Finset

namespace Nibble.AX1

variable {Z : Type*} [AddCommGroup Z]

/-- **The coarse-cell index of a cluster.**  Three blocks `Z × Z`, one per role a cluster pair can
play inside a cluster triple: the first block carries the `(S,T)` ownership rule, the second the
`(S,Y)` rule, the third the `(T,Y)` rule. -/
abbrev CellIdx (Z : Type*) := (Z × Z) × (Z × Z) × (Z × Z)

/-! ### The ownership rule -/

/-- **The cell triangle is coherent for the triple with value sets `A₀`, `B₀`, `C₀`**: each of its
three cells is owned by that triple, by the sum rule in the block belonging to that pair. -/
def CoherentCell (A₀ B₀ C₀ : Finset (Z × Z)) (gS gT gY : CellIdx Z) : Prop :=
  (gS + gT).1 ∈ A₀ ∧ (gS + gY).2.1 ∈ B₀ ∧ (gT + gY).2.2 ∈ C₀

/-- **Ownership is disjoint**: two cluster triples whose `(S,T)` value sets are disjoint own
disjoint sets of cells of the pair `(S,T)`.  This is the disjointness clause of the residual, for
free. -/
theorem diagonalOwnership_disjoint {A₀ A₁ : Finset (Z × Z)} (h : Disjoint A₀ A₁)
    (gS gT : CellIdx Z) (h₀ : (gS + gT).1 ∈ A₀) : (gS + gT).1 ∉ A₁ :=
  fun h₁ => (Finset.disjoint_left.mp h) h₀ h₁

variable [Fintype Z] [DecidableEq Z]

/-- **Ownership has exactly the prescribed density, in every row.**  For a fixed cell `gS` of the
cluster `S`, the cells `(gS, gT)` of the pair `(S,T)` owned by the triple are exactly a
`#A₀ / #(Z × Z)` fraction of the row.  No rounding, hence no loss against the LP value. -/
theorem diagonalOwnership_fibre_card (A₀ : Finset (Z × Z)) (gS : CellIdx Z) :
    #((univ : Finset (CellIdx Z)).filter (fun gT => (gS + gT).1 ∈ A₀))
      = #A₀ * Fintype.card (Z × Z) * Fintype.card (Z × Z) := by
  classical
  have hset : (univ : Finset (CellIdx Z)).filter (fun gT => (gS + gT).1 ∈ A₀)
      = (A₀.image (fun x => x - gS.1)) ×ˢ (univ : Finset ((Z × Z) × (Z × Z))) := by
    ext g
    constructor
    · intro hg
      have hg' : gS.1 + g.1 ∈ A₀ := by
        simpa [Prod.fst_add] using (Finset.mem_filter.mp hg).2
      exact Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨gS.1 + g.1, hg', by abel⟩, Finset.mem_univ _⟩
    · intro hg
      obtain ⟨x, hx, hx2⟩ := Finset.mem_image.mp (Finset.mem_product.mp hg).1
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hgx : (gS + g).1 = x := by
        rw [Prod.fst_add, ← hx2]; abel
      rw [hgx]
      exact hx
  have himg : #(A₀.image (fun x => x - gS.1)) = #A₀ :=
    Finset.card_image_of_injective _ (fun a b hab => by
      have := congrArg (fun t => t + gS.1) hab
      simpa [sub_add_cancel] using this)
  rw [hset, Finset.card_product, himg, Finset.card_univ]
  simp [Fintype.card_prod, mul_assoc]

/-- Coherence is decidable. -/
instance decidableCoherentCell (A₀ B₀ C₀ : Finset (Z × Z)) (gS gT gY : CellIdx Z) :
    Decidable (CoherentCell A₀ B₀ C₀ gS gT gY) :=
  inferInstanceAs (Decidable ((gS + gT).1 ∈ A₀ ∧ (gS + gY).2.1 ∈ B₀ ∧ (gT + gY).2.2 ∈ C₀))

/-! ### The block-group assignment -/

/-- The block group that the coherent cell triangle `(gS, gT, gY)` uses inside its cell of the
cluster `S`.  Its first component is the `(T,Y)` ownership value, so it ranges over `C₀`. -/
def psiS (gS gT gY : CellIdx Z) : (Z × Z) × Z :=
  ((gT + gY).2.2, (gS + gY).1.1 + (gT + gY).2.1.2)

/-- The block group inside the cell of the cluster `T`; its first component ranges over `B₀`. -/
def psiT (gS gT gY : CellIdx Z) : (Z × Z) × Z :=
  ((gS + gY).2.1, (gT + gY).1.2 + (gS + gT).2.2.1)

/-- The block group inside the cell of the cluster `Y`; its first component ranges over `A₀`. -/
def psiY (gS gT gY : CellIdx Z) : (Z × Z) × Z :=
  ((gS + gT).1, (gT + gY).2.1.1 + (gS + gY).2.2.2)

omit [Fintype Z] [DecidableEq Z] in
theorem psi_ST_injective (gS gT : CellIdx Z) :
    Function.Injective (fun gY : CellIdx Z => (psiS gS gT gY, psiT gS gT gY)) := by
  intro y y' h
  simp only [psiS, psiT, Prod.mk.injEq, Prod.fst_add, Prod.snd_add] at h
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h
  have e2 : y.2.1 = y'.2.1 := add_left_cancel h3
  have e3 : y.2.2 = y'.2.2 := add_left_cancel h1
  rw [e2] at h2
  exact Prod.ext (Prod.ext (add_left_cancel (add_right_cancel h2))
    (add_left_cancel (add_right_cancel h4))) (Prod.ext e2 e3)

omit [Fintype Z] [DecidableEq Z] in
theorem psi_SY_injective (gS gY : CellIdx Z) :
    Function.Injective (fun gT : CellIdx Z => (psiS gS gT gY, psiY gS gT gY)) := by
  intro y y' h
  simp only [psiS, psiY, Prod.mk.injEq, Prod.fst_add, Prod.snd_add] at h
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h
  have e1 : y.1 = y'.1 := add_left_cancel h3
  have e22 : y.2.2 = y'.2.2 := add_right_cancel h1
  have e212 : y.2.1.2 = y'.2.1.2 := add_right_cancel (add_left_cancel h2)
  have e211 : y.2.1.1 = y'.2.1.1 := add_right_cancel (add_right_cancel h4)
  exact Prod.ext e1 (Prod.ext (Prod.ext e211 e212) e22)

omit [Fintype Z] [DecidableEq Z] in
theorem psi_TY_injective (gT gY : CellIdx Z) :
    Function.Injective (fun gS : CellIdx Z => (psiT gS gT gY, psiY gS gT gY)) := by
  intro y y' h
  simp only [psiT, psiY, Prod.mk.injEq, Prod.fst_add, Prod.snd_add] at h
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h
  have e1 : y.1 = y'.1 := add_right_cancel h3
  have e21 : y.2.1 = y'.2.1 := add_right_cancel h1
  have e221 : y.2.2.1 = y'.2.2.1 := add_right_cancel (add_left_cancel h2)
  have e222 : y.2.2.2 = y'.2.2.2 := add_right_cancel (add_left_cancel h4)
  exact Prod.ext e1 (Prod.ext e21 (Prod.ext e221 e222))

omit [DecidableEq Z] in
/-- **Fixing the `(S,T)` face, the block groups of `S` and `T` are a perfect coordinate system.** -/
theorem psi_ST_bijective (gS gT : CellIdx Z) :
    Function.Bijective (fun gY : CellIdx Z => (psiS gS gT gY, psiT gS gT gY)) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨psi_ST_injective gS gT, ?_⟩
  simp [Fintype.card_prod]
  ring

omit [DecidableEq Z] in
/-- **Fixing the `(S,Y)` face, the block groups of `S` and `Y` are a perfect coordinate system.** -/
theorem psi_SY_bijective (gS gY : CellIdx Z) :
    Function.Bijective (fun gT : CellIdx Z => (psiS gS gT gY, psiY gS gT gY)) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨psi_SY_injective gS gY, ?_⟩
  simp [Fintype.card_prod]
  ring

omit [DecidableEq Z] in
/-- **Fixing the `(T,Y)` face, the block groups of `T` and `Y` are a perfect coordinate system.** -/
theorem psi_TY_bijective (gT gY : CellIdx Z) :
    Function.Bijective (fun gS : CellIdx Z => (psiT gS gT gY, psiY gS gT gY)) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨psi_TY_injective gT gY, ?_⟩
  simp [Fintype.card_prod]
  ring

/-! ### Every cell of every pair is filled exactly -/

omit [DecidableEq Z] in
/-- **The `(S,T)` face is filled exactly.**  For a cell `(gS, gT)` of the pair `(S,T)` owned by the
triple, the coherent cell triangles through it correspond **bijectively** to the pairs
(block group of `S`, block group of `T`) available in that cell.  So the triangles sharing the cell
partition its block rectangles, each used exactly once: the disjointness clause holds inside the
cell and the cell is used with no waste. -/
theorem faceST_exact (A₀ B₀ C₀ : Finset (Z × Z)) (gS gT : CellIdx Z)
    (hA : (gS + gT).1 ∈ A₀) :
    Set.BijOn (fun gY : CellIdx Z => (psiS gS gT gY, psiT gS gT gY))
      {gY | CoherentCell A₀ B₀ C₀ gS gT gY}
      {P : ((Z × Z) × Z) × ((Z × Z) × Z) | P.1.1 ∈ C₀ ∧ P.2.1 ∈ B₀} := by
  refine ⟨?_, (psi_ST_injective gS gT).injOn, ?_⟩
  · rintro gY ⟨-, hB, hC⟩
    exact ⟨hC, hB⟩
  · rintro P ⟨hC, hB⟩
    obtain ⟨gY, hgY⟩ := (psi_ST_bijective gS gT).2 P
    have h1 : (gT + gY).2.2 = P.1.1 := congrArg (fun Q => Q.1.1) hgY
    have h2 : (gS + gY).2.1 = P.2.1 := congrArg (fun Q => Q.2.1) hgY
    exact ⟨gY, ⟨hA, h2 ▸ hB, h1 ▸ hC⟩, hgY⟩

omit [DecidableEq Z] in
/-- **The `(S,Y)` face is filled exactly.** -/
theorem faceSY_exact (A₀ B₀ C₀ : Finset (Z × Z)) (gS gY : CellIdx Z)
    (hB : (gS + gY).2.1 ∈ B₀) :
    Set.BijOn (fun gT : CellIdx Z => (psiS gS gT gY, psiY gS gT gY))
      {gT | CoherentCell A₀ B₀ C₀ gS gT gY}
      {P : ((Z × Z) × Z) × ((Z × Z) × Z) | P.1.1 ∈ C₀ ∧ P.2.1 ∈ A₀} := by
  refine ⟨?_, (psi_SY_injective gS gY).injOn, ?_⟩
  · rintro gT ⟨hA, -, hC⟩
    exact ⟨hC, hA⟩
  · rintro P ⟨hC, hA⟩
    obtain ⟨gT, hgT⟩ := (psi_SY_bijective gS gY).2 P
    have h1 : (gT + gY).2.2 = P.1.1 := congrArg (fun Q => Q.1.1) hgT
    have h2 : (gS + gT).1 = P.2.1 := congrArg (fun Q => Q.2.1) hgT
    exact ⟨gT, ⟨h2 ▸ hA, hB, h1 ▸ hC⟩, hgT⟩

omit [DecidableEq Z] in
/-- **The `(T,Y)` face is filled exactly.** -/
theorem faceTY_exact (A₀ B₀ C₀ : Finset (Z × Z)) (gT gY : CellIdx Z)
    (hC : (gT + gY).2.2 ∈ C₀) :
    Set.BijOn (fun gS : CellIdx Z => (psiT gS gT gY, psiY gS gT gY))
      {gS | CoherentCell A₀ B₀ C₀ gS gT gY}
      {P : ((Z × Z) × Z) × ((Z × Z) × Z) | P.1.1 ∈ B₀ ∧ P.2.1 ∈ A₀} := by
  refine ⟨?_, (psi_TY_injective gT gY).injOn, ?_⟩
  · rintro gS ⟨hA, hB, -⟩
    exact ⟨hB, hA⟩
  · rintro P ⟨hB, hA⟩
    obtain ⟨gS, hgS⟩ := (psi_TY_bijective gT gY).2 P
    have h1 : (gS + gY).2.1 = P.1.1 := congrArg (fun Q => Q.1.1) hgS
    have h2 : (gS + gT).1 = P.2.1 := congrArg (fun Q => Q.2.1) hgS
    exact ⟨gS, ⟨h2 ▸ hA, h1 ▸ hB, hC⟩, hgS⟩

/-! ### The three sharing multiplicities -/

omit [AddCommGroup Z] [DecidableEq Z] in
private theorem face_fibre_card_aux (D₀ E₀ : Finset (Z × Z))
    (f : CellIdx Z → ((Z × Z) × Z) × ((Z × Z) × Z)) (hf : Function.Bijective f)
    (S : Finset (CellIdx Z))
    (hS : ∀ g, g ∈ S ↔ ((f g).1.1 ∈ D₀ ∧ (f g).2.1 ∈ E₀)) :
    #S = #D₀ * #E₀ * (Fintype.card Z * Fintype.card Z) := by
  classical
  have hcard : #S
      = #(((D₀ ×ˢ (univ : Finset Z)) ×ˢ (E₀ ×ˢ (univ : Finset Z)))) := by
    refine Finset.card_bij (fun g _ => f g) ?_ ?_ ?_
    · intro g hg
      have := (hS g).mp hg
      simp [Finset.mem_product, this.1, this.2]
    · intro g _ g' _ h
      exact hf.1 h
    · intro P hP
      obtain ⟨g, rfl⟩ := hf.2 P
      simp only [Finset.mem_product, Finset.mem_univ, and_true] at hP
      exact ⟨g, (hS g).mpr ⟨hP.1, hP.2⟩, rfl⟩
  rw [hcard]
  simp [Finset.card_product, Finset.card_univ]
  ring

/-- **The `(S,T)` cells are shared by exactly `#C₀·#B₀·|Z|²` coherent triangles.** -/
theorem faceST_fibre_card (A₀ B₀ C₀ : Finset (Z × Z)) (gS gT : CellIdx Z)
    (hA : (gS + gT).1 ∈ A₀) :
    #((univ : Finset (CellIdx Z)).filter (fun gY => CoherentCell A₀ B₀ C₀ gS gT gY))
      = #C₀ * #B₀ * (Fintype.card Z * Fintype.card Z) := by
  refine face_fibre_card_aux C₀ B₀ _ (psi_ST_bijective gS gT) _ ?_
  intro g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, CoherentCell, psiS, psiT]
  exact ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨hA, h.2, h.1⟩⟩

/-- **The `(S,Y)` cells are shared by exactly `#C₀·#A₀·|Z|²` coherent triangles.** -/
theorem faceSY_fibre_card (A₀ B₀ C₀ : Finset (Z × Z)) (gS gY : CellIdx Z)
    (hB : (gS + gY).2.1 ∈ B₀) :
    #((univ : Finset (CellIdx Z)).filter (fun gT => CoherentCell A₀ B₀ C₀ gS gT gY))
      = #C₀ * #A₀ * (Fintype.card Z * Fintype.card Z) := by
  refine face_fibre_card_aux C₀ A₀ _ (psi_SY_bijective gS gY) _ ?_
  intro g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, CoherentCell, psiS, psiY]
  exact ⟨fun h => ⟨h.2.2, h.1⟩, fun h => ⟨h.2, hB, h.1⟩⟩

/-- **The `(T,Y)` cells are shared by exactly `#B₀·#A₀·|Z|²` coherent triangles.** -/
theorem faceTY_fibre_card (A₀ B₀ C₀ : Finset (Z × Z)) (gT gY : CellIdx Z)
    (hC : (gT + gY).2.2 ∈ C₀) :
    #((univ : Finset (CellIdx Z)).filter (fun gS => CoherentCell A₀ B₀ C₀ gS gT gY))
      = #B₀ * #A₀ * (Fintype.card Z * Fintype.card Z) := by
  refine face_fibre_card_aux B₀ A₀ _ (psi_TY_bijective gT gY) _ ?_
  intro g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, CoherentCell, psiT, psiY]
  exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, hC⟩⟩

/-! ### Axiom check -/

section AxCheck

#print axioms Nibble.AX1.diagonalOwnership_disjoint
#print axioms Nibble.AX1.diagonalOwnership_fibre_card
#print axioms Nibble.AX1.psi_ST_bijective
#print axioms Nibble.AX1.psi_SY_bijective
#print axioms Nibble.AX1.psi_TY_bijective
#print axioms Nibble.AX1.faceST_exact
#print axioms Nibble.AX1.faceSY_exact
#print axioms Nibble.AX1.faceTY_exact
#print axioms Nibble.AX1.faceST_fibre_card
#print axioms Nibble.AX1.faceSY_fibre_card
#print axioms Nibble.AX1.faceTY_fibre_card

end AxCheck

end Nibble.AX1
