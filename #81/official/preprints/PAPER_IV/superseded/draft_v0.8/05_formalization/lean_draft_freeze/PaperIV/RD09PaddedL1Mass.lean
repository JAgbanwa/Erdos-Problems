import PaperIV.RD09PaddedL1Adapter

/-!
# From the heavy padded palette to the literal RD09-L1 inequality

This module combines the two independently proved finite certificates:

* the selected `p` colour classes contain at least `p/c` of all exterior
  edges;
* cyclic assignment loses at most `(w-1)A/p` compatible bases.

Under the calibrated bounds `c ≤ 73p/40` and `w-1 ≤ 3p/40`, their integral
combination is exactly `L9`.
-/

namespace PaperIV.RD09PaddedL1Mass

open Finset PaperIV.Model PaperIV.RD09L1Adapter
open PaperIV.RD09PaddedHostBase PaperIV.RD09PaddedL1Adapter
open PaperIV.MultiHostTriangleLift PaperIV.RD09RootedOrderAdapter
open PaperIV.PaddedEquitableColouring

/-- Pure integral elimination of the selected-class total. -/
theorem L9_of_heavy_selection
    {p c m selected kept width A : ℕ} (hp : 0 < p)
    (hmass : p * m ≤ c * selected)
    (hkeep : p * selected ≤ p * kept + width * A)
    (hpalette : 40 * c ≤ 73 * p)
    (hwidth : 40 * width ≤ 3 * p) :
    1600 * m ≤ 2920 * kept + 219 * A := by
  have h1 := Nat.mul_le_mul_left (40 * p) hmass
  have h2 := Nat.mul_le_mul_left (p * selected) hpalette
  have h3 := Nat.mul_le_mul_left (2920 * p) hkeep
  have h4 := Nat.mul_le_mul_left (73 * p * A) hwidth
  have hscaled :
      (p * p) * (1600 * m) ≤ (p * p) * (2920 * kept + 219 * A) := by
    nlinarith
  exact Nat.le_of_mul_le_mul_left hscaled (Nat.mul_pos hp hp)

variable {V A I : Type*} [Fintype V] [DecidableEq V]
variable [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
variable [Nonempty I] [Group I]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {H : SimpleGraph A} [DecidableRel H.Adj]

/-- The sharp phase-I output together with the literal translated root
enumeration used by the averaging argument.  Keeping `shift` and `hz` is
essential for phase II: they certify that the physical L1 hosts still
enumerate the complete root, rather than merely having the right cardinality. -/
theorem exists_padded_phaseI_with_L9_and_roots
    {P : Finset V} (O : PaperIV.RootedEliminationOrder.Order G P)
    (f : A ↪ V) (root : I → V)
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b))
    (hreflect : ∀ a b : A, G.Adj (f a) (f b) → H.Adj a b)
    (hrootInj : Function.Injective root)
    (hroot : ∀ r, root r ∈ P)
    (hout : ∀ a : A, f a ∉ P)
    (hpalette : 40 * paddedPaletteSize H (Fintype.card I) ≤
      73 * Fintype.card I)
    (hwidth : 40 * (H.cliqueNum - 1) ≤ 3 * Fintype.card I) :
    ∃ shift : I, ∃ z : I → V, ∃ E : I → Finset (Sym2 V),
      (∀ i, z i = root (i * shift)) ∧
      (∀ i, E i = compatiblePaddedHostBase G H I f (z i) i) ∧
      IsMultiExteriorHub G z E ∧
      IsPacking G (multiLiftedPacking z E) ∧
      1600 * (graphEdges H).card ≤
        2920 * (multiLiftedPacking z E).card +
          219 * (missingIncidences G root f).card := by
  obtain ⟨shift, z, E, hz, hE, hhub, hpack, hadd, hledger⟩ :=
    rd09PaddedL1_ledger_cliqueNum_of_rooted_order O f root hcore hreflect
      hrootInj hroot hout
  refine ⟨shift, z, E, hz, hE, hhub, hpack, ?_⟩
  have hmass := card_mul_graphEdges_le_palette_mul_sum_card_paddedHostBase
    (H := H) (I := I) f
  have hp : 0 < Fintype.card I := Fintype.card_pos
  apply L9_of_heavy_selection hp hmass
  · simpa [hE] using hledger
  · exact hpalette
  · exact hwidth

/-- Complete phase-I output with the literal natural-number `L9`.  All graph
structure is discharged by the rooted PEO; only the two calibrated scalar
bounds on palette size and exterior clique width remain. -/
theorem exists_padded_phaseI_with_L9
    {P : Finset V} (O : PaperIV.RootedEliminationOrder.Order G P)
    (f : A ↪ V) (root : I → V)
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b))
    (hreflect : ∀ a b : A, G.Adj (f a) (f b) → H.Adj a b)
    (hrootInj : Function.Injective root)
    (hroot : ∀ r, root r ∈ P)
    (hout : ∀ a : A, f a ∉ P)
    (hpalette : 40 * paddedPaletteSize H (Fintype.card I) ≤
      73 * Fintype.card I)
    (hwidth : 40 * (H.cliqueNum - 1) ≤ 3 * Fintype.card I) :
    ∃ z : I → V, ∃ E : I → Finset (Sym2 V),
      IsMultiExteriorHub G z E ∧
      IsPacking G (multiLiftedPacking z E) ∧
      1600 * (graphEdges H).card ≤
        2920 * (multiLiftedPacking z E).card +
          219 * (missingIncidences G root f).card := by
  obtain ⟨_, z, E, -, -, hhub, hpack, hL9⟩ :=
    exists_padded_phaseI_with_L9_and_roots O f root hcore hreflect
      hrootInj hroot hout hpalette hwidth
  exact ⟨z, E, hhub, hpack, hL9⟩

end PaperIV.RD09PaddedL1Mass
