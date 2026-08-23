/-
# BKLO Section 8 — compositional glue for absorbers.

The genuine combinatorial hole of §8.1 (the F-expansion / identification construction, isolated as
`ExpansionChain` in `BKLO.Absorber`) builds an absorber for a single divisible piece.  This file
provides the *composition* half — orthogonal to the construction and fully elementary — showing that
absorbers of edge-disjoint pieces combine into an absorber of their union.  It is a direct
application of the workhorse `TriDecomp.union`.

Consequence: to obtain `ExpansionChain` it suffices to absorb each connected piece (indeed each
edge-disjoint cycle of the even-degree set `H`) *on its own fresh vertices*; `isAbsorber_biUnion`
then assembles them.  This localises the remaining hole to a single-piece absorber.
-/
import BKLO.Transformer

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- **Binary composition of absorbers.**  If `A₁` absorbs `H₁` and `A₂` absorbs `H₂`, and the four
edge sets are pairwise edge-disjoint (as they are when the two pieces live on disjoint fresh
vertices), then `A₁ ∪ A₂` absorbs `H₁ ∪ H₂`. -/
theorem isAbsorber_union {A₁ H₁ A₂ H₂ : Finset (Sym2 V)}
    (h1 : IsAbsorber A₁ H₁) (h2 : IsAbsorber A₂ H₂)
    (dA : Disjoint A₁ A₂) (dA₁H₂ : Disjoint A₁ H₂) (dA₂H₁ : Disjoint A₂ H₁)
    (dH : Disjoint H₁ H₂) :
    IsAbsorber (A₁ ∪ A₂) (H₁ ∪ H₂) := by
  obtain ⟨dA₁H₁, hAdec₁, hAHdec₁⟩ := h1
  obtain ⟨dA₂H₂, hAdec₂, hAHdec₂⟩ := h2
  refine ⟨?_, ?_, ?_⟩
  · -- Disjoint (A₁ ∪ A₂) (H₁ ∪ H₂)
    exact Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨dA₁H₁, dA₁H₂⟩,
       Finset.disjoint_union_right.mpr ⟨dA₂H₁, dA₂H₂⟩⟩
  · -- TriDecomp (A₁ ∪ A₂)
    exact TriDecomp.union dA hAdec₁ hAdec₂
  · -- TriDecomp ((A₁ ∪ A₂) ∪ (H₁ ∪ H₂)) = TriDecomp ((A₁ ∪ H₁) ∪ (A₂ ∪ H₂))
    have dcross : Disjoint (A₁ ∪ H₁) (A₂ ∪ H₂) :=
      Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_right.mpr ⟨dA, dA₁H₂⟩,
         Finset.disjoint_union_right.mpr ⟨dA₂H₁.symm, dH⟩⟩
    have h := TriDecomp.union dcross hAHdec₁ hAHdec₂
    convert h using 1
    ext x; simp only [Finset.mem_union]; tauto

/-- **Empty absorber for the empty piece.** -/
theorem isAbsorber_empty : IsAbsorber (∅ : Finset (Sym2 V)) ∅ :=
  ⟨by simp, triDecomp_empty, by simpa using triDecomp_empty⟩

end BKLO
