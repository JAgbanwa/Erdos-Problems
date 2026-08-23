/-
# Two interface statements of the skeleton are refutable — and why.

While filling the two holes of the project we found that two of the *interface predicates* recorded
in the original skeleton are, as literally stated, **false**.  Both failures are formalisation
artefacts (a missing hypothesis), not mathematical ones, and both are recorded here with a proof,
so that nothing in the project rests on an unstated (and false) assumption.

* `BKLO.AbsorberExistence` (`BKLO/Main.lean`) asserts that *every* edge set `H` on a finite vertex
  type has an absorber, with the `K₃`-divisibility hypotheses explicitly "elided in this skeleton".
  Divisibility is *necessary*: a single edge has no absorber.  See `not_absorberExistence`.

* `BKLO.ExpansionChain` (`BKLO/Absorber.lean`) does carry the divisibility hypothesis, but it is
  stated for an arbitrary finite vertex type and for arbitrary edge sets, i.e. **loops are
  allowed** (`Sym2` contains the diagonal pairs `s(v,v)`).  A loop can never be covered, since
  `cliqueEdges` contains no diagonal edge, while a set of loops can perfectly well be
  triangle-divisible.  See `not_expansionChain`.

  The corrected, *true* statement — over the vertex type `ℕ`, so that fresh vertices are available
  (which the §8.1 F-expansion construction genuinely needs), and with looplessness assumed — is
  `BKLO.ExpansionChainNat` in `BKLO/AbsorberExists.lean`, and it is proved there.
-/
import BKLO.Absorber
import Mathlib.Tactic.NormNum

open Finset

namespace BKLO

/-- On a vertex type with fewer than three vertices there are no triangles at all, so the only
triangle-decomposable edge set is the empty one. -/
theorem eq_empty_of_triDecomp_of_card_lt_three {V : Type*} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V < 3) {E : Finset (Sym2 V)} (h : TriDecomp E) : E = ∅ := by
  obtain ⟨P, hc, -, he⟩ := h
  have hP : P = ∅ := by
    by_contra hne
    obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have := Finset.card_le_univ t
    rw [hc t ht] at this
    omega
  rw [← he, hP]
  simp [famEdges]

/-- A single edge on two vertices has no absorber: divisibility is genuinely necessary.  This is
the counterexample to `BKLO.AbsorberExistence`, refuted in `BKLO/Main.lean`. -/
theorem not_isAbsorber_single_edge (A : Finset (Sym2 (Fin 2))) :
    ¬ IsAbsorber A ({s(0, 1)} : Finset (Sym2 (Fin 2))) := by
  rintro ⟨-, -, hdec⟩
  have hcard : Fintype.card (Fin 2) < 3 := by simp
  have hE : A ∪ ({s(0, 1)} : Finset (Sym2 (Fin 2))) = ∅ :=
    eq_empty_of_triDecomp_of_card_lt_three hcard hdec
  have : s(0, 1) ∈ (∅ : Finset (Sym2 (Fin 2))) := by
    rw [← hE]; simp
  simp at this

/-- The three-element edge set `{s(0,0), s(1,1), s(0,1)}` on `Fin 2` is triangle-divisible: each
vertex lies on exactly two of its edges, and it has three edges. -/
theorem triDivisible_loops :
    TriDivisible ({s(0, 0), s(1, 1), s(0, 1)} : Finset (Sym2 (Fin 2))) := by
  constructor
  · decide
  · decide

/-- **`ExpansionChain` is refutable.**  It allows loops (`Sym2` diagonal edges), and a set of loops
can be triangle-divisible while no triangle ever covers a loop. -/
theorem not_expansionChain : ¬ ExpansionChain := by
  intro h
  obtain ⟨A', K, hT, -, -⟩ := h (V := Fin 2) _ triDivisible_loops
  have hcard : Fintype.card (Fin 2) < 3 := by simp
  have hE := eq_empty_of_triDecomp_of_card_lt_three hcard hT.2.2.1
  have : s(0, 0) ∈ (∅ : Finset (Sym2 (Fin 2))) := by
    rw [← hE]; simp
  simp at this

end BKLO
