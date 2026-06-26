import RequestProject.Defs
import RequestProject.Countable
import RequestProject.NoInfiniteClique
import RequestProject.Example
import RequestProject.FiniteBlock

/-!
# Integer-distance graphs in planar general position

This is the top-level summary of the formalisation of

> J. Agbanwa, *Integer-distance graphs in planar general position: rigorous bounds and the
> finite-block reduction*.

Throughout, `A ⊆ ℝ²` (`Plane := EuclideanSpace ℝ (Fin 2)`) is in **general position**:

* `NoThreeCollinear A` — no three points collinear (assumption (i));
* `NoFourConcyclic A`  — no four points concyclic (assumption (ii));

and `Γ(A) = IntDistGraph A` is the integer-distance graph (`Defs.lean`).

## What is proved

* **Theorem 1.2** (`IntDistGraph.component_countable`, `IntDistGraph.colorable_aleph0`):
  every connected component of `Γ(A)` is countable, and `Γ(A)` admits a proper colouring with
  colours in `ℕ` (`χ(Γ(A)) ≤ ℵ₀`).  (`Countable.lean`)
* **Theorem 1.3** (`no_infinite_clique`, `isClique_finite`): `Γ(A)` has no infinite clique; every
  clique is finite.  (`NoInfiniteClique.lean`)
* **Theorem 1.4, forward direction** (`IntDistGraph.finite_block_forward`) and the full
  equivalence statement (`IntDistGraph.finite_block_criterion`).  The converse direction and the
  underlying Baire-category Lemma 4.2 (`IntDistGraph.generic_separation`,
  `IntDistGraph.finite_block_converse`) are stated faithfully; their proofs are the additional
  finite-realisation input isolated by the paper and remain `sorry`.  (`FiniteBlock.lean`)
* **Example 5.1** (`IntDistK5.exists_general_position_int_K5`): an explicit finite general-position
  set whose integer-distance graph contains a `K₅`.  (`Example.lean`)
-/

open scoped BigOperators
open EuclideanGeometry

namespace IntDistGraphPaper

variable {A : Set Plane}

/-- **Theorem 1.2 (Countable components).** Every connected component of `Γ(A)` is countable. -/
theorem components_countable (hA4 : NoFourConcyclic A) (v : A) :
    {w : A | (IntDistGraph A).Reachable v w}.Countable :=
  IntDistGraph.component_countable hA4 v

/-- **Theorem 1.2 (`χ(Γ(A)) ≤ ℵ₀`).** `Γ(A)` admits a proper colouring with colours in `ℕ`. -/
theorem chromatic_le_aleph0 (hA4 : NoFourConcyclic A) :
    Nonempty ((IntDistGraph A).Coloring ℕ) :=
  IntDistGraph.colorable_aleph0 hA4

/-- **Theorem 1.3 (No infinite clique).** No infinite subset of `A` has all pairs at integer
distance. -/
theorem no_infinite_integral_clique (hA3 : NoThreeCollinear A) :
    ¬ ∃ B : Set Plane, B ⊆ A ∧ B.Infinite ∧
        ∀ P ∈ B, ∀ Q ∈ B, P ≠ Q → IsIntDist P Q :=
  no_infinite_clique hA3

/-- **Theorem 1.3 (graph form).** Every clique of `Γ(A)` is finite. -/
theorem every_clique_finite (hA3 : NoThreeCollinear A)
    (s : Set A) (hs : (IntDistGraph A).IsClique s) : s.Finite :=
  isClique_finite hA3 s hs

/-- **Theorem 1.4 (Finite-block criterion).** -/
theorem finite_block_criterion :
    (∃ A : Set Plane, A.Infinite ∧ NoThreeCollinear A ∧ NoFourConcyclic A ∧
        ∀ n : ℕ, ¬ (IntDistGraph A).Colorable n)
    ↔
    (∀ k : ℕ, ∃ B : Finset Plane, NoThreeCollinear (↑B : Set Plane) ∧
        NoFourConcyclic (↑B : Set Plane) ∧
        (k : ℕ∞) ≤ (IntDistGraph (↑B : Set Plane)).chromaticNumber) :=
  IntDistGraph.finite_block_criterion

/-- **Example 5.1.** There is a finite general-position set whose integer-distance graph contains
a clique of size `5`. -/
theorem exists_finite_general_position_K5 :
    ∃ F : Finset Plane, NoThreeCollinear (↑F : Set Plane) ∧ NoFourConcyclic (↑F : Set Plane) ∧
      F.card = 5 ∧ ∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → IsIntDist P Q :=
  IntDistK5.exists_general_position_int_K5

end IntDistGraphPaper
