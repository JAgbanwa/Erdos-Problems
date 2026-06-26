import Mathlib
/-!
# Integer-distance graphs in planar general position: basic definitions
This file sets up the basic objects from the paper
*Integer-distance graphs in planar general position: rigorous bounds and the
finite-block reduction* (J. Agbanwa).
We work in the Euclidean plane `Plane := EuclideanSpace ℝ (Fin 2)`.
* `IsIntDist P Q` : the Euclidean distance between `P` and `Q` is a (nonnegative) integer.
* `NoThreeCollinear A` : no three points of `A` are collinear.
* `NoFourConcyclic A`  : no four points of `A` lie on a common circle.
* `IntDistGraph A` : the integer-distance graph `Γ(A)`, with vertex set `A` and an edge
  between two distinct points exactly when their distance is a positive integer.
-/
open scoped BigOperators
open EuclideanGeometry
/-- The Euclidean plane. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)
/-- Two points are at integer distance when their Euclidean distance is a natural number. -/
def IsIntDist (P Q : Plane) : Prop := ∃ n : ℕ, dist P Q = n
/-- General-position assumption (i): no three points of `A` are collinear. -/
def NoThreeCollinear (A : Set Plane) : Prop :=
  ∀ s : Finset Plane, ↑s ⊆ A → s.card = 3 → ¬ Collinear ℝ (↑s : Set Plane)
/-- General-position assumption (ii): no four points of `A` are concyclic
(lie on one common Euclidean circle). Lines are not counted as circles, which is
automatic since `Cospherical` requires a genuine center and radius. -/
def NoFourConcyclic (A : Set Plane) : Prop :=
  ∀ s : Finset Plane, ↑s ⊆ A → s.card = 4 → ¬ Cospherical (↑s : Set Plane)
/-- The integer-distance graph `Γ(A)`: vertices are the points of `A`, and two
distinct points are adjacent exactly when their distance is a positive integer.
(Positivity is automatic: distinct points have positive distance.) -/
def IntDistGraph (A : Set Plane) : SimpleGraph A where
  Adj P Q := (P : Plane) ≠ Q ∧ IsIntDist (P : Plane) Q
  symm := by
    rintro P Q ⟨hne, n, hn⟩
    exact ⟨hne.symm, n, by rw [dist_comm]; exact hn⟩
  loopless := by
    constructor
    intro P
    rintro ⟨hne, _⟩
    exact hne rfl
