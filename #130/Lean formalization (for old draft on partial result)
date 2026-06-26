import Mathlib

/-!
# Erdős Problem #130 — Clique and chromatic numbers of the integer-distance graph
# on planar point sets in general position

Formalization of the results of the paper *"Clique and chromatic numbers of the
integer-distance graph on planar point sets in general position"* (folder `#130`).

Let `A ⊆ ℝ²` be a set in *general position* (no 3 points collinear, no 4 concyclic)
and let `G_A` be the graph joining pairs of points of `A` at integer Euclidean
distance.  The paper proves:

* **Theorem 2.1** (Anning–Erdős): an infinite set with pairwise integral distances is
  collinear.  Stated here as `AnningErdosStatement`.
* **Corollary 2.2**: every clique of `G_A` is finite — proved here from
  `AnningErdosStatement` (`cliques_finite`).
* **Proposition 3.1** (kite, n = 4), **Theorem 3.2** (six-point certificate) and
  **Remark 3.4** (five-point certificate): explicit integral point sets in general
  position, *fully verified here in exact integer arithmetic* via `decide`
  (`four_point_certificate`, `six_point_certificate`, `five_point_certificate`).
  Consequently `ω, χ ≥ 6` (`six_point_isNClique`, `exists_genPos_not_colorable_five`).
* **Theorem 4.1**: `χ(G_A) ≤ ℵ₀` for every admissible `A`, of any cardinality —
  *fully proved here* (`chromatic_le_aleph0`), via countability of neighbourhoods
  (`neighborSet_countable`, using "no 4 concyclic" on circles centred at a vertex)
  and countability of connected components of locally countable graphs
  (`coloring_of_locally_countable`).
* **Theorem 5.1** (transfer principle): stated as `TransferPrinciple`; its proof in
  the paper rests on De Bruijn–Erdős compactness and a generic placement lemma,
  which are not formalized here.
* **The open Erdős problem** (Section 6): stated as `ErdosOpenProblem`; the paper's
  results pin it down between the proven `IntegralGenPosConfigs n` for all `n ≤ 6`
  (`integralGenPosConfigs_of_le_six`) and the open general case.

The exact-arithmetic verification scheme follows Appendix A of the paper: points are
stored as integer pairs `(X, m)` representing `(X, m·√k)`; integrality of distances is
a perfect-square test, non-collinearity an integer `2×2` cross product, and
non-concyclicity an integer `4×4` determinant with `√k` factored out of one column.
-/

namespace ErdosProblem130

open EuclideanGeometry Real

noncomputable section

/-- The Euclidean plane `ℝ²`. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-! ## Definition 1.1: admissible sets and the integer-distance graph -/

/-- Two points lie at a positive integer Euclidean distance. -/
def IntegerDist (p q : Plane) : Prop :=
  ∃ n : ℕ, 0 < n ∧ dist p q = n

/-- A set `A ⊆ ℝ²` is *admissible* (in *general position*) if no three of its points
are collinear and no four of its points are concyclic.  In the plane, `Cospherical`
is precisely concyclicity. -/
def InGenPos (A : Set Plane) : Prop :=
  (∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, p ≠ q → p ≠ r → q ≠ r →
    ¬ Collinear ℝ ({p, q, r} : Set Plane)) ∧
  (∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, ∀ s ∈ A,
    p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
    ¬ Cospherical ({p, q, r, s} : Set Plane))

/-- General position is inherited by subsets. -/
lemma InGenPos.mono {A B : Set Plane} (hAB : A ⊆ B) (hB : InGenPos B) : InGenPos A :=
  ⟨fun p hp q hq r hr => hB.1 p (hAB hp) q (hAB hq) r (hAB hr),
   fun p hp q hq r hr s hs => hB.2 p (hAB hp) q (hAB hq) r (hAB hr) s (hAB hs)⟩

-- the linters below are disabled because one branch of each `first` in `distGraph`
-- is intentionally dead code, kept for compatibility across Mathlib versions
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The *integer-distance graph* `G_A` on an admissible set `A`: vertices are the
points of `A`, edges join pairs at positive integer distance. -/
def distGraph (A : Set Plane) : SimpleGraph A where
  Adj u v := IntegerDist u.1 v.1
  symm := by
    have h : ∀ u v : A, IntegerDist u.1 v.1 → IntegerDist v.1 u.1 := by
      rintro u v ⟨n, hn, hd⟩
      exact ⟨n, hn, by rwa [dist_comm]⟩
    -- `symm` is `Symmetric Adj` in some Mathlib versions, `Std.Symm Adj` in others
    first
    | exact h
    | exact ⟨h⟩
  loopless := by
    have h : ∀ u : A, ¬ IntegerDist u.1 u.1 := by
      rintro u ⟨n, hn, hd⟩
      rw [dist_self] at hd
      exact hn.ne' (by exact_mod_cast hd.symm)
    -- `loopless` is `Irreflexive Adj` in some Mathlib versions, `Std.Irrefl Adj` in others
    first
    | exact ⟨h⟩
    | exact h

/-! ## Exact-arithmetic infrastructure (Appendix A)

Points are represented by integer data `(X, m)` standing for `(X, m·√k)`.
All geometric degeneracy tests reduce to integer arithmetic. -/

/-- The point `(X, m·√k) ∈ ℝ²`. -/
def pt (k : ℕ) (X m : ℤ) : Plane := !₂[(X : ℝ), (m : ℝ) * √(k : ℝ)]

@[simp] lemma pt_apply_zero (k : ℕ) (X m : ℤ) : pt k X m 0 = (X : ℝ) := rfl

@[simp] lemma pt_apply_one (k : ℕ) (X m : ℤ) : pt k X m 1 = (m : ℝ) * √(k : ℝ) := rfl

/-- The planar cross product `(q - p) × (r - p)`; it vanishes iff `p, q, r` are
collinear (only this direction is needed). -/
def cross (p q r : Plane) : ℝ :=
  (q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0)

/-- The `3×3` determinant `det [[x₁,y₁,1],[x₂,y₂,1],[x₃,y₃,1]]`. -/
def tri (x₁ y₁ x₂ y₂ x₃ y₃ : ℝ) : ℝ :=
  x₁ * y₂ - x₂ * y₁ - x₁ * y₃ + x₃ * y₁ + x₂ * y₃ - x₃ * y₂

/-- The `4×4` concyclicity determinant `det [(xᵢ²+yᵢ², xᵢ, yᵢ, 1)]ᵢ`, written via
cofactor expansion along the first column. -/
def circleDet (x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : ℝ) : ℝ :=
  (x₁ ^ 2 + y₁ ^ 2) * tri x₂ y₂ x₃ y₃ x₄ y₄
    - (x₂ ^ 2 + y₂ ^ 2) * tri x₁ y₁ x₃ y₃ x₄ y₄
    + (x₃ ^ 2 + y₃ ^ 2) * tri x₁ y₁ x₂ y₂ x₄ y₄
    - (x₄ ^ 2 + y₄ ^ 2) * tri x₁ y₁ x₂ y₂ x₃ y₃

/-- Integer version of `tri`. -/
def triZ (X₁ m₁ X₂ m₂ X₃ m₃ : ℤ) : ℤ :=
  X₁ * m₂ - X₂ * m₁ - X₁ * m₃ + X₃ * m₁ + X₂ * m₃ - X₃ * m₂

/-- Integer concyclicity determinant for points `(Xᵢ, mᵢ·√k)`: the first column is the
integer `Xᵢ² + k·mᵢ²` and `√k` is factored out of the third column. -/
def circleDetZ (k X₁ m₁ X₂ m₂ X₃ m₃ X₄ m₄ : ℤ) : ℤ :=
  (X₁ ^ 2 + k * m₁ ^ 2) * triZ X₂ m₂ X₃ m₃ X₄ m₄
    - (X₂ ^ 2 + k * m₂ ^ 2) * triZ X₁ m₁ X₃ m₃ X₄ m₄
    + (X₃ ^ 2 + k * m₃ ^ 2) * triZ X₁ m₁ X₂ m₂ X₄ m₄
    - (X₄ ^ 2 + k * m₄ ^ 2) * triZ X₁ m₁ X₂ m₂ X₃ m₃

/-- Squared distance between data points, exactly: `(ΔX)² + k·(Δm)²`. -/
lemma dist_sq_pt (k : ℕ) (X₁ m₁ X₂ m₂ : ℤ) :
    dist (pt k X₁ m₁) (pt k X₂ m₂) ^ 2
      = (((X₁ - X₂) ^ 2 + (k : ℤ) * (m₁ - m₂) ^ 2 : ℤ) : ℝ) := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [pt_apply_zero, pt_apply_one, Real.dist_eq, sq_abs]
  have hκ : √(k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt (Nat.cast_nonneg k)
  push_cast
  linear_combination ((m₁ : ℝ) - (m₂ : ℝ)) ^ 2 * hκ

/-- Integrality of a distance from a perfect-square certificate. -/
lemma dist_pt_eq (k : ℕ) (X₁ m₁ X₂ m₂ : ℤ) (n : ℕ)
    (h : (X₁ - X₂) ^ 2 + (k : ℤ) * (m₁ - m₂) ^ 2 = (n : ℤ) ^ 2) :
    dist (pt k X₁ m₁) (pt k X₂ m₂) = n := by
  have hsq : dist (pt k X₁ m₁) (pt k X₂ m₂) ^ 2 = ((n : ℝ)) ^ 2 := by
    rw [dist_sq_pt, h]; push_cast; ring
  calc dist (pt k X₁ m₁) (pt k X₂ m₂)
      = √(dist (pt k X₁ m₁) (pt k X₂ m₂) ^ 2) := (Real.sqrt_sq dist_nonneg).symm
    _ = √((n : ℝ) ^ 2) := by rw [hsq]
    _ = n := Real.sqrt_sq (Nat.cast_nonneg n)

/-- A collinear triple has vanishing cross product. -/
lemma cross_eq_zero_of_collinear {p q r : Plane}
    (h : Collinear ℝ ({p, q, r} : Set Plane)) : cross p q r = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (Set.mem_insert p {q, r})).mp h
  obtain ⟨a, ha⟩ := hv q (by simp)
  obtain ⟨b, hb⟩ := hv r (by simp)
  subst ha hb
  simp only [cross, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- Non-collinearity from a nonzero integer cross product (`√k` cancels). -/
lemma not_collinear_pt {k : ℕ} (hk : 0 < k) {X₁ m₁ X₂ m₂ X₃ m₃ : ℤ}
    (h : (X₂ - X₁) * (m₃ - m₁) - (m₂ - m₁) * (X₃ - X₁) ≠ 0) :
    ¬ Collinear ℝ ({pt k X₁ m₁, pt k X₂ m₂, pt k X₃ m₃} : Set Plane) := by
  intro hc
  have h0 := cross_eq_zero_of_collinear hc
  have hκ : (0 : ℝ) < √(k : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  have hexp : cross (pt k X₁ m₁) (pt k X₂ m₂) (pt k X₃ m₃)
      = √(k : ℝ) * (((X₂ - X₁) * (m₃ - m₁) - (m₂ - m₁) * (X₃ - X₁) : ℤ) : ℝ) := by
    simp only [cross, pt_apply_zero, pt_apply_one]
    push_cast
    ring
  rw [hexp] at h0
  rcases mul_eq_zero.mp h0 with h' | h'
  · exact hκ.ne' h'
  · exact h (by exact_mod_cast h')

/-- A point on a circle, in coordinates. -/
lemma onCircle_coords {p c : Plane} {ρ : ℝ} (h : dist p c = ρ) :
    (p 0 - c 0) ^ 2 + (p 1 - c 1) ^ 2 = ρ ^ 2 := by
  have hd := EuclideanSpace.dist_sq_eq p c
  rw [h, Fin.sum_univ_two] at hd
  simpa [Real.dist_eq, sq_abs] using hd.symm

/-- Four points on a common circle have vanishing concyclicity determinant: the first
column of the determinant is a linear combination of the other three. -/
lemma circleDet_eq_zero {x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ a b ρ : ℝ}
    (h₁ : (x₁ - a) ^ 2 + (y₁ - b) ^ 2 = ρ ^ 2)
    (h₂ : (x₂ - a) ^ 2 + (y₂ - b) ^ 2 = ρ ^ 2)
    (h₃ : (x₃ - a) ^ 2 + (y₃ - b) ^ 2 = ρ ^ 2)
    (h₄ : (x₄ - a) ^ 2 + (y₄ - b) ^ 2 = ρ ^ 2) :
    circleDet x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ = 0 := by
  simp only [circleDet, tri]
  linear_combination
    (x₂ * y₃ - x₃ * y₂ - x₂ * y₄ + x₄ * y₂ + x₃ * y₄ - x₄ * y₃) * h₁
      - (x₁ * y₃ - x₃ * y₁ - x₁ * y₄ + x₄ * y₁ + x₃ * y₄ - x₄ * y₃) * h₂
      + (x₁ * y₂ - x₂ * y₁ - x₁ * y₄ + x₄ * y₁ + x₂ * y₄ - x₄ * y₂) * h₃
      - (x₁ * y₂ - x₂ * y₁ - x₁ * y₃ + x₃ * y₁ + x₂ * y₃ - x₃ * y₂) * h₄

/-- Factoring `√k` out of the concyclicity determinant of data points
(legitimate, since scaling a column by a nonzero scalar preserves vanishing). -/
lemma circleDet_factor (κ X₁ m₁ X₂ m₂ X₃ m₃ X₄ m₄ : ℝ) :
    circleDet X₁ (m₁ * κ) X₂ (m₂ * κ) X₃ (m₃ * κ) X₄ (m₄ * κ)
      = κ * ((X₁ ^ 2 + κ ^ 2 * m₁ ^ 2) * tri X₂ m₂ X₃ m₃ X₄ m₄
          - (X₂ ^ 2 + κ ^ 2 * m₂ ^ 2) * tri X₁ m₁ X₃ m₃ X₄ m₄
          + (X₃ ^ 2 + κ ^ 2 * m₃ ^ 2) * tri X₁ m₁ X₂ m₂ X₄ m₄
          - (X₄ ^ 2 + κ ^ 2 * m₄ ^ 2) * tri X₁ m₁ X₂ m₂ X₃ m₃) := by
  simp only [circleDet, tri]
  ring

/-- Non-concyclicity from a nonzero integer determinant. -/
lemma not_cospherical_pt {k : ℕ} (hk : 0 < k) {X₁ m₁ X₂ m₂ X₃ m₃ X₄ m₄ : ℤ}
    (h : circleDetZ (k : ℤ) X₁ m₁ X₂ m₂ X₃ m₃ X₄ m₄ ≠ 0) :
    ¬ Cospherical ({pt k X₁ m₁, pt k X₂ m₂, pt k X₃ m₃, pt k X₄ m₄} : Set Plane) := by
  rintro ⟨c, ρ, hc⟩
  have h₁ := onCircle_coords (hc (pt k X₁ m₁) (by simp))
  have h₂ := onCircle_coords (hc (pt k X₂ m₂) (by simp))
  have h₃ := onCircle_coords (hc (pt k X₃ m₃) (by simp))
  have h₄ := onCircle_coords (hc (pt k X₄ m₄) (by simp))
  simp only [pt_apply_zero, pt_apply_one] at h₁ h₂ h₃ h₄
  have h0 := circleDet_eq_zero h₁ h₂ h₃ h₄
  rw [circleDet_factor, Real.sq_sqrt (Nat.cast_nonneg k)] at h0
  have hκ : (0 : ℝ) < √(k : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  rcases mul_eq_zero.mp h0 with h' | h'
  · exact hκ.ne' h'
  · apply h
    have hcast : (((circleDetZ (k : ℤ) X₁ m₁ X₂ m₂ X₃ m₃ X₄ m₄ : ℤ)) : ℝ)
        = ((X₁ : ℝ) ^ 2 + (k : ℝ) * (m₁ : ℝ) ^ 2) * tri X₂ m₂ X₃ m₃ X₄ m₄
          - ((X₂ : ℝ) ^ 2 + (k : ℝ) * (m₂ : ℝ) ^ 2) * tri X₁ m₁ X₃ m₃ X₄ m₄
          + ((X₃ : ℝ) ^ 2 + (k : ℝ) * (m₃ : ℝ) ^ 2) * tri X₁ m₁ X₂ m₂ X₄ m₄
          - ((X₄ : ℝ) ^ 2 + (k : ℝ) * (m₄ : ℝ) ^ 2) * tri X₁ m₁ X₂ m₂ X₃ m₃ := by
      simp only [circleDetZ, triZ, tri]
      push_cast
      ring
    exact_mod_cast hcast.trans h'

/-- General position for the range of a family, from indexed degeneracy tests. -/
lemma inGenPos_range {n : ℕ} (P : Fin n → Plane)
    (h3 : ∀ i j l : Fin n, i ≠ j → i ≠ l → j ≠ l →
      ¬ Collinear ℝ ({P i, P j, P l} : Set Plane))
    (h4 : ∀ i j l m : Fin n, i ≠ j → i ≠ l → i ≠ m → j ≠ l → j ≠ m → l ≠ m →
      ¬ Cospherical ({P i, P j, P l, P m} : Set Plane)) :
    InGenPos (Set.range P) := by
  constructor
  · rintro p ⟨i, rfl⟩ q ⟨j, rfl⟩ r ⟨l, rfl⟩ hpq hpr hqr
    exact h3 i j l (fun h => hpq (congrArg P h)) (fun h => hpr (congrArg P h))
      (fun h => hqr (congrArg P h))
  · rintro p ⟨i, rfl⟩ q ⟨j, rfl⟩ r ⟨l, rfl⟩ s ⟨m, rfl⟩ h1 h2 h3' h4' h5 h6
    exact h4 i j l m (fun h => h1 (congrArg P h)) (fun h => h2 (congrArg P h))
      (fun h => h3' (congrArg P h)) (fun h => h4' (congrArg P h))
      (fun h => h5 (congrArg P h)) (fun h => h6 (congrArg P h))

/-- Master verification theorem: integer data `(X, M)` together with exact
integer certificates (perfect squares, nonzero cross products, nonzero
determinants) yield an integral point set in general position. -/
theorem config_of_data {n : ℕ} (k : ℕ) (hk : 0 < k)
    (X M : Fin n → ℤ) (D : Fin n → Fin n → ℕ)
    (hdist : ∀ i j, i ≠ j →
      0 < D i j ∧ (X i - X j) ^ 2 + (k : ℤ) * (M i - M j) ^ 2 = (D i j : ℤ) ^ 2)
    (hcross : ∀ i j l, i ≠ j → i ≠ l → j ≠ l →
      (X j - X i) * (M l - M i) - (M j - M i) * (X l - X i) ≠ 0)
    (hdet : ∀ i j l m, i ≠ j → i ≠ l → i ≠ m → j ≠ l → j ≠ m → l ≠ m →
      circleDetZ (k : ℤ) (X i) (M i) (X j) (M j) (X l) (M l) (X m) (M m) ≠ 0) :
    ∃ P : Fin n → Plane, Function.Injective P ∧ InGenPos (Set.range P) ∧
      ∀ i j, i ≠ j → IntegerDist (P i) (P j) := by
  refine ⟨fun i => pt k (X i) (M i), ?_, ?_, ?_⟩
  · -- injectivity: distinct indices are at positive distance
    intro i j hij
    by_contra hne
    obtain ⟨hpos, heq⟩ := hdist i j hne
    have hd : dist (pt k (X i) (M i)) (pt k (X j) (M j)) = (D i j : ℝ) :=
      dist_pt_eq k _ _ _ _ _ heq
    rw [show pt k (X i) (M i) = pt k (X j) (M j) from hij, dist_self] at hd
    exact hpos.ne (by exact_mod_cast hd)
  · refine inGenPos_range _ (fun i j l hij hil hjl => ?_)
      (fun i j l m h1 h2 h3 h4 h5 h6 => ?_)
    · exact not_collinear_pt hk (hcross i j l hij hil hjl)
    · exact not_cospherical_pt hk (hdet i j l m h1 h2 h3 h4 h5 h6)
  · intro i j hij
    obtain ⟨hpos, heq⟩ := hdist i j hij
    exact ⟨D i j, hpos, dist_pt_eq k _ _ _ _ _ heq⟩

/-! ## Section 3: explicit certificates

The integer data below is exactly that of the paper; every certificate is checked by
`decide`, i.e. by kernel-level exact integer arithmetic — no floating point anywhere. -/

/-- A configuration of `n` points in general position with all pairwise distances
positive integers (an *integral point set in general position*). -/
def IntegralGenPosConfigs (n : ℕ) : Prop :=
  ∃ P : Fin n → Plane, Function.Injective P ∧ InGenPos (Set.range P) ∧
    ∀ i j, i ≠ j → IntegerDist (P i) (P j)

section SixPoint

/-- `X`-coordinates of the six-point certificate (Theorem 3.2). -/
def X6 : Fin 6 → ℤ := ![0, 2312, 535, 621, 1691, 1777]

/-- `√2002`-multipliers of the six-point certificate. -/
def M6 : Fin 6 → ℤ := ![0, 0, 30, -30, 30, -30]

/-- The distance matrix of Theorem 3.2. -/
def D6 : Fin 6 → Fin 6 → ℕ :=
  ![![0, 2312, 1445, 1479, 2159, 2227],
    ![2312, 0, 2227, 2159, 1479, 1445],
    ![1445, 2227, 0, 2686, 1156, 2958],
    ![1479, 2159, 2686, 0, 2890, 1156],
    ![2159, 1479, 1156, 2890, 0, 2686],
    ![2227, 1445, 2958, 1156, 2686, 0]]

/-- All 15 squared distances are the claimed perfect squares (exact arithmetic). -/
lemma six_dist_fact : ∀ i j : Fin 6, i ≠ j →
    0 < D6 i j ∧ (X6 i - X6 j) ^ 2 + 2002 * (M6 i - M6 j) ^ 2 = (D6 i j : ℤ) ^ 2 := by
  decide

/-- All 20 triples are non-collinear: integer cross products are nonzero. -/
lemma six_cross_fact : ∀ i j l : Fin 6, i ≠ j → i ≠ l → j ≠ l →
    (X6 j - X6 i) * (M6 l - M6 i) - (M6 j - M6 i) * (X6 l - X6 i) ≠ 0 := by
  decide

/-- All 15 quadruples are non-concyclic: integer `4×4` determinants are nonzero. -/
lemma six_det_fact : ∀ i j l m : Fin 6, i ≠ j → i ≠ l → i ≠ m → j ≠ l → j ≠ m → l ≠ m →
    circleDetZ 2002 (X6 i) (M6 i) (X6 j) (M6 j) (X6 l) (M6 l) (X6 m) (M6 m) ≠ 0 := by
  decide

/-- **Theorem 3.2.** There exist six points in general position with all fifteen
pairwise distances positive integers; the induced integer-distance graph is `K₆`.
Explicitly, with `κ = √2002`: `(0,0)`, `(2312,0)`, `(535,30κ)`, `(621,−30κ)`,
`(1691,30κ)`, `(1777,−30κ)`. -/
theorem six_point_certificate : IntegralGenPosConfigs 6 := by
  refine config_of_data 2002 (by norm_num) X6 M6 D6 ?_ six_cross_fact ?_
  · intro i j hij
    exact_mod_cast six_dist_fact i j hij
  · intro i j l m h1 h2 h3 h4 h5 h6
    exact_mod_cast six_det_fact i j l m h1 h2 h3 h4 h5 h6

end SixPoint

section Kite

/-- The kite of Proposition 3.1 (plain integer coordinates, `k = 1`). -/
def X4 : Fin 4 → ℤ := ![0, 8, 4, 4]

def M4 : Fin 4 → ℤ := ![0, 0, 3, -3]

def D4 : Fin 4 → Fin 4 → ℕ :=
  ![![0, 8, 5, 5], ![8, 0, 5, 5], ![5, 5, 0, 6], ![5, 5, 6, 0]]

/-- **Proposition 3.1** (warm-up, `n = 4`).  The kite `{(0,0), (8,0), (4,3), (4,−3)}`
is admissible with the six pairwise distances `8, 5, 5, 5, 5, 6`. -/
theorem four_point_certificate : IntegralGenPosConfigs 4 := by
  refine config_of_data 1 (by norm_num) X4 M4 D4 ?_ ?_ ?_
  · intro i j hij
    exact_mod_cast
      (by decide : ∀ i j : Fin 4, i ≠ j →
        0 < D4 i j ∧ (X4 i - X4 j) ^ 2 + 1 * (M4 i - M4 j) ^ 2 = (D4 i j : ℤ) ^ 2) i j hij
  · exact fun i j l h1 h2 h3 =>
      (by decide : ∀ i j l : Fin 4, i ≠ j → i ≠ l → j ≠ l →
        (X4 j - X4 i) * (M4 l - M4 i) - (M4 j - M4 i) * (X4 l - X4 i) ≠ 0) i j l h1 h2 h3
  · intro i j l m h1 h2 h3 h4 h5 h6
    exact_mod_cast
      (by decide : ∀ i j l m : Fin 4, i ≠ j → i ≠ l → i ≠ m → j ≠ l → j ≠ m → l ≠ m →
        circleDetZ 1 (X4 i) (M4 i) (X4 j) (M4 j) (X4 l) (M4 l) (X4 m) (M4 m) ≠ 0)
      i j l m h1 h2 h3 h4 h5 h6

end Kite

section FivePoint

/-- The five-point certificate of Remark 3.4 (plain integer coordinates). -/
def X5 : Fin 5 → ℤ := ![0, 4225, 3713, 2079, 2975]

def M5 : Fin 5 → ℤ := ![0, 0, 2016, 528, -3000]

def D5 : Fin 5 → Fin 5 → ℕ :=
  ![![0, 4225, 4225, 2145, 4225],
    ![4225, 0, 2080, 2210, 3250],
    ![4225, 2080, 0, 2210, 5070],
    ![2145, 2210, 2210, 0, 3640],
    ![4225, 3250, 5070, 3640, 0]]

/-- **Remark 3.4.**  The five points `(0,0)`, `(4225,0)`, `(3713,2016)`,
`(2079,528)`, `(2975,−3000)` form an integral point set in general position. -/
theorem five_point_certificate : IntegralGenPosConfigs 5 := by
  refine config_of_data 1 (by norm_num) X5 M5 D5 ?_ ?_ ?_
  · intro i j hij
    exact_mod_cast
      (by decide : ∀ i j : Fin 5, i ≠ j →
        0 < D5 i j ∧ (X5 i - X5 j) ^ 2 + 1 * (M5 i - M5 j) ^ 2 = (D5 i j : ℤ) ^ 2) i j hij
  · exact fun i j l h1 h2 h3 =>
      (by decide : ∀ i j l : Fin 5, i ≠ j → i ≠ l → j ≠ l →
        (X5 j - X5 i) * (M5 l - M5 i) - (M5 j - M5 i) * (X5 l - X5 i) ≠ 0) i j l h1 h2 h3
  · intro i j l m h1 h2 h3 h4 h5 h6
    exact_mod_cast
      (by decide : ∀ i j l m : Fin 5, i ≠ j → i ≠ l → i ≠ m → j ≠ l → j ≠ m → l ≠ m →
        circleDetZ 1 (X5 i) (M5 i) (X5 j) (M5 j) (X5 l) (M5 l) (X5 m) (M5 m) ≠ 0)
      i j l m h1 h2 h3 h4 h5 h6

end FivePoint

/-- Integral point sets in general position exist at every size up to six. -/
theorem integralGenPosConfigs_of_le_six : ∀ n ≤ 6, IntegralGenPosConfigs n := by
  intro n hn
  obtain ⟨P, hinj, hgen, hdist⟩ := six_point_certificate
  refine ⟨P ∘ Fin.castLE hn, hinj.comp (Fin.strictMono_castLE hn).injective, ?_, ?_⟩
  · exact InGenPos.mono (Set.range_comp_subset_range _ _) hgen
  · intro i j hij
    exact hdist _ _ fun h => hij ((Fin.strictMono_castLE hn).injective h)

/-! ## Consequences: `ω ≥ 6` and `χ ≥ 6` -/

/-- A clique of `Fin (n+1)` points pairwise at integer distance defeats every proper
`n`-colouring (pigeonhole). -/
theorem not_colorable_of_clique {n : ℕ} {A : Set Plane} (P : Fin (n + 1) → Plane)
    (hP : ∀ i, P i ∈ A) (hclique : ∀ i j, i ≠ j → IntegerDist (P i) (P j)) :
    ¬ (distGraph A).Colorable n := by
  rintro ⟨c⟩
  have hcard : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by
    simp [Fintype.card_fin]
  obtain ⟨i, j, hne, hc⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (n + 1) => c ⟨P i, hP i⟩) hcard
  have hadj : (distGraph A).Adj ⟨P i, hP i⟩ ⟨P j, hP j⟩ := hclique i j hne
  exact c.valid hadj hc

/-- The six-point certificate is a `6`-clique of its own integer-distance graph. -/
theorem six_point_isNClique :
    ∃ (A : Set Plane) (_ : InGenPos A) (s : Finset A),
      (distGraph A).IsNClique 6 s := by
  obtain ⟨P, hinj, hgen, hdist⟩ := six_point_certificate
  refine ⟨Set.range P, hgen,
    Finset.univ.image fun i => (⟨P i, Set.mem_range_self i⟩ : Set.range P), ?_, ?_⟩
  · -- pairwise adjacency
    rintro u hu v hv hne
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ] at hu hv
    obtain ⟨⟨i, -, rfl⟩, ⟨j, -, rfl⟩⟩ := And.intro hu hv
    exact hdist i j fun h => hne (by simp [h])
  · -- cardinality 6
    rw [Finset.card_image_of_injective _ fun i j h => hinj (congrArg Subtype.val h)]
    simp

/-- `χ ≥ 6`: an admissible set whose integer-distance graph is not `5`-colourable
(Theorem 3.2 together with Lemma 3.5 of the paper gives infinite such sets). -/
theorem exists_genPos_not_colorable_five :
    ∃ A : Set Plane, InGenPos A ∧ ¬ (distGraph A).Colorable 5 := by
  obtain ⟨P, hinj, hgen, hdist⟩ := six_point_certificate
  exact ⟨Set.range P, hgen,
    not_colorable_of_clique P (fun i => Set.mem_range_self i) hdist⟩

/-! ## Section 2: every clique is finite (Anning–Erdős)

The quantitative Anning–Erdős theorem (Theorem 2.1 of the paper) is *stated* here;
its corollary — finiteness of all cliques of `G_A` — is *proved* from it. -/

/-- **Theorem 2.1** (Anning–Erdős, statement).  An infinite planar set with all
pairwise distances positive integers lies on a line.  (The paper gives a complete
quantitative proof via resultants; that proof is not formalized here.) -/
def AnningErdosStatement : Prop :=
  ∀ S : Set Plane, (∀ p ∈ S, ∀ q ∈ S, p ≠ q → IntegerDist p q) →
    S.Infinite → Collinear ℝ S

/-- Removing one point keeps an infinite set infinite.  (Version-stable form of
`Set.Infinite.diff`/`Set.Infinite.sdiff`.) -/
lemma infinite_diff_singleton {α : Type*} {s : Set α} (hs : s.Infinite) (a : α) :
    (s \ {a}).Infinite := by
  intro h
  refine hs ((h.union (Set.finite_singleton a)).subset fun x hx => ?_)
  by_cases hxa : x = a
  · exact Or.inr (hxa ▸ rfl)
  · exact Or.inl ⟨hx, hxa⟩

/-- An infinite set contains three pairwise distinct elements. -/
lemma exists_three_of_infinite {α : Type*} {s : Set α} (hs : s.Infinite) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨a, ha⟩ := hs.nonempty
  obtain ⟨b, hb⟩ := (infinite_diff_singleton hs a).nonempty
  obtain ⟨c, hc⟩ :=
    (infinite_diff_singleton (infinite_diff_singleton hs a) b).nonempty
  exact ⟨a, ha, b, hb.1, c, hc.1.1,
    fun h => hb.2 h.symm, fun h => hc.1.2 h.symm, fun h => hc.2 h.symm⟩

/-- An infinite set contains four pairwise distinct elements. -/
lemma exists_four_of_infinite {α : Type*} {s : Set α} (hs : s.Infinite) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ d ∈ s,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  obtain ⟨a, ha⟩ := hs.nonempty
  obtain ⟨b, hb⟩ := (infinite_diff_singleton hs a).nonempty
  obtain ⟨c, hc⟩ :=
    (infinite_diff_singleton (infinite_diff_singleton hs a) b).nonempty
  obtain ⟨d, hd⟩ :=
    (infinite_diff_singleton
      (infinite_diff_singleton (infinite_diff_singleton hs a) b) c).nonempty
  exact ⟨a, ha, b, hb.1, c, hc.1.1, d, hd.1.1.1,
    fun h => hb.2 h.symm, fun h => hc.1.2 h.symm, fun h => hd.1.1.2 h.symm,
    fun h => hc.2 h.symm, fun h => hd.1.2 h.symm, fun h => hd.2 h.symm⟩

/-- **Corollary 2.2.**  Assuming Anning–Erdős, every clique of the integer-distance
graph of an admissible set is finite: an infinite clique would be an infinite
integral-distance set, hence collinear — but admissible sets contain no three
collinear points. -/
theorem cliques_finite (hAE : AnningErdosStatement) {A : Set Plane}
    (hA : InGenPos A) {s : Set A} (hs : (distGraph A).IsClique s) : s.Finite := by
  by_contra hinf
  have hinf' : s.Infinite := hinf
  have hSinf : (Subtype.val '' s).Infinite :=
    hinf'.image (Set.injOn_of_injective Subtype.val_injective)
  have hint : ∀ p ∈ Subtype.val '' s, ∀ q ∈ Subtype.val '' s, p ≠ q → IntegerDist p q := by
    rintro p ⟨u, hu, rfl⟩ q ⟨v, hv, rfl⟩ hne
    exact hs hu hv fun h => hne (congrArg Subtype.val h)
  have hcol := hAE _ hint hSinf
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := exists_three_of_infinite hSinf
  have hsubA : Subtype.val '' s ⊆ A := by rintro x ⟨u, -, rfl⟩; exact u.2
  exact hA.1 p (hsubA hp) q (hsubA hq) r (hsubA hr) hpq hpr hqr
    (hcol.subset (by intro x hx; rcases hx with rfl | rfl | rfl <;> assumption))

/-! ## Section 4: the chromatic number is at most `ℵ₀` (Theorem 4.1)

Fully proved.  Step 1: each integer-radius circle centred at a vertex carries at most
three points of `A` ("no four concyclic" applied to circles centred at a vertex), so
neighbourhoods are countable.  Step 2: a graph with countable neighbourhoods has
countable connected components (breadth-first balls).  Step 3: colour each component
injectively by `ℕ`. -/

section LocallyCountable

variable {V : Type*}

/-- Breadth-first balls around a vertex. -/
def gball (G : SimpleGraph V) (w : V) : ℕ → Set V
  | 0 => {w}
  | n + 1 => ⋃ u ∈ gball G w n, insert u (G.neighborSet u)

lemma mem_gball_of_walk {G : SimpleGraph V} {w v : V} (p : G.Walk v w) :
    v ∈ gball G w p.length := by
  induction p with
  | nil => exact Set.mem_singleton _
  | cons h q ih =>
    simp only [SimpleGraph.Walk.length_cons, gball]
    exact Set.mem_biUnion ih (Set.mem_insert_iff.mpr (Or.inr h.symm))

lemma gball_countable {G : SimpleGraph V}
    (hloc : ∀ u, (G.neighborSet u).Countable) (w : V) :
    ∀ n, (gball G w n).Countable
  | 0 => Set.countable_singleton w
  | n + 1 => (gball_countable hloc w n).biUnion fun u _ => (hloc u).insert u

/-- The reachability class of a vertex in a locally countable graph is countable:
breadth-first levels are countable by induction, and the class is their union. -/
lemma reachableSet_countable {G : SimpleGraph V}
    (hloc : ∀ u, (G.neighborSet u).Countable) (w : V) :
    {v | G.Reachable w v}.Countable := by
  refine Set.Countable.mono ?_ (Set.countable_iUnion (gball_countable hloc w))
  rintro v hv
  obtain ⟨p⟩ := hv
  exact Set.mem_iUnion.mpr ⟨p.reverse.length, mem_gball_of_walk p.reverse⟩

/-- A graph all of whose neighbourhoods are countable admits a proper colouring with
countably many colours: components are countable, and each is coloured injectively. -/
theorem coloring_of_locally_countable {G : SimpleGraph V}
    (hloc : ∀ u, (G.neighborSet u).Countable) : Nonempty (G.Coloring ℕ) := by
  classical
  have hsupp : ∀ K : G.ConnectedComponent, K.supp.Countable := by
    refine SimpleGraph.ConnectedComponent.ind fun w => ?_
    refine Set.Countable.mono ?_ (reachableSet_countable hloc w)
    intro v hv
    exact (SimpleGraph.ConnectedComponent.exact hv).symm
  choose f hf using fun K => Set.countable_iff_exists_injective.mp (hsupp K)
  set g : G.ConnectedComponent → V → ℕ :=
    fun K v => if h : v ∈ K.supp then f K ⟨v, h⟩ else 0 with hg
  refine ⟨SimpleGraph.Coloring.mk (fun v => g (G.connectedComponentMk v) v) ?_⟩
  intro u v huv heq
  have hcomp : G.connectedComponentMk u = G.connectedComponentMk v :=
    SimpleGraph.ConnectedComponent.sound huv.reachable
  have hu : u ∈ (G.connectedComponentMk v).supp := hcomp
  have hv' : v ∈ (G.connectedComponentMk v).supp := rfl
  rw [hcomp] at heq
  simp only [hg, dif_pos hu, dif_pos hv'] at heq
  exact huv.ne (congrArg Subtype.val (hf _ heq))

end LocallyCountable

/-- Step 1 of Theorem 4.1: in an admissible set, every vertex of the integer-distance
graph has countable neighbourhood — the neighbours lie on the integer-radius circles
centred at the vertex, and "no four concyclic" allows at most three per circle. -/
theorem neighborSet_countable {A : Set Plane} (hA : InGenPos A) (v : A) :
    ((distGraph A).neighborSet v).Countable := by
  have hsub : (distGraph A).neighborSet v ⊆
      ⋃ n : ℕ, {u : A | dist (v : Plane) (u : Plane) = n} := by
    rintro u ⟨n, hn, hd⟩
    exact Set.mem_iUnion.mpr ⟨n, hd⟩
  refine Set.Countable.mono hsub
    (Set.countable_iUnion fun n => Set.Finite.countable ?_)
  by_contra hinf
  have hinf' : {u : A | dist (v : Plane) (u : Plane) = (n : ℝ)}.Infinite := hinf
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
    exists_four_of_infinite hinf'
  refine hA.2 a.1 a.2 b.1 b.2 c.1 c.2 d.1 d.2
    (Subtype.coe_ne_coe.mpr hab) (Subtype.coe_ne_coe.mpr hac)
    (Subtype.coe_ne_coe.mpr had) (Subtype.coe_ne_coe.mpr hbc)
    (Subtype.coe_ne_coe.mpr hbd) (Subtype.coe_ne_coe.mpr hcd)
    ⟨(v : Plane), n, ?_⟩
  rintro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · rw [dist_comm]; exact ha
  · rw [dist_comm]; exact hb
  · rw [dist_comm]; exact hc
  · rw [dist_comm]; exact hd

/-- **Theorem 4.1.**  For every admissible `A ⊆ ℝ²`, of any cardinality, the
integer-distance graph `G_A` has a proper colouring with countably many colours,
i.e. `χ(G_A) ≤ ℵ₀`. -/
theorem chromatic_le_aleph0 {A : Set Plane} (hA : InGenPos A) :
    Nonempty ((distGraph A).Coloring ℕ) :=
  coloring_of_locally_countable (neighborSet_countable hA)

/-! ## Sections 5–6: the transfer principle and the open problem

These are the statements whose proofs in the paper use De Bruijn–Erdős compactness
and the generic rigid-motion placement lemma; they are recorded here as `Prop`s. -/

/-- Finite admissible configurations of unbounded chromatic number exist
(condition (b) of Theorem 5.1). -/
def UnboundedFiniteChromatic : Prop :=
  ∀ n : ℕ, ∃ F : Set Plane, F.Finite ∧ InGenPos F ∧ ¬ (distGraph F).Colorable n

/-- Some admissible set has infinite chromatic number — by Theorem 4.1 this can only
mean `χ = ℵ₀` (condition (a) of Theorem 5.1). -/
def ExistsInfiniteChromatic : Prop :=
  ∃ A : Set Plane, InGenPos A ∧ ∀ n : ℕ, ¬ (distGraph A).Colorable n

/-- **Theorem 5.1** (transfer principle, statement).  Some admissible `A` has
`χ(G_A) = ℵ₀` iff finite admissible configurations of unbounded chromatic number
exist.  The forward direction is De Bruijn–Erdős compactness; the construction
direction rests on the generic placement Lemma 5.2 of the paper. -/
def TransferPrinciple : Prop := ExistsInfiniteChromatic ↔ UnboundedFiniteChromatic

/-- **Lemma 3.5** (extension to infinite sets, statement): every finite admissible set
extends to an infinite admissible set. -/
def ExtensionLemma : Prop :=
  ∀ F : Set Plane, F.Finite → InGenPos F →
    ∃ A : Set Plane, A.Infinite ∧ InGenPos A ∧ F ⊆ A

/-- **The open Erdős problem** (Section 6): do integral point sets in general position
exist at every finite size?  By the transfer principle this is what `χ = ℵ₀` reduces
to; the largest known such set has 7 points. -/
def ErdosOpenProblem : Prop := ∀ n : ℕ, IntegralGenPosConfigs n

/-- What is known unconditionally (Section 1): the open problem holds up to `n = 6`,
witnessed by the exactly verified certificate of Theorem 3.2. -/
theorem erdosOpenProblem_up_to_six : ∀ n ≤ 6, IntegralGenPosConfigs n :=
  integralGenPosConfigs_of_le_six

end

end ErdosProblem130
