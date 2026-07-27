import Mathlib
/-!
# Universal monochromatic arithmetic progressions
A formalization of the paper's formulation and its decisive first conclusion: under the
paper's definition of admissibility there cannot be a best function.  We also formalize the
fixed-colour pigeonhole observation and the finite-perturbation argument on which that
conclusion rests.
We use `ℕ` for positive differences, explicitly requiring `0 < d`, and `ℤ` for the coloured
integers.  Length zero and one are allowed by the predicate `MonochromaticAP`; this makes
the definition meaningful for arbitrary `ℕ → ℕ`, while the paper's functions have positive
values.
-/
open Set
/-- The progression `a, a+d, ..., a+(length-1)d` has the fixed colour `c`. -/
def MonochromaticAP (χ : ℤ → Fin 2) (c : Fin 2) (a : ℤ) (d length : ℕ) : Prop :=
  ∀ i : ℕ, i < length → χ (a + (i : ℤ) * (d : ℤ)) = c
/-- The paper's definition of an admissible progression-length profile. -/
def Admissible (f : ℕ → ℕ) : Prop :=
  ∀ χ : ℤ → Fin 2, ∃ c : Fin 2, ∃ D : Set ℕ,
    D.Infinite ∧ ∀ d ∈ D, 0 < d ∧ ∃ a : ℤ, MonochromaticAP χ c a d (f d)
/-- A version in which the monochromatic colour is initially allowed to depend on `d`. -/
def WeaklyAdmissible (f : ℕ → ℕ) : Prop :=
  ∀ χ : ℤ → Fin 2, ∃ D : Set ℕ, D.Infinite ∧
    ∀ d ∈ D, 0 < d ∧ ∃ c : Fin 2, ∃ a : ℤ, MonochromaticAP χ c a d (f d)
/-- The colour may depend on the difference without changing admissibility: one of two
colours occurs infinitely often. -/
theorem admissible_iff_weaklyAdmissible (f : ℕ → ℕ) :
    Admissible f ↔ WeaklyAdmissible f := by
  constructor
  · -- Admissible → WeaklyAdmissible: just use the same color for all
    intro hf χ
    obtain ⟨c, D, hD_inf, hD⟩ := hf χ
    exact ⟨D, hD_inf, fun d hd => ⟨hD d hd |>.1, c, hD d hd |>.2⟩⟩
  · -- WeaklyAdmissible → Admissible: extract a color that occurs infinitely often
    intro hf χ
    obtain ⟨D, hD_inf, hD⟩ := hf χ
    -- Define the two subsets based on color
    let D0 := {d ∈ D | ∃ a : ℤ, MonochromaticAP χ 0 a d (f d)}
    let D1 := {d ∈ D | ∃ a : ℤ, MonochromaticAP χ 1 a d (f d)}
    -- One of them must be infinite
    have hD0_or_D1 : D0.Infinite ∨ D1.Infinite := by
      by_contra h
      push_neg at h
      have : D.Finite := by
        have hUD : D ⊆ D0 ∪ D1 := by
          intro d hd
          have := hD d hd
          have := this.2
          rcases this with ⟨c, a, hAP⟩
          fin_cases c <;> simp [D0, D1] <;> tauto
        exact Set.Finite.subset (h.1.union h.2) hUD
      exact hD_inf this
    rcases hD0_or_D1 with h0 | h1
    · refine ⟨0, D0, h0, fun d hd => ?_⟩
      exact ⟨hD d hd.1 |>.1, hd.2⟩
    · refine ⟨1, D1, h1, fun d hd => ?_⟩
      exact ⟨hD d hd.1 |>.1, hd.2⟩
/-- Proposition 1.2: changing an admissible function at finitely many arguments preserves
admissibility. -/
theorem admissible_of_finite_perturbation {f g : ℕ → ℕ} (hf : Admissible f)
    (hfg : {d : ℕ | f d ≠ g d}.Finite) : Admissible g := by
  intro χ
  obtain ⟨c, D, hD_inf, hD⟩ := hf χ
  use c, D \ {d : ℕ | f d ≠ g d}
  constructor
  · exact hD_inf.diff hfg
  · intro d hd
    have hdD : d ∈ D := hd.1
    have hneq : ¬(f d ≠ g d) := hd.2
    simp at hneq
    obtain ⟨a, ha⟩ := (hD d hdD).2
    exact ⟨(hD d hdD).1, ⟨a, by simpa [hneq] using ha⟩⟩
/-- Pointwise monotonicity in the useful direction: asking for shorter progressions preserves
admissibility. -/
theorem Admissible.mono {f g : ℕ → ℕ} (hf : Admissible f) (hgf : ∀ d, g d ≤ f d) :
    Admissible g := by
  intro χ
  obtain ⟨c, D, hD_inf, hD⟩ := hf χ
  refine ⟨c, D, hD_inf, ?_⟩
  intro d hd
  obtain ⟨hd_pos, a, ha⟩ := hD d hd
  exact ⟨hd_pos, a, fun i hi => ha i (hi.trans_le (hgf d))⟩
/-- The constant-one profile is admissible, so the class under discussion is nonempty. -/
theorem admissible_one : Admissible (fun _ => 1) := by
  intro χ
  -- χ : ℤ → Fin 2, find a color c that χ takes at some point
  -- Since ℤ is nonempty, χ takes some value
  have h : ∃ a : ℤ, True := ⟨0, trivial⟩
  -- Use the color of χ(0)
  use χ 0, {d : ℕ | 0 < d}
  constructor
  · exact Set.infinite_of_forall_exists_gt (fun n => ⟨n + 1, by simp⟩)
  · intro d hd
    exact ⟨hd, 0, fun i hi => by simp [Nat.lt_one_iff.mp hi]⟩
/-- Every admissible profile has an admissible strict pointwise improvement at any prescribed
argument.  This is the exact content behind Corollary 1.3. -/
theorem no_pointwise_maximal_step (f : ℕ → ℕ) (hf : Admissible f) (d₀ : ℕ) :
    ∃ g : ℕ → ℕ, Admissible g ∧ (∀ d, f d ≤ g d) ∧ f d₀ < g d₀ := by
  let g : ℕ → ℕ := fun d => if d = d₀ then f d + 1 else f d
  refine ⟨g, ?_, ?_, ?_⟩
  · apply admissible_of_finite_perturbation hf
    simp [g]
  · intro d; simp [g]; split <;> linarith
  · simp [g]
/-- Corollary 1.3, stated order-theoretically: there is no greatest admissible function for
the pointwise order. -/
theorem no_pointwise_best_function :
    ¬ ∃ f : ℕ → ℕ, Admissible f ∧ ∀ g : ℕ → ℕ, Admissible g → ∀ d, g d ≤ f d := by
  intro ⟨f, hf, hbest⟩
  obtain ⟨g, hg, hg_ge, hg_gt⟩ := no_pointwise_maximal_step f hf 0
  exact not_lt.mpr (hbest g hg 0) hg_gt
/-- Even restricting profiles to positive values does not repair pointwise maximality. -/
theorem no_positive_pointwise_best_function :
    ¬ ∃ f : ℕ → ℕ, (∀ d, 0 < f d) ∧ Admissible f ∧
      ∀ g : ℕ → ℕ, (∀ d, 0 < g d) → Admissible g → ∀ d, g d ≤ f d := by
  intro ⟨f, hf_pos, hf, hbest⟩
  obtain ⟨g, hg, hfg, hstrict⟩ := no_pointwise_maximal_step f hf 0
  have hg_pos : ∀ d, 0 < g d := fun d => (hf_pos d).trans_le (hfg d)
  exact (not_lt_of_ge (hbest g hg_pos hg 0)) hstrict
