/-
# Nibble — the residual, stated with no loss at all

`Nibble/DrossSpread.lean` reduces the spread Dross input `Nibble.DrossFractionalQuantSpread` to a
correction of the uniform triangle weighting `1/(|V|-2)`, and shows the two are equivalent *once the
constant is fixed* (`Nibble.drossUniformCorrection_iff_boundedDecomp`, which pins the target
constant at `2/(|V|-2)`).

This file removes the last slack in that reduction by carrying the scale of the uniform base as a
parameter: `Nibble.IsScaledDeficiencyCorrection G lam x` is a correction of the base weighting
`lam/(|V|-2)`, bounded by `lam/(|V|-2)` in absolute value.  The resulting global statement
`Nibble.DrossScaledCorrection` is **equivalent** to `Nibble.DrossFractionalQuantSpread`
(`Nibble.drossFractionalQuantSpread_iff_scaledCorrection`), so nothing whatsoever is lost in
passing to the correction form: the two are the same problem.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DrossSpread

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The scaled correction -/

/-- **A bounded correction of the scaled uniform weighting.**  A signed triangle weighting `x`,
bounded by `lam/(|V|-2)` in absolute value, whose coverage at every edge `e` is the deficiency
`1 - lam * codeg(e)/(|V|-2)` of the base weighting `lam/(|V|-2)`.

For `lam = 1` this is `Nibble.IsUniformDeficiencyCorrection`. -/
def IsScaledDeficiencyCorrection (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (x : Finset (EdgeV G) → ℝ) : Prop :=
  (∀ T ∈ triangleHypergraphSub G, |x T| ≤ lam / ((Fintype.card V : ℝ) - 2)) ∧
    ∀ e : EdgeV G, ∑ T ∈ trianglesThrough G e, x T
      = 1 - lam * ((commonNbrs G e).card : ℝ) / ((Fintype.card V : ℝ) - 2)

/-- At `lam = 1` the scaled correction is the uniform-deficiency correction. -/
theorem isScaledDeficiencyCorrection_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : Finset (EdgeV G) → ℝ) :
    IsScaledDeficiencyCorrection G 1 x ↔ IsUniformDeficiencyCorrection G x := by
  unfold IsScaledDeficiencyCorrection IsUniformDeficiencyCorrection
  simp only [one_mul, one_div]

/-- **The scaled correction form is exactly a decomposition with weights `≤ 2·lam/(|V|-2)`.** -/
theorem exists_scaledCorrection_iff_bounded_decomp (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : 3 ≤ Fintype.card V) (lam : ℝ) :
    (∃ x : Finset (EdgeV G) → ℝ, IsScaledDeficiencyCorrection G lam x) ↔
      ∃ w : Finset (EdgeV G) → ℝ, IsFracTriangleDecomp G w ∧
        ∀ T ∈ triangleHypergraphSub G, w T ≤ 2 * lam / ((Fintype.card V : ℝ) - 2) := by
  have h3 : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV
  have h2 : (0 : ℝ) < (Fintype.card V : ℝ) - 2 := by linarith
  set t : ℝ := lam / ((Fintype.card V : ℝ) - 2) with ht_def
  have hcard : ∀ e : EdgeV G,
      ((trianglesThrough G e).card : ℝ) = ((commonNbrs G e).card : ℝ) := by
    intro e
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (card_trianglesThrough_eq_commonNbrs G e)
  constructor
  · rintro ⟨x, hxb, hxs⟩
    refine ⟨fun T => t + x T, ⟨fun T hT => ?_, fun e => ?_⟩, fun T hT => ?_⟩
    · have := abs_le.mp (hxb T hT)
      have h := this.1
      rw [← ht_def] at h
      linarith
    · rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hxs e, hcard e, ht_def]
      field_simp
      ring
    · have := abs_le.mp (hxb T hT)
      have hle : x T ≤ t := by rw [ht_def]; exact this.2
      have : t + x T ≤ t + t := by linarith
      calc t + x T ≤ t + t := this
        _ = 2 * lam / ((Fintype.card V : ℝ) - 2) := by rw [ht_def]; ring
  · rintro ⟨w, ⟨hwnn, hwsum⟩, hwb⟩
    refine ⟨fun T => w T - t, fun T hT => ?_, fun e => ?_⟩
    · have h1 : 0 ≤ w T := hwnn T hT
      have h2' : w T ≤ 2 * t := by
        have hb := hwb T hT
        rw [ht_def]
        calc w T ≤ 2 * lam / ((Fintype.card V : ℝ) - 2) := hb
          _ = 2 * (lam / ((Fintype.card V : ℝ) - 2)) := by ring
      rw [abs_le, ← ht_def]
      constructor <;> linarith
    · rw [Finset.sum_sub_distrib, hwsum e, Finset.sum_const, nsmul_eq_mul, hcard e, ht_def]
      field_simp

/-- **The degenerate case.** -/
theorem exists_scaledCorrection_of_not_nonempty (G : SimpleGraph V) [DecidableRel G.Adj]
    (hne : ¬ Nonempty V) (lam : ℝ) :
    ∃ x : Finset (EdgeV G) → ℝ, IsScaledDeficiencyCorrection G lam x := by
  refine ⟨fun _ => 0, fun T hT => ?_, fun e => absurd (nonempty_of_edgeV G e) hne⟩
  obtain ⟨e, -⟩ := exists_edge_of_mem_triangleHypergraphSub G hT
  exact absurd (nonempty_of_edgeV G e) hne

/-! ### The residual, with no loss -/

/-- **The residual as a single global statement, with the base scale free.**  At the Dross density
some base weighting `lam/(|V|-2)` admits a correction bounded by `lam/(|V|-2)`, with `lam` bounded
uniformly over all graphs. -/
def DrossScaledCorrection : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ x : Finset (EdgeV G) → ℝ, IsScaledDeficiencyCorrection G K x

/-- **The residual is the target.**  `Nibble.DrossScaledCorrection` and
`Nibble.DrossFractionalQuantSpread` are equivalent: passing to the correction form loses nothing,
so the correction statement is an exact reformulation of the missing input. -/
theorem drossFractionalQuantSpread_iff_scaledCorrection :
    DrossFractionalQuantSpread ↔ DrossScaledCorrection := by
  constructor
  · rintro ⟨C, hC, hmain⟩
    refine ⟨C, hC, ?_⟩
    intro V _ _ G _ hdense
    by_cases hne : Nonempty V
    · obtain ⟨v⟩ := hne
      have hten : 10 ≤ Fintype.card V := ten_le_card_of_dense G hdense v
      have hV : 3 ≤ Fintype.card V := by omega
      have htenR : (10 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hten
      obtain ⟨w, hw, hwb⟩ := hmain G hdense
      refine (exists_scaledCorrection_iff_bounded_decomp G hV C).mpr ⟨w, hw, fun T hT => ?_⟩
      refine le_trans (hwb T hT) ?_
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    · exact exists_scaledCorrection_of_not_nonempty G hne C
  · rintro ⟨K, hK, hmain⟩
    refine ⟨3 * K, by linarith, ?_⟩
    intro V _ _ G _ hdense
    by_cases hne : Nonempty V
    · obtain ⟨v⟩ := hne
      have hten : 10 ≤ Fintype.card V := ten_le_card_of_dense G hdense v
      have hV : 3 ≤ Fintype.card V := by omega
      have htenR : (10 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hten
      obtain ⟨w, hw, hwb⟩ :=
        (exists_scaledCorrection_iff_bounded_decomp G hV K).mp (hmain G hdense)
      refine ⟨w, hw, fun T hT => ?_⟩
      refine le_trans (hwb T hT) ?_
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    · exact exists_decomp_of_not_nonempty G hne _

/-- The unscaled residual of `Nibble/DrossSpread.lean` implies the scaled one. -/
theorem drossScaledCorrection_of_uniformCorrection (h : DrossUniformCorrection) :
    DrossScaledCorrection := by
  refine ⟨1, one_pos, ?_⟩
  intro V _ _ G _ hdense
  obtain ⟨x, hx⟩ := h G hdense
  exact ⟨x, (isScaledDeficiencyCorrection_one G x).mpr hx⟩

end Nibble
