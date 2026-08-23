/-
# Nibble — sum-estimate for the sharp McDiarmid coefficient (reduction)

Standalone, Mathlib-only. The sharp per-edge McDiarmid coefficient of `deg_residual(v)` is the *count*
`neighborCoef H v e` of `v`-edges meeting the toggled edge's neighbourhood
(`residualDegConfig_boundedDiff_sharp`). The sharp M8 denominator is `∑_{e∈H} (neighborCoef H v e)²`,
and feasibility needs it `≲ deg(v)·K²` (K a local conflict bound) — which, in the dense triangle-packing
regime (`d ≈ n²`, `K ≈ n`), gives the window `c ≈ √(d log n) ≪ d`.

This file supplies the hypothesis-free **reduction**: a generic `∑ f² ≤ M·∑ f` bound
(`sum_sq_le_max_mul_sum`) specialised to `neighborCoef`, so the whole sum-estimate reduces to two clean
magnitude bounds — the per-edge maximum `neighborCoef ≤ M` and the total `∑ neighborCoef ≤ S`. Those two
are the remaining combinatorial content (bounded in terms of degree/codegree of `H`).

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.ResidualBoundedDiffSharp

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- **Generic sum-of-squares bound.** For nonnegative terms bounded by `M`,
`∑ f² ≤ M·∑ f`. The lever that turns two magnitude bounds (max and total) into the sum-estimate. -/
theorem sum_sq_le_max_mul_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) {M : ℝ} (hM : ∀ i ∈ s, f i ≤ M) :
    ∑ i ∈ s, (f i) ^ 2 ≤ M * ∑ i ∈ s, f i := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i hi => ?_)
  rw [sq]
  exact mul_le_mul_of_nonneg_right (hM i hi) (hf i hi)

/-- The sharp per-edge McDiarmid coefficient: the number of `v`-edges of `H` meeting the neighbourhood
`e ∪ support(H-conflicts of e)`. This is exactly the coefficient of
`residualDegConfig_boundedDiff_sharp`. -/
def neighborCoef (H : Finset (Finset V)) (v : V) (e : Finset V) : ℕ :=
  ((H.filter (fun f => v ∈ f)).filter
    (fun f => ¬ Disjoint f (e ∪ support (H.filter (fun g => ¬ Disjoint e g))))).card

/-- **Sum-estimate reduction.** Given a per-edge maximum `M` and a total `S` for `neighborCoef`, the
sharp McDiarmid denominator is bounded: `∑_{e∈H} (neighborCoef H v e)² ≤ M·S`. Reduces the whole
sum-estimate to the two magnitude bounds `hM` and `hS`. -/
theorem sumSq_neighborCoef_le (H : Finset (Finset V)) (v : V) {M S : ℝ}
    (hM : ∀ e ∈ H, (neighborCoef H v e : ℝ) ≤ M)
    (hS : (∑ e ∈ H, (neighborCoef H v e : ℝ)) ≤ S) (hM0 : 0 ≤ M) :
    (∑ e ∈ H, (neighborCoef H v e : ℝ) ^ 2) ≤ M * S := by
  refine le_trans (sum_sq_le_max_mul_sum H (fun e => (neighborCoef H v e : ℝ))
    (fun e _ => Nat.cast_nonneg _) hM) ?_
  exact mul_le_mul_of_nonneg_left hS hM0

/-- **Max-side bound (hypothesis-free).** The per-edge coefficient is bounded by the codegrees along
the toggled edge's neighbourhood: `neighborCoef H v e ≤ ∑_{x ∈ N_e} codegree(v,x)`. Each `v`-edge
meeting `N_e` shares some `x ∈ N_e`, hence lies in the codegree-`(v,x)` set; `card_biUnion_le` collects
them. Under `CodegreeBounded H C` this gives `neighborCoef ≤ |N_e|·C` — the `M` of the reduction. -/
theorem neighborCoef_le_sum_codegree (H : Finset (Finset V)) (v : V) (e : Finset V) :
    neighborCoef H v e
      ≤ ∑ x ∈ (e ∪ support (H.filter (fun g => ¬ Disjoint e g))), codegree H v x := by
  rw [neighborCoef]
  have hsub : (H.filter (fun f => v ∈ f)).filter
        (fun f => ¬ Disjoint f (e ∪ support (H.filter (fun g => ¬ Disjoint e g))))
      ⊆ (e ∪ support (H.filter (fun g => ¬ Disjoint e g))).biUnion
          (fun x => (H.filter (fun f => v ∈ f)).filter (fun f => x ∈ f)) := by
    intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨hf1, hf2⟩ := hf
    rw [Finset.not_disjoint_iff] at hf2
    obtain ⟨x, hxf, hxN⟩ := hf2
    rw [Finset.mem_biUnion]
    exact ⟨x, hxN, Finset.mem_filter.mpr ⟨hf1, hxf⟩⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_biUnion_le) ?_)
  apply Finset.sum_le_sum
  intro x _
  apply le_of_eq
  rw [codegree, Finset.filter_filter]

/-- The sharp bounded-difference bound, restated with `neighborCoef`. -/
theorem residualDegConfig_boundedDiff_neighborCoef (H : Finset (Finset V)) (v : V) (e : Finset V)
    (ω ω' : Finset V → Bool) (hagree : ∀ g, g ≠ e → ω g = ω' g) :
    |(degree (residual H (H.filter (fun g => ω g = true))) v : ℝ)
       - (degree (residual H (H.filter (fun g => ω' g = true))) v : ℝ)|
      ≤ (neighborCoef H v e : ℝ) :=
  residualDegConfig_boundedDiff_sharp H v e ω ω' hagree

end Hypergraph
