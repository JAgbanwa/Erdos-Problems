/-
# Yuster — assembling `NearlyRegularMost` for the triangle hypergraph

Standalone, Mathlib-only. Connects the Szemerédi+counting Y1c reconstruction to the majority
near-regularity interface. Given a global `ε`-uniform, `2ε`-dense pair `(s, t)`, the *capturing*
vertices (those whose neighbourhood contains `ε`-fractions of both parts) have triangle degree
`≥ ε³|s||t|` (via `triangleHypergraph_degree_lower_of_capture`, Y1c-i). Taking the exceptional set to be
the NON-capturing vertices, the triangle hypergraph is `NearlyRegularMost d μ η` — provided the
exceptional count is `≤ η|V|` (from `card_capturing_lower`, Y1c-ii) and the choose-`2` upper bound
holds on capturing vertices (both supplied as hypotheses here, discharged by the full application).

* `triangleHypergraph_nearlyRegularMost` — the assembly.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.YusterCapture
import Nibble.RegularMost

open Finset SimpleGraph Hypergraph

namespace Nibble.Yuster

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Y3 (majority) — the triangle hypergraph is `NearlyRegularMost`.** From a global `ε`-uniform,
`2ε`-dense disjoint pair `(s, t)`, with the exceptional (non-capturing) set of size `≤ η|V|` and the
choose-`2` upper bound `≤ (1+μ)d` on capturing vertices, and `(1-μ)d ≤ ε³|s||t|`, the triangle
hypergraph is `NearlyRegularMost d μ η`. The lower bound on capturing vertices is Y1c-i. -/
theorem triangleHypergraph_nearlyRegularMost {ε d μ η : ℝ} {s t : Finset V}
    (hε0 : 0 ≤ ε) (hunif : G.IsUniform ε s t) (hdense : 2 * ε ≤ (G.edgeDensity s t : ℝ))
    (hst : Disjoint s t)
    (hlo : (1 - μ) * d ≤ ε * ((s.card : ℝ) * ε) * ((t.card : ℝ) * ε))
    (hhi : ∀ v, (s.card : ℝ) * ε ≤ ((s ∩ G.neighborFinset v).card : ℝ) →
                (t.card : ℝ) * ε ≤ ((t ∩ G.neighborFinset v).card : ℝ) →
                (degree (triangleHypergraph G) v : ℝ) ≤ (1 + μ) * d)
    (hη : ((Finset.univ.filter (fun v =>
              ¬ ((s.card : ℝ) * ε ≤ ((s ∩ G.neighborFinset v).card : ℝ) ∧
                 (t.card : ℝ) * ε ≤ ((t ∩ G.neighborFinset v).card : ℝ)))).card : ℝ)
          ≤ η * (Fintype.card V : ℝ)) :
    NearlyRegularMost (triangleHypergraph G) d μ η := by
  refine ⟨Finset.univ.filter (fun v =>
      ¬ ((s.card : ℝ) * ε ≤ ((s ∩ G.neighborFinset v).card : ℝ) ∧
         (t.card : ℝ) * ε ≤ ((t ∩ G.neighborFinset v).card : ℝ))), hη, ?_⟩
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hv
  obtain ⟨hscap, htcap⟩ := hv
  refine ⟨?_, hhi v hscap htcap⟩
  -- lower bound: (1-μ)d ≤ ε³|s||t| ≤ ε|s∩N(v)||t∩N(v)| ≤ deg
  have hsnn : (0 : ℝ) ≤ (s.card : ℝ) * ε := mul_nonneg (Nat.cast_nonneg _) hε0
  have htnn : (0 : ℝ) ≤ (t.card : ℝ) * ε := mul_nonneg (Nat.cast_nonneg _) hε0
  have hAB : (s.card : ℝ) * ε * ((t.card : ℝ) * ε)
      ≤ ((s ∩ G.neighborFinset v).card : ℝ) * ((t ∩ G.neighborFinset v).card : ℝ) :=
    mul_le_mul hscap htcap htnn (le_trans hsnn hscap)
  have hmono : ε * ((s.card : ℝ) * ε) * ((t.card : ℝ) * ε)
      ≤ ε * ((s ∩ G.neighborFinset v).card : ℝ) * ((t ∩ G.neighborFinset v).card : ℝ) := by
    calc ε * ((s.card : ℝ) * ε) * ((t.card : ℝ) * ε)
        = ε * ((s.card : ℝ) * ε * ((t.card : ℝ) * ε)) := by ring
      _ ≤ ε * (((s ∩ G.neighborFinset v).card : ℝ) * ((t ∩ G.neighborFinset v).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hAB hε0
      _ = ε * ((s ∩ G.neighborFinset v).card : ℝ) * ((t ∩ G.neighborFinset v).card : ℝ) := by ring
  exact le_trans hlo (le_trans hmono
    (triangleHypergraph_degree_lower_of_capture G hunif hdense hst hscap htcap))

end Nibble.Yuster
