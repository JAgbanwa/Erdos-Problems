/-
# Nibble — unconditional near-perfect triangle packings of near-complete graphs

`Nibble.spreadTriangleRounding` (see `Nibble/FracRounding.lean`) rounds a *spread* fractional
triangle decomposition to an integral triangle packing with `o(|V|²)` uncovered incidences,
unconditionally.  This file feeds it the cheapest possible spread decomposition — the *uniform*
weighting `w_T = 1/|V|` — which is near-perfect exactly when all codegrees are close to `|V|`.

The result is an unconditional theorem with no fractional-decomposition hypothesis at all:

* `Nibble.nearComplete_smallLeftover` — for every `ε > 0` there is `c > 0` such that every large
  graph with minimum degree at least `(1 - c)|V|` has an edge-disjoint family of triangles leaving
  at most `ε|V|²` uncovered edge incidences.

It strictly generalizes `Nibble.completeGraph_smallLeftover`, and certifies that the spread
rounding theorem applies to graphs that are not complete.  The constant `c` it produces is small
(it is the tolerance coming out of the nibble), so this does *not* reach the Dross density
`9|V| ≤ 10δ(G)`: at that density the uniform weighting has deficiency of order `|V|²`, and a
genuinely spread *decomposition* is needed — that is the residual `Nibble.FracDecompSpreading`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.FracRounding

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The uniform weighting `1/|V|` loads every edge exactly to its codegree over `|V|`. -/
theorem uniform_load_eq (G : SimpleGraph V) [DecidableRel G.Adj] (E : EdgeV G) :
    ∑ _T ∈ (triangleHypergraphSub G).filter (fun T => E ∈ T),
        (1 / (Fintype.card V : ℝ))
      = ((commonNbrs G E).card : ℝ) / (Fintype.card V : ℝ) := by
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [show ((triangleHypergraphSub G).filter (fun T => E ∈ T)).card
      = degree (triangleHypergraphSub G) E from rfl, triangleSub_degree_eq_commonNbrs]
  ring

/-- **Codegrees of a near-complete graph.**  If every degree is at least `(1 - c)|V|`, every edge
has at least `(1 - 2c)|V|` common neighbours. -/
theorem card_commonNbrs_ge_of_minDegree (G : SimpleGraph V) [DecidableRel G.Adj] {c : ℝ}
    (hmin : (1 - c) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ)) (E : EdgeV G) :
    (1 - 2 * c) * (Fintype.card V : ℝ) ≤ ((commonNbrs G E).card : ℝ) := by
  obtain ⟨u, v, huv, hadj, hval⟩ := exists_pair_of_edgeV G E
  have hdeg := degree_add_degree_le G hval
  have hdegR : (G.degree u : ℝ) + (G.degree v : ℝ)
      ≤ (Fintype.card V : ℝ) + ((commonNbrs G E).card : ℝ) := by
    exact_mod_cast (by exact_mod_cast hdeg :
      ((G.degree u + G.degree v : ℕ) : ℝ)
        ≤ ((Fintype.card V + (commonNbrs G E).card : ℕ) : ℝ))
  have hu : ((G.minDegree : ℕ) : ℝ) ≤ (G.degree u : ℝ) := by exact_mod_cast G.minDegree_le_degree u
  have hv : ((G.minDegree : ℕ) : ℝ) ≤ (G.degree v : ℝ) := by exact_mod_cast G.minDegree_le_degree v
  linarith

/-- **Near-complete graphs have near-perfect integral triangle packings — unconditionally.**

For every `ε > 0` there is a `c > 0` such that every graph on at least `n₀` vertices with minimum
degree at least `(1 - c)|V|` carries an edge-disjoint family of triangles leaving at most `ε|V|²`
uncovered edge incidences.  No fractional decomposition of `G` is assumed: the uniform weighting
`1/|V|` is itself a `δ`-spread fractional triangle decomposition covering every edge to level
`≥ 1 - 2c`, and `Nibble.spreadTriangleRounding` rounds it. -/
theorem nearComplete_smallLeftover (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → (1 - c) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
          (uncoveredTot G M : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨δ, hδ, γ, hγ, ρ, hρ, hround⟩ := spreadTriangleRounding ε hε
  refine ⟨γ / 2, by positivity, ⌈1 / δ⌉₊ + 1, ?_⟩
  intro V _ _ G _ hV hmin
  have hVpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    have : 0 < Fintype.card V := by omega
    exact_mod_cast this
  have hinv : (1 / δ : ℝ) ≤ (Fintype.card V : ℝ) := by
    have h1 : (1 / δ : ℝ) ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈1 / δ⌉₊ : ℕ) : ℝ) + 1 ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast (by omega : ⌈1 / δ⌉₊ + 1 ≤ Fintype.card V)
    linarith
  refine hround G (fun _ => 1 / (Fintype.card V : ℝ)) Finset.univ
    ⟨fun T _ => ⟨by positivity, ?_⟩, fun E => ?_, fun E _ => ?_⟩ ?_
  · rw [div_le_iff₀ hVpos]
    rw [div_le_iff₀ hδ] at hinv
    linarith
  · rw [uniform_load_eq G E, div_le_one hVpos]
    have := card_commonNbrs_le G E
    have : ((commonNbrs G E).card : ℝ) + 2 ≤ (Fintype.card V : ℝ) := by exact_mod_cast this
    linarith
  · rw [uniform_load_eq G E, le_div_iff₀ hVpos]
    have := card_commonNbrs_ge_of_minDegree G hmin E
    linarith
  · simp only [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero]
    positivity

end Nibble
