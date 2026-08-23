/-
# Nibble — the per-vertex nibble bound, unconditionally, at minimum degree `(15/16)|V|`

`Nibble/DrossFlowDense.lean` produces, unconditionally and with no lower bound on `|V|`, a *spread*
fractional triangle decomposition (all weights at most `3/|V|`) of every graph with minimum degree
at least `(1 - 1/16)|V|`.  Feeding it into the unconditional rounding half of the chain
(`Nibble.spreadFracRounding_of_decomp`) and the per-graph exchange rate
(`Nibble.uncoveredAt_le_of_leftover_matching`) gives the full conclusion of the Dross programme
over the class `δ(G) ≥ (15/16)|V|` — widening `Nibble.nearComplete_triangleNibbleDeg`, which needs
`δ(G) ≥ (99/100)|V|`.

* `Nibble.dense16_smallLeftover_fixed` — for **every** `ε > 0`, every large graph of minimum degree
  at least `(1 - 1/16)|V|` has a triangle matching leaving at most `ε|V|²` uncovered incidences;
* `Nibble.dense16_triangleNibbleDeg` — **the theorem**: for every `β > 1/10` every large graph of
  minimum degree at least `(1 - 1/16)|V|` has a triangle matching whose uncovered star at every
  vertex has size at most `β|V|`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DrossFlowDense
import Nibble.NearCompleteNibble

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Minimum degree at least `(1 - 1/16)|V|` is above the Dross density. -/
theorem dense_of_dense16 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : (1 - 1 / 16 : ℝ) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ)) :
    9 * Fintype.card V ≤ 10 * G.minDegree := by
  have hnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  have : (9 : ℝ) * (Fintype.card V : ℝ) ≤ 10 * (G.minDegree : ℝ) := by linarith
  exact_mod_cast this

/-- **Uniform-in-`ε` near-perfect packings at minimum degree `(15/16)|V|`.**  For every `ε > 0`
every sufficiently large graph with minimum degree at least `(1 - 1/16)|V|` has an edge-disjoint
family of triangles leaving at most `ε|V|²` uncovered incidences; the density threshold `1/16` does
not depend on `ε`. -/
theorem dense16_smallLeftover_fixed (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → (1 - 1 / 16 : ℝ) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        (uncoveredTot G M : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨δ, hδ, hround⟩ := spreadFracRounding_of_decomp ε hε
  refine ⟨⌈3 / δ⌉₊, ?_⟩
  intro V _ _ G _ hV hmin
  obtain ⟨w, hw, hwb⟩ := hasSpreadFracTriangleDecomp_of_minDegree G hmin
  refine hround G w hw (fun T hT => ?_)
  have hceil : (⌈3 / δ⌉₊ : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV
  have h3δ : (3 : ℝ) / δ ≤ (Fintype.card V : ℝ) := le_trans (Nat.le_ceil _) hceil
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    have : (0 : ℝ) < 3 / δ := by positivity
    linarith
  refine le_trans (hwb T hT) ?_
  rw [div_le_iff₀ hnpos]
  rw [div_le_iff₀ hδ] at h3δ
  linarith

/-- **The theorem.**  For every `β > 1/10` every sufficiently large graph with minimum degree at
least `(1 - 1/16)|V|` has an edge-disjoint family of triangles whose uncovered star at every vertex
has at most `β|V|` edges.  This is the conclusion of `Nibble.DenseTriangleNibbleDeg`,
unconditionally, over the class `δ(G) ≥ (15/16)|V|`. -/
theorem dense16_triangleNibbleDeg {β : ℝ} (hβ : 1 / 10 < β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → (1 - 1 / 16 : ℝ) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) := by
  set c : ℝ := (10 * β ^ 2 - β) / 20 with hcdef
  have hcpos : 0 < c := by
    have : 0 < 10 * β ^ 2 - β := by nlinarith
    rw [hcdef]; linarith
  have hstar : starBoundOf c < β := by
    have hpos : 0 < 20 * β - 1 := by linarith
    have hsq : 1 + 400 * c < (20 * β - 1) ^ 2 := by rw [hcdef]; linarith
    have hlt : Real.sqrt (1 + 400 * c) < 20 * β - 1 := by
      have := Real.sqrt_lt_sqrt (by positivity) hsq
      rwa [Real.sqrt_sq (le_of_lt hpos)] at this
    unfold starBoundOf; linarith
  have hSpos : 0 < 10 * β ^ 2 - β - 10 * c := key_quadratic_gap hcpos.le hstar
  have h10 : 0 < 10 * β - 1 := by linarith
  obtain ⟨n₁, hleft⟩ := dense16_smallLeftover_fixed c hcpos
  refine ⟨max n₁ (max ⌈20 * β / (10 * β ^ 2 - β - 10 * c)⌉₊ ⌈(20 : ℝ) / (10 * β - 1)⌉₊) + 1, ?_⟩
  intro V _ _ G _ hV hmin
  have hn₁ : n₁ ≤ Fintype.card V := by
    have := le_trans (le_max_left n₁ _) (Nat.le_of_succ_le hV)
    omega
  obtain ⟨M₀, hM₀, hK⟩ := hleft G hn₁ hmin
  have hgapS : 20 * β < (Fintype.card V : ℝ) * (10 * β ^ 2 - β - 10 * c) := by
    have hlt : ⌈20 * β / (10 * β ^ 2 - β - 10 * c)⌉₊ < Fintype.card V :=
      lt_of_lt_of_le
        (Nat.lt_succ_of_le (le_trans (le_max_left _ _) (le_max_right n₁ _))) hV
    have hR : (20 : ℝ) * β / (10 * β ^ 2 - β - 10 * c) < (Fintype.card V : ℝ) :=
      lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hlt)
    rw [div_lt_iff₀ hSpos] at hR
    linarith
  have hgapT : (20 : ℝ) < (Fintype.card V : ℝ) * (10 * β - 1) := by
    have hlt : ⌈(20 : ℝ) / (10 * β - 1)⌉₊ < Fintype.card V :=
      lt_of_lt_of_le
        (Nat.lt_succ_of_le (le_trans (le_max_right _ _) (le_max_right n₁ _))) hV
    have hR : (20 : ℝ) / (10 * β - 1) < (Fintype.card V : ℝ) :=
      lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hlt)
    rw [div_lt_iff₀ h10] at hR
    linarith
  exact uncoveredAt_le_of_leftover_matching hcpos.le hstar G (dense_of_dense16 G hmin)
    hgapS hgapT hM₀ hK

end Nibble
