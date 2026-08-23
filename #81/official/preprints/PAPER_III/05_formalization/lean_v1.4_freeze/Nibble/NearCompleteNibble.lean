/-
# Nibble — the per-vertex nibble bound, unconditionally, for near-complete graphs

`Nibble/NearCompleteFrac.lean` produces, unconditionally, a *spread* fractional triangle
decomposition (all weights at most `3/|V|`) of every graph on at least `1000` vertices with minimum
degree at least `(1 - 1/100)|V|`.  The rounding half of the chain
(`Nibble.spreadFracRounding_of_decomp`) and the exchange rate from a global leftover constant to a
per-vertex star bound (`Nibble.denseTriangleNibbleDeg_of_leftoverConst`) are unconditional and act
graph by graph.  Chaining them gives the full conclusion of the Dross programme — but only over the
near-complete class, not at the Dross density `9|V| ≤ 10δ(G)`.

* `Nibble.uncoveredAt_le_of_leftover_matching` — the per-graph core of the exchange rate: a single
  triangle matching with at most `c|V|²` uncovered incidences upgrades, on the same graph, to one
  with at most `β|V|` uncovered incidences at *every* vertex, for any `β > (1+√(1+400c))/20`.
* `Nibble.nearComplete_smallLeftover_fixed` — for **every** `ε > 0` (with the density threshold no
  longer depending on `ε`, unlike `Nibble.nearComplete_smallLeftover`) every large graph of minimum
  degree at least `(1 - 1/100)|V|` has a triangle matching leaving at most `ε|V|²` uncovered
  incidences.
* `Nibble.nearComplete_triangleNibbleDeg` — **the theorem**: for every `β > 1/10` every large graph
  of minimum degree at least `(1 - 1/100)|V|` has a triangle matching whose uncovered star at every
  vertex has size at most `β|V|`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.NearCompleteFrac
import Nibble.DenseGlobalLeftoverConst

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The exchange rate, one graph at a time -/

/-- **The per-graph exchange rate.**  On a single graph at the Dross density, a triangle matching
with at most `c|V|²` uncovered incidences upgrades to one whose uncovered star at every vertex is at
most `β|V|`, provided `β` exceeds the star bound `(1 + √(1 + 400c))/20` and `|V|` is large enough
for the two explicit gap inequalities. -/
theorem uncoveredAt_le_of_leftover_matching {c β : ℝ} (hc : 0 ≤ c) (hβ : starBoundOf c < β)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (hgapS : 20 * β < (Fintype.card V : ℝ) * (10 * β ^ 2 - β - 10 * c))
    (hgapT : (20 : ℝ) < (Fintype.card V : ℝ) * (10 * β - 1))
    {M₀ : Finset (Finset (EdgeV G))} (hM₀ : IsMatching (triangleHypergraphSub G) M₀)
    (hK : (uncoveredTot G M₀ : ℝ) ≤ c * (Fintype.card V : ℝ) ^ 2) :
    ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
      ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) := by
  have hten : 1 / 10 < β := tenth_lt_of_starBoundOf_lt hc hβ
  have hβpos : 0 < β := by linarith only [hten]
  have h10 : 0 < 10 * β - 1 := by linarith only [hten]
  have hSpos : 0 < 10 * β ^ 2 - β - 10 * c := key_quadratic_gap hc hβ
  obtain ⟨M, hM, -, hquad⟩ :=
    dense_uncoveredAt_quadratic G hdense (uncoveredTot G M₀) hM₀ le_rfl
  refine ⟨M, hM, fun v => ?_⟩
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hnpos : 0 < n := by nlinarith only [h10, hgapT]
  set d : ℝ := ((uncoveredAt G M v).card : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hq : 10 * d * d ≤ 10 * (uncoveredTot G M₀ : ℝ) + n * d + 20 * d := by
    rw [hn, hd]; exact_mod_cast hquad v
  have hqc : 10 * d * d ≤ 10 * (c * n ^ 2) + n * d + 20 * d := by
    have := mul_le_mul_of_nonneg_left hK (by norm_num : (0:ℝ) ≤ 10)
    linarith only [hK, hq]
  by_contra hcon
  push_neg at hcon
  have hfac0 : 0 < 10 * (β * n) - n - 20 := by nlinarith only [hgapT]
  have hβn : 0 < β * n := by positivity
  have hprod : 0 < (d - β * n) * (10 * (d + β * n) - n - 20) :=
    mul_pos (by linarith) (by linarith)
  have hkey : 10 * (β * n) * (β * n) - (n + 20) * (β * n) < 10 * d * d - (n + 20) * d := by
    nlinarith only [hprod]
  have hB : 10 * d * d - (n + 20) * d ≤ 10 * c * n ^ 2 := by nlinarith only [hqc]
  have hCn : 20 * β * n < n ^ 2 * (10 * β ^ 2 - β - 10 * c) := by
    have := mul_lt_mul_of_pos_right hgapS hnpos
    nlinarith only [this]
  nlinarith only [hkey, hB, hCn]

/-! ### The near-complete class -/

omit [DecidableEq V] in
/-- Minimum degree at least `(1 - 1/100)|V|` is above the Dross density. -/
theorem dense_of_nearComplete (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : (1 - 1 / 100 : ℝ) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ)) :
    9 * Fintype.card V ≤ 10 * G.minDegree := by
  have hnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  have : (9 : ℝ) * (Fintype.card V : ℝ) ≤ 10 * (G.minDegree : ℝ) := by linarith only [hmin]
  exact_mod_cast this

/-- **Uniform-in-`ε` near-perfect packings of near-complete graphs.**  For every `ε > 0` every
sufficiently large graph with minimum degree at least `(1 - 1/100)|V|` has an edge-disjoint family
of triangles leaving at most `ε|V|²` uncovered incidences.  Unlike
`Nibble.nearComplete_smallLeftover`, the density threshold `1/100` does not depend on `ε`. -/
theorem nearComplete_smallLeftover_fixed (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → (1 - 1 / 100 : ℝ) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        (uncoveredTot G M : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨δ, hδ, hround⟩ := spreadFracRounding_of_decomp ε hε
  refine ⟨max 1000 ⌈3 / δ⌉₊, ?_⟩
  intro V _ _ G _ hV hmin
  have h1000 : 1000 ≤ Fintype.card V := le_trans (le_max_left _ _) hV
  obtain ⟨w, hw, hwb⟩ := nearComplete_hasSpreadFracTriangleDecomp G h1000 hmin
  refine hround G w hw (fun T hT => ?_)
  have hceil : (⌈3 / δ⌉₊ : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast le_trans (le_max_right _ _) hV
  have h3δ : (3 : ℝ) / δ ≤ (Fintype.card V : ℝ) := le_trans (Nat.le_ceil _) hceil
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    have : (0 : ℝ) < 3 / δ := by positivity
    linarith
  refine le_trans (hwb T hT) ?_
  rw [div_le_iff₀ hnpos]
  rw [div_le_iff₀ hδ] at h3δ
  linarith

/-- **The theorem.**  For every `β > 1/10` every sufficiently large graph with minimum degree at
least `(1 - 1/100)|V|` has an edge-disjoint family of triangles whose uncovered star at every
vertex has at most `β|V|` edges.  This is the conclusion of `Nibble.DenseTriangleNibbleDeg`,
unconditionally, over the near-complete class. -/
theorem nearComplete_triangleNibbleDeg {β : ℝ} (hβ : 1 / 10 < β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → (1 - 1 / 100 : ℝ) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) := by
  set c : ℝ := (10 * β ^ 2 - β) / 20 with hcdef
  have hcpos : 0 < c := by
    have : 0 < 10 * β ^ 2 - β := by nlinarith only [hβ]
    rw [hcdef]; linarith only [this]
  have hstar : starBoundOf c < β := by
    have hpos : 0 < 20 * β - 1 := by linarith only [hβ]
    have hsq : 1 + 400 * c < (20 * β - 1) ^ 2 := by rw [hcdef]; nlinarith only [hβ]
    have hlt : Real.sqrt (1 + 400 * c) < 20 * β - 1 := by
      have := Real.sqrt_lt_sqrt (by positivity) hsq
      rwa [Real.sqrt_sq (le_of_lt hpos)] at this
    unfold starBoundOf; linarith only [hlt]
  have hSpos : 0 < 10 * β ^ 2 - β - 10 * c := key_quadratic_gap hcpos.le hstar
  have h10 : 0 < 10 * β - 1 := by linarith only [hβ]
  obtain ⟨n₁, hleft⟩ := nearComplete_smallLeftover_fixed c hcpos
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
  exact uncoveredAt_le_of_leftover_matching hcpos.le hstar G (dense_of_nearComplete G hmin)
    hgapS hgapT hM₀ hK

end Nibble
