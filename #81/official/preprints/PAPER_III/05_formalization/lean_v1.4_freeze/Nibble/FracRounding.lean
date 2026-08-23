/-
# Nibble — rounding a *spread* fractional triangle decomposition, and the residual for
`FracRoundingToPacking`

`Nibble.FracRoundingToPacking` (see `Nibble/DrossFractional.lean`) is the global rounding input of
the `1/5` chain: a graph carrying a fractional triangle decomposition has, for large `|V|`, an
integral triangle packing with `o(|V|²)` uncovered incidences.  Together with Dross's theorem —
proved unconditionally in the sister development at the density `9|V| ≤ 10δ(G)` — it makes
`Nibble.DenseGlobalSmallLeftover`, and everything downstream of it, unconditional.

This file discharges `FracRoundingToPacking` **for spread fractional decompositions**, and isolates
the exact remaining residual.

* `Nibble.IsSpreadFracTriangleDecompOn` — a fractional triangle decomposition of `G` whose weights
  are all at most `δ`, supported on a set `R` of edges, covering each edge of `R` to level
  `≥ 1 - γ`.
* `Nibble.spreadTriangleRounding` — **unconditional**: for every `ε > 0` there are `δ, γ, ρ > 0`
  such that every graph carrying such a decomposition with `|E ∖ R| ≤ ρ|V|²` has an integral
  triangle packing with at most `ε|V|²` uncovered incidences.  No lower bound on `|V|` is needed.
  The proof runs the deterministic Beck–Fiala regularization of `Nibble/SpreadNibble.lean` into the
  library's own nibble.
* `Nibble.spreadFracRounding_of_decomp` — the clean special case: a *perfect* fractional triangle
  decomposition all of whose weights are at most `δ`.
* `Nibble.FracDecompSpreading` — **the residual**: every graph with a fractional triangle
  decomposition has, for large `|V|`, a spread one after deleting `ρ|V|²` edges.
* `Nibble.fracRoundingToPacking_of_spreading` — the machine-checked reduction
  `FracDecompSpreading → FracRoundingToPacking`, and its downstream consequences.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.SpreadNibble
import Nibble.UniformRounding
import Nibble.DrossFractional

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A **`δ`-spread fractional triangle decomposition of `G` on the edge set `R`**: nonnegative
triangle weights, each at most `δ`, carried only by triangles all of whose edges lie in `R`, giving
every edge of `R` total weight in `[1 - γ, 1]`. -/
def IsSpreadFracTriangleDecompOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset (EdgeV G) → ℝ) (δ γ : ℝ) (R : Finset (EdgeV G)) : Prop :=
  IsSpreadFracMatchingOn (triangleHypergraphSub G) w δ γ R

/-- The empty family is a matching. -/
theorem isMatching_empty (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsMatching (triangleHypergraphSub G) (∅ : Finset (Finset (EdgeV G))) :=
  ⟨Finset.empty_subset _, fun e he => absurd he (Finset.notMem_empty e)⟩

/-- **Rounding a spread fractional triangle decomposition — unconditionally.**

For every `ε > 0` there are tolerances `δ, γ, ρ > 0` such that any graph carrying a `δ`-spread
fractional triangle decomposition on an edge set `R` missing at most `ρ|V|²` edges, covering each
edge of `R` to level at least `1 - γ`, has an integral triangle packing whose uncovered incidence
count is at most `ε|V|²`. -/
theorem spreadTriangleRounding (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ γ : ℝ, 0 < γ ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (w : Finset (EdgeV G) → ℝ) (R : Finset (EdgeV G)),
        IsSpreadFracTriangleDecompOn G w δ γ R →
        ((Finset.univ \ R).card : ℝ) ≤ ρ * (Fintype.card V : ℝ) ^ 2 →
        ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
          (uncoveredTot G M : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨δ, hδ, γ, hγ, η, hη, hmain⟩ := exists_matching_of_spread 3 (by norm_num) (ε / 2) (by positivity)
  refine ⟨δ, hδ, γ, hγ, η * ε / 4, by positivity, ?_⟩
  intro V _ _ G _ w R hspread hRsmall
  set N : ℝ := (Fintype.card (EdgeV G) : ℝ) with hNdef
  have hNsq : 2 * N ≤ (Fintype.card V : ℝ) ^ 2 := card_edgeV_le_sq G
  have hNnn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  by_cases hbig : (ε / 4) * (Fintype.card V : ℝ) ^ 2 ≤ N
  · -- the edge set is quadratically large: the nibble applies
    have hRη : ((Finset.univ \ R).card : ℝ) ≤ η * N := by
      have h1 : η * ((ε / 4) * (Fintype.card V : ℝ) ^ 2) ≤ η * N :=
        mul_le_mul_of_nonneg_left hbig hη.le
      calc ((Finset.univ \ R).card : ℝ) ≤ η * ε / 4 * (Fintype.card V : ℝ) ^ 2 := hRsmall
        _ = η * ((ε / 4) * (Fintype.card V : ℝ) ^ 2) := by ring
        _ ≤ η * N := h1
    obtain ⟨M, hM, hMcard⟩ :=
      hmain (triangleHypergraphSub G) w R (triangleHypergraphSub_uniform G)
        (fun x y hxy => by exact_mod_cast triangleHypergraphSub_codegree_le_one G hxy)
        hspread hRη
    refine ⟨M, hM, ?_⟩
    rw [uncoveredTot_eq G hM]
    have hεN : ε * N ≤ ε * ((Fintype.card V : ℝ) ^ 2 / 2) := by
      have : N ≤ (Fintype.card V : ℝ) ^ 2 / 2 := by linarith
      exact mul_le_mul_of_nonneg_left this hε.le
    nlinarith [hMcard, hεN]
  · -- few edges: the empty packing already works
    push_neg at hbig
    refine ⟨∅, isMatching_empty G, ?_⟩
    rw [uncoveredTot_eq G (isMatching_empty G)]
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero, sub_zero]
    nlinarith only [hbig]

/-- **The clean special case.**  A *perfect* fractional triangle decomposition all of whose weights
are at most `δ` rounds to an integral packing with at most `ε|V|²` uncovered incidences. -/
theorem spreadFracRounding_of_decomp (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (w : Finset (EdgeV G) → ℝ),
        IsFracTriangleDecomp G w → (∀ T ∈ triangleHypergraphSub G, w T ≤ δ) →
        ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
          (uncoveredTot G M : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨δ, hδ, γ, hγ, ρ, hρ, hmain⟩ := spreadTriangleRounding ε hε
  refine ⟨δ, hδ, ?_⟩
  intro V _ _ G _ w hw hwδ
  obtain ⟨hnn, hsum⟩ := hw
  have hsum' : ∀ x : EdgeV G,
      ∑ T ∈ (triangleHypergraphSub G).filter (fun T => x ∈ T), w T = 1 := fun x => hsum x
  refine hmain G w Finset.univ ⟨fun t ht => ⟨hnn t ht, hwδ t ht⟩, fun x => ?_, fun x _ => ?_⟩ ?_
  · rw [hsum' x]
  · rw [hsum' x]; linarith
  · simp only [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero]
    positivity

/-! ### Non-vacuity: complete graphs -/

/-- **The complete graph has a near-perfect integral triangle packing.**  For every `ε > 0`, once
`|V|` is large, `K_{|V|}` has an edge-disjoint family of triangles leaving at most `ε|V|²` uncovered
edge incidences.  This is `Nibble.spreadFracRounding_of_decomp` applied to the uniform fractional
decomposition `1/(|V| - 2)` of `Nibble.isFracTriangleDecomp_top`, which is spread once
`|V| ≥ 2 + 1/δ`; in particular the hypotheses of the spread rounding theorem are satisfiable. -/
theorem completeGraph_smallLeftover (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V], n₀ ≤ Fintype.card V →
      ∃ M : Finset (Finset (EdgeV (⊤ : SimpleGraph V))),
        IsMatching (triangleHypergraphSub (⊤ : SimpleGraph V)) M ∧
        (uncoveredTot (⊤ : SimpleGraph V) M : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  obtain ⟨δ, hδ, hround⟩ := spreadFracRounding_of_decomp ε hε
  refine ⟨⌈1 / δ⌉₊ + 3, ?_⟩
  intro V _ _ hV
  have hV3 : 3 ≤ Fintype.card V := by omega
  have hinv : (1 / δ : ℝ) ≤ (Fintype.card V : ℝ) - 2 := by
    have h1 : (1 / δ : ℝ) ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈1 / δ⌉₊ : ℕ) : ℝ) + 3 ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast (by omega : ⌈1 / δ⌉₊ + 3 ≤ Fintype.card V)
    linarith
  have hpos : (0 : ℝ) < (Fintype.card V : ℝ) - 2 := by
    have : (0 : ℝ) < 1 / δ := by positivity
    linarith
  refine hround (⊤ : SimpleGraph V) _ (isFracTriangleDecomp_top hV3) (fun T _ => ?_)
  rw [div_le_iff₀ hpos]
  rw [div_le_iff₀ hδ] at hinv
  linarith

/-! ### The residual -/

/-- **The spreading residual.**  Every graph carrying a fractional triangle decomposition carries,
once `|V|` is large, a `δ`-*spread* one after deleting at most `ρ|V|²` edges.

This is the only missing input: `Nibble.fracRoundingToPacking_of_spreading` turns it into
`Nibble.FracRoundingToPacking`, using the unconditional `Nibble.spreadTriangleRounding`.

It is a genuinely weaker statement than the rounding it replaces: it asks nothing probabilistic and
nothing about matchings, only that the *weights* of a fractional decomposition can be smoothed out
(over all but a quadratically small set of edges).  Smoothing is necessary: a fractional
decomposition can be concentrated (e.g. weight `1/2` on the four triangles of each block of a
`K₄`-decomposition), and the support of such a decomposition alone does not carry a near-perfect
integral packing. -/
def FracDecompSpreading : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ γ : ℝ, 0 < γ → ∀ ρ : ℝ, 0 < ρ → ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → HasFracTriangleDecomp G →
      ∃ (w : Finset (EdgeV G) → ℝ) (R : Finset (EdgeV G)),
        IsSpreadFracTriangleDecompOn G w δ γ R ∧
        ((Finset.univ \ R).card : ℝ) ≤ ρ * (Fintype.card V : ℝ) ^ 2

/-- **The reduction.**  `FracRoundingToPacking` follows from the spreading residual alone. -/
theorem fracRoundingToPacking_of_spreading (h : FracDecompSpreading) : FracRoundingToPacking := by
  intro ε hε
  obtain ⟨δ, hδ, γ, hγ, ρ, hρ, hround⟩ := spreadTriangleRounding ε hε
  obtain ⟨n₀, hspread⟩ := h δ hδ γ hγ ρ hρ
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV hdecomp
  obtain ⟨w, R, hw, hR⟩ := hspread G hV hdecomp
  exact hround G w R hw hR

/-- **Dross + spreading give the `o(|V|²)` residual.** -/
theorem denseGlobalSmallLeftover_of_dross_of_spreading (hdross : DrossFractional)
    (hspread : FracDecompSpreading) : DenseGlobalSmallLeftover :=
  denseGlobalSmallLeftover_of_dross_of_rounding hdross (fracRoundingToPacking_of_spreading hspread)

/-- **Dross + spreading cross the `1/5` wall.** -/
theorem leftoverConst_below_fifth_of_dross_of_spreading (hdross : DrossFractional)
    (hspread : FracDecompSpreading) :
    ∃ c : ℝ, c < 1 / 5 ∧ DenseGlobalLeftoverConst c :=
  leftoverConst_below_fifth_of_dross_of_rounding hdross
    (fracRoundingToPacking_of_spreading hspread)

/-! ### The single-input route: a *spread* Dross theorem

The chain above still consumes two global inputs.  In fact one suffices: the rounding step is
unconditional for spread decompositions, so a version of Dross's theorem that produces a spread
decomposition — which is what a flow/absorption construction naturally yields, its weights having
denominators of order `|V|` — closes the whole chain by itself. -/

/-- **A spread Dross theorem**: at the Dross density, a fractional triangle decomposition all of
whose weights are at most `δ`, once `|V|` is large. -/
def DrossFractionalSpread : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ w : Finset (EdgeV G) → ℝ, IsFracTriangleDecomp G w ∧
        ∀ T ∈ triangleHypergraphSub G, w T ≤ δ

/-- **A quantitatively spread Dross theorem**: at the Dross density, a fractional triangle
decomposition with all weights `≤ C/|V|`. -/
def DrossFractionalQuantSpread : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ w : Finset (EdgeV G) → ℝ, IsFracTriangleDecomp G w ∧
        ∀ T ∈ triangleHypergraphSub G, w T ≤ C / (Fintype.card V : ℝ)

/-- The quantitative form implies the qualitative one. -/
theorem drossFractionalSpread_of_quant (h : DrossFractionalQuantSpread) :
    DrossFractionalSpread := by
  obtain ⟨C, hC, hmain⟩ := h
  intro δ hδ
  refine ⟨⌈C / δ⌉₊ + 1, ?_⟩
  intro V _ _ G _ hV hdense
  obtain ⟨w, hw, hwC⟩ := hmain G hdense
  refine ⟨w, hw, fun T hT => ?_⟩
  have hn : (C / δ : ℝ) ≤ (Fintype.card V : ℝ) := by
    have h1 : (C / δ : ℝ) ≤ (⌈C / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈C / δ⌉₊ : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast (by omega : ⌈C / δ⌉₊ ≤ Fintype.card V)
    linarith
  have hVpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    have : (0 : ℝ) < C / δ := by positivity
    linarith
  have : C / (Fintype.card V : ℝ) ≤ δ := by
    rw [div_le_iff₀ hVpos]
    rw [div_le_iff₀ hδ] at hn
    linarith
  exact le_trans (hwC T hT) this

/-- **The spread Dross theorem alone gives the `o(|V|²)` residual** — no separate rounding input. -/
theorem denseGlobalSmallLeftover_of_drossSpread (h : DrossFractionalSpread) :
    DenseGlobalSmallLeftover := by
  intro ε hε
  obtain ⟨δ, hδ, hround⟩ := spreadFracRounding_of_decomp ε hε
  obtain ⟨n₀, hd⟩ := h δ hδ
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV hdense
  obtain ⟨w, hw, hwδ⟩ := hd G hV hdense
  exact hround G w hw hwδ

/-- **The spread Dross theorem alone crosses the `1/5` wall.** -/
theorem leftoverConst_below_fifth_of_drossSpread (h : DrossFractionalSpread) :
    ∃ c : ℝ, c < 1 / 5 ∧ DenseGlobalLeftoverConst c := by
  refine ⟨1 / 10, by norm_num, ?_⟩
  exact denseGlobalLeftoverConst_of_smallLeftover
    (denseGlobalSmallLeftover_of_drossSpread h) (by norm_num)

/-- **The spread Dross theorem alone gives the full `1/10` per-vertex bound**, i.e.
`Nibble.DenseTriangleNibbleDeg` for every `β > 1/10`. -/
theorem denseTriangleNibbleDeg_of_drossSpread (h : DrossFractionalSpread) {β : ℝ}
    (hβ : 1 / 10 < β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) :=
  denseTriangleNibbleDeg_of_tenth_lt_of_const (denseGlobalSmallLeftover_of_drossSpread h) hβ

/-- **Dross + spreading give the full `1/10` per-vertex bound.** -/
theorem denseTriangleNibbleDeg_of_dross_of_spreading (hdross : DrossFractional)
    (hspread : FracDecompSpreading) {β : ℝ} (hβ : 1 / 10 < β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) :=
  denseTriangleNibbleDeg_of_dross_of_rounding hdross
    (fracRoundingToPacking_of_spreading hspread) hβ

end Nibble
