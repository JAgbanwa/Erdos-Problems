/-
# Nibble — the *constant*-leftover residual, and the exact leftover ↦ star exchange rate

`Nibble.DenseGlobalSmallLeftover` (stated in `Nibble.DenseTriangleNibbleDegHalf`) asks, at the Dross
density `9|V| ≤ 10 δ(G)`, for triangle packings whose uncovered incidence count is `o(|V|²)`: one
packing for *every* `ε > 0`.  That is an approximate triangle decomposition at density `9/10`, and
the present library does not have it (`Nibble.dense_approx_global` supplies its `o(|V|²)` leftover
only in the near-complete band `δ(G) ≥ (1 − μ/2)|V|`).

This file isolates a **strictly weaker residual**, in which `ε` is *not* quantified: a single
constant `c` suffices.

* `Nibble.DenseGlobalLeftoverConst c` — at the Dross density, some triangle packing leaves at most
  `c|V|²` uncovered incidences (`uncoveredTot = ∑_v |uncoveredAt v| =` twice the number of uncovered
  edges).
* `Nibble.denseGlobalLeftoverConst_of_smallLeftover` — `DenseGlobalSmallLeftover` implies
  `DenseGlobalLeftoverConst c` for every `c > 0`: the new residual really is narrower.
* `Nibble.denseTriangleNibbleDeg_of_leftoverConst` — **the exchange rate**, machine-checked: a
  constant leftover `c` feeds the swap engine `Nibble.dense_uncoveredAt_quadratic` and yields the
  per-vertex star bound for every

  `β > (1 + √(1 + 400c)) / 20`.

  At `c → 0` this is the known `1/10` (`Nibble.denseTriangleNibbleDeg_of_tenth_lt`, re-derived here
  as `Nibble.denseTriangleNibbleDeg_of_tenth_lt_of_const`), and it is `< 1/2` — i.e. it beats the
  unconditional wall of `Nibble.dense_uncoveredAt_le_half` — exactly when `c < 1/5`
  (`Nibble.leftoverConst_beats_half_iff`).
* `Nibble.denseGlobalLeftoverConst_half` — **unconditional**: `DenseGlobalLeftoverConst c` holds for
  every `c > 1/2`, because the unconditional per-vertex bound `2|uncoveredAt v| ≤ |V| + 4` sums to
  `uncoveredTot ≤ |V|(|V| + 4)/2`.  The exchange rate turns `c = 1/2` into
  `(1 + √201)/20 ≈ 0.7589`, which is *worse* than the direct star count `1/2`
  (`Nibble.half_calibration_is_worse`): the global route only starts paying off below `c = 1/5`.

So the whole gap between the proved `1/2` and the target `1/10` is the single scalar question:
*how small a constant `c` can be certified for the uncovered-incidence count at density `9/10`?*
The two local moves of `Nibble.DenseTriangleNibbleDegProof` are stuck at `c = 1/2`, and every
`c < 1/5` is new information.

The two routes that suggest themselves for certifying such a `c` from the library's existing nibble
are refuted concretely in `Nibble.DenseGlobalRoutes` (cleaning to a near-complete induced subgraph;
iterating on the residual graph), and the third — running the nibble at the triangle hypergraph's
own band `μ = 1/5` — is refuted in `Nibble.BandFifthRefutation`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DenseTriangleNibbleDegHalf
import Mathlib.Tactic.NormNum.RealSqrt

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

/-! ### The narrowed residual -/

/-- **The constant-leftover residual.**  At the Dross density `9|V| ≤ 10 δ(G)`, some edge-disjoint
triangle family leaves at most `c|V|²` uncovered incidences.  Unlike
`Nibble.DenseGlobalSmallLeftover`, the constant `c` is *fixed*: no `o(|V|²)` is asked for. -/
def DenseGlobalLeftoverConst (c : ℝ) : Prop :=
  ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        (uncoveredTot G M : ℝ) ≤ c * (Fintype.card V : ℝ) ^ 2

/-- **The new residual is narrower**: the `o(|V|²)` input gives the constant input at every `c`. -/
theorem denseGlobalLeftoverConst_of_smallLeftover (h : DenseGlobalSmallLeftover) {c : ℝ}
    (hc : 0 < c) : DenseGlobalLeftoverConst c := h c hc

/-- The constant-leftover residual is monotone in `c`. -/
theorem DenseGlobalLeftoverConst.mono {c c' : ℝ} (hcc : c ≤ c')
    (h : DenseGlobalLeftoverConst c) : DenseGlobalLeftoverConst c' := by
  obtain ⟨n₀, hmain⟩ := h
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV hdense
  obtain ⟨M, hM, hle⟩ := hmain G hV hdense
  exact ⟨M, hM, le_trans hle (by nlinarith [sq_nonneg ((Fintype.card V : ℝ))])⟩

/-! ### The exchange rate: leftover constant ↦ per-vertex star bound -/

/-- The star bound delivered by a leftover constant `c`. -/
noncomputable def starBoundOf (c : ℝ) : ℝ := (1 + Real.sqrt (1 + 400 * c)) / 20

theorem starBoundOf_nonneg (c : ℝ) : 0 ≤ starBoundOf c := by
  have := Real.sqrt_nonneg (1 + 400 * c)
  unfold starBoundOf; linarith

/-- The exchange rate at `c = 0` is the target `1/10`. -/
theorem starBoundOf_zero : starBoundOf 0 = 1 / 10 := by
  unfold starBoundOf
  norm_num

/-- Above the star bound the quantity `10β² − β − 10c` is positive: this is the algebraic content of
the exchange rate. -/
theorem key_quadratic_gap {c β : ℝ} (hc : 0 ≤ c) (hβ : starBoundOf c < β) :
    0 < 10 * β ^ 2 - β - 10 * c := by
  have hs : Real.sqrt (1 + 400 * c) ^ 2 = 1 + 400 * c :=
    Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ Real.sqrt (1 + 400 * c) := Real.sqrt_nonneg _
  have h1 : Real.sqrt (1 + 400 * c) < 20 * β - 1 := by
    unfold starBoundOf at hβ; linarith
  nlinarith

/-- Above the star bound we are in particular above `1/10`. -/
theorem tenth_lt_of_starBoundOf_lt {c β : ℝ} (hc : 0 ≤ c) (hβ : starBoundOf c < β) :
    1 / 10 < β := by
  have hs2 : Real.sqrt (1 + 400 * c) ^ 2 = 1 + 400 * c := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ Real.sqrt (1 + 400 * c) := Real.sqrt_nonneg _
  have hs : (1 : ℝ) ≤ Real.sqrt (1 + 400 * c) := by nlinarith
  unfold starBoundOf at hβ
  linarith

/-- **The exchange rate, machine-checked.**  A leftover constant `c` at the Dross density pushes the
per-vertex uncovered star down to `β|V|` for every `β > (1 + √(1 + 400c))/20`. -/
theorem denseTriangleNibbleDeg_of_leftoverConst {c : ℝ} (hc : 0 ≤ c)
    (hglob : DenseGlobalLeftoverConst c) {β : ℝ} (hβ : starBoundOf c < β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) := by
  obtain ⟨n₁, hmain⟩ := hglob
  have hten : 1 / 10 < β := tenth_lt_of_starBoundOf_lt hc hβ
  have hβpos : 0 < β := by linarith
  have h10 : 0 < 10 * β - 1 := by linarith
  set S : ℝ := 10 * β ^ 2 - β - 10 * c with hS
  have hSpos : 0 < S := key_quadratic_gap hc hβ
  set a : ℕ := ⌈20 * β / S⌉₊ with ha
  set b : ℕ := ⌈(20 : ℝ) / (10 * β - 1)⌉₊ with hb
  have hle1 : n₁ ≤ max n₁ (max a b) := le_max_left _ _
  have hle2 : a ≤ max n₁ (max a b) := le_trans (le_max_left a b) (le_max_right _ _)
  have hle3 : b ≤ max n₁ (max a b) := le_trans (le_max_right a b) (le_max_right _ _)
  refine ⟨max n₁ (max a b) + 1, ?_⟩
  intro V _ _ G _ hV hdense
  obtain ⟨M₀, hM₀, hK⟩ :=
    hmain G (le_trans (le_trans hle1 (Nat.le_succ _)) hV) hdense
  obtain ⟨M, hM, hMK, hquad⟩ :=
    dense_uncoveredAt_quadratic G hdense (uncoveredTot G M₀) hM₀ le_rfl
  refine ⟨M, hM, fun v => ?_⟩
  set n : ℝ := (Fintype.card V : ℝ) with hn
  -- the two size thresholds, in real form
  have hn1 : (a : ℝ) < n := by
    have h : a < Fintype.card V := lt_of_lt_of_le (Nat.lt_succ_of_le hle2) hV
    rw [hn]; exact_mod_cast h
  have hn2 : (b : ℝ) < n := by
    have h : b < Fintype.card V := lt_of_lt_of_le (Nat.lt_succ_of_le hle3) hV
    rw [hn]; exact_mod_cast h
  have hgap1 : 20 * β / S < n := lt_of_le_of_lt (by rw [ha]; exact Nat.le_ceil _) hn1
  have hgap2 : (20 : ℝ) / (10 * β - 1) < n := lt_of_le_of_lt (by rw [hb]; exact Nat.le_ceil _) hn2
  have hnpos : 0 < n := lt_of_le_of_lt (by positivity) hgap2
  have hgapS : 20 * β < n * S := by
    rw [div_lt_iff₀ hSpos] at hgap1; linarith
  have hgapT : (20 : ℝ) < n * (10 * β - 1) := by
    rw [div_lt_iff₀ h10] at hgap2; linarith
  -- the quadratic inequality at `v`
  set d : ℝ := ((uncoveredAt G M v).card : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hq : 10 * d * d ≤ 10 * (uncoveredTot G M₀ : ℝ) + n * d + 20 * d := by
    rw [hn, hd]; exact_mod_cast hquad v
  have hqc : 10 * d * d ≤ 10 * (c * n ^ 2) + n * d + 20 * d := by
    have := (mul_le_mul_of_nonneg_left hK (by norm_num : (0:ℝ) ≤ 10))
    linarith
  by_contra hcon
  push_neg at hcon
  -- `d > βn`, and the increasing factor makes the quadratic bound worse at `d` than at `βn`
  have hfac0 : 0 < 10 * (β * n) - n - 20 := by linarith
  have hβn : 0 < β * n := by positivity
  have hprod : 0 < (d - β * n) * (10 * (d + β * n) - n - 20) :=
    mul_pos (by linarith) (by linarith)
  have hkey : 10 * (β * n) * (β * n) - (n + 20) * (β * n) < 10 * d * d - (n + 20) * d := by
    linarith only [hprod]
  have hB : 10 * d * d - (n + 20) * d ≤ 10 * c * n ^ 2 := by linarith only [hqc]
  have hCn : 20 * β * n < n ^ 2 * S := by
    have := mul_lt_mul_of_pos_right hgapS hnpos
    linarith only [this]
  rw [hS] at hCn
  linarith only [hkey, hB, hCn]

/-- **Consistency with the known route**: `Nibble.DenseGlobalSmallLeftover` and the exchange rate
re-derive `Nibble.denseTriangleNibbleDeg_of_tenth_lt`. -/
theorem denseTriangleNibbleDeg_of_tenth_lt_of_const (hglob : DenseGlobalSmallLeftover) {β : ℝ}
    (hβ : 1 / 10 < β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) := by
  set c : ℝ := (10 * β ^ 2 - β) / 20 with hc
  have hcpos : 0 < c := by
    have : 0 < 10 * β ^ 2 - β := by nlinarith
    rw [hc]; linarith
  refine denseTriangleNibbleDeg_of_leftoverConst (le_of_lt hcpos)
    (denseGlobalLeftoverConst_of_smallLeftover hglob hcpos) ?_
  -- `√(1 + 400c) < 20β − 1`
  have hpos : 0 < 20 * β - 1 := by linarith
  have hsq : 1 + 400 * c < (20 * β - 1) ^ 2 := by rw [hc]; nlinarith
  have hlt : Real.sqrt (1 + 400 * c) < 20 * β - 1 := by
    have := Real.sqrt_lt_sqrt (by positivity) hsq
    rwa [Real.sqrt_sq (le_of_lt hpos)] at this
  unfold starBoundOf; linarith

/-! ### Where the exchange rate crosses the unconditional wall -/

/-- **The crossing point is `c = 1/5`.**  The leftover constant `c` beats the unconditional
per-vertex wall `1/2` of `Nibble.dense_uncoveredAt_le_half` precisely when `c < 1/5`. -/
theorem leftoverConst_beats_half_iff {c : ℝ} (hc : 0 ≤ c) : starBoundOf c < 1 / 2 ↔ c < 1 / 5 := by
  have hs : Real.sqrt (1 + 400 * c) ^ 2 = 1 + 400 * c := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ Real.sqrt (1 + 400 * c) := Real.sqrt_nonneg _
  unfold starBoundOf
  constructor
  · intro h; nlinarith
  · intro h
    have : Real.sqrt (1 + 400 * c) < 9 := by nlinarith
    linarith

/-- **The exact relation between the two residuals**: `DenseGlobalSmallLeftover` is precisely the
conjunction of the constant-leftover residuals over all `c > 0`. -/
theorem denseGlobalSmallLeftover_iff_forall_const :
    DenseGlobalSmallLeftover ↔ ∀ c : ℝ, 0 < c → DenseGlobalLeftoverConst c := by
  constructor
  · intro h c hc; exact h c hc
  · intro h ε hε; exact h ε hε

/-- **Breaking the `1/2` wall needs only a single constant.**  Any certified leftover constant
`c < 1/5` at the Dross density already yields a per-vertex star bound `β < 1/2`, i.e. strictly beats
the unconditional wall `Nibble.dense_uncoveredAt_le_half`. -/
theorem beats_half_of_leftoverConst {c : ℝ} (hc : 0 ≤ c) (hlt : c < 1 / 5)
    (hglob : DenseGlobalLeftoverConst c) :
    ∃ β : ℝ, β < 1 / 2 ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
        ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
          ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) := by
  have hbound : starBoundOf c < 1 / 2 := (leftoverConst_beats_half_iff hc).mpr hlt
  refine ⟨(starBoundOf c + 1 / 2) / 2, by linarith, ?_⟩
  exact denseTriangleNibbleDeg_of_leftoverConst hc hglob (by linarith)

/-! ### The unconditional calibration `c = 1/2` -/

/-- **Unconditional**: at the Dross density the local moves already give the leftover constant
`c` for every `c > 1/2`.  (`2|uncoveredAt v| ≤ |V| + 4` for all `v`, summed over `v`.) -/
theorem denseGlobalLeftoverConst_half {c : ℝ} (hc : 1 / 2 < c) : DenseGlobalLeftoverConst c := by
  refine ⟨⌈2 / (c - 1 / 2)⌉₊, ?_⟩
  intro V _ _ G _ hV hdense
  obtain ⟨M, hM, hbound⟩ := dense_uncoveredAt_le_half G hdense
  refine ⟨M, hM, ?_⟩
  have hsum : 2 * uncoveredTot G M ≤ Fintype.card V * (Fintype.card V + 4) := by
    have : ∑ v : V, 2 * unDeg G M v ≤ ∑ _v : V, (Fintype.card V + 4) :=
      Finset.sum_le_sum (fun v _ => hbound v)
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
    exact this
  have hsumR : 2 * (uncoveredTot G M : ℝ)
      ≤ (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) + 4) := by exact_mod_cast hsum
  have hnR : 2 / (c - 1 / 2) ≤ (Fintype.card V : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hV)
  have hcpos : 0 < c - 1 / 2 := by linarith
  have hn0 : 0 < (Fintype.card V : ℝ) := lt_of_lt_of_le (by positivity) hnR
  have h4 : 2 ≤ (Fintype.card V : ℝ) * (c - 1 / 2) := (div_le_iff₀ hcpos).mp hnR
  nlinarith

/-- **The calibration is not yet useful**: routed through the exchange rate, the unconditional
constant `c = 1/2` gives only `(1 + √201)/20 ≈ 0.7589`, which is worse than the per-vertex bound
`1/2` proved directly in `Nibble.dense_uncoveredAt_le_half`. -/
theorem half_calibration_is_worse : 1 / 2 < starBoundOf (1 / 2) := by
  have h9 : (9 : ℝ) < Real.sqrt (1 + 400 * (1 / 2)) := by
    have : Real.sqrt 81 < Real.sqrt (1 + 400 * (1 / 2)) := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    rwa [show (81 : ℝ) = 9 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 9)] at this
  unfold starBoundOf; linarith

end Nibble
