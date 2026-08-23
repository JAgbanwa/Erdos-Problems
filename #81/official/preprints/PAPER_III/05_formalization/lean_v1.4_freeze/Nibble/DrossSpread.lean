/-
# Nibble — the *quantitatively spread* Dross input

`Nibble.DrossFractionalQuantSpread` (see `Nibble/FracRounding.lean`) is the single global input that
closes the whole `1/5` chain: at the Dross density `9|V| ≤ 10 δ(G)` a fractional triangle
decomposition all of whose weights are at most `C/|V|`.  The rounding half is unconditional
(`Nibble.spreadFracRounding_of_decomp`), so the spread decomposition alone yields
`Nibble.DenseGlobalSmallLeftover` and everything below it.

This file

* normalises the target as `Nibble.HasSpreadFracTriangleDecomp G K` — a fractional triangle
  decomposition of `G` with all weights at most `K/|V|`;
* isolates the residual in *correction* form, `Nibble.IsUniformDeficiencyCorrection`: a **signed**
  perturbation `x` of the uniform triangle weighting `1/(|V|-2)`, bounded by `1/(|V|-2)` in absolute
  value, whose coverage at every edge equals the uniform weighting's *deficiency*
  `1 - codeg(e)/(|V|-2)`;
* proves that the two are **equivalent** (`Nibble.exists_correction_iff_bounded_decomp`) — no loss
  of strength in the reduction — and that the correction form implies the target with `C = 3`
  (`Nibble.drossFractionalQuantSpread_of_correction`), hence the entire downstream chain;
* proves the residual **unconditionally for codegree-regular graphs**
  (`Nibble.isUniformDeficiencyCorrection_of_codegree_const`,
  `Nibble.hasSpreadFracTriangleDecomp_of_codegree_const`), which at the Dross density covers `Kₙ`,
  `Kₙ` minus a perfect matching, and the balanced complete multipartite graphs with at least ten
  parts, so the residual statement is not vacuous;
* records the **sharpness** of the constant: at the Dross density no exact decomposition can have
  all weights below `1/(|V|-2)`, so `C ≥ 1` is forced
  (`Nibble.exists_weight_ge_of_fracTriangleDecomp`).

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.NearComplete
import Nibble.FracPackingDense

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Spread fractional triangle decompositions -/

/-- `G` carries a **`K`-spread fractional triangle decomposition**: a fractional triangle
decomposition all of whose weights are at most `K/|V|`. -/
def HasSpreadFracTriangleDecomp (G : SimpleGraph V) [DecidableRel G.Adj] (K : ℝ) : Prop :=
  ∃ w : Finset (EdgeV G) → ℝ, IsFracTriangleDecomp G w ∧
    ∀ T ∈ triangleHypergraphSub G, w T ≤ K / (Fintype.card V : ℝ)

/-- Every triangle of `G` contains an edge. -/
theorem exists_edge_of_mem_triangleHypergraphSub (G : SimpleGraph V) [DecidableRel G.Adj]
    {T : Finset (EdgeV G)} (hT : T ∈ triangleHypergraphSub G) : ∃ e : EdgeV G, e ∈ T := by
  have hcard : T.card = 3 := triangleHypergraphSub_uniform G T hT
  have : T.Nonempty := Finset.card_pos.mp (by omega)
  exact this

/-- A graph with an edge has a vertex. -/
theorem nonempty_of_edgeV (G : SimpleGraph V) [DecidableRel G.Adj] (e : EdgeV G) : Nonempty V := by
  obtain ⟨u, -, -, -, -⟩ := exists_pair_of_edgeV G e
  exact ⟨u⟩

/-- **The degenerate case.**  A graph on an empty vertex set has no edges and no triangles, so the
zero weighting is a fractional triangle decomposition satisfying every weight bound. -/
theorem exists_decomp_of_not_nonempty (G : SimpleGraph V) [DecidableRel G.Adj]
    (hne : ¬ Nonempty V) (K : ℝ) :
    ∃ w : Finset (EdgeV G) → ℝ, IsFracTriangleDecomp G w ∧
      ∀ T ∈ triangleHypergraphSub G, w T ≤ K := by
  refine ⟨fun _ => 0, ⟨fun _ _ => le_rfl, fun e => absurd (nonempty_of_edgeV G e) hne⟩,
    fun T hT => ?_⟩
  obtain ⟨e, -⟩ := exists_edge_of_mem_triangleHypergraphSub G hT
  exact absurd (nonempty_of_edgeV G e) hne

omit [DecidableEq V] in
/-- **At the Dross density a nonempty graph has at least ten vertices.**  `δ(G) ≤ |V| - 1`, so
`9|V| ≤ 10 δ(G)` forces `9|V| ≤ 10|V| - 10`. -/
theorem ten_le_card_of_dense (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) (v : V) : 10 ≤ Fintype.card V := by
  have h1 : G.minDegree ≤ G.degree v := G.minDegree_le_degree v
  have h2 : G.degree v < Fintype.card V := G.degree_lt_card_verts v
  omega

/-! ### The residual, in correction form -/

/-- **A bounded uniform-deficiency correction.**  A signed weighting `x` of the triangles of `G`,
bounded by the uniform weight `1/(|V|-2)` in absolute value, whose total weight on the triangles
through each edge `e` equals the deficiency `1 - codeg(e)/(|V|-2)` of the uniform weighting. -/
def IsUniformDeficiencyCorrection (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : Finset (EdgeV G) → ℝ) : Prop :=
  (∀ T ∈ triangleHypergraphSub G, |x T| ≤ 1 / ((Fintype.card V : ℝ) - 2)) ∧
    ∀ e : EdgeV G, ∑ T ∈ trianglesThrough G e, x T
      = 1 - ((commonNbrs G e).card : ℝ) / ((Fintype.card V : ℝ) - 2)

/-- **The degenerate case, in correction form.** -/
theorem exists_correction_of_not_nonempty (G : SimpleGraph V) [DecidableRel G.Adj]
    (hne : ¬ Nonempty V) :
    ∃ x : Finset (EdgeV G) → ℝ, IsUniformDeficiencyCorrection G x := by
  refine ⟨fun _ => 0, fun T hT => ?_, fun e => absurd (nonempty_of_edgeV G e) hne⟩
  obtain ⟨e, -⟩ := exists_edge_of_mem_triangleHypergraphSub G hT
  exact absurd (nonempty_of_edgeV G e) hne

/-- **The correction form is equivalent to a decomposition with weights `≤ 2/(|V|-2)`.**
Adding the uniform weighting `1/(|V|-2)` to a bounded correction gives a fractional triangle
decomposition with all weights in `[0, 2/(|V|-2)]`, and subtracting it inverts the passage. -/
theorem exists_correction_iff_bounded_decomp (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : 3 ≤ Fintype.card V) :
    (∃ x : Finset (EdgeV G) → ℝ, IsUniformDeficiencyCorrection G x) ↔
      ∃ w : Finset (EdgeV G) → ℝ, IsFracTriangleDecomp G w ∧
        ∀ T ∈ triangleHypergraphSub G, w T ≤ 2 / ((Fintype.card V : ℝ) - 2) := by
  have h3 : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV
  have h2 : (0 : ℝ) < (Fintype.card V : ℝ) - 2 := by linarith
  set t : ℝ := 1 / ((Fintype.card V : ℝ) - 2) with ht_def
  have htpos : 0 < t := by rw [ht_def]; positivity
  have hcard : ∀ e : EdgeV G,
      ((trianglesThrough G e).card : ℝ) = ((commonNbrs G e).card : ℝ) := by
    intro e
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (card_trianglesThrough_eq_commonNbrs G e)
  constructor
  · rintro ⟨x, hxb, hxs⟩
    refine ⟨fun T => t + x T, ⟨fun T hT => ?_, fun e => ?_⟩, fun T hT => ?_⟩
    · have := abs_le.mp (hxb T hT)
      linarith only [this.1]
    · rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hxs e, hcard e, ht_def]
      field_simp
      ring
    · have := abs_le.mp (hxb T hT)
      have : x T ≤ t := this.2
      rw [ht_def] at this ⊢
      have : (1 : ℝ) / ((Fintype.card V : ℝ) - 2) + x T
          ≤ 1 / ((Fintype.card V : ℝ) - 2) + 1 / ((Fintype.card V : ℝ) - 2) := by linarith
      calc (1 : ℝ) / ((Fintype.card V : ℝ) - 2) + x T
          ≤ 1 / ((Fintype.card V : ℝ) - 2) + 1 / ((Fintype.card V : ℝ) - 2) := this
        _ = 2 / ((Fintype.card V : ℝ) - 2) := by ring
  · rintro ⟨w, ⟨hwnn, hwsum⟩, hwb⟩
    refine ⟨fun T => w T - t, fun T hT => ?_, fun e => ?_⟩
    · have h1 : 0 ≤ w T := hwnn T hT
      have h2' : w T ≤ 2 * t := by
        have := hwb T hT
        rw [ht_def]
        calc w T ≤ 2 / ((Fintype.card V : ℝ) - 2) := this
          _ = 2 * (1 / ((Fintype.card V : ℝ) - 2)) := by ring
      rw [abs_le]
      constructor <;> [linarith; linarith]
    · rw [Finset.sum_sub_distrib, hwsum e, Finset.sum_const, nsmul_eq_mul, hcard e, ht_def]
      field_simp

/-! ### The reduction to `DrossFractionalQuantSpread` -/

/-- **The residual as a single global statement**: at the Dross density the uniform triangle
weighting `1/(|V|-2)` admits a correction bounded by `1/(|V|-2)`. -/
def DrossUniformCorrection : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    9 * Fintype.card V ≤ 10 * G.minDegree →
    ∃ x : Finset (EdgeV G) → ℝ, IsUniformDeficiencyCorrection G x

/-- **The reduction.**  A bounded uniform-deficiency correction at the Dross density gives the
quantitatively spread Dross theorem with `C = 3`. -/
theorem drossFractionalQuantSpread_of_correction (h : DrossUniformCorrection) :
    DrossFractionalQuantSpread := by
  refine ⟨3, by norm_num, ?_⟩
  intro V _ _ G _ hdense
  by_cases hne : Nonempty V
  · obtain ⟨v⟩ := hne
    have hten : 10 ≤ Fintype.card V := ten_le_card_of_dense G hdense v
    have hV : 3 ≤ Fintype.card V := by omega
    have hten' : (10 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hten
    obtain ⟨w, hw, hwb⟩ :=
      (exists_correction_iff_bounded_decomp G hV).mp (h G hdense)
    refine ⟨w, hw, fun T hT => ?_⟩
    refine le_trans (hwb T hT) ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  · exact exists_decomp_of_not_nonempty G hne _

/-- **A decomposition with weights `≤ 2/(|V|-2)` at the Dross density** — the target of the
reduction, in the form in which it is equivalent to `Nibble.DrossUniformCorrection`. -/
def DrossBoundedDecomp : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    9 * Fintype.card V ≤ 10 * G.minDegree →
    ∃ w : Finset (EdgeV G) → ℝ, IsFracTriangleDecomp G w ∧
      ∀ T ∈ triangleHypergraphSub G, w T ≤ 2 / ((Fintype.card V : ℝ) - 2)

/-- **The residual loses nothing**: the correction form and the bounded-decomposition form of the
spread Dross theorem are equivalent. -/
theorem drossUniformCorrection_iff_boundedDecomp :
    DrossUniformCorrection ↔ DrossBoundedDecomp := by
  constructor
  · intro h V _ _ G _ hdense
    by_cases hne : Nonempty V
    · obtain ⟨v⟩ := hne
      have hV : 3 ≤ Fintype.card V := by
        have := ten_le_card_of_dense G hdense v; omega
      exact (exists_correction_iff_bounded_decomp G hV).mp (h G hdense)
    · exact exists_decomp_of_not_nonempty G hne _
  · intro h V _ _ G _ hdense
    by_cases hne : Nonempty V
    · obtain ⟨v⟩ := hne
      have hV : 3 ≤ Fintype.card V := by
        have := ten_le_card_of_dense G hdense v; omega
      exact (exists_correction_iff_bounded_decomp G hV).mpr (h G hdense)
    · exact exists_correction_of_not_nonempty G hne

/-- **The residual implies Dross's theorem.**  Honest bookkeeping: the residual is at least as
strong as `Nibble.DrossFractional`, so it is a genuine (research-level) input, not a repackaging of
something weaker. -/
theorem drossFractional_of_correction (h : DrossUniformCorrection) : DrossFractional := by
  intro V _ _ G _ hdense
  obtain ⟨C, -, hmain⟩ := drossFractionalQuantSpread_of_correction h
  obtain ⟨w, hw, -⟩ := hmain G hdense
  exact ⟨w, hw⟩

/-- **The residual closes the `o(|V|²)` leftover.** -/
theorem denseGlobalSmallLeftover_of_correction (h : DrossUniformCorrection) :
    DenseGlobalSmallLeftover :=
  denseGlobalSmallLeftover_of_drossSpread
    (drossFractionalSpread_of_quant (drossFractionalQuantSpread_of_correction h))

/-- **The residual crosses the `1/5` wall.** -/
theorem leftoverConst_below_fifth_of_correction (h : DrossUniformCorrection) :
    ∃ c : ℝ, c < 1 / 5 ∧ DenseGlobalLeftoverConst c :=
  leftoverConst_below_fifth_of_drossSpread
    (drossFractionalSpread_of_quant (drossFractionalQuantSpread_of_correction h))

/-- **The residual gives the full `1/10` per-vertex bound**, i.e. `Nibble.DenseTriangleNibbleDeg`
for every `β > 1/10`. -/
theorem denseTriangleNibbleDeg_of_correction (h : DrossUniformCorrection) {β : ℝ}
    (hβ : 1 / 10 < β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) :=
  denseTriangleNibbleDeg_of_drossSpread
    (drossFractionalSpread_of_quant (drossFractionalQuantSpread_of_correction h)) hβ

/-! ### The residual is not vacuous: codegree-regular graphs -/

/-- **Codegree-regular graphs admit a bounded uniform-deficiency correction.**  If every edge of `G`
lies in exactly `d` triangles with `2d ≥ |V| - 2`, the constant correction `1/d - 1/(|V|-2)` works.
-/
theorem isUniformDeficiencyCorrection_of_codegree_const (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 0 < d) (hV : 3 ≤ Fintype.card V)
    (hbig : (Fintype.card V : ℝ) - 2 ≤ 2 * (d : ℝ))
    (hreg : ∀ e : EdgeV G, (commonNbrs G e).card = d) :
    IsUniformDeficiencyCorrection G
      (fun _ => 1 / (d : ℝ) - 1 / ((Fintype.card V : ℝ) - 2)) := by
  have h3 : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV
  have h2 : (0 : ℝ) < (Fintype.card V : ℝ) - 2 := by linarith
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hle : 1 / (d : ℝ) ≤ 2 / ((Fintype.card V : ℝ) - 2) := by
    rw [div_le_div_iff₀ hdR h2]
    linarith
  have hge : ∀ e : EdgeV G, 1 / ((Fintype.card V : ℝ) - 2) ≤ 1 / (d : ℝ) := by
    intro e
    have h1 : ((commonNbrs G e).card : ℝ) + 2 ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast card_commonNbrs_le G e
    rw [hreg e] at h1
    rw [div_le_div_iff₀ h2 hdR]
    linarith
  refine ⟨fun T hT => ?_, fun e => ?_⟩
  · obtain ⟨e, -⟩ := exists_edge_of_mem_triangleHypergraphSub G hT
    have hge' := hge e
    have htwo : 2 / ((Fintype.card V : ℝ) - 2) = 2 * (1 / ((Fintype.card V : ℝ) - 2)) := by ring
    rw [htwo] at hle
    have hgoal : |1 / (d : ℝ) - 1 / ((Fintype.card V : ℝ) - 2)|
        ≤ 1 / ((Fintype.card V : ℝ) - 2) := by
      rw [abs_le]
      constructor <;> linarith
    exact hgoal
  · rw [Finset.sum_const, nsmul_eq_mul, card_trianglesThrough_eq_commonNbrs, hreg e, mul_sub,
      mul_one_div, div_self (ne_of_gt hdR), mul_one_div]

/-- **Codegree-regular graphs at the Dross density carry a `5/4`-spread fractional triangle
decomposition.**  The uniform weighting `1/d` is exact, and `d ≥ (4/5)|V|` at this density. -/
theorem hasSpreadFracTriangleDecomp_of_codegree_const (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 0 < d) (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (hreg : ∀ e : EdgeV G, (commonNbrs G e).card = d) :
    HasSpreadFracTriangleDecomp G (5 / 4) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  refine ⟨fun _ => 1 / (d : ℝ), ⟨fun T _ => by positivity, fun e => ?_⟩, fun T hT => ?_⟩
  · rw [Finset.sum_const, nsmul_eq_mul, card_trianglesThrough_eq_commonNbrs, hreg e, mul_one_div,
      div_self (ne_of_gt hdR)]
  · -- the bound `1/d ≤ (5/4)/|V|`
    obtain ⟨e, -⟩ := exists_edge_of_mem_triangleHypergraphSub G hT
    obtain ⟨u, -, -, -, -⟩ := exists_pair_of_edgeV G e
    have hten : 10 ≤ Fintype.card V := ten_le_card_of_dense G hdense u
    have htenR : (10 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hten
    have hmin : (1 - 1 / 10) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) := by
      have : (9 : ℝ) * (Fintype.card V : ℝ) ≤ 10 * (G.minDegree : ℝ) := by exact_mod_cast hdense
      linarith
    have hcod := card_commonNbrs_ge_of_minDegree G hmin e
    rw [hreg e] at hcod
    have h4 : (4 / 5 : ℝ) * (Fintype.card V : ℝ) ≤ (d : ℝ) := by linarith
    rw [div_le_div_iff₀ hdR (by linarith)]
    linarith

/-- **The complete graph.**  `Kₙ` carries a `5/4`-spread fractional triangle decomposition once
`n ≥ 10`; here the uniform weighting is `1/(n-2)`. -/
theorem hasSpreadFracTriangleDecomp_top (hV : 10 ≤ Fintype.card V) :
    HasSpreadFracTriangleDecomp (⊤ : SimpleGraph V) (5 / 4) := by
  have hV3 : 3 ≤ Fintype.card V := by omega
  have hVR : (10 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV
  have h2 : (0 : ℝ) < (Fintype.card V : ℝ) - 2 := by linarith
  refine ⟨_, isFracTriangleDecomp_top hV3, fun T _ => ?_⟩
  have hgoal : (1 : ℝ) / ((Fintype.card V : ℝ) - 2) ≤ (5 / 4) / (Fintype.card V : ℝ) := by
    rw [div_le_div_iff₀ h2 (by linarith)]
    linarith
  exact hgoal

/-! ### Sharpness of the constant -/

/-- **No exact decomposition is spread below `1/(|V|-2)`.**  Every edge lies in at most `|V| - 2`
triangles, so in any fractional triangle decomposition some triangle through a given edge carries
weight at least `1/(|V|-2)`.  In particular the constant `C` of
`Nibble.DrossFractionalQuantSpread` cannot be taken below `1`. -/
theorem exists_weight_ge_of_fracTriangleDecomp (G : SimpleGraph V) [DecidableRel G.Adj]
    {w : Finset (EdgeV G) → ℝ} (hw : IsFracTriangleDecomp G w) (e : EdgeV G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ T ∈ trianglesThrough G e, 1 / ((Fintype.card V : ℝ) - 2) ≤ w T := by
  classical
  have h3 : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV
  have h2 : (0 : ℝ) < (Fintype.card V : ℝ) - 2 := by linarith
  have hsum := hw.2 e
  by_contra hcon
  push_neg at hcon
  have hlt : ∑ T ∈ trianglesThrough G e, w T
      < ∑ _T ∈ trianglesThrough G e, 1 / ((Fintype.card V : ℝ) - 2) := by
    refine Finset.sum_lt_sum_of_nonempty ?_ (fun T hT => hcon T hT)
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.sum_empty] at hsum
    exact absurd hsum (by norm_num)
  rw [hsum, Finset.sum_const, nsmul_eq_mul, card_trianglesThrough_eq_commonNbrs] at hlt
  have hle : ((commonNbrs G e).card : ℝ) + 2 ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast card_commonNbrs_le G e
  rw [mul_one_div, lt_div_iff₀ h2] at hlt
  linarith

end Nibble
