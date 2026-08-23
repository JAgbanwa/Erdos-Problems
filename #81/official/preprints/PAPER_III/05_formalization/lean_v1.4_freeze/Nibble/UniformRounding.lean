/-
# Nibble — discharging `UniformTriangleRounding`

The single global hypothesis left in the `1/5` chain of `Nibble/FracPackingDense.lean` is
`Nibble.UniformTriangleRounding`: at the Dross density, an integral triangle packing whose uncovered
incidence count exceeds that of the *uniform* fractional triangle packing `1/(|V|-2)` by at most
`ε|V|²`.

This file discharges it.  The triangle hypergraph `triangleHypergraphSub G` on the edge type is
`3`-uniform with codegree `≤ 1` and degrees bounded by `|V| - 2`, so the deficiency-aware rounding
theorem `Nibble.Pad.exists_matching_defic` (the library's own nibble, fed through the explicit
degree-balancing padding of `Nibble/PadHypergraph.lean`) applies verbatim; and the uncovered count of
the uniform fractional packing is *exactly* twice the total deficiency divided by `|V| - 2`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.FracPackingDense
import Nibble.PadRounding

open Finset Hypergraph SimpleGraph

namespace Nibble

open YusterE Pad

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The hypergraph degree of an edge in the triangle hypergraph is its common-neighbour count. -/
theorem triangleSub_degree_eq_commonNbrs (G : SimpleGraph V) [DecidableRel G.Adj] (E : EdgeV G) :
    degree (triangleHypergraphSub G) E = (commonNbrs G E).card := by
  rw [triangleHypergraphSub_degree_eq, ← card_trianglesThrough_eq,
    card_trianglesThrough_eq_commonNbrs]

/-- Every edge lies in at most `|V| - 2` triangles. -/
theorem triangleSub_degree_le (G : SimpleGraph V) [DecidableRel G.Adj] (E : EdgeV G) :
    degree (triangleHypergraphSub G) E ≤ Fintype.card V - 2 := by
  rw [triangleSub_degree_eq_commonNbrs]
  have := card_commonNbrs_le G E
  omega

/-- **The uniform fractional packing's uncovered count is twice the total deficiency over `d`.** -/
theorem fracUncoveredTot_uniform_eq_defic (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : 3 ≤ Fintype.card V) :
    fracUncoveredTot G (fun _ => 1 / ((Fintype.card V : ℝ) - 2))
      = 2 * (deficTot (triangleHypergraphSub G) (Fintype.card V - 2) : ℝ)
          / ((Fintype.card V : ℝ) - 2) := by
  have hV2 : 2 ≤ Fintype.card V := by omega
  have hnR : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV
  have hDpos : (0 : ℝ) < (Fintype.card V : ℝ) - 2 := by linarith only [hnR]
  set d : ℕ := Fintype.card V - 2 with hddef
  have hD : (d : ℝ) = (Fintype.card V : ℝ) - 2 := by
    rw [hddef, Nat.cast_sub hV2]; norm_num
  -- deficiencies complement degrees
  have hsum : (∑ E : EdgeV G, degree (triangleHypergraphSub G) E)
      + deficTot (triangleHypergraphSub G) d = Fintype.card (EdgeV G) * d := by
    rw [deficTot, ← Finset.sum_add_distrib]
    have hterm : ∀ E : EdgeV G, degree (triangleHypergraphSub G) E
        + defic (triangleHypergraphSub G) d E = d := by
      intro E
      have := triangleSub_degree_le G E
      simp only [defic, hddef] at *
      omega
    rw [Finset.sum_congr rfl (fun E _ => hterm E), Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  have hsumR : (∑ E : EdgeV G, ((commonNbrs G E).card : ℝ))
      + (deficTot (triangleHypergraphSub G) d : ℝ)
      = (Fintype.card (EdgeV G) : ℝ) * (d : ℝ) := by
    have hc : ((((∑ E : EdgeV G, degree (triangleHypergraphSub G) E)
        + deficTot (triangleHypergraphSub G) d : ℕ)) : ℝ)
        = ((Fintype.card (EdgeV G) * d : ℕ) : ℝ) := by exact_mod_cast hsum
    push_cast at hc
    rw [← hc]
    congr 1
    exact Finset.sum_congr rfl fun E _ => by
      rw [triangleSub_degree_eq_commonNbrs]
  rw [fracUncoveredTot_uniform G]
  rw [hD] at hsumR
  field_simp
  linarith only [hsumR]

/-- **The uncovered incidence count of a matching**, in terms of its size. -/
theorem uncoveredTot_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M) :
    (uncoveredTot G M : ℝ) = 2 * ((Fintype.card (EdgeV G) : ℝ) - 3 * (M.card : ℝ)) := by
  have h1 := two_mul_card_uncovered G M
  have h2 := card_uncovered_add G hM
  have h3 : uncoveredTot G M + 2 * (3 * M.card) = 2 * Fintype.card (EdgeV G) := by omega
  have h4 : ((uncoveredTot G M + 2 * (3 * M.card) : ℕ) : ℝ)
      = ((2 * Fintype.card (EdgeV G) : ℕ) : ℝ) := by exact_mod_cast h3
  push_cast at h4
  linarith only [h4]

/-- The number of edges is at most `|V|²`. -/
theorem card_edgeV_le_sq (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * (Fintype.card (EdgeV G) : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
  rw [two_mul_card_edgeV G]
  calc ∑ v : V, (G.degree v : ℝ) ≤ ∑ _v : V, (Fintype.card V : ℝ) := by
        refine Finset.sum_le_sum fun v _ => ?_
        have : G.degree v ≤ Fintype.card V := by
          rw [SimpleGraph.degree]
          simpa using Finset.card_le_univ (G.neighborFinset v)
        exact_mod_cast this
    _ = (Fintype.card V : ℝ) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring

/-- At the Dross density the number of edges is at least `(9/20)|V|²`. -/
theorem card_edgeV_ge_dense (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) :
    (9 / 20) * (Fintype.card V : ℝ) ^ 2 ≤ (Fintype.card (EdgeV G) : ℝ) := by
  have hhand : 2 * (Fintype.card (EdgeV G) : ℝ) = ∑ v : V, (G.degree v : ℝ) :=
    two_mul_card_edgeV G
  have hmin : ∀ v : V, ((G.minDegree : ℕ) : ℝ) ≤ (G.degree v : ℝ) := fun v => by
    exact_mod_cast G.minDegree_le_degree v
  have hdense' : 9 * (Fintype.card V : ℝ) ≤ 10 * ((G.minDegree : ℕ) : ℝ) := by
    exact_mod_cast hdense
  have hnnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  have hlow : (Fintype.card V : ℝ) * ((G.minDegree : ℕ) : ℝ) ≤ ∑ v : V, (G.degree v : ℝ) := by
    calc (Fintype.card V : ℝ) * ((G.minDegree : ℕ) : ℝ)
        = ∑ _v : V, ((G.minDegree : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ ≤ ∑ v : V, (G.degree v : ℝ) := Finset.sum_le_sum fun v _ => hmin v
  nlinarith only [hhand, hlow, hdense', hnnn]

/-- **The rounding step holds unconditionally.** -/
theorem uniformTriangleRounding_holds : UniformTriangleRounding := by
  intro ε hε
  obtain ⟨d₀, C, hround⟩ := Pad.exists_matching_defic (ε / 2) (by positivity)
  set C' : ℝ := max C 1 with hC'def
  have hC'pos : (0 : ℝ) < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCC' : C ≤ C' := le_max_left _ _
  refine ⟨max (d₀ + 2) (max 3 (⌈C' * 20 / 9⌉₊ + 1)), ?_⟩
  intro V _ _ G _ hV hdense
  have hn3 : 3 ≤ Fintype.card V := le_trans (le_trans (le_max_left 3 _) (le_max_right _ _)) hV
  have hnC : ⌈C' * 20 / 9⌉₊ + 1 ≤ Fintype.card V :=
    le_trans (le_trans (le_max_right 3 _) (le_max_right _ _)) hV
  have hd0 : d₀ + 2 ≤ Fintype.card V := le_trans (le_max_left _ _) hV
  have hnR : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn3
  set d : ℕ := Fintype.card V - 2 with hddef
  have hdd0 : d₀ ≤ d := by omega
  have hD : (d : ℝ) = (Fintype.card V : ℝ) - 2 := by
    rw [hddef, Nat.cast_sub (by omega : 2 ≤ Fintype.card V)]; norm_num
  have hDpos : (0 : ℝ) < (d : ℝ) := by rw [hD]; linarith
  -- the size hypothesis of the abstract rounding theorem
  have hedges := card_edgeV_ge_dense G hdense
  have hCn : C' * 20 / 9 ≤ (Fintype.card V : ℝ) := by
    have h1 : (C' * 20 / 9 : ℝ) ≤ (⌈C' * 20 / 9⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈C' * 20 / 9⌉₊ : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast (by omega : ⌈C' * 20 / 9⌉₊ ≤ Fintype.card V)
    linarith
  have hCd : C * (d : ℝ) ≤ (Fintype.card (EdgeV G) : ℝ) := by
    have hdle : (d : ℝ) ≤ (Fintype.card V : ℝ) := by rw [hD]; linarith
    have h1 : C * (d : ℝ) ≤ C' * (Fintype.card V : ℝ) := by nlinarith
    have h2 : C' * (Fintype.card V : ℝ) ≤ (9 / 20) * (Fintype.card V : ℝ) ^ 2 := by nlinarith
    linarith
  obtain ⟨M, hM, hMle⟩ := hround (triangleHypergraphSub G) d hdd0
    (triangleHypergraphSub_uniform G)
    (fun x y hxy => triangleHypergraphSub_codegree_le_one G hxy)
    (triangleSub_degree_le G) hCd
  refine ⟨M, hM, ?_⟩
  rw [uncoveredTot_eq G hM, fracUncoveredTot_uniform_eq_defic G hn3, ← hddef, ← hD]
  have hNsq := card_edgeV_le_sq G
  have hεN : ε * (Fintype.card (EdgeV G) : ℝ) ≤ ε * ((Fintype.card V : ℝ) ^ 2 / 2) := by
    have : (Fintype.card (EdgeV G) : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 2 := by linarith
    exact mul_le_mul_of_nonneg_left this (le_of_lt hε)
  have hsq : (0 : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by positivity
  have hdiv : 2 * ((deficTot (triangleHypergraphSub G) d : ℝ) / (d : ℝ))
      = 2 * (deficTot (triangleHypergraphSub G) d : ℝ) / (d : ℝ) := by ring
  linarith only [hMle, hεN, hsq, hdiv]

/-- **The `1/5` barrier is crossed unconditionally.** -/
theorem denseGlobalLeftoverConst_195 : DenseGlobalLeftoverConst (195 / 1000) :=
  denseGlobalLeftoverConst_of_uniformTriangleRounding uniformTriangleRounding_holds

/-- **The target, unconditionally.** -/
theorem leftoverConst_below_fifth : ∃ c : ℝ, c < 1 / 5 ∧ DenseGlobalLeftoverConst c :=
  leftoverConst_below_fifth_of_uniformTriangleRounding uniformTriangleRounding_holds

end Nibble
