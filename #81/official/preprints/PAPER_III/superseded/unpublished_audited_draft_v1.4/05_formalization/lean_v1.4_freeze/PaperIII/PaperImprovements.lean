import PaperIII.PackingCorollaries
import PaperIII.Prop_10_1
import PaperIII.Main
import PaperIII.ShiftedCenterRobust
import PaperIII.Addenda
import PaperIII.E_4_2
import PaperIII.DiracMatching
import PaperIII.E_8_Divisible
import Nibble.PaperImprovements
import Nibble.DenseNearRegular
import Nibble.DenseTriNibbleMaxDeg
import Nibble.StrongDualityInst
import Nibble.YusterFracUpper
import Nibble.YusterNu3
import Nibble.YusterEdgeType
import Nibble.YusterSubBridge
import Nibble.YusterSubDegree

/-!
# Paper III — formalization byproducts for the manuscript

This module collects low-cost mathematical strengthenings surfaced by the Lean development.
The statements are wrappers around already-proved core lemmas, with stable names suitable for
the paper's "formalization byproducts" paragraph.
-/

namespace PaperIII

open SplitGraph
open scoped Classical

/-- Packing-native factor-assignment bound from §5.1. -/
theorem Byproduct_factorization_assignment_packing (G : SplitGraph) :
    ∀ σ : Fin (rp G.p) ↪ Fin G.q,
      (∑ j, (factorEdges G (Classical.choose (complete_graph_edge_coloring G.p))
        j (σ j)).card : ℝ) ≤ G.nu3' :=
  factorization_assignment_packing G

/-- Packing-native double-factorization bound from §5.2. -/
theorem Byproduct_double_factorization_packing (G : SplitGraph)
    (hrp : rp G.p ≤ G.q) (hq2 : 2 ≤ G.q) :
    (1 / (G.q : ℝ)) * ∑ i, ((G.d i).choose 2 : ℝ)
      + ((G.doubledFactors : ℝ) / (rp G.p : ℝ)) * (G.dispersionV : ℝ)
        / ((G.q : ℝ) * ((G.q : ℝ) - 1)) ≤ (G.nu3' : ℝ) :=
  double_factorization_packing G hrp hq2

/-- Packing-native reserved-gain bound from §7. -/
theorem Byproduct_reserved_gain_packing_bound_subset (G : SplitGraph) (R : Finset (Fin G.p))
    {J : Finset (Fin G.q)}
    (hb2 : 2 ≤ G.p - R.card)
    (hJrb : rp (G.p - R.card) ≤ J.card)
    (hbrho : rp R.card ≤ G.p - R.card)
    (hhost : ∀ i ∈ J,
      max R.card (J.card - rp (G.p - R.card)) ≤ (G.N i \ R).card) :
    (((G.p - R.card).choose 2 : ℕ) : ℝ) + ((R.card.choose 2 : ℕ) : ℝ)
      - (((2 * (G.p - R.card) - 1 : ℕ) : ℝ) * (ShiftedCenter.AJ G R J : ℝ) -
          (ShiftedCenter.A2J G R J : ℝ)) / (2 * (J.card : ℝ))
      + (1 - ShiftedCenter.thetaR G R) *
          ((J.card - rp (G.p - R.card) : ℕ) : ℝ) * (ShiftedCenter.BJ G R J : ℝ) /
            (J.card : ℝ)
    ≤ (G.nu3' : ℝ) :=
  reserved_gain_packing_bound_subset G R J hb2 hbrho hJrb hhost

/-- Sharp short-corridor arithmetic constant: `C_corr = 3/2` from threshold `p ≥ 37`. -/
theorem Byproduct_short_corridor_constant_three_halves {p s : ℕ}
    (hp : 37 ≤ p) (hs : s ^ 2 ≤ 36 * p) :
    (p : ℝ) / 2 + ((s : ℝ) ^ 2 - 6 * (s : ℝ) + 3) / 12
      ≤ (3 / 2) * (3 * (p : ℝ) - (s : ℝ)) :=
  short_corridor_sharp hp hs

/-- Sharp low-corridor `Φ` bound with linear constant `3/2`. -/
theorem Byproduct_low_corridor_phi_three_halves (G : SplitGraph) (hp : 37 ≤ G.p)
    (hs0 : 0 ≤ G.s) (hs : (G.s : ℝ) ^ 2 ≤ 36 * (G.p : ℝ)) :
    ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + (3 / 2) * (G.n : ℝ) :=
  Prop_10_1_low G hp hs0 hs

/-- Mid-corridor part of Prop. 10.1: in this corridor the formalized bound has no linear loss. -/
theorem Byproduct_mid_corridor_phi_no_linear_loss (G : SplitGraph) (hp : 2304 ≤ G.p)
    (hs : 36 * (G.p : ℝ) ≤ (G.s : ℝ) ^ 2) (hs8 : 8 * (G.s : ℝ) ≤ (G.p : ℝ))
    (hdeg : ∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + 1 < (G.d i : ℝ)) :
    ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 :=
  Prop_10_1_mid G hp hs hs8 hdeg

/-- High-ratio range: factorization controls the range `q ≥ 2p - 1` with constant `1/2`. -/
theorem Byproduct_high_ratio_phi_half_linear (G : SplitGraph) (hq : 2 * G.p ≤ G.q + 1) :
    ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + (G.n : ℝ) / 2 :=
  Phi_le_high_ratio G hq

/-- Clique-partition is controlled by the potential `Φ`; this is the bridge from potential bounds
to clique-partition bounds. -/
theorem Byproduct_cp_le_Phi (G : SplitGraph) :
    (G.cp : ℤ) ≤ G.Phi :=
  cp_le_Phi G

/-- Low-corridor clique-partition bound with the same sharp `3/2` linear constant. -/
theorem Byproduct_low_corridor_cp_three_halves (G : SplitGraph) (hp : 37 ≤ G.p)
    (hs0 : 0 ≤ G.s) (hs : (G.s : ℝ) ^ 2 ≤ 36 * (G.p : ℝ)) :
    (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + (3 / 2) * (G.n : ℝ) :=
  Corollary_12_2_bound G hp hs0 hs

/-- Mid-corridor clique-partition bound: the observable `cp` inherits the no-linear-loss
potential bound. -/
theorem Byproduct_mid_corridor_cp_no_linear_loss (G : SplitGraph) (hp : 2304 ≤ G.p)
    (hs : 36 * (G.p : ℝ) ≤ (G.s : ℝ) ^ 2) (hs8 : 8 * (G.s : ℝ) ≤ (G.p : ℝ))
    (hdeg : ∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + 1 < (G.d i : ℝ)) :
    (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 := by
  have hcp : (G.cp : ℝ) ≤ ((G.Phi : ℤ) : ℝ) := by
    exact_mod_cast cp_le_Phi G
  exact hcp.trans (Prop_10_1_mid G hp hs hs8 hdeg)

/-- High-ratio clique-partition bound: in the range `q ≥ 2p - 1`, `cp` has linear constant `1/2`. -/
theorem Byproduct_high_ratio_cp_half_linear (G : SplitGraph) (hq : 2 * G.p ≤ G.q + 1) :
    (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + (G.n : ℝ) / 2 := by
  have hcp : (G.cp : ℝ) ≤ ((G.Phi : ℤ) : ℝ) := by
    exact_mod_cast cp_le_Phi G
  exact hcp.trans (Phi_le_high_ratio G hq)

/-- Mesoscopic-localization interface: once the high-degree/eventual regime is excluded from some
threshold `N`, minimal-counterexample induction gives a global linear bound. -/
theorem Byproduct_localization_from_eventual_high_degree
    (N : ℕ)
    (heventual : ∀ G : SplitGraph, N ≤ G.n →
      (∀ i : Fin G.q, (2 * (G.n : ℝ) - 1) / 6 + 1 < (G.d i : ℝ)) →
      ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + 2 * (G.n : ℝ)) :
    ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤
      (G.n : ℝ) ^ 2 / 6 + (max 2 (N : ℝ)) * (G.n : ℝ) :=
  global_bound_from_eventual_high_degree N heventual

/-- Exact common-profile benchmark family: for every `H(p,q,d)`, the fractional triangle-cover
optimum has the closed value `F(p,q,d)`. This is the paper-facing exact solvable family isolated
by the formalization. -/
theorem Byproduct_commonProfile_tau3Star_eq_F
    (p q d : ℕ) (hp : 3 ≤ p) (hq : 1 ≤ q) (hd : d ≤ p) :
    tau3Star (commonProfile p q d).graph = ((F p q d : ℚ) : ℝ) :=
  Corollary_10_4 p q d hp hq hd

/-- Algebraic branch comparison for the common-profile family: uniform branch below the
separated branch. -/
theorem Byproduct_commonProfile_uniform_le_separated_of_quad
    (p q d : ℕ)
    (h : 3 * (d : ℚ) ^ 2 - 3 * (d : ℚ) * (p : ℚ) - (d : ℚ) * (q : ℚ) +
        (p : ℚ) ^ 2 - (p : ℚ) ≥ 0) :
    (C2 p + q * d) / 3 ≤ C2 d + C2 ((p : ℚ) - d) := by
  unfold C2
  ring_nf at h ⊢
  nlinarith

/-- Algebraic branch comparison for the common-profile family: uniform branch below the
hot-neighbourhood branch. -/
theorem Byproduct_commonProfile_uniform_le_hot_of_q_succ_le_d
    (p q d : ℕ) (h : q + 1 ≤ d) :
    (C2 p + q * d) / 3 ≤
      C2 d + ((d : ℚ) * ((p : ℚ) - d) + C2 ((p : ℚ) - d)) / 3 := by
  unfold C2
  have hq : (q : ℚ) + 1 ≤ d := by exact_mod_cast h
  have hd0 : (0 : ℚ) ≤ d := by exact_mod_cast Nat.zero_le d
  have hprod : 0 ≤ (d : ℚ) * ((d : ℚ) - ((q : ℚ) + 1)) :=
    mul_nonneg hd0 (sub_nonneg.mpr hq)
  ring_nf at hprod ⊢
  linarith

/-- Algebraic branch comparison for the common-profile family: separated branch below the
hot-neighbourhood branch, in the upper half of the natural range `d ≤ p`. -/
theorem Byproduct_commonProfile_separated_le_hot_of_upper_half
    (p q d : ℕ) (hhi : p ≤ 2 * d + 1) (hd : d ≤ p) :
    C2 d + C2 ((p : ℚ) - d) ≤
      C2 d + ((d : ℚ) * ((p : ℚ) - d) + C2 ((p : ℚ) - d)) / 3 := by
  unfold C2
  have hpD : (d : ℚ) ≤ (p : ℚ) := by exact_mod_cast hd
  have hhalf : (p : ℚ) ≤ (2 : ℚ) * d + 1 := by exact_mod_cast hhi
  ring_nf at hhalf ⊢
  nlinarith

/-- Algebraic branch comparison for the common-profile family: hot-neighbourhood branch below
the separated branch, in the lower half of the natural range `d ≤ p`. -/
theorem Byproduct_commonProfile_hot_le_separated_of_lower_half
    (p q d : ℕ) (hlo : 2 * d + 1 ≤ p) (hd : d ≤ p) :
    C2 d + ((d : ℚ) * ((p : ℚ) - d) + C2 ((p : ℚ) - d)) / 3 ≤
      C2 d + C2 ((p : ℚ) - d) := by
  unfold C2
  have hpD : (d : ℚ) ≤ (p : ℚ) := by exact_mod_cast hd
  have hhalf : (2 : ℚ) * d + 1 ≤ (p : ℚ) := by exact_mod_cast hlo
  have hhalf' : (2 : ℚ) * d ≤ (p : ℚ) - 1 := by linarith
  have hprod : (0 : ℚ) ≤ ((p : ℚ) - d) * ((p : ℚ) - 1 - 2 * d) :=
    mul_nonneg (sub_nonneg.mpr hpD) (sub_nonneg.mpr hhalf')
  ring_nf at hprod ⊢
  linarith

/-- Common-profile exact family, uniform branch with explicit algebraic region certificate. -/
theorem Byproduct_commonProfile_tau3Star_eq_uniform_region
    (p q d : ℕ) (hp : 3 ≤ p) (hq : 1 ≤ q) (hd : d ≤ p)
    (hAB : 3 * (d : ℚ) ^ 2 - 3 * (d : ℚ) * (p : ℚ) - (d : ℚ) * (q : ℚ) +
        (p : ℚ) ^ 2 - (p : ℚ) ≥ 0)
    (hAC : q + 1 ≤ d) :
    tau3Star (commonProfile p q d).graph =
      (((C2 p + q * d) / 3 : ℚ) : ℝ) := by
  have hF : F p q d = (C2 p + q * d) / 3 := by
    simp only [F]
    exact min_eq_left (le_min
      (Byproduct_commonProfile_uniform_le_separated_of_quad p q d hAB)
      (Byproduct_commonProfile_uniform_le_hot_of_q_succ_le_d p q d hAC))
  calc
    tau3Star (commonProfile p q d).graph = ((F p q d : ℚ) : ℝ) :=
      Byproduct_commonProfile_tau3Star_eq_F p q d hp hq hd
    _ = (((C2 p + q * d) / 3 : ℚ) : ℝ) := by rw [hF]

/-- Common-profile exact family, separated branch with explicit algebraic region certificate. -/
theorem Byproduct_commonProfile_tau3Star_eq_separated_region
    (p q d : ℕ) (hp : 3 ≤ p) (hq : 1 ≤ q) (hd : d ≤ p)
    (hBA : C2 d + C2 ((p : ℚ) - d) ≤ (C2 p + q * d) / 3)
    (hBC : p ≤ 2 * d + 1) :
    tau3Star (commonProfile p q d).graph =
      ((C2 d + C2 ((p : ℚ) - d) : ℚ) : ℝ) := by
  have hF : F p q d = C2 d + C2 ((p : ℚ) - d) := by
    simp only [F]
    have hminBC := min_eq_left
      (Byproduct_commonProfile_separated_le_hot_of_upper_half p q d hBC hd)
    rw [hminBC]
    exact min_eq_right hBA
  calc
    tau3Star (commonProfile p q d).graph = ((F p q d : ℚ) : ℝ) :=
      Byproduct_commonProfile_tau3Star_eq_F p q d hp hq hd
    _ = ((C2 d + C2 ((p : ℚ) - d) : ℚ) : ℝ) := by rw [hF]

/-- Common-profile exact family, hot-neighbourhood branch with explicit algebraic region
certificate. -/
theorem Byproduct_commonProfile_tau3Star_eq_hot_region
    (p q d : ℕ) (hp : 3 ≤ p) (hq : 1 ≤ q) (hd : d ≤ p)
    (hCA : C2 d + ((d : ℚ) * ((p : ℚ) - d) + C2 ((p : ℚ) - d)) / 3 ≤
      (C2 p + q * d) / 3)
    (hCB : 2 * d + 1 ≤ p) :
    tau3Star (commonProfile p q d).graph =
      ((C2 d + ((d : ℚ) * ((p : ℚ) - d) + C2 ((p : ℚ) - d)) / 3 : ℚ) : ℝ) := by
  have hF : F p q d =
      C2 d + ((d : ℚ) * ((p : ℚ) - d) + C2 ((p : ℚ) - d)) / 3 := by
    simp only [F]
    have hminBC := min_eq_right
      (Byproduct_commonProfile_hot_le_separated_of_lower_half p q d hCB hd)
    rw [hminBC]
    exact min_eq_right hCA
  calc
    tau3Star (commonProfile p q d).graph = ((F p q d : ℚ) : ℝ) :=
      Byproduct_commonProfile_tau3Star_eq_F p q d hp hq hd
    _ = ((C2 d + ((d : ℚ) * ((p : ℚ) - d) + C2 ((p : ℚ) - d)) / 3 : ℚ) : ℝ) := by
      rw [hF]

/-- Common-profile exact family, uniform-cover branch. If the uniform branch is the value of
`F(p,q,d)`, then the fractional optimum is `(C(p,2)+qd)/3`. -/
theorem Byproduct_commonProfile_tau3Star_eq_uniform_branch
    (p q d : ℕ) (hp : 3 ≤ p) (hq : 1 ≤ q) (hd : d ≤ p)
    (hF : F p q d = (C2 p + q * d) / 3) :
    tau3Star (commonProfile p q d).graph =
      (((C2 p + q * d) / 3 : ℚ) : ℝ) := by
  rw [Byproduct_commonProfile_tau3Star_eq_F p q d hp hq hd, hF]

/-- Common-profile exact family, separated-cover branch. If the separated branch is the value of
`F(p,q,d)`, then the fractional optimum is `C(d,2)+C(p-d,2)`. -/
theorem Byproduct_commonProfile_tau3Star_eq_separated_branch
    (p q d : ℕ) (hp : 3 ≤ p) (hq : 1 ≤ q) (hd : d ≤ p)
    (hF : F p q d = C2 d + C2 ((p : ℚ) - d)) :
    tau3Star (commonProfile p q d).graph =
      ((C2 d + C2 ((p : ℚ) - d) : ℚ) : ℝ) := by
  rw [Byproduct_commonProfile_tau3Star_eq_F p q d hp hq hd, hF]

/-- Common-profile exact family, hot-neighbourhood branch. If the hot branch is the value of
`F(p,q,d)`, then the fractional optimum is the corresponding hot-cover formula. -/
theorem Byproduct_commonProfile_tau3Star_eq_hot_branch
    (p q d : ℕ) (hp : 3 ≤ p) (hq : 1 ≤ q) (hd : d ≤ p)
    (hF : F p q d =
      C2 d + ((d : ℚ) * ((p : ℚ) - d) + C2 ((p : ℚ) - d)) / 3) :
    tau3Star (commonProfile p q d).graph =
      ((C2 d + ((d : ℚ) * ((p : ℚ) - d) + C2 ((p : ℚ) - d)) / 3 : ℚ) : ℝ) := by
  rw [Byproduct_commonProfile_tau3Star_eq_F p q d hp hq hd, hF]

/-- Unified fractional margin: in the range `p ≥ 3`, `0 < q ≤ 2p`, the formalized LP lower
bound has the explicit margin `μ(α)p² - p/4` over the threshold term `T(G)`. -/
theorem Byproduct_unified_fractional_margin
    (G : SplitGraph) (hp : 3 ≤ G.p) (hq1 : 1 ≤ G.q) (hq2 : G.q ≤ 2 * G.p) :
    ((G.T + SplitGraph.mu G.α * (G.p : ℚ) ^ 2 - (G.p : ℚ) / 4 : ℚ) : ℝ)
      ≤ tau3Star G.graph :=
  E_4_2 G hp hq1 hq2

/-- Threshold/complete-split specialization: the complete-split family `K_p ∨ K̄_{2p}` inherits
the final linear-error clique-partition bound from the clean AX1/AX2 assembly. -/
theorem Byproduct_completeSplit_threshold_linear_bound
    (hAX1 : AX1Assumption) (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ p : ℕ,
      ((completeSplit p).cp : ℝ)
        ≤ ((completeSplit p).n : ℝ) ^ 2 / 6 + C * ((completeSplit p).n : ℝ) :=
  Corollary_10_4b_of_AX1_AX2 hAX1 hAX2

/-- The complete-split threshold benchmark has exactly `3p` vertices. -/
theorem Byproduct_completeSplit_vertex_count (p : ℕ) :
    (completeSplit p).n = 3 * p := by
  simp [completeSplit, SplitGraph.n]
  omega

/-- Complete-split/threshold specialization in the paper-facing `3p` form. -/
theorem Byproduct_completeSplit_threshold_linear_bound_three_p
    (hAX1 : AX1Assumption) (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ p : ℕ,
      ((completeSplit p).cp : ℝ)
        ≤ ((3 * p : ℕ) : ℝ) ^ 2 / 6 + C * ((3 * p : ℕ) : ℝ) := by
  obtain ⟨C, hC⟩ := Byproduct_completeSplit_threshold_linear_bound hAX1 hAX2
  refine ⟨C, fun p => ?_⟩
  simpa [Byproduct_completeSplit_vertex_count p] using hC p

/-- In the complete-split benchmark every independent vertex sees the full clique. -/
theorem Byproduct_completeSplit_degree (p : ℕ) (i : Fin (completeSplit p).q) :
    (completeSplit p).d i = p := by
  simp [completeSplit, SplitGraph.d]

/-- Exact edge count for the complete-split benchmark. -/
theorem Byproduct_completeSplit_edgeCount (p : ℕ) :
    (completeSplit p).edgeCount = p.choose 2 + 2 * p * p := by
  rw [SplitGraph.edgeCount_eq]
  simp [completeSplit, SplitGraph.d]

/-- The round-robin factor count of `K_p` fits inside the `2p` independent vertices of
the complete-split benchmark. -/
theorem Byproduct_rp_le_two_mul (p : ℕ) : rp p ≤ 2 * p := by
  exact le_trans (rp_le p) (by omega)

/-- The factorization packing covers all clique edges in the complete-split benchmark. -/
theorem Byproduct_completeSplit_nu3_ge_clique_edges (p : ℕ) :
    ((p.choose 2 : ℕ) : ℝ) ≤ ((completeSplit p).nu3' : ℝ) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have hq : 1 ≤ (completeSplit p).q := by
    simp [completeSplit]
    omega
  have hpack := E_5_1 (completeSplit p) (Byproduct_rp_le_two_mul p) hq
  have hsum :
      (∑ i : Fin (completeSplit p).q, (((completeSplit p).d i).choose 2 : ℝ)) =
        (2 * p : ℕ) * (p.choose 2 : ℕ) := by
    simp [completeSplit, SplitGraph.d]
  have hqpos : ((completeSplit p).q : ℝ) ≠ 0 := by
    positivity
  rw [hsum] at hpack
  simp [completeSplit] at hpack
  field_simp [hp0] at hpack
  simpa [mul_comm, mul_left_comm, mul_assoc] using hpack

/-- Complete-split exact upper bound: the factorization packing uses every clique edge, so
`cp` is at most `2p² - C(p,2)`. -/
theorem Byproduct_completeSplit_cp_le_exact_value (p : ℕ) :
    ((completeSplit p).cp : ℤ) ≤ (2 * p * p : ℤ) - (p.choose 2 : ℤ) := by
  have hcp := cp_le_Phi (completeSplit p)
  have hnuR := Byproduct_completeSplit_nu3_ge_clique_edges p
  have hnuZ : (p.choose 2 : ℤ) ≤ ((completeSplit p).nu3' : ℤ) := by
    exact_mod_cast hnuR
  have hEdge := Byproduct_completeSplit_edgeCount p
  have hfinal :
      ((p.choose 2 + 2 * p * p : ℕ) : ℤ) - 2 * (p.choose 2 : ℤ) =
        ((2 * p * p : ℕ) : ℤ) - (p.choose 2 : ℤ) := by
    norm_num
    omega
  calc
    ((completeSplit p).cp : ℤ) ≤ (completeSplit p).Phi := hcp
    _ = ((completeSplit p).edgeCount : ℤ) - 2 * ((completeSplit p).nu3' : ℤ) := by
      rfl
    _ ≤ ((p.choose 2 + 2 * p * p : ℕ) : ℤ) - 2 * (p.choose 2 : ℤ) := by
      rw [hEdge]
      nlinarith [hnuZ]
    _ = ((2 * p * p : ℕ) : ℤ) - (p.choose 2 : ℤ) := hfinal

private def completeSplitCovered {p : ℕ}
    (c : Finset (completeSplit p).V) (e : Sym2 (completeSplit p).V) : Bool :=
  decide (e.toFinset ⊆ c)

private def completeSplitLeftSet (p : ℕ) (c : Finset (completeSplit p).V) : Finset (Fin p) :=
  Finset.univ.filter fun a => Sum.inl a ∈ c

private def completeSplitRightSet (p : ℕ)
    (c : Finset (completeSplit p).V) : Finset (Fin (2 * p)) :=
  Finset.univ.filter fun i => Sum.inr i ∈ c

private def completeSplitEdgeWeight (p : ℕ) (e : Sym2 (completeSplit p).V) : ℤ :=
  if e ∈ (completeSplit p).crossEdges then 1 else -1

private def completeSplitBlockWeight (p : ℕ) (c : Finset (completeSplit p).V) : ℤ :=
  ∑ e ∈ (completeSplit p).graph.edgeFinset,
    if completeSplitCovered c e then completeSplitEdgeWeight p e else 0

private lemma completeSplitEdgeWeight_cross (p : ℕ) (a : Fin p) (i : Fin (2 * p)) :
    completeSplitEdgeWeight p s(Sum.inl a, Sum.inr i) = 1 := by
  simp [completeSplitEdgeWeight, completeSplit, SplitGraph.crossEdges]

private lemma completeSplitEdgeWeight_clique (p : ℕ) (e : Sym2 (Fin p)) :
    completeSplitEdgeWeight p (e.map Sum.inl) = -1 := by
  simp [completeSplitEdgeWeight, completeSplit, SplitGraph.crossEdges]
  intro a b h
  revert h
  refine Sym2.ind ?_ e
  intro x y h
  rw [Sym2.map_pair_eq, Sym2.eq_iff] at h
  rcases h with h | h <;> simp at h

private lemma completeSplitCovered_cross (p : ℕ) (c : Finset (completeSplit p).V)
    (a : Fin p) (i : Fin (2 * p)) :
    completeSplitCovered c s(Sum.inl a, Sum.inr i) = true ↔
      Sum.inl a ∈ c ∧ Sum.inr i ∈ c := by
  simp [completeSplitCovered, Finset.subset_iff, Sym2.toFinset, Sym2.toMultiset]

private lemma completeSplitCovered_map_inl (p : ℕ) (c : Finset (completeSplit p).V)
    (e : Sym2 (Fin p)) :
    completeSplitCovered c (e.map Sum.inl) = true ↔ ∀ v ∈ e, Sum.inl v ∈ c := by
  revert e
  refine Sym2.ind ?_
  intro a b
  simp [completeSplitCovered, Finset.subset_iff, Sym2.toFinset, Sym2.toMultiset,
    Sym2.map_pair_eq]

private lemma completeSplit_right_card_le_one (p : ℕ) (c : Finset (completeSplit p).V)
    (hc : (completeSplit p).graph.IsClique (c : Set (completeSplit p).V)) :
    (completeSplitRightSet p c).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro i hi j hj
  have hci : (Sum.inr i : (completeSplit p).V) ∈ c := by
    simpa [completeSplitRightSet] using hi
  have hcj : (Sum.inr j : (completeSplit p).V) ∈ c := by
    simpa [completeSplitRightSet] using hj
  by_contra hne
  rw [SimpleGraph.isClique_iff] at hc
  have hPair := hc hci hcj ?_
  · simpa [completeSplit, SplitGraph.graph, SplitGraph.Adj] using hPair
  · intro hEq
    exact hne (Sum.inr.inj hEq)

private lemma completeSplit_cross_sum (p : ℕ) (c : Finset (completeSplit p).V) :
    (∑ i : Fin (2 * p), ∑ a : Fin p,
      (if completeSplitCovered c s(Sum.inl a, Sum.inr i) then (1 : ℤ) else 0))
      = ((completeSplitLeftSet p c).card * (completeSplitRightSet p c).card : ℕ) := by
  classical
  rw [Finset.sum_comm]
  have hinner : ∀ a : Fin p,
      (∑ i : Fin (2 * p), if Sum.inl a ∈ c ∧ Sum.inr i ∈ c then (1 : ℤ) else 0)
        = if Sum.inl a ∈ c then ((completeSplitRightSet p c).card : ℤ) else 0 := by
    intro a
    by_cases ha : Sum.inl a ∈ c
    · simp [ha, completeSplitRightSet]
    · simp [ha]
  calc
    (∑ a : Fin p, ∑ i : Fin (2 * p),
        if completeSplitCovered c s(Sum.inl a, Sum.inr i) then (1 : ℤ) else 0)
        = ∑ a : Fin p, if Sum.inl a ∈ c then
            ((completeSplitRightSet p c).card : ℤ) else 0 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← hinner a]
          simp [completeSplitCovered_cross]
    _ = ((completeSplitLeftSet p c).card : ℤ) *
        ((completeSplitRightSet p c).card : ℤ) := by
          rw [← Finset.sum_filter]
          simp [completeSplitLeftSet]
    _ = ((completeSplitLeftSet p c).card *
        (completeSplitRightSet p c).card : ℕ) := by norm_num

private lemma completeSplit_clique_sum (p : ℕ) (c : Finset (completeSplit p).V) :
    (∑ e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset,
      (if completeSplitCovered c (e.map Sum.inl) then (-1 : ℤ) else 0))
      = -(((completeSplitLeftSet p c).card.choose 2 : ℕ) : ℤ) := by
  classical
  have hfilter :
      ((⊤ : SimpleGraph (Fin p)).edgeFinset.filter fun e =>
          completeSplitCovered c (e.map Sum.inl) = true)
        = ((⊤ : SimpleGraph (Fin p)).edgeFinset.filter fun e =>
          ∀ v ∈ e, v ∈ completeSplitLeftSet p c) := by
    ext e
    simp [completeSplitCovered_map_inl, completeSplitLeftSet]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hfilter]
  have hcard :
      ((⊤ : SimpleGraph (Fin p)).edgeFinset.filter fun e =>
          ∀ v ∈ e, v ∈ completeSplitLeftSet p c).card =
        (completeSplitLeftSet p c).card.choose 2 := by
    convert (@card_top_edges_within (Fin p) _ _ (completeSplitLeftSet p c)) using 1
    apply congrArg Finset.card
    ext e
    simp [SimpleGraph.edgeFinset]
  change (((⊤ : SimpleGraph (Fin p)).edgeFinset.filter fun e =>
      ∀ v ∈ e, v ∈ completeSplitLeftSet p c).card : ℤ) * -1 =
    -(((completeSplitLeftSet p c).card.choose 2 : ℕ) : ℤ)
  norm_num [← hcard]

private lemma completeSplitBlockWeight_eq (p : ℕ) (c : Finset (completeSplit p).V) :
    completeSplitBlockWeight p c =
      ((completeSplitLeftSet p c).card * (completeSplitRightSet p c).card : ℕ) -
        ((completeSplitLeftSet p c).card.choose 2 : ℕ) := by
  classical
  unfold completeSplitBlockWeight
  rw [SplitGraph.sum_edgeFinset]
  have hleft :
      (∑ e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset,
        (if completeSplitCovered c (e.map Sum.inl) then
          completeSplitEdgeWeight p (e.map Sum.inl) else 0)) =
      ∑ e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset,
        (if completeSplitCovered c (e.map Sum.inl) then (-1 : ℤ) else 0) := by
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [completeSplitEdgeWeight_clique]
  have hcross :
      (∑ i : Fin (completeSplit p).q, ∑ a ∈ (completeSplit p).N i,
        (if completeSplitCovered c s(Sum.inl a, Sum.inr i) then
          completeSplitEdgeWeight p s(Sum.inl a, Sum.inr i) else 0)) =
      ∑ i : Fin (2 * p), ∑ a : Fin p,
        (if completeSplitCovered c s(Sum.inl a, Sum.inr i) then (1 : ℤ) else 0) := by
    change (∑ i : Fin (2 * p), ∑ a ∈ (Finset.univ : Finset (Fin p)),
        (if completeSplitCovered c s(Sum.inl a, Sum.inr i) then
          completeSplitEdgeWeight p s(Sum.inl a, Sum.inr i) else 0)) =
      ∑ i : Fin (2 * p), ∑ a : Fin p,
        (if completeSplitCovered c s(Sum.inl a, Sum.inr i) then (1 : ℤ) else 0)
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [completeSplitEdgeWeight_cross]
  calc
    ((∑ e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset,
        (if completeSplitCovered c (e.map Sum.inl) then
          completeSplitEdgeWeight p (e.map Sum.inl) else 0)) +
      ∑ i : Fin (completeSplit p).q, ∑ a ∈ (completeSplit p).N i,
        (if completeSplitCovered c s(Sum.inl a, Sum.inr i) then
          completeSplitEdgeWeight p s(Sum.inl a, Sum.inr i) else 0))
        = (∑ e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset,
            (if completeSplitCovered c (e.map Sum.inl) then (-1 : ℤ) else 0)) +
          ∑ i : Fin (2 * p), ∑ a : Fin p,
            (if completeSplitCovered c s(Sum.inl a, Sum.inr i) then (1 : ℤ) else 0) := by
          rw [hleft, hcross]
    _ = ((completeSplitLeftSet p c).card * (completeSplitRightSet p c).card : ℕ) -
        ((completeSplitLeftSet p c).card.choose 2 : ℕ) := by
          rw [completeSplit_clique_sum, completeSplit_cross_sum]
          ring

private lemma nat_le_choose_two_add_one_of_three_le (n : ℕ) (h : 3 ≤ n) :
    n ≤ n.choose 2 + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.choose_two_right]
  rw [← Nat.sub_le_iff_le_add]
  rw [Nat.le_div_iff_mul_le (by omega : 0 < 2)]
  nlinarith

private lemma completeSplitBlockWeight_le_one (p : ℕ) (c : Finset (completeSplit p).V)
    (hc : (completeSplit p).graph.IsClique (c : Set (completeSplit p).V)) :
    completeSplitBlockWeight p c ≤ 1 := by
  classical
  rw [completeSplitBlockWeight_eq]
  have hr := completeSplit_right_card_le_one p c hc
  interval_cases hrc : (completeSplitRightSet p c).card
  · simp
  · simp
    have hcases : (completeSplitLeftSet p c).card ≤ 2 ∨
        3 ≤ (completeSplitLeftSet p c).card := by omega
    rcases hcases with hle | hge
    · interval_cases (completeSplitLeftSet p c).card <;> norm_num
    · have hnat := nat_le_choose_two_add_one_of_three_le
        (completeSplitLeftSet p c).card hge
      have hint : ((completeSplitLeftSet p c).card : ℤ) ≤
          (((completeSplitLeftSet p c).card.choose 2 : ℕ) : ℤ) + 1 := by
        exact_mod_cast hnat
      linarith

private lemma completeSplitCovered_iff_full (p : ℕ) (c : Finset (completeSplit p).V)
    (e : Sym2 (completeSplit p).V) :
    completeSplitCovered c e = true ↔ ∀ v ∈ e, v ∈ c := by
  revert e
  refine Sym2.ind ?_
  intro x y
  simp [completeSplitCovered, Finset.subset_iff, Sym2.toFinset, Sym2.toMultiset]

private def completeSplitTotalWeight (p : ℕ) : ℤ :=
  ∑ e ∈ (completeSplit p).graph.edgeFinset, completeSplitEdgeWeight p e

private lemma completeSplitTotalWeight_eq (p : ℕ) :
    completeSplitTotalWeight p = (2 * p * p : ℕ) - (p.choose 2 : ℕ) := by
  unfold completeSplitTotalWeight
  rw [SplitGraph.sum_edgeFinset]
  have hleft :
      (∑ e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset,
        completeSplitEdgeWeight p (e.map Sum.inl)) =
        -((p.choose 2 : ℕ) : ℤ) := by
    have hsum : (∑ e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset,
        completeSplitEdgeWeight p (e.map Sum.inl)) =
        ∑ e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset, (-1 : ℤ) := by
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [completeSplitEdgeWeight_clique]
    rw [hsum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have htop := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin p)
    rw [Fintype.card_fin] at htop
    norm_num [← htop]
  have hcross :
      (∑ i : Fin (completeSplit p).q, ∑ a ∈ (completeSplit p).N i,
        completeSplitEdgeWeight p s(Sum.inl a, Sum.inr i)) = (2 * p * p : ℕ) := by
    change (∑ i : Fin (2 * p), ∑ a ∈ (Finset.univ : Finset (Fin p)),
        completeSplitEdgeWeight p s(Sum.inl a, Sum.inr i)) = (2 * p * p : ℕ)
    simp [completeSplitEdgeWeight_cross]
  calc
    (∑ e ∈ (⊤ : SimpleGraph (Fin p)).edgeFinset,
        completeSplitEdgeWeight p (e.map Sum.inl)) +
        ∑ i : Fin (completeSplit p).q, ∑ a ∈ (completeSplit p).N i,
          completeSplitEdgeWeight p s(Sum.inl a, Sum.inr i)
        = -((p.choose 2 : ℕ) : ℤ) + ((2 * p * p : ℕ) : ℤ) := by
          rw [hleft, hcross]
    _ = ((2 * p * p : ℕ) : ℤ) - ((p.choose 2 : ℕ) : ℤ) := by ring

private lemma completeSplit_partition_weight_le_card (p : ℕ)
    (P : Finset (Finset (completeSplit p).V))
    (hclique : ∀ c ∈ P, (completeSplit p).graph.IsClique (c : Set (completeSplit p).V))
    (hcover : ∀ e ∈ (completeSplit p).graph.edgeFinset,
      ∃! c, c ∈ P ∧ ∀ v ∈ e, v ∈ c) :
    completeSplitTotalWeight p ≤ (P.card : ℤ) := by
  classical
  have hedge : ∀ e ∈ (completeSplit p).graph.edgeFinset,
      (∑ c ∈ P, if completeSplitCovered c e then completeSplitEdgeWeight p e else 0) =
        completeSplitEdgeWeight p e := by
    intro e he
    obtain ⟨c0, hc0, huniq⟩ := hcover e he
    have hcov0 : completeSplitCovered c0 e = true :=
      (completeSplitCovered_iff_full p c0 e).mpr hc0.2
    calc
      (∑ c ∈ P, if completeSplitCovered c e then completeSplitEdgeWeight p e else 0)
          = if completeSplitCovered c0 e then completeSplitEdgeWeight p e else 0 := by
            refine Finset.sum_eq_single (s := P)
              (f := fun c => if completeSplitCovered c e then completeSplitEdgeWeight p e else 0)
              c0 ?main ?zero
            · intro c hcP hne
              have hfalse : completeSplitCovered c e = false := by
                apply Bool.eq_false_iff.mpr
                intro htrue
                have hcand : c ∈ P ∧ ∀ v ∈ e, v ∈ c :=
                  ⟨hcP, (completeSplitCovered_iff_full p c e).mp htrue⟩
                have hceq : c = c0 := huniq c hcand
                exact hne hceq
              simp [hfalse]
            · intro hc0not
              exact False.elim (hc0not hc0.1)
      _ = completeSplitEdgeWeight p e := by simp [hcov0]
  calc
    completeSplitTotalWeight p
        = ∑ e ∈ (completeSplit p).graph.edgeFinset, completeSplitEdgeWeight p e := rfl
    _ = ∑ e ∈ (completeSplit p).graph.edgeFinset,
          ∑ c ∈ P, if completeSplitCovered c e then completeSplitEdgeWeight p e else 0 := by
          refine Finset.sum_congr rfl fun e he => ?_
          rw [hedge e he]
    _ = ∑ c ∈ P, completeSplitBlockWeight p c := by
          rw [Finset.sum_comm]
          rfl
    _ ≤ ∑ c ∈ P, (1 : ℤ) := by
          refine Finset.sum_le_sum fun c hc => ?_
          exact completeSplitBlockWeight_le_one p c (hclique c hc)
    _ = (P.card : ℤ) := by simp

private lemma completeSplit_edge_toFinset_inj {p : ℕ} {e e' : Sym2 (completeSplit p).V}
    (_he : e ∈ (completeSplit p).graph.edgeFinset)
    (_he' : e' ∈ (completeSplit p).graph.edgeFinset)
    (h : e.toFinset = e'.toFinset) :
    e = e' := by
  rw [Sym2.ext_iff]
  intro v
  rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, h]

private lemma completeSplit_edge_toFinset_card_two {p : ℕ}
    {e : Sym2 (completeSplit p).V}
    (he : e ∈ (completeSplit p).graph.edgeFinset) :
    e.toFinset.card = 2 := by
  rcases e with ⟨x, y⟩
  simp [SimpleGraph.mem_edgeFinset, Sym2.toFinset, Sym2.toMultiset] at he ⊢
  simpa using Finset.card_pair he.ne

private lemma completeSplit_cp_lower_nat (p : ℕ) :
    (2 * p * p - p.choose 2) ≤ (completeSplit p).cp := by
  classical
  unfold SplitGraph.cp
  refine le_csInf ?nonempty ?lower
  · refine ⟨(completeSplit p).edgeCount, ?_⟩
    let P : Finset (Finset (completeSplit p).V) :=
      (completeSplit p).graph.edgeFinset.image fun e => e.toFinset
    refine ⟨P, ?_, ?_, ?_⟩
    · intro c hc
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
      rcases e with ⟨x, y⟩
      simp [SimpleGraph.isClique_iff, SimpleGraph.mem_edgeFinset] at he ⊢
      intro a ha b hb hne
      simp at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · contradiction
      · exact he
      · exact he.symm
      · contradiction
    · unfold P
      rw [Finset.card_image_of_injOn]
      · rfl
      · intro e he e' he' h
        exact completeSplit_edge_toFinset_inj he he' h
    · intro e he
      refine ⟨e.toFinset, ?_, ?_⟩
      · constructor
        · exact Finset.mem_image.mpr ⟨e, he, rfl⟩
        · intro v hv
          simpa [Sym2.mem_toFinset] using hv
      · intro c hc
        rcases hc with ⟨hcP, hcov⟩
        obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hcP
        have hsub : e.toFinset ⊆ e'.toFinset := by
          intro v hv
          exact hcov v (by simpa [Sym2.mem_toFinset] using hv)
        exact (Finset.eq_of_subset_of_card_le (s := e.toFinset) (t := e'.toFinset) hsub (by
          rw [completeSplit_edge_toFinset_card_two he,
            completeSplit_edge_toFinset_card_two he'])).symm
  · intro k hk
    obtain ⟨P, hclique, hcard, hcover⟩ := hk
    have hweight := completeSplit_partition_weight_le_card p P hclique hcover
    rw [completeSplitTotalWeight_eq, hcard] at hweight
    have hchoose : p.choose 2 ≤ 2 * p * p := by
      have hpow : p.choose 2 ≤ p ^ 2 := Nat.choose_le_pow p 2
      have hpown : p ^ 2 = p * p := by ring
      rw [hpown] at hpow
      nlinarith
    have hnatcast : ((2 * p * p - p.choose 2 : ℕ) : ℤ) =
        ((2 * p * p : ℕ) : ℤ) - (p.choose 2 : ℤ) := by
      rw [Nat.cast_sub hchoose]
    exact Nat.cast_le.mp (by
      rw [hnatcast]
      exact hweight)

/-- Complete-split exact lower bound: every clique partition needs at least
`2p² - C(p,2)` blocks. -/
theorem Byproduct_completeSplit_cp_ge_exact_value (p : ℕ) :
    (2 * p * p : ℤ) - (p.choose 2 : ℤ) ≤ ((completeSplit p).cp : ℤ) := by
  have hnat := completeSplit_cp_lower_nat p
  have hchoose : p.choose 2 ≤ 2 * p * p := by
    have hpow : p.choose 2 ≤ p ^ 2 := Nat.choose_le_pow p 2
    have hpown : p ^ 2 = p * p := by ring
    rw [hpown] at hpow
    nlinarith
  have hcast : ((2 * p * p - p.choose 2 : ℕ) : ℤ) =
      ((2 * p * p : ℕ) : ℤ) - (p.choose 2 : ℤ) := by
    rw [Nat.cast_sub hchoose]
  exact hcast ▸ (by exact_mod_cast hnat)

/-- Complete-split exact clique-partition value:
`cp(K_p ∨ K̄_{2p}) = 2p² - C(p,2)`. -/
theorem Byproduct_completeSplit_cp_exact_value (p : ℕ) :
    ((completeSplit p).cp : ℤ) = (2 * p * p : ℤ) - (p.choose 2 : ℤ) :=
  le_antisymm (Byproduct_completeSplit_cp_le_exact_value p)
    (Byproduct_completeSplit_cp_ge_exact_value p)

/-- **Sharpness of the leading constant `1/6`.**  On the complete-split extremal family the
clique-partition number hits `n²/6 + n/6` *exactly*: `cp(K_p ∨ K̄_{2p}) = n²/6 + n/6` with
`n = 3p`.  Together with `Theorem_1_1` (`cp ≤ n²/6 + C·n`) this shows the coefficient `1/6` of the
quadratic term is best possible, and that any absolute constant `C` valid for all split graphs must
satisfy `C ≥ 1/6` asymptotically — a matching lower bound witnessing tightness. -/
theorem Byproduct_completeSplit_cp_sharp (p : ℕ) :
    ((completeSplit p).cp : ℝ)
      = ((completeSplit p).n : ℝ) ^ 2 / 6 + ((completeSplit p).n : ℝ) / 6 := by
  have hn : (completeSplit p).n = 3 * p := Byproduct_completeSplit_vertex_count p
  have hcpR : ((completeSplit p).cp : ℝ) = (2 * p * p : ℝ) - (p.choose 2 : ℝ) := by
    exact_mod_cast Byproduct_completeSplit_cp_exact_value p
  rw [hcpR, hn, Nat.cast_choose_two]
  push_cast
  ring

/-- The coefficient `1/6` is sharp: no absolute constant strictly below `1/6` can bound the
quadratic term for all split graphs, since the complete-split family realizes `n²/6 + n/6`. -/
theorem Byproduct_leading_constant_sharp (p : ℕ) :
    ((completeSplit p).n : ℝ) ^ 2 / 6 ≤ ((completeSplit p).cp : ℝ) := by
  have h := Byproduct_completeSplit_cp_sharp p
  have hn0 : (0 : ℝ) ≤ ((completeSplit p).n : ℝ) := by positivity
  rw [h]; linarith

/-- **The leading constant `1/6` is forced (I.3.1 — extremal / matching lower bound).**  Any
absolute constant `C` for which `cp(G) ≤ n²/6 + C·n` holds across ALL split graphs must satisfy
`C ≥ 1/6`, because the complete-split family realizes `cp = n²/6 + n/6` exactly (`…cp_sharp`).  So
`1/6` is the best possible coefficient of the linear term for a uniform bound. -/
theorem Byproduct_leading_constant_forced (C : ℝ)
    (hbound : ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ)) :
    (1 : ℝ) / 6 ≤ C := by
  have hb := hbound (completeSplit 1)
  rw [Byproduct_completeSplit_cp_sharp 1] at hb
  have hn : ((completeSplit 1).n : ℝ) = 3 := by
    rw [Byproduct_completeSplit_vertex_count 1]; norm_num
  rw [hn] at hb
  linarith

/-- **The high-ratio corridor bound is not tight on the extremal family (I.3.2).**  For the
complete-split family the proven high-ratio bound gives `cp ≤ n²/6 + n/2`, while the exact value is
`cp = n²/6 + n/6`; hence the bound overshoots by exactly `n/3` there. -/
theorem Byproduct_completeSplit_high_ratio_bound (p : ℕ) :
    ((completeSplit p).cp : ℝ) ≤ ((completeSplit p).n : ℝ) ^ 2 / 6 + ((completeSplit p).n : ℝ) / 2 :=
  Byproduct_high_ratio_cp_half_linear (completeSplit p) (by simp [completeSplit])

/-- The exact slack: on the complete-split family the high-ratio upper bound `n²/6 + n/2` exceeds the
true value `cp` by exactly `n/3`. -/
theorem Byproduct_completeSplit_high_ratio_slack (p : ℕ) :
    ((completeSplit p).cp : ℝ) + ((completeSplit p).n : ℝ) / 3
      = ((completeSplit p).n : ℝ) ^ 2 / 6 + ((completeSplit p).n : ℝ) / 2 := by
  rw [Byproduct_completeSplit_cp_sharp p]; ring

/-- Effective low-corridor clique-partition bound: in the low corridor the observable `cp`
has the explicit `3/2` linear constant. This is the formalizable part of the effective
low-corridor corollary. -/
theorem Byproduct_effective_low_corridor_cp_bound
    (G : SplitGraph) (hp : 37 ≤ G.p)
    (hs0 : 0 ≤ G.s) (hs : (G.s : ℝ) ^ 2 ≤ 36 * (G.p : ℝ)) :
    (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + (3 / 2) * (G.n : ℝ) :=
  Corollary_12_2_bound G hp hs0 hs

/-- Dirac/Tutte byproduct: an even finite graph with `|V| ≤ 2δ(G)` has a perfect matching. -/
theorem Byproduct_dirac_perfect_matching_even
    {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (hev : Even (Fintype.card W)) (hcard : Fintype.card W ≤ 2 * G.minDegree) :
    ∃ M : G.Subgraph, M.IsPerfectMatching :=
  exists_isPerfectMatching_of_minDegree G hev hcard

/-- Dirac/Tutte byproduct: if `|V| ≤ 2δ(G)+1`, then there is a matching covering all but
at most one vertex. -/
theorem Byproduct_dirac_near_perfect_matching
    {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (hcard : Fintype.card W ≤ 2 * G.minDegree + 1) :
    ∃ M : G.Subgraph, M.IsMatching ∧ Fintype.card W ≤ M.verts.toFinset.card + 1 :=
  exists_near_perfect_matching G hcard

/-- Dense divisibility-correction byproduct from the `E_8` formalization. In a graph on `p`
vertices with `δ ≥ 0.9p`, one can delete at most `p+8` edges, with incidence loss at most `6`
at every vertex, so that all residual degrees are even and the residual edge count is divisible
by `3`. -/
theorem Byproduct_dense_divisible_correction_edges
    {p : ℕ} (H : SimpleGraph (Fin p)) [DecidableRel H.Adj]
    (hp : 2000 ≤ p) (hδ : ∀ v, 9 * p ≤ 10 * H.degree v) :
    ∃ C : Finset (Sym2 (Fin p)),
      (C : Set (Sym2 (Fin p))) ⊆ H.edgeSet ∧
      C.card ≤ p + 8 ∧
      (∀ v, incDeg C v ≤ 6) ∧
      (∀ v, Even (H.degree v - incDeg C v)) ∧
      (H.edgeFinset.card - C.card) % 3 = 0 :=
  exists_divisible_correction_edges H hp hδ

/-- Dense triangle-hypergraph near-regularity package, surfaced as a paper byproduct. -/
theorem Byproduct_dense_triangleSub_linearSized_data_of_minDeg
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : ℕ)
    (hD : ∀ x, D ≤ G.degree x)
    (hcardD : Fintype.card V ≤ 2 * D) :
    ∀ {μ η d L : ℝ}, 0 ≤ η → 1 ≤ μ * d → (Fintype.card V : ℝ) ≤ L * d →
      (1 - μ) * d ≤ 2 * (D : ℝ) - (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ (1 + μ) * d →
      Hypergraph.NearlyRegularMost (Nibble.YusterE.triangleHypergraphSub G) d μ η ∧
        Hypergraph.CodegreeBounded (Nibble.YusterE.triangleHypergraphSub G) (μ * d) ∧
          (∀ E : Nibble.YusterE.EdgeV G,
            (Hypergraph.degree (Nibble.YusterE.triangleHypergraphSub G) E : ℝ) ≤ (1 + μ) * d) ∧
            (Fintype.card V : ℝ) ≤ L * d :=
  Nibble.YusterE.triangleSub_linearSized_data_of_minDeg G D hD hcardD

/-- Edge-degree in the typed triangle hypergraph is common-neighbourhood size. -/
theorem Byproduct_triangleSub_degree_eq_common_neighbors
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Nibble.YusterE.EdgeV G) (u v : V) (huv : E.val = ({u, v} : Finset V)) :
    Hypergraph.degree (Nibble.YusterE.triangleHypergraphSub G) E
      = (G.neighborFinset u ∩ G.neighborFinset v).card :=
  Nibble.YusterE.triangleSub_degree_eq_inter G E u v huv

/-- Dense-regime global ceiling: every graph edge lies in at most `|V|` graph triangles. -/
theorem Byproduct_triangleSub_degree_le_card
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Nibble.YusterE.EdgeV G) :
    Hypergraph.degree (Nibble.YusterE.triangleHypergraphSub G) E ≤ Fintype.card V :=
  Nibble.YusterE.triangleSub_degree_le_card G E

/-- Dense-regime global floor: minimum degree `D` forces every graph edge to lie in at least
`2D - |V|` graph triangles. -/
theorem Byproduct_triangleSub_degree_ge_of_minDeg
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Nibble.YusterE.EdgeV G) {D : ℕ} (hD : ∀ x, D ≤ G.degree x) :
    2 * D - Fintype.card V ≤ Hypergraph.degree (Nibble.YusterE.triangleHypergraphSub G) E :=
  Nibble.YusterE.triangleSub_degree_ge_of_minDeg G E hD

/-- Dense-regime pointwise near-regularity window for every graph edge. This is the explicit
non-exceptional regularity input behind the dense triangle-hypergraph package. -/
theorem Byproduct_triangleSub_degree_window
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Nibble.YusterE.EdgeV G) (D : ℕ) (hD : ∀ x, D ≤ G.degree x)
    (h2D : Fintype.card V ≤ 2 * D) {μ d : ℝ}
    (hlo : (1 - μ) * d ≤ 2 * (D : ℝ) - (Fintype.card V : ℝ))
    (hhi : (Fintype.card V : ℝ) ≤ (1 + μ) * d) :
    (1 - μ) * d ≤
        (Hypergraph.degree (Nibble.YusterE.triangleHypergraphSub G) E : ℝ) ∧
      (Hypergraph.degree (Nibble.YusterE.triangleHypergraphSub G) E : ℝ) ≤ (1 + μ) * d :=
  Nibble.YusterE.triangleSub_degree_window G E D hD h2D hlo hhi

/-- Explicit dense-regime lower bound: if `δ(G) ≥ 0.9 |V|`, then every graph edge lies in at
least `0.8 |V|` triangles, in integer cross-multiplied form. -/
theorem Byproduct_triangleSub_degree_ge_eight_tenths
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (E : Nibble.YusterE.EdgeV G) :
    8 * Fintype.card V ≤ 10 * Hypergraph.degree (Nibble.YusterE.triangleHypergraphSub G) E := by
  have hfloor := Nibble.YusterE.triangleSub_degree_ge_of_minDeg G E
    (fun x => G.minDegree_le_degree x)
  have h2D : Fintype.card V ≤ 2 * G.minDegree := by omega
  have hnum : 8 * Fintype.card V ≤ 10 * (2 * G.minDegree - Fintype.card V) := by omega
  exact hnum.trans (Nat.mul_le_mul_left 10 hfloor)

/-- Explicit dense-regime real window: if `δ(G) ≥ 0.9 |V|`, then every graph edge lies in
between `0.8 |V|` and `|V|` graph triangles. -/
theorem Byproduct_triangleSub_degree_real_window_nine_tenths
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (E : Nibble.YusterE.EdgeV G) :
    (4 / 5) * (Fintype.card V : ℝ) ≤
        (Hypergraph.degree (Nibble.YusterE.triangleHypergraphSub G) E : ℝ) ∧
      (Hypergraph.degree (Nibble.YusterE.triangleHypergraphSub G) E : ℝ) ≤
        (Fintype.card V : ℝ) := by
  constructor
  · have h := Byproduct_triangleSub_degree_ge_eight_tenths G hmin E
    have hR : (8 * Fintype.card V : ℝ) ≤
        10 * (Hypergraph.degree (Nibble.YusterE.triangleHypergraphSub G) E : ℝ) := by
      exact_mod_cast h
    nlinarith
  · exact_mod_cast Nibble.YusterE.triangleSub_degree_le_card G E

/-- Parametric dense-regime triangle-degree window. If `δ(G) ≥ a|V|` in cross-multiplied
integer form `b|V| ≤ cδ(G)`, then every graph edge lies in at least `(2b-c)|V|/c`
triangles, and at most `|V|` triangles. The `9/10` lemma is the `b=9,c=10` instance. -/
theorem Byproduct_triangleSub_degree_window_of_minDegree_ratio
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {b c : ℕ} (hcpos : 0 < c) (hdense : c ≤ 2 * b)
    (hmin : b * Fintype.card V ≤ c * G.minDegree)
    (E : Nibble.YusterE.EdgeV G) :
    (2 * b - c) * Fintype.card V ≤
        c * Hypergraph.degree (Nibble.YusterE.triangleHypergraphSub G) E ∧
      Hypergraph.degree (Nibble.YusterE.triangleHypergraphSub G) E ≤ Fintype.card V := by
  constructor
  · have hfloor := Nibble.YusterE.triangleSub_degree_ge_of_minDeg G E
      (fun x => G.minDegree_le_degree x)
    have h2bn : 2 * b * Fintype.card V ≤ 2 * c * G.minDegree := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        Nat.mul_le_mul_left 2 hmin
    have hcn_left : c * Fintype.card V ≤ 2 * b * Fintype.card V := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        Nat.mul_le_mul_right (Fintype.card V) hdense
    have hcn : c * Fintype.card V ≤ c * (2 * G.minDegree) := by
      exact hcn_left.trans (by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h2bn)
    have h2D : Fintype.card V ≤ 2 * G.minDegree :=
      Nat.le_of_mul_le_mul_left hcn hcpos
    have hnum : (2 * b - c) * Fintype.card V ≤
        c * (2 * G.minDegree - Fintype.card V) := by
      calc
        (2 * b - c) * Fintype.card V
            = 2 * b * Fintype.card V - c * Fintype.card V := by
              rw [Nat.sub_mul]
        _ ≤ 2 * c * G.minDegree - c * Fintype.card V := by
              exact Nat.sub_le_sub_right h2bn (c * Fintype.card V)
        _ = c * (2 * G.minDegree - Fintype.card V) := by
              rw [Nat.mul_sub_left_distrib]
              simp [Nat.mul_assoc, Nat.mul_comm]
    exact hnum.trans (Nat.mul_le_mul_left c hfloor)
  · exact Nibble.YusterE.triangleSub_degree_le_card G E

/-- Explicit dense-regime near-regularity window with `d = 9|V|/10` and `μ = 1/9`. -/
theorem Byproduct_triangleSub_degree_window_mu_one_ninth
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (E : Nibble.YusterE.EdgeV G) :
    (1 - (1 / 9 : ℝ)) * ((9 / 10 : ℝ) * (Fintype.card V : ℝ)) ≤
        (Hypergraph.degree (Nibble.YusterE.triangleHypergraphSub G) E : ℝ) ∧
      (Hypergraph.degree (Nibble.YusterE.triangleHypergraphSub G) E : ℝ) ≤
        (1 + (1 / 9 : ℝ)) * ((9 / 10 : ℝ) * (Fintype.card V : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := Byproduct_triangleSub_degree_real_window_nine_tenths G hmin E
  constructor <;> nlinarith

/-- No-exception dense-regime regularity: under `δ(G) ≥ 0.9 |V|`, the typed triangle
hypergraph is strictly near-regular with `d = 9|V|/10` and `μ = 1/9`. The majority form used
by the nibble is only a technical weakening of this statement in the dense regime. -/
theorem Byproduct_triangleSub_nearlyRegular_nine_tenths
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : 9 * Fintype.card V ≤ 10 * G.minDegree) :
    Hypergraph.NearlyRegular
      (Nibble.YusterE.triangleHypergraphSub G)
      ((9 / 10 : ℝ) * (Fintype.card V : ℝ)) (1 / 9) := by
  intro E
  exact Byproduct_triangleSub_degree_window_mu_one_ninth G hmin E

/-- Explicit dense-regime corrected-nibble data with constants visible in the statement.
If `δ(G) ≥ 0.9 |V|` and `|V| ≥ 10`, then the typed triangle hypergraph is majority-regular
with `d = 9|V|/10`, `μ = 1/9`, has the required codegree bound, and has linear vertex size
with `L = 10/9`. -/
theorem Byproduct_dense_triangleSub_linearSized_data_nine_tenths
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (hcard : 10 ≤ Fintype.card V) {η : ℝ} (hη : 0 ≤ η) :
    Hypergraph.NearlyRegularMost
        (Nibble.YusterE.triangleHypergraphSub G)
        ((9 / 10 : ℝ) * (Fintype.card V : ℝ)) (1 / 9) η ∧
      Hypergraph.CodegreeBounded
        (Nibble.YusterE.triangleHypergraphSub G)
        ((1 / 9 : ℝ) * ((9 / 10 : ℝ) * (Fintype.card V : ℝ))) ∧
      (∀ E : Nibble.YusterE.EdgeV G,
        (Hypergraph.degree (Nibble.YusterE.triangleHypergraphSub G) E : ℝ) ≤
          (1 + (1 / 9 : ℝ)) * ((9 / 10 : ℝ) * (Fintype.card V : ℝ))) ∧
      (Fintype.card V : ℝ) ≤
        (10 / 9 : ℝ) * ((9 / 10 : ℝ) * (Fintype.card V : ℝ)) := by
  refine Nibble.YusterE.triangleSub_linearSized_data_of_window G hη ?_ ?_ ?_
  · have hcardR : (10 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hcard
    nlinarith
  · nlinarith
  · intro E
    exact Byproduct_triangleSub_degree_window_mu_one_ninth G hmin E

/-- Full explicit dense-regime nibble input for the typed triangle hypergraph, including
3-uniformity. This is the paper-facing one-line package behind the dense `9/10` route. -/
theorem Byproduct_dense_triangleSub_full_nibble_input_nine_tenths
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (hcard : 10 ≤ Fintype.card V) {η : ℝ} (hη : 0 ≤ η) :
    Hypergraph.IsUniform (Nibble.YusterE.triangleHypergraphSub G) 3 ∧
      Hypergraph.NearlyRegularMost
        (Nibble.YusterE.triangleHypergraphSub G)
        ((9 / 10 : ℝ) * (Fintype.card V : ℝ)) (1 / 9) η ∧
      Hypergraph.CodegreeBounded
        (Nibble.YusterE.triangleHypergraphSub G)
        ((1 / 9 : ℝ) * ((9 / 10 : ℝ) * (Fintype.card V : ℝ))) ∧
      (∀ E : Nibble.YusterE.EdgeV G,
        (Hypergraph.degree (Nibble.YusterE.triangleHypergraphSub G) E : ℝ) ≤
          (1 + (1 / 9 : ℝ)) * ((9 / 10 : ℝ) * (Fintype.card V : ℝ))) ∧
      (Fintype.card V : ℝ) ≤
        (10 / 9 : ℝ) * ((9 / 10 : ℝ) * (Fintype.card V : ℝ)) := by
  exact ⟨Nibble.YusterE.triangleHypergraphSub_uniform G,
    Byproduct_dense_triangleSub_linearSized_data_nine_tenths G hmin hcard hη⟩

/-- Majority near-regularity is monotone in the tolerance parameters: increasing `μ` and `η`
preserves the hypothesis. This is the formal parameter-compatibility lemma needed when matching
dense inputs to a nibble tolerance. -/
theorem Byproduct_nearlyRegularMost_mono_mu_eta
    {V : Type} [Fintype V] [DecidableEq V] {H : Finset (Finset V)} {d μ μ' η η' : ℝ}
    (hd : 0 ≤ d) (hμμ : μ ≤ μ') (hηη : η ≤ η')
    (hReg : Hypergraph.NearlyRegularMost H d μ η) :
    Hypergraph.NearlyRegularMost H d μ' η' := by
  rcases hReg with ⟨Exc, hExc, hdeg⟩
  refine ⟨Exc, ?_, ?_⟩
  · exact hExc.trans (mul_le_mul_of_nonneg_right hηη (Nat.cast_nonneg _))
  · intro v hv
    obtain ⟨hlo, hhi⟩ := hdeg v hv
    constructor
    · have hleft : (1 - μ') * d ≤ (1 - μ) * d := by
        exact mul_le_mul_of_nonneg_right (by linarith) hd
      exact hleft.trans hlo
    · have hright : (1 + μ) * d ≤ (1 + μ') * d := by
        exact mul_le_mul_of_nonneg_right (by linarith) hd
      exact hhi.trans hright

/-- Majority near-regularity is monotone in the exceptional-set tolerance alone. -/
theorem Byproduct_nearlyRegularMost_mono_eta
    {V : Type} [Fintype V] [DecidableEq V] {H : Finset (Finset V)} {d μ η η' : ℝ}
    (hηη : η ≤ η') (hReg : Hypergraph.NearlyRegularMost H d μ η) :
    Hypergraph.NearlyRegularMost H d μ η' := by
  rcases hReg with ⟨Exc, hExc, hdeg⟩
  refine ⟨Exc, ?_, hdeg⟩
  exact hExc.trans (mul_le_mul_of_nonneg_right hηη (Nat.cast_nonneg _))

/-- Strict near-regularity gives the majority version with any nonnegative exceptional-set
tolerance. This is the explicit no-exception-to-majority bridge used by the dense route. -/
theorem Byproduct_nearlyRegular_to_nearlyRegularMost
    {V : Type} [Fintype V] [DecidableEq V] {H : Finset (Finset V)} {d μ η : ℝ}
    (hη : 0 ≤ η) (hReg : Hypergraph.NearlyRegular H d μ) :
    Hypergraph.NearlyRegularMost H d μ η :=
  hReg.nearlyRegularMost hη

/-- Codegree boundedness is monotone in the bound. -/
theorem Byproduct_codegreeBounded_mono
    {V : Type} [DecidableEq V] {H : Finset (Finset V)} {C C' : ℝ}
    (hCC : C ≤ C') (hCod : Hypergraph.CodegreeBounded H C) :
    Hypergraph.CodegreeBounded H C' := by
  intro x y hxy
  exact (hCod x y hxy).trans hCC

/-- The typed triangle hypergraph is `CodegreeBounded C` for every `C ≥ 1`. This is the
paper-facing monotone form of the sharp codegree-one fact. -/
theorem Byproduct_triangleHypergraphSub_codegreeBounded_of_one_le
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : ℝ} (hC : 1 ≤ C) :
    Hypergraph.CodegreeBounded (Nibble.YusterE.triangleHypergraphSub G) C := by
  intro E E' hne
  have hle1 : (Hypergraph.codegree (Nibble.YusterE.triangleHypergraphSub G) E E' : ℝ) ≤ 1 := by
    exact_mod_cast Nibble.YusterE.triangleHypergraphSub_codegree_le_one G hne
  exact hle1.trans hC

/-- Finite triangle-incidence LP duality byproduct: cover optimum is bounded by packing optimum. -/
theorem Byproduct_triangle_LP_duality
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Nibble.AX1.tau3Star G ≤ Nibble.YusterE.nu3star G :=
  Nibble.AX1.tau3Star_le_nu3star G

/-- The edge-based triangle hypergraph is exactly 3-uniform. -/
theorem Byproduct_triangleHypergraphE_uniform
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Hypergraph.IsUniform (Nibble.YusterE.triangleHypergraphE G) 3 :=
  Nibble.YusterE.triangleHypergraphE_uniform G

/-- Sharp codegree input for the edge-based triangle hypergraph: two distinct graph-edges
belong to at most one common triangle. -/
theorem Byproduct_triangleHypergraphE_codegree_le_one
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {e e' : Finset V} (hne : e ≠ e') :
    Hypergraph.codegree (Nibble.YusterE.triangleHypergraphE G) e e' ≤ 1 :=
  Nibble.YusterE.triangleHypergraphE_codegree_le_one G hne

/-- Degree in the edge-based triangle hypergraph is the number of graph-triangles using that edge. -/
theorem Byproduct_triangleHypergraphE_degree
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) :
    Hypergraph.degree (Nibble.YusterE.triangleHypergraphE G) e
      = ((G.cliqueFinset 3).filter (fun t => e ∈ t.powersetCard 2)).card :=
  Nibble.YusterE.triangleHypergraphE_degree G e

/-- The maximum defining `ν₃` is attained by an actual edge-disjoint triangle packing. -/
theorem Byproduct_nu3_achieved
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ M, Hypergraph.IsMatching (Nibble.YusterE.triangleHypergraphE G) M ∧
      M.card = Nibble.YusterE.nu3 G :=
  Nibble.YusterE.nu3_achieved G

/-- Weak triangle-packing duality: the integral packing number is bounded by its fractional
relaxation. -/
theorem Byproduct_nu3_le_nu3star
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Nibble.YusterE.nu3 G : ℝ) ≤ Nibble.YusterE.nu3star G :=
  Nibble.YusterE.nu3_le_nu3star G

/-- Fractional triangle packing is bounded by one third of the graph-edge count. -/
theorem Byproduct_nu3star_le_edges_div_three
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Nibble.YusterE.nu3star G ≤ ((G.cliqueFinset 2).card : ℝ) / 3 :=
  Nibble.YusterE.nu3star_le G

/-- Fine edge-count bound used in the vertex-gap conversion: `|E(G)| ≤ |V(G)|²/2`. -/
theorem Byproduct_edge_card_le_card_sq_div_two
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((G.cliqueFinset 2).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 2 := by
  have hle : (G.cliqueFinset 2).card ≤ (Fintype.card V).choose 2 := by
    have hsub : (G.cliqueFinset 2).card ≤
        (Finset.univ.powersetCard 2 : Finset (Finset V)).card := by
      apply Finset.card_le_card
      intro e he
      rw [SimpleGraph.mem_cliqueFinset_iff] at he
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ e, he.card_eq⟩
    rwa [Finset.card_powersetCard, Finset.card_univ] at hsub
  have hchooseNat : 2 * (Fintype.card V).choose 2 ≤ (Fintype.card V) ^ 2 := by
    rw [Nat.choose_two_right]
    have hdiv : 2 * (Fintype.card V * (Fintype.card V - 1) / 2)
        ≤ Fintype.card V * (Fintype.card V - 1) := by
      simpa [Nat.mul_comm] using
        (Nat.div_mul_le_self (Fintype.card V * (Fintype.card V - 1)) 2)
    have hmul : Fintype.card V * (Fintype.card V - 1) ≤ (Fintype.card V) ^ 2 := by
      nlinarith [Nat.sub_le (Fintype.card V) 1]
    exact hdiv.trans hmul
  have htwo : 2 * (G.cliqueFinset 2).card ≤ (Fintype.card V) ^ 2 := by omega
  have htwoR : (2 : ℝ) * ((G.cliqueFinset 2).card : ℝ) ≤
      (Fintype.card V : ℝ) ^ 2 := by
    exact_mod_cast htwo
  nlinarith

/-- Explicit majority-regular integrality-gap bound:
`ν₃* - ν₃ ≤ β |E(G)| / 3`. -/
theorem Byproduct_nu3star_sub_nu3_le_edge_gap_most
    (hN : Nibble.NibbleTheoremMost)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ},
      0 < d → d₀ ≤ d →
      Hypergraph.NearlyRegularMost (Nibble.YusterE.triangleHypergraphSub G) d μ η →
      Hypergraph.CodegreeBounded (Nibble.YusterE.triangleHypergraphSub G) (μ * d) →
      Nibble.YusterE.nu3star G - (Nibble.YusterE.nu3 G : ℝ) ≤
        β * ((G.cliqueFinset 2).card : ℝ) / 3 :=
  Nibble.YusterE.nu3star_sub_nu3_le_most G hN hβ

/-- Monotonicity of the edge-gap constant: once the gap is bounded with `β`, it is bounded
with any larger `β'`. -/
theorem Byproduct_edge_gap_mono
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {β β' : ℝ} (hβle : β ≤ β')
    (hgap : Nibble.YusterE.nu3star G - (Nibble.YusterE.nu3 G : ℝ) ≤
      β * ((G.cliqueFinset 2).card : ℝ) / 3) :
    Nibble.YusterE.nu3star G - (Nibble.YusterE.nu3 G : ℝ) ≤
      β' * ((G.cliqueFinset 2).card : ℝ) / 3 := by
  have hE : 0 ≤ ((G.cliqueFinset 2).card : ℝ) / 3 := by positivity
  have hmono : β * (((G.cliqueFinset 2).card : ℝ) / 3) ≤
      β' * (((G.cliqueFinset 2).card : ℝ) / 3) :=
    mul_le_mul_of_nonneg_right hβle hE
  have hleft : β * ((G.cliqueFinset 2).card : ℝ) / 3 =
      β * (((G.cliqueFinset 2).card : ℝ) / 3) := by ring
  have hright : β' * ((G.cliqueFinset 2).card : ℝ) / 3 =
      β' * (((G.cliqueFinset 2).card : ℝ) / 3) := by ring
  rw [hleft] at hgap
  rw [hright]
  exact hgap.trans hmono

/-- Majority-regular gap converted to vertex form using the fine edge bound
`|E(G)| ≤ |V(G)|²/2`. This is the optimized version of the coarse `|E|≤|V|²` conversion. -/
theorem Byproduct_nu3star_sub_nu3_le_eps_most_fine_edges
    (hN : Nibble.NibbleTheoremMost)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ},
      0 < d → d₀ ≤ d →
      Hypergraph.NearlyRegularMost (Nibble.YusterE.triangleHypergraphSub G) d μ η →
      Hypergraph.CodegreeBounded (Nibble.YusterE.triangleHypergraphSub G) (μ * d) →
      Nibble.YusterE.nu3star G - (Nibble.YusterE.nu3 G : ℝ) ≤
        ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ :=
    Nibble.YusterE.nu3star_sub_nu3_le_most G hN (by linarith : (0 : ℝ) < 6 * ε)
  refine ⟨μ, hμ, η, hη, d₀, hd₀, fun {d} hd hd0 hReg hCod => ?_⟩
  have hgap := hmain hd hd0 hReg hCod
  have hE := Byproduct_edge_card_le_card_sq_div_two G
  calc Nibble.YusterE.nu3star G - (Nibble.YusterE.nu3 G : ℝ)
      ≤ (6 * ε) * ((G.cliqueFinset 2).card : ℝ) / 3 := hgap
    _ = 2 * ε * ((G.cliqueFinset 2).card : ℝ) := by ring
    _ ≤ 2 * ε * ((Fintype.card V : ℝ) ^ 2 / 2) := by
      exact mul_le_mul_of_nonneg_left hE (by positivity)
    _ = ε * (Fintype.card V : ℝ) ^ 2 := by ring

/-- Attained packing witness for the majority-regular nibble lower bound: not only
`ν₃ ≥ (1-β)|E|/3`, but an actual edge-disjoint triangle packing realizes that bound. -/
theorem Byproduct_nu3_lower_bound_attained_most
    (hN : Nibble.NibbleTheoremMost)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ},
      0 < d → d₀ ≤ d →
      Hypergraph.NearlyRegularMost (Nibble.YusterE.triangleHypergraphSub G) d μ η →
      Hypergraph.CodegreeBounded (Nibble.YusterE.triangleHypergraphSub G) (μ * d) →
      ∃ M, Hypergraph.IsMatching (Nibble.YusterE.triangleHypergraphE G) M ∧
        (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤ (M.card : ℝ) := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hlb⟩ := Nibble.YusterE.nu3_ge_nibble_most G hN hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, fun {d} hd hd0 hReg hCod => ?_⟩
  obtain ⟨M, hM, hMcard⟩ := Nibble.YusterE.nu3_achieved G
  refine ⟨M, hM, ?_⟩
  rw [hMcard]
  exact hlb hd hd0 hReg hCod

/-- The edge vertex type has cardinality equal to the number of graph edges. -/
theorem Byproduct_card_EdgeV
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card (Nibble.YusterE.EdgeV G) = (G.cliqueFinset 2).card :=
  Nibble.YusterE.card_EdgeV G

/-- The typed edge-vertex triangle hypergraph is exactly 3-uniform. -/
theorem Byproduct_triangleHypergraphSub_uniform
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Hypergraph.IsUniform (Nibble.YusterE.triangleHypergraphSub G) 3 :=
  Nibble.YusterE.triangleHypergraphSub_uniform G

/-- The typed edge-vertex triangle hypergraph also has sharp codegree at most one. -/
theorem Byproduct_triangleHypergraphSub_codegree_le_one
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {E E' : Nibble.YusterE.EdgeV G} (hne : E ≠ E') :
    Hypergraph.codegree (Nibble.YusterE.triangleHypergraphSub G) E E' ≤ 1 :=
  Nibble.YusterE.triangleHypergraphSub_codegree_le_one G hne

/-- The typed edge-vertex triangle hypergraph has one hyperedge for each graph triangle. -/
theorem Byproduct_triangleHypergraphSub_card
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Nibble.YusterE.triangleHypergraphSub G).card = (G.cliqueFinset 3).card :=
  Nibble.YusterE.triangleHypergraphSub_card G

/-- Handshake for the typed edge-vertex triangle hypergraph:
the total typed edge-degree is three times the number of graph triangles. -/
theorem Byproduct_sum_degree_triangleHypergraphSub
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ E : Nibble.YusterE.EdgeV G,
      Hypergraph.degree (Nibble.YusterE.triangleHypergraphSub G) E
        = 3 * (G.cliqueFinset 3).card :=
  Nibble.YusterE.sum_degree_triangleHypergraphSub G

/-- A matching in the typed edge-vertex triangle hypergraph gives an edge-disjoint triangle
packing counted by the paper's `ν₃`. This is the clean bridge from the nibble's typed
hypergraph output to the manuscript's triangle-packing invariant. -/
theorem Byproduct_triangleHypergraphSub_matching_card_le_nu3
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (Nibble.YusterE.EdgeV G))}
    (hM : Hypergraph.IsMatching (Nibble.YusterE.triangleHypergraphSub G) M) :
    M.card ≤ Nibble.YusterE.nu3 G :=
  Nibble.YusterE.sub_matching_card_le_nu3 G hM

/-- Real-valued form of the typed-hypergraph-to-`ν₃` bridge, convenient for LP and asymptotic
inequality chains. -/
theorem Byproduct_triangleHypergraphSub_matching_card_le_nu3_real
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (Nibble.YusterE.EdgeV G))}
    (hM : Hypergraph.IsMatching (Nibble.YusterE.triangleHypergraphSub G) M) :
    (M.card : ℝ) ≤ (Nibble.YusterE.nu3 G : ℝ) := by
  exact_mod_cast Byproduct_triangleHypergraphSub_matching_card_le_nu3 G hM

/-- Dense `9/10` graph-only packing lower bound, conditional on a nibble instance compatible with
the dense tolerance `μ = 1/9`. This theorem isolates the small remaining crux: the abstract
`NibbleTheoremMost` interface chooses `μ` existentially, while the dense window supplies
`μ = 1/9`. -/
theorem Byproduct_dense_nine_tenths_nu3_lower_bound_of_compatible_nibble
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {β η d₀ : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (hNib :
      ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
        Hypergraph.NearlyRegularMost
          (Nibble.YusterE.triangleHypergraphSub G) d (1 / 9) η →
        Hypergraph.CodegreeBounded
          (Nibble.YusterE.triangleHypergraphSub G) ((1 / 9 : ℝ) * d) →
        ∃ M : Finset (Finset (Nibble.YusterE.EdgeV G)),
          Hypergraph.IsMatching (Nibble.YusterE.triangleHypergraphSub G) M ∧
          (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤ (M.card : ℝ))
    (hmin : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (hcard : 10 ≤ Fintype.card V)
    (hd₀ : d₀ ≤ (9 / 10 : ℝ) * (Fintype.card V : ℝ)) :
    (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤
      (Nibble.YusterE.nu3 G : ℝ) := by
  have hηnonneg : 0 ≤ η := le_of_lt hη
  obtain ⟨_hunif, hReg, hCod, _hceil, _hsize⟩ :=
    Byproduct_dense_triangleSub_full_nibble_input_nine_tenths G hmin hcard hηnonneg
  have hd : 0 < (9 / 10 : ℝ) * (Fintype.card V : ℝ) := by
    have hcardR : (0 : ℝ) < (Fintype.card V : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 10) hcard)
    positivity
  obtain ⟨M, hM, hMcard⟩ := hNib hd hd₀ hReg hCod
  exact hMcard.trans (Byproduct_triangleHypergraphSub_matching_card_le_nu3_real G hM)

/-- Attained dense packing witness under the same `μ = 1/9` compatibility hypothesis: the dense
route produces an actual typed edge-disjoint triangle packing with the target lower bound. -/
theorem Byproduct_dense_nine_tenths_attained_matching_of_compatible_nibble
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {β η d₀ : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (hNib :
      ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
        Hypergraph.NearlyRegularMost
          (Nibble.YusterE.triangleHypergraphSub G) d (1 / 9) η →
        Hypergraph.CodegreeBounded
          (Nibble.YusterE.triangleHypergraphSub G) ((1 / 9 : ℝ) * d) →
        ∃ M : Finset (Finset (Nibble.YusterE.EdgeV G)),
          Hypergraph.IsMatching (Nibble.YusterE.triangleHypergraphSub G) M ∧
          (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤ (M.card : ℝ))
    (hmin : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (hcard : 10 ≤ Fintype.card V)
    (hd₀ : d₀ ≤ (9 / 10 : ℝ) * (Fintype.card V : ℝ)) :
    ∃ M : Finset (Finset (Nibble.YusterE.EdgeV G)),
      Hypergraph.IsMatching (Nibble.YusterE.triangleHypergraphSub G) M ∧
      (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤ (M.card : ℝ) := by
  have hηnonneg : 0 ≤ η := le_of_lt hη
  obtain ⟨_hunif, hReg, hCod, _hceil, _hsize⟩ :=
    Byproduct_dense_triangleSub_full_nibble_input_nine_tenths G hmin hcard hηnonneg
  have hd : 0 < (9 / 10 : ℝ) * (Fintype.card V : ℝ) := by
    have hcardR : (0 : ℝ) < (Fintype.card V : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 10) hcard)
    positivity
  exact hNib hd hd₀ hReg hCod

/-- Dense `9/10` graph-only integrality-gap bound, again conditional on a nibble instance
compatible with the dense tolerance `μ = 1/9`. The edge-to-vertex conversion uses the sharper
formalized bound `|E| ≤ |V|²/2`. -/
theorem Byproduct_dense_nine_tenths_gap_of_compatible_nibble
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε η d₀ : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hNib :
      ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
        Hypergraph.NearlyRegularMost
          (Nibble.YusterE.triangleHypergraphSub G) d (1 / 9) η →
        Hypergraph.CodegreeBounded
          (Nibble.YusterE.triangleHypergraphSub G) ((1 / 9 : ℝ) * d) →
        ∃ M : Finset (Finset (Nibble.YusterE.EdgeV G)),
          Hypergraph.IsMatching (Nibble.YusterE.triangleHypergraphSub G) M ∧
          (1 - 6 * ε) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤ (M.card : ℝ))
    (hmin : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (hcard : 10 ≤ Fintype.card V)
    (hd₀ : d₀ ≤ (9 / 10 : ℝ) * (Fintype.card V : ℝ)) :
    Nibble.YusterE.nu3star G - (Nibble.YusterE.nu3 G : ℝ) ≤
      ε * (Fintype.card V : ℝ) ^ 2 := by
  have hβ : 0 < 6 * ε := by positivity
  have hlb := Byproduct_dense_nine_tenths_nu3_lower_bound_of_compatible_nibble
    G hβ hη hNib hmin hcard hd₀
  have hfrac := Byproduct_nu3star_le_edges_div_three G
  have hE := Byproduct_edge_card_le_card_sq_div_two G
  have hgap_edge : Nibble.YusterE.nu3star G - (Nibble.YusterE.nu3 G : ℝ)
      ≤ 2 * ε * ((G.cliqueFinset 2).card : ℝ) := by
    have hrewrite : (1 - 6 * ε) * (((G.cliqueFinset 2).card : ℝ) / 3)
        = ((G.cliqueFinset 2).card : ℝ) / 3 -
          (6 * ε) * (((G.cliqueFinset 2).card : ℝ) / 3) := by ring
    rw [hrewrite] at hlb
    have hscale : (6 * ε) * (((G.cliqueFinset 2).card : ℝ) / 3)
        = 2 * ε * ((G.cliqueFinset 2).card : ℝ) := by ring
    rw [hscale] at hlb
    linarith
  calc Nibble.YusterE.nu3star G - (Nibble.YusterE.nu3 G : ℝ)
      ≤ 2 * ε * ((G.cliqueFinset 2).card : ℝ) := hgap_edge
    _ ≤ 2 * ε * ((Fintype.card V : ℝ) ^ 2 / 2) := by
      exact mul_le_mul_of_nonneg_left hE (by positivity)
    _ = ε * (Fintype.card V : ℝ) ^ 2 := by ring

/-- Dense graph-only gap with the tolerance extracted from the nibble theorem. This removes the
fixed `μ = 1/9` compatibility clause: the minimum-degree threshold is instead the algebraic
threshold attached to the nibble's own `μ`. -/
theorem Byproduct_dense_graph_only_gap_of_nibble_tolerance
    (hN : Nibble.NibbleTheoremMost)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      (d₀ ≤ (Fintype.card V : ℝ) / (1 + μ) →
        1 ≤ μ * ((Fintype.card V : ℝ) / (1 + μ)) →
        Fintype.card V ≤ 2 * G.minDegree →
        (Fintype.card V : ℝ) / (1 + μ) ≤ (G.minDegree : ℝ) →
        Nibble.YusterE.nu3star G - (Nibble.YusterE.nu3 G : ℝ) ≤
          ε * (Fintype.card V : ℝ) ^ 2) := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ :=
    Nibble.YusterE.nu3star_sub_nu3_le_most G hN (by linarith : (0 : ℝ) < 6 * ε)
  refine ⟨μ, hμ, η, hη, d₀, hd₀, ?_⟩
  intro hd0 hcodeg h2D hmin
  let d : ℝ := (Fintype.card V : ℝ) / (1 + μ)
  have hdenpos : 0 < 1 + μ := by linarith
  have hdpos : 0 < d := lt_of_lt_of_le hd₀ hd0
  have hscale : (1 + μ) * d = (Fintype.card V : ℝ) := by
    dsimp [d]
    field_simp [ne_of_gt hdenpos]
  have hbase : (Fintype.card V : ℝ) ≤ (1 + μ) * d := by
    linarith
  have hhi : (Fintype.card V : ℝ) ≤ (1 + μ) * d := hbase
  have hlo : (1 - μ) * d ≤ 2 * (G.minDegree : ℝ) - (Fintype.card V : ℝ) := by
    dsimp [d] at hmin ⊢
    have hmin2 : 2 * ((Fintype.card V : ℝ) / (1 + μ)) ≤ 2 * (G.minDegree : ℝ) :=
      mul_le_mul_of_nonneg_left hmin (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hdata := Nibble.YusterE.triangleSub_linearSized_data_of_minDeg G G.minDegree
    (fun x => G.minDegree_le_degree x) h2D
    (μ := μ) (η := η) (d := d) (L := 1 + μ)
    (le_of_lt hη) hcodeg hbase hlo hhi
  have hgap := hmain hdpos hd0 hdata.1 hdata.2.1
  have hE := Byproduct_edge_card_le_card_sq_div_two G
  calc Nibble.YusterE.nu3star G - (Nibble.YusterE.nu3 G : ℝ)
      ≤ (6 * ε) * ((G.cliqueFinset 2).card : ℝ) / 3 := hgap
    _ = 2 * ε * ((G.cliqueFinset 2).card : ℝ) := by ring
    _ ≤ 2 * ε * ((Fintype.card V : ℝ) ^ 2 / 2) := by
      exact mul_le_mul_of_nonneg_left hE (by positivity)
    _ = ε * (Fintype.card V : ℝ) ^ 2 := by ring

/-- `r`-uniform nibble byproduct; the triangle case is one specialization. -/
theorem Byproduct_almostPerfectMatching_uniform
    (hN : Nibble.NibbleTheoremMost)
    (r : ℕ) (hr : 2 ≤ r) {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
    ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (d : ℝ), 0 < d → d₀ ≤ d →
      Hypergraph.IsUniform H r → Hypergraph.NearlyRegularMost H d μ η →
      Hypergraph.CodegreeBounded H (μ * d) →
      ∃ M : Finset (Finset W), Hypergraph.IsMatching H M ∧
        (1 - β) * ((Fintype.card W : ℝ) / r) ≤ (M.card : ℝ) :=
  Nibble.YusterE.almostPerfectMatching_uniform hN r hr hβ

/-- Strict near-regular triangle-packing gap, obtained as a specialization of the majority-regular
nibble transfer. -/
theorem Byproduct_nu3star_sub_nu3_le_eps_strict
    (hN : Nibble.NibbleTheoremMost)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ},
      0 < d → d₀ ≤ d →
      Hypergraph.NearlyRegular (Nibble.YusterE.triangleHypergraphSub G) d μ →
      Hypergraph.CodegreeBounded (Nibble.YusterE.triangleHypergraphSub G) (μ * d) →
      Nibble.YusterE.nu3star G - (Nibble.YusterE.nu3 G : ℝ) ≤
        ε * (Fintype.card V : ℝ) ^ 2 :=
  Nibble.YusterE.nu3star_sub_nu3_le_eps_strict G hN hε

/-- **Byproduct (dense maximum-degree triangle nibble).**  In the dense regime `9|V| ≤ 10·δ(G)`,
every sufficiently large graph has an edge-disjoint family of triangles whose *uncovered leftover
has maximum degree at most `η|V|`*, for every `η > 0`.  This is the per-vertex (maximum-degree) form
of the Haxell–Rödl / Pippenger–Spencer nibble — strictly stronger than the near-regularity data of
`PaperIII.Byproduct_dense_triangleSub_linearSized_data_of_minDeg`: it is the actual approximate
triangle decomposition, with degree control on the remainder rather than only a total-leftover
bound.  Proved from the corrected nibble engine `Nibble.nibbleTheoremMostCeil_holds` via the dense
star-potential argument, unconditionally (no residual interface). -/
theorem Byproduct_dense_triangleNibble_maxDegree (η : ℝ) (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ P : Finset (Finset V),
        (∀ t ∈ P, G.IsNClique 3 t) ∧
        (P : Set (Finset V)).Pairwise (fun s t => Disjoint (Nibble.triEdges s) (Nibble.triEdges t)) ∧
        ∀ v : V,
          (((G.edgeFinset \ (P.biUnion Nibble.triEdges)).filter (fun e => v ∈ e)).card : ℝ)
            ≤ η * (Fintype.card V : ℝ) :=
  Nibble.denseTriNibbleMaxDeg_holds η hη

end PaperIII
