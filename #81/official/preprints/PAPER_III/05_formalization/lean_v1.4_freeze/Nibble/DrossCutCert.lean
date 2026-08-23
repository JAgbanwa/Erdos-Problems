/-
# Nibble — the Dross transfer certificate at the density `9|V| ≤ 10 δ(G)`

This file assembles the refined cut estimate.  For a graph `G` at the Dross density the uniform
capacity

  `cap = uniformCap G ((2 / (3|V|)) · baseWeight G)`

is a Dross transfer certificate at the balanced base weight:

* its throughput at every triangle is *exactly* `baseWeight G`
  (`Nibble.throughput_uniformCap_le` with `(3/2)|V| · c = w₀`);
* the base weight cancels out of the cut condition, which becomes the purely combinatorial
  inequality `3|V|(LA - KC) ≤ 2|E|X` supplied by `Nibble.cut_master`, whose six inputs come from
  `Nibble/DrossCutCount.lean` and `Nibble/DrossCutPartners.lean`.

Consequences: `Nibble.drossTransferFeasible`, and with it `Nibble.DrossFractionalQuantSpread`,
`Nibble.DenseGlobalSmallLeftover` and `Nibble.DenseTriangleNibbleDeg` for every `β > 1/10`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DrossCutPartners

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Small graphs at the Dross density are complete -/

/-- At the Dross density with fewer than `20` vertices every vertex is adjacent to every other. -/
theorem adj_of_dense_of_small (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) (hsmall : Fintype.card V < 20)
    {x z : V} (hxz : x ≠ z) : G.Adj x z := by
  classical
  have hdeg : G.minDegree ≤ G.degree x := G.minDegree_le_degree x
  have hlt : G.degree x < Fintype.card V := G.degree_lt_card_verts x
  have hdx : Fintype.card V - 1 ≤ G.degree x := by omega
  have hsub : G.neighborFinset x ⊆ Finset.univ.erase x := by
    intro y hy
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro h
    subst h
    exact (SimpleGraph.mem_neighborFinset G y y).mp hy |>.ne rfl
  have hcard : (Finset.univ.erase x).card = Fintype.card V - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have heq : G.neighborFinset x = Finset.univ.erase x := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [hcard, SimpleGraph.card_neighborFinset_eq_degree]
    exact hdx
  have : z ∈ G.neighborFinset x := by
    rw [heq]
    exact Finset.mem_erase.mpr ⟨hxz.symm, Finset.mem_univ _⟩
  exact (SimpleGraph.mem_neighborFinset G x z).mp this

/-- A complete graph at the Dross density is codegree-regular. -/
theorem card_trianglesThrough_of_small (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) (hsmall : Fintype.card V < 20)
    (e : EdgeV G) : (trianglesThrough G e).card = Fintype.card V - 2 := by
  classical
  have hcn : commonNbrs G e = Finset.univ \ e.val := by
    ext z
    simp only [commonNbrs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor
    · intro h hz
      exact (h z hz).ne rfl
    · intro hz x hx
      exact adj_of_dense_of_small G hdense hsmall (by rintro rfl; exact hz hx)
  have hval : e.val.card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp e.property).card_eq
  rw [card_trianglesThrough_eq_commonNbrs, hcn]
  have hkey := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ e.val)
  rw [Finset.card_univ, hval] at hkey
  omega

/-! ### The certificate -/

set_option maxHeartbeats 1000000 in
/-- **The refined transfer certificate.**  Every graph at the Dross density `9|V| ≤ 10 δ(G)` with
at least one edge admits the uniform capacity `(2/(3|V|)) · w₀` on the opposite pairs of its `K₄`s
as a Dross transfer certificate at its balanced base weight `w₀`. -/
theorem isDrossTransferCert_of_dense (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) (e0 : EdgeV G) :
    IsDrossTransferCert G (baseWeight G)
      (uniformCap G ((2 / (3 * (Fintype.card V : ℝ))) * baseWeight G)) := by
  classical
  by_cases hsmall : Fintype.card V < 20
  · -- the graph is complete: the codegrees are constant, so every deficiency vanishes
    have hV : 10 ≤ Fintype.card V := ten_le_card_of_dense G hdense (nonempty_of_edgeV G e0).some
    have hreg := card_trianglesThrough_of_small G hdense hsmall
    have hk : 0 < Fintype.card V - 2 := by omega
    have hn2 : ((Fintype.card V - 2 : ℕ) : ℝ) = (Fintype.card V : ℝ) - 2 := by
      have h2 : 2 ≤ Fintype.card V := by omega
      push_cast [Nat.cast_sub h2]
      ring
    have hn10 : (10 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV
    have hmpos : 0 < Fintype.card (EdgeV G) := Fintype.card_pos_iff.mpr ⟨e0⟩
    have hcod : ∀ e : EdgeV G,
        ((trianglesThrough G e).card : ℝ) = (Fintype.card V : ℝ) - 2 := by
      intro e; rw [hreg e, hn2]
    have hw0le : baseWeight G ≤ 1 / ((Fintype.card V : ℝ) - 2) :=
      baseWeight_le_of_codegree_ge G (by linarith) (fun e => le_of_eq (hcod e).symm) hmpos
    have hw0ge : 1 / ((Fintype.card V : ℝ) - 2) ≤ baseWeight G :=
      baseWeight_ge_of_codegree_le G (by linarith) (fun e => le_of_eq (hcod e))
        (triangleHypergraphSub_nonempty_of_dense G hdense e0)
    have hw0eq : baseWeight G = 1 / ((Fintype.card V : ℝ) - 2) := le_antisymm hw0le hw0ge
    have hne2 : ((Fintype.card V : ℝ) - 2) ≠ 0 := by intro h; linarith only [hn10, h]
    have hw0nn : 0 ≤ baseWeight G := by
      rw [hw0eq]; exact div_nonneg zero_le_one (by linarith)
    have hcnn : (0 : ℝ) ≤ (2 / (3 * (Fintype.card V : ℝ))) * baseWeight G := by
      have : (0 : ℝ) ≤ 2 / (3 * (Fintype.card V : ℝ)) := by positivity
      exact mul_nonneg this hw0nn
    have hzero : ∀ e : EdgeV G, 1 - baseWeight G * ((trianglesThrough G e).card : ℝ) = 0 := by
      intro e
      rw [hcod e, hw0eq]
      field_simp
      norm_num
    refine ⟨fun e₁ e₂ => ?_, fun e₁ e₂ => ?_, fun e₁ e₂ h => ?_, fun T hT => ?_, fun S => ?_⟩
    · rw [uniformCap]; split_ifs
      · exact hcnn
      · exact le_rfl
    · rw [uniformCap, uniformCap]
      by_cases hopp : IsOppPair G e₁ e₂
      · rw [if_pos hopp, if_pos hopp.symm]
      · rw [if_neg hopp, if_neg (fun hc => hopp hc.symm)]
    · by_contra hopp
      rw [uniformCap, if_neg hopp] at h
      exact h rfl
    · refine le_trans (throughput_uniformCap_le G hcnn hT) ?_
      have hne : (Fintype.card V : ℝ) ≠ 0 := by linarith only [hn10]
      have heq : (3 / 2 : ℝ) * (Fintype.card V : ℝ)
          * ((2 / (3 * (Fintype.card V : ℝ))) * baseWeight G) = baseWeight G := by field_simp
      rw [heq]
    · have hL : ∑ e ∈ S, (1 - baseWeight G * ((trianglesThrough G e).card : ℝ)) = 0 := by
        rw [Finset.sum_congr rfl (fun e (_ : e ∈ S) => hzero e), Finset.sum_const_zero]
      rw [hL, cut_uniformCap]
      have hX : 0 ≤ crossSum G S := by
        rw [crossSum]
        refine Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => ?_))
        split_ifs <;> norm_num
      exact mul_nonneg hcnn hX
  -- the main case
  push_neg at hsmall
  set n : ℝ := (Fintype.card V : ℝ) with hnd
  have hn20 : (20 : ℝ) ≤ n := by rw [hnd]; exact_mod_cast hsmall
  have hn0 : (0 : ℝ) < n := by linarith only [hn20]
  have hmpos : 0 < Fintype.card (EdgeV G) := Fintype.card_pos_iff.mpr ⟨e0⟩
  have hmposR : (0 : ℝ) < (Fintype.card (EdgeV G) : ℝ) := by exact_mod_cast hmpos
  have hTpos : 0 < (triangleHypergraphSub G).card :=
    triangleHypergraphSub_nonempty_of_dense G hdense e0
  have hTposR : (0 : ℝ) < ((triangleHypergraphSub G).card : ℝ) := by exact_mod_cast hTpos
  have hw0pos : 0 < baseWeight G := by
    rw [baseWeight]; positivity
  have hcnn : (0 : ℝ) ≤ (2 / (3 * n)) * baseWeight G := by positivity
  have hmin : (1 - (1 / 10 : ℝ)) * n ≤ (G.minDegree : ℝ) := by
    have : (9 : ℝ) * n ≤ 10 * (G.minDegree : ℝ) := by rw [hnd]; exact_mod_cast hdense
    linarith only [this]
  -- the codegree defect
  have hcodeq : ∀ e : EdgeV G,
      ((trianglesThrough G e).card : ℝ) = n - 2 - ((outsideOf G e).card : ℝ) := by
    intro e
    have h1 : ((trianglesThrough G e).card : ℝ) = ((commonNbrs G e).card : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (card_trianglesThrough_eq_commonNbrs G e)
    have h2 : ((outsideOf G e).card : ℝ) + ((commonNbrs G e).card : ℝ) + 2 = n := by
      rw [hnd]; exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (card_outsideOf G e)
    rw [h1]; linarith only [h2]
  have hsig_le : ∀ e : EdgeV G, ((outsideOf G e).card : ℝ) ≤ n / 5 - 2 := by
    intro e
    have h := card_commonNbrs_ge_of_minDegree G hmin e
    have h2 : ((outsideOf G e).card : ℝ) + ((commonNbrs G e).card : ℝ) + 2 = n := by
      rw [hnd]; exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (card_outsideOf G e)
    rw [← hnd] at h
    linarith only [h, h2]
  have hsig_nn : ∀ e : EdgeV G, (0 : ℝ) ≤ ((outsideOf G e).card : ℝ) :=
    fun e => Nat.cast_nonneg _
  -- the edge count
  have hm1 : (9 / 20) * n ^ 2 ≤ (Fintype.card (EdgeV G) : ℝ) := by
    have h := two_mul_card_edgeV G
    have hdeg : ∑ v : V, (G.degree v : ℝ) ≥ n * ((9 : ℝ) * n / 10) := by
      calc ∑ v : V, (G.degree v : ℝ) ≥ ∑ _v : V, ((9 : ℝ) * n / 10) := by
            refine Finset.sum_le_sum (fun v _ => ?_)
            have : (G.minDegree : ℝ) ≤ (G.degree v : ℝ) := by
              exact_mod_cast G.minDegree_le_degree v
            linarith only [hmin, this]
        _ = n * ((9 : ℝ) * n / 10) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hnd]
    nlinarith only [h, hdeg]
  -- the base weight identity
  have hsumcod : ∑ e : EdgeV G, ((trianglesThrough G e).card : ℝ)
      = 3 * ((triangleHypergraphSub G).card : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (sum_card_trianglesThrough G)
  have hbase : baseWeight G * (3 * ((triangleHypergraphSub G).card : ℝ))
      = (Fintype.card (EdgeV G) : ℝ) := by
    rw [baseWeight]
    field_simp
  refine ⟨fun e₁ e₂ => ?_, fun e₁ e₂ => ?_, fun e₁ e₂ h => ?_, fun T hT => ?_, fun S => ?_⟩
  · rw [uniformCap]; split_ifs
    · exact hcnn
    · exact le_rfl
  · rw [uniformCap, uniformCap]
    by_cases hopp : IsOppPair G e₁ e₂
    · rw [if_pos hopp, if_pos hopp.symm]
    · rw [if_neg hopp, if_neg (fun hc => hopp hc.symm)]
  · by_contra hopp
    rw [uniformCap, if_neg hopp] at h
    exact h rfl
  · refine le_trans (throughput_uniformCap_le G hcnn hT) ?_
    have hne : n ≠ 0 := ne_of_gt hn0
    have : (3 / 2 : ℝ) * n * ((2 / (3 * n)) * baseWeight G) = baseWeight G := by field_simp
    rw [this]
  -- the cut condition
  · rw [cut_uniformCap]
    set K : ℝ := (S.card : ℝ) with hK
    set L : ℝ := (Sᶜ.card : ℝ) with hL
    set A : ℝ := ∑ e ∈ S, ((outsideOf G e).card : ℝ) with hA
    set C : ℝ := ∑ e ∈ Sᶜ, ((outsideOf G e).card : ℝ) with hC
    have hKL : K + L = (Fintype.card (EdgeV G) : ℝ) := by
      rw [hK, hL]
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (Finset.card_add_card_compl S)
    have hACsum : A + C = ∑ e : EdgeV G, ((outsideOf G e).card : ℝ) := by
      rw [hA, hC, Finset.sum_add_sum_compl]
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have hA0 : (0 : ℝ) ≤ A := Finset.sum_nonneg (fun e _ => hsig_nn e)
    have hC0 : (0 : ℝ) ≤ C := Finset.sum_nonneg (fun e _ => hsig_nn e)
    have hAle : A ≤ (n / 5 - 2) * K := by
      calc A ≤ ∑ _e ∈ S, (n / 5 - 2) := Finset.sum_le_sum (fun e _ => hsig_le e)
        _ = (n / 5 - 2) * K := by rw [Finset.sum_const, nsmul_eq_mul, hK]; ring
    have hCle : C ≤ (n / 5 - 2) * L := by
      calc C ≤ ∑ _e ∈ Sᶜ, (n / 5 - 2) := Finset.sum_le_sum (fun e _ => hsig_le e)
        _ = (n / 5 - 2) * L := by rw [Finset.sum_const, nsmul_eq_mul, hL]; ring
    have hAC : (17 * n / 20) * (n * (n - 1) - 2 * (K + L)) ≤ A + C := by
      rw [hACsum, hKL]
      exact sum_card_outsideOf_ge G (by omega) hdense
    have hX0 : (0 : ℝ) ≤ crossSum G S := by
      rw [crossSum]
      refine Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => ?_))
      split_ifs <;> norm_num
    have hXK := cut_input_side G S
    have hXL0 := cut_input_side G Sᶜ
    rw [compl_compl, ← crossSum_compl G S] at hXL0
    have hXL : 2 * L * (K * L - (C + 2 * L) * (21 * n / 20) + C) + C ^ 2
        ≤ 2 * L * crossSum G S := by
      rw [← hnd] at hXL0
      rw [← hK, ← hL, ← hC] at hXL0
      linarith only [hXL0]
    have hXK' : 2 * K * (K * L - (A + 2 * K) * (21 * n / 20) + A) + A ^ 2
        ≤ 2 * K * crossSum G S := by
      rw [← hnd, ← hK, ← hL, ← hA] at hXK
      linarith only [hXK]
    have hmaster := cut_master hn20 hK0 hL0 hA0 hC0 hAle hCle hAC (by rw [hKL]; exact hm1)
      hX0 hXK' hXL
    -- turn the master inequality into the cut condition
    have hcodS : ∑ e ∈ S, (1 - baseWeight G * ((trianglesThrough G e).card : ℝ))
        = K - baseWeight G * (K * (n - 2) - A) := by
      have hstep : ∀ e ∈ S, (1 - baseWeight G * ((trianglesThrough G e).card : ℝ))
          = 1 - baseWeight G * (n - 2) + baseWeight G * ((outsideOf G e).card : ℝ) := by
        intro e _
        rw [hcodeq e]; ring
      rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum, ← hA, ← hK]
      ring
    have hall : baseWeight G * ((Fintype.card (EdgeV G) : ℝ) * (n - 2) - (A + C))
        = (Fintype.card (EdgeV G) : ℝ) := by
      have hs : ∑ e : EdgeV G, ((trianglesThrough G e).card : ℝ)
          = (Fintype.card (EdgeV G) : ℝ) * (n - 2) - (A + C) := by
        rw [hACsum]
        rw [Finset.sum_congr rfl (fun e (_ : e ∈ Finset.univ) => hcodeq e)]
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← hs, hsumcod, hbase]
    rw [hcodS]
    have hkey : (K - baseWeight G * (K * (n - 2) - A)) * (Fintype.card (EdgeV G) : ℝ)
        = baseWeight G * (L * A - K * C) := by
      linear_combination (-K) * hall + (-(baseWeight G * A)) * hKL
    have hpos : (0 : ℝ) < (Fintype.card (EdgeV G) : ℝ) * (3 * n) := by positivity
    refine le_of_mul_le_mul_right ?_ hpos
    have h1 : 3 * n * (L * A - K * C) ≤ 2 * (Fintype.card (EdgeV G) : ℝ) * crossSum G S := by
      rw [← hKL]; exact hmaster
    have h2 : (K - baseWeight G * (K * (n - 2) - A))
        * ((Fintype.card (EdgeV G) : ℝ) * (3 * n))
        = baseWeight G * (3 * n * (L * A - K * C)) := by
      rw [show (K - baseWeight G * (K * (n - 2) - A)) * ((Fintype.card (EdgeV G) : ℝ) * (3 * n))
          = ((K - baseWeight G * (K * (n - 2) - A)) * (Fintype.card (EdgeV G) : ℝ)) * (3 * n) from
        by ring, hkey]
      ring
    have h3 : (2 / (3 * n)) * baseWeight G * crossSum G S
        * ((Fintype.card (EdgeV G) : ℝ) * (3 * n))
        = baseWeight G * (2 * (Fintype.card (EdgeV G) : ℝ) * crossSum G S) := by
      field_simp
    rw [h2, h3]
    exact mul_le_mul_of_nonneg_left h1 hw0pos.le

/-! ### The target -/

/-- **Dross's flow input holds.**  Every graph at the Dross density `9|V| ≤ 10 δ(G)` admits a
transfer certificate at its balanced base weight. -/
theorem drossTransferFeasible : DrossTransferFeasible := by
  intro V _ _ G _ hdense
  classical
  by_cases hedge : Nonempty (EdgeV G)
  · obtain ⟨e0⟩ := hedge
    exact ⟨_, isDrossTransferCert_of_dense G hdense e0⟩
  · have hempty : IsEmpty (EdgeV G) := not_nonempty_iff.mp hedge
    refine ⟨fun _ _ => 0, fun _ _ => le_rfl, fun _ _ => rfl, fun _ _ h => absurd rfl h,
      fun T hT => ?_, fun S => ?_⟩
    · simp only [zero_mul, Finset.sum_const_zero, mul_zero]
      rw [baseWeight]
      positivity
    · simp [Finset.eq_empty_of_isEmpty S]

/-- **The Dross fractional spread target.** -/
theorem drossFractionalQuantSpread_final : DrossFractionalQuantSpread :=
  drossFractionalQuantSpread_of_transferFeasible drossTransferFeasible

/-- **The dense global small-leftover statement.** -/
theorem denseGlobalSmallLeftover_final : DenseGlobalSmallLeftover :=
  denseGlobalSmallLeftover_of_transferFeasible drossTransferFeasible

/-- **The `1/10` per-vertex nibble bound.** -/
theorem denseTriangleNibbleDeg_final {β : ℝ} (hβ : 1 / 10 < β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) :=
  denseTriangleNibbleDeg_of_transferFeasible drossTransferFeasible hβ

end Nibble
