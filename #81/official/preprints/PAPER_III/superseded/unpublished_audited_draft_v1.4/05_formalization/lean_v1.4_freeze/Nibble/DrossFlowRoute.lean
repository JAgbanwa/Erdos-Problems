/-
# Nibble — Dross's flow route to a spread fractional triangle decomposition

`Nibble/DrossTransfer.lean` builds the `K₄` transfer machinery: a nonnegative flow `f` on the
network whose nodes are the edges of `G` and whose arcs are the *opposite pairs* of `K₄`s turns the
constant base weighting `w0` into

  `transferDecomp G w0 f`,

whose coverage at an edge `e` is `w0 · codeg(e) + div f (e)`, and whose deviation from `w0` at a
triangle is at most half the total capacity flowing through that triangle.

This file closes the loop with the max-flow–min-cut theorem of `Nibble/FlowFeasibility.lean`:

* `Nibble.baseWeight` — the *balanced* base weight `|E| / (3 · #triangles)`, the unique constant
  weighting whose total deficiency vanishes (`Nibble.sum_deficiency_baseWeight`);
* `Nibble.IsDrossTransferCert` — a **transfer certificate** for `G` at base weight `w0`: capacities
  supported on opposite pairs of `K₄`s, whose throughput at every triangle is at most `w0` and
  which satisfy the **cut condition** for the deficiency demands;
* `Nibble.exists_spread_decomp_of_cert` — a transfer certificate yields an *exact* fractional
  triangle decomposition with all weights in `[0, 2 w0]`;
* `Nibble.DrossTransferFeasible`, `Nibble.drossFractionalQuantSpread_of_transferFeasible` —
  consequently, if every graph at the Dross density `9|V| ≤ 10 δ(G)` admits a transfer
  certificate, then `Nibble.DrossFractionalQuantSpread` holds with `C = 5/2`, and with it the whole
  chain down to `Nibble.DenseTriangleNibbleDeg` for every `β > 1/10`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DrossTransfer
import Nibble.FracRounding

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Double counting triangles -/

/-- **Double counting.**  Summing the codegree over the edges counts every triangle three times. -/
theorem sum_card_trianglesThrough (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ e : EdgeV G, (trianglesThrough G e).card = 3 * (triangleHypergraphSub G).card := by
  classical
  have hstep : ∀ e : EdgeV G, (trianglesThrough G e).card
      = ∑ T ∈ triangleHypergraphSub G, if e ∈ T then 1 else 0 := by
    intro e
    rw [trianglesThrough, Finset.card_filter]
  rw [Finset.sum_congr rfl (fun e _ => hstep e), Finset.sum_comm]
  have hinner : ∀ T ∈ triangleHypergraphSub G,
      (∑ e : EdgeV G, if e ∈ T then 1 else 0) = 3 := by
    intro T hT
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]
    exact triangleHypergraphSub_uniform G T hT
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, mul_comm]

/-! ### The balanced base weight -/

/-- **The balanced base weight** `|E| / (3 · #triangles)`: the unique constant triangle weighting
whose total coverage equals the number of edges. -/
noncomputable def baseWeight (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (Fintype.card (EdgeV G) : ℝ) / (3 * ((triangleHypergraphSub G).card : ℝ))

/-- **The base weight is balanced**: the deficiencies `1 - w0 · codeg(e)` sum to zero. -/
theorem sum_deficiency_baseWeight (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : 0 < (triangleHypergraphSub G).card) :
    ∑ e : EdgeV G, (1 - baseWeight G * ((trianglesThrough G e).card : ℝ)) = 0 := by
  have hTR : (0 : ℝ) < ((triangleHypergraphSub G).card : ℝ) := by exact_mod_cast hT
  have hsum : ∑ e : EdgeV G, ((trianglesThrough G e).card : ℝ)
      = 3 * ((triangleHypergraphSub G).card : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (sum_card_trianglesThrough G)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum, hsum, baseWeight, div_mul_cancel₀]
  · ring
  · positivity

/-! ### Transfer certificates -/

/-- **A transfer certificate** for `G` at base weight `w0`: nonnegative capacities supported on the
opposite pairs of `K₄`s of `G`, whose total throughput at every triangle is at most `w0`, and which
satisfy the cut condition for the deficiency demands `1 - w0 · codeg(e)`.

The cut condition is exactly the min-cut side of Dross's auxiliary network. -/
def IsDrossTransferCert (G : SimpleGraph V) [DecidableRel G.Adj] (w0 : ℝ)
    (cap : EdgeV G → EdgeV G → ℝ) : Prop :=
  (∀ e₁ e₂, 0 ≤ cap e₁ e₂) ∧
  (∀ e₁ e₂, cap e₁ e₂ = cap e₂ e₁) ∧
  (∀ e₁ e₂, cap e₁ e₂ ≠ 0 → IsOppPair G e₁ e₂) ∧
  (∀ T ∈ triangleHypergraphSub G,
    (1 / 4) * ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G, cap e₁ e₂ * |transferSign G e₁ e₂ T| ≤ w0) ∧
  (∀ S : Finset (EdgeV G),
    ∑ e ∈ S, (1 - w0 * ((trianglesThrough G e).card : ℝ)) ≤ ∑ x ∈ Sᶜ, ∑ y ∈ S, cap x y)

/-- **A transfer certificate produces an exact spread decomposition.**  Given the certificate and
the balance of the deficiencies, the max-flow–min-cut theorem supplies a feasible flow, and the
`K₄` transfer machinery converts the base weighting into an exact fractional triangle decomposition
with all weights in `[0, 2 w0]`. -/
theorem exists_spread_decomp_of_cert (G : SimpleGraph V) [DecidableRel G.Adj] {w0 : ℝ}
    {cap : EdgeV G → EdgeV G → ℝ}
    (hbal : ∑ e : EdgeV G, (1 - w0 * ((trianglesThrough G e).card : ℝ)) = 0)
    (hcert : IsDrossTransferCert G w0 cap) :
    ∃ w : Finset (EdgeV G) → ℝ, IsFracTriangleDecomp G w ∧
      ∀ T ∈ triangleHypergraphSub G, w T ≤ 2 * w0 := by
  classical
  obtain ⟨hcapnn, hcapsymm, hcapsupp, hcapthr, hcapcut⟩ := hcert
  obtain ⟨f, hf0, hfle, hfdiv⟩ :=
    Flow.exists_feasible_of_cut cap (fun e => 1 - w0 * ((trianglesThrough G e).card : ℝ))
      hcapnn hbal hcapcut
  -- cancel opposite flows: on each unordered pair only one direction survives
  set f' : EdgeV G → EdgeV G → ℝ := fun a b => max (f a b - f b a) 0 with hf'_def
  have hf'0 : ∀ a b, 0 ≤ f' a b := fun a b => le_max_right _ _
  have hf'le : ∀ a b, f' a b ≤ f a b := by
    intro a b
    exact max_le (by linarith only [hf0 b a]) (hf0 a b)
  have hf'pair : ∀ a b, f' a b + f' b a = |f a b - f b a| := by
    intro a b
    rcases le_total (f a b) (f b a) with h | h
    · rw [hf'_def]
      simp only
      rw [max_eq_right (by linarith), max_eq_left (by linarith),
        abs_of_nonpos (by linarith)]
      ring
    · rw [hf'_def]
      simp only
      rw [max_eq_left (by linarith), max_eq_right (by linarith),
        abs_of_nonneg (by linarith)]
      ring
  have hf'net : ∀ e : EdgeV G, Flow.netFlow f' e = Flow.netFlow f e := by
    intro e
    rw [Flow.netFlow, Flow.netFlow, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rcases le_total (f y e) (f e y) with h | h
    · rw [hf'_def]
      simp only
      rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      ring
    · rw [hf'_def]
      simp only
      rw [max_eq_left (by linarith), max_eq_right (by linarith)]
      ring
  have hf'div : ∀ e : EdgeV G, Flow.netFlow f' e = 1 - w0 * ((trianglesThrough G e).card : ℝ) :=
    fun e => (hf'net e).trans (hfdiv e)
  refine ⟨transferDecomp G w0 f', ?_⟩
  have hsupp : ∀ e₁ e₂, f' e₁ e₂ ≠ 0 → IsOppPair G e₁ e₂ := by
    intro e₁ e₂ hne
    refine hcapsupp e₁ e₂ (fun hc => hne ?_)
    have h1 := hf'0 e₁ e₂
    have h2 := (hf'le e₁ e₂).trans (hfle e₁ e₂)
    rw [hc] at h2
    linarith
  have hbnd : ∀ T ∈ triangleHypergraphSub G,
      (1 / 2) * ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G, f' e₁ e₂ * |transferSign G e₁ e₂ T| ≤ w0 := by
    intro T hT
    -- symmetrise: pair each arc with its reverse
    have hswap : ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G, f' e₁ e₂ * |transferSign G e₁ e₂ T|
        = ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G, f' e₂ e₁ * |transferSign G e₁ e₂ T| := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun e₁ _ => Finset.sum_congr rfl (fun e₂ _ => by
        rw [abs_transferSign_swap]))
    have hhalf : ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G, f' e₁ e₂ * |transferSign G e₁ e₂ T|
        = (1 / 2) * ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G,
            (f' e₁ e₂ + f' e₂ e₁) * |transferSign G e₁ e₂ T| := by
      have : ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G, (f' e₁ e₂ + f' e₂ e₁) * |transferSign G e₁ e₂ T|
          = (∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G, f' e₁ e₂ * |transferSign G e₁ e₂ T|)
            + ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G, f' e₂ e₁ * |transferSign G e₁ e₂ T| := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun e₁ _ => by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun e₂ _ => by ring))
      rw [this, ← hswap]
      ring
    have hpt : ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G,
        (f' e₁ e₂ + f' e₂ e₁) * |transferSign G e₁ e₂ T|
        ≤ ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G, cap e₁ e₂ * |transferSign G e₁ e₂ T| := by
      refine Finset.sum_le_sum (fun e₁ _ => Finset.sum_le_sum (fun e₂ _ => ?_))
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rw [hf'pair]
      rcases le_total (f e₁ e₂) (f e₂ e₁) with h | h
      · rw [abs_of_nonpos (by linarith)]
        have := hfle e₂ e₁
        have := hf0 e₁ e₂
        rw [hcapsymm e₁ e₂]
        linarith
      · rw [abs_of_nonneg (by linarith)]
        have := hfle e₁ e₂
        have := hf0 e₂ e₁
        linarith
    have := hcapthr T hT
    rw [hhalf]
    linarith
  exact isFracTriangleDecomp_transfer G hf'0 hsupp hf'div hbnd

/-! ### Non-vacuity -/

/-- **The codegree-regular case.**  If every edge of `G` lies in the same number `k > 0` of
triangles, the base weight is `1/k`, the uniform weighting is already exact, and the zero capacity
is a transfer certificate. -/
theorem isDrossTransferCert_zero_of_codegree_const (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 0 < k) (hreg : ∀ e : EdgeV G, (trianglesThrough G e).card = k)
    (he : Nonempty (EdgeV G)) :
    IsDrossTransferCert G (baseWeight G) (fun _ _ => 0) := by
  classical
  have hm : 0 < Fintype.card (EdgeV G) := Fintype.card_pos_iff.mpr he
  have hmR : (0 : ℝ) < (Fintype.card (EdgeV G) : ℝ) := by exact_mod_cast hm
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hsum : (3 : ℝ) * ((triangleHypergraphSub G).card : ℝ)
      = (Fintype.card (EdgeV G) : ℝ) * (k : ℝ) := by
    have h := sum_card_trianglesThrough G
    rw [Finset.sum_congr rfl (fun e (_ : e ∈ Finset.univ) => hreg e), Finset.sum_const,
      Finset.card_univ, smul_eq_mul] at h
    have : ((Fintype.card (EdgeV G) * k : ℕ) : ℝ) = ((3 * (triangleHypergraphSub G).card : ℕ) : ℝ) :=
      congrArg (fun j : ℕ => (j : ℝ)) h
    push_cast at this
    linarith
  have hbw : baseWeight G = 1 / (k : ℝ) := by
    rw [baseWeight, hsum]
    field_simp
  refine ⟨fun _ _ => le_rfl, fun _ _ => rfl, fun _ _ h => absurd rfl h, fun T _ => ?_, fun S => ?_⟩
  · simp only [zero_mul, Finset.sum_const_zero, mul_zero]
    rw [hbw]
    positivity
  · have hzero : ∀ e : EdgeV G, 1 - baseWeight G * ((trianglesThrough G e).card : ℝ) = 0 := by
      intro e
      rw [hreg e, hbw, one_div, inv_mul_cancel₀ (ne_of_gt hkR), sub_self]
    rw [Finset.sum_congr rfl (fun e (_ : e ∈ S) => hzero e)]
    simp

/-! ### The base weight at the Dross density -/

/-- At the Dross density every edge of a graph with an edge lies in a triangle, so there is a
triangle. -/
theorem triangleHypergraphSub_nonempty_of_dense (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) (e : EdgeV G) :
    0 < (triangleHypergraphSub G).card := by
  classical
  have hV : 10 ≤ Fintype.card V := ten_le_card_of_dense G hdense (nonempty_of_edgeV G e).some
  have hmin : (1 - (1 / 10 : ℝ)) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) := by
    have : (9 : ℝ) * (Fintype.card V : ℝ) ≤ 10 * (G.minDegree : ℝ) := by exact_mod_cast hdense
    linarith
  have hcod := card_commonNbrs_ge_of_minDegree G hmin e
  have hVR : (10 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV
  have hpos : (0 : ℝ) < ((commonNbrs G e).card : ℝ) := by linarith
  have hcard : 0 < (trianglesThrough G e).card := by
    rw [card_trianglesThrough_eq_commonNbrs]
    exact_mod_cast hpos
  obtain ⟨T, hT⟩ := Finset.card_pos.mp hcard
  exact Finset.card_pos.mpr ⟨T, (Finset.mem_filter.mp hT).1⟩

/-- **The base weight is `O(1/|V|)` at the Dross density**: `w0 ≤ 5 / (4|V|)`. -/
theorem baseWeight_le_of_dense (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) (e : EdgeV G) :
    baseWeight G ≤ 5 / (4 * (Fintype.card V : ℝ)) := by
  classical
  have hV : 10 ≤ Fintype.card V := ten_le_card_of_dense G hdense (nonempty_of_edgeV G e).some
  have hVR : (10 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV
  have hmin : (1 - (1 / 10 : ℝ)) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) := by
    have : (9 : ℝ) * (Fintype.card V : ℝ) ≤ 10 * (G.minDegree : ℝ) := by exact_mod_cast hdense
    linarith
  -- every edge has codegree at least `(4/5)|V|`
  have hcod : ∀ e' : EdgeV G, (4 / 5 : ℝ) * (Fintype.card V : ℝ)
      ≤ ((trianglesThrough G e').card : ℝ) := by
    intro e'
    have h := card_commonNbrs_ge_of_minDegree G hmin e'
    rw [show ((trianglesThrough G e').card : ℝ) = ((commonNbrs G e').card : ℝ) from by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (card_trianglesThrough_eq_commonNbrs G e')]
    linarith
  have hm : 0 < Fintype.card (EdgeV G) := Fintype.card_pos_iff.mpr ⟨e⟩
  have hmR : (0 : ℝ) < (Fintype.card (EdgeV G) : ℝ) := by exact_mod_cast hm
  have hsum : ∑ e' : EdgeV G, ((trianglesThrough G e').card : ℝ)
      = 3 * ((triangleHypergraphSub G).card : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (sum_card_trianglesThrough G)
  have hlow : (4 / 5 : ℝ) * (Fintype.card V : ℝ) * (Fintype.card (EdgeV G) : ℝ)
      ≤ 3 * ((triangleHypergraphSub G).card : ℝ) := by
    rw [← hsum]
    calc (4 / 5 : ℝ) * (Fintype.card V : ℝ) * (Fintype.card (EdgeV G) : ℝ)
        = ∑ _e' : EdgeV G, (4 / 5 : ℝ) * (Fintype.card V : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      _ ≤ ∑ e' : EdgeV G, ((trianglesThrough G e').card : ℝ) :=
          Finset.sum_le_sum (fun e' _ => hcod e')
  have hTpos : (0 : ℝ) < 3 * ((triangleHypergraphSub G).card : ℝ) := by nlinarith
  rw [baseWeight, div_le_div_iff₀ hTpos (by nlinarith)]
  linarith

/-! ### The route to the target -/

/-- **Dross's flow input.**  Every graph at the Dross density admits a transfer certificate at its
balanced base weight. -/
def DrossTransferFeasible : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    9 * Fintype.card V ≤ 10 * G.minDegree →
    ∃ cap : EdgeV G → EdgeV G → ℝ, IsDrossTransferCert G (baseWeight G) cap

/-- **The flow input closes the target.**  Transfer certificates at the Dross density give
`Nibble.DrossFractionalQuantSpread` with `C = 5/2`. -/
theorem drossFractionalQuantSpread_of_transferFeasible (h : DrossTransferFeasible) :
    DrossFractionalQuantSpread := by
  classical
  refine ⟨5 / 2, by norm_num, ?_⟩
  intro V _ _ G _ hdense
  by_cases hedge : Nonempty (EdgeV G)
  · obtain ⟨e⟩ := hedge
    have hV : 10 ≤ Fintype.card V := ten_le_card_of_dense G hdense (nonempty_of_edgeV G e).some
    have hVR : (10 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV
    obtain ⟨cap, hcert⟩ := h G hdense
    obtain ⟨w, hw, hwb⟩ := exists_spread_decomp_of_cert G
      (sum_deficiency_baseWeight G (triangleHypergraphSub_nonempty_of_dense G hdense e)) hcert
    refine ⟨w, hw, fun T hT => le_trans (hwb T hT) ?_⟩
    have hb := baseWeight_le_of_dense G hdense e
    have hn : (0 : ℝ) < (Fintype.card V : ℝ) := by linarith
    calc 2 * baseWeight G ≤ 2 * (5 / (4 * (Fintype.card V : ℝ))) := by linarith
      _ = 5 / 2 / (Fintype.card V : ℝ) := by field_simp; ring
  · -- no edges: the zero weighting works
    refine ⟨fun _ => 0, ⟨fun _ _ => le_rfl, fun e => absurd ⟨e⟩ hedge⟩, fun T hT => ?_⟩
    obtain ⟨e, -⟩ := exists_edge_of_mem_triangleHypergraphSub G hT
    exact absurd ⟨e⟩ hedge

/-- **The whole chain.**  Transfer certificates at the Dross density give
`Nibble.DenseGlobalSmallLeftover`. -/
theorem denseGlobalSmallLeftover_of_transferFeasible (h : DrossTransferFeasible) :
    DenseGlobalSmallLeftover :=
  denseGlobalSmallLeftover_of_drossSpread
    (drossFractionalSpread_of_quant (drossFractionalQuantSpread_of_transferFeasible h))

/-- **The `1/10` per-vertex bound** follows too. -/
theorem denseTriangleNibbleDeg_of_transferFeasible (h : DrossTransferFeasible) {β : ℝ}
    (hβ : 1 / 10 < β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) :=
  denseTriangleNibbleDeg_of_drossSpread
    (drossFractionalSpread_of_quant (drossFractionalQuantSpread_of_transferFeasible h)) hβ

end Nibble
