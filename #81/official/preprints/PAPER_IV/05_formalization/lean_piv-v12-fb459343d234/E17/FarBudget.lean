import E17.Cleanup
import PaperIV.RC01DenseAssembly

/-!
# E17 Part B7: the improved far-branch cleanup budget, fed to the RC01 dense interface

The tree's far-branch (C.2) residual budget is
`5 (3δ + 1/k₀ + d) n² + 5 |H| θ`
(`PaperIV.RC01ResidualCoverage.offCanonicalValue_le_regularity_budget`,
`PaperIV.RC01ResidualTransferClosure.value_sub_dense_regularity_budget_le_profiles`,
`PaperIV.RC01DenseAssembly.packing_loss_le_of_dense_profile_round`), with `H = mixedPatterns R`.

Here the discarded edges `B = discardEdges G R (garbage R) d` are removed by the R3 cleanup of
`E17.Cleanup` instead of dropping every damaged copy, which costs `3|B|` instead of `5|B|`, and the
light profiles are handled by F1 + dropping, which costs `(N4 + 2 N3) θ` instead of `5 |H| θ`.

* `improved_copy_budget` — `V - w(R3(x)) ≤ 3 (3δ + 1/k₀ + d) n²`, and `R3(x)` avoids every
  discarded edge.  Fully proved from the tree's discard counts.
* `card_mixedPatterns` and `improved_le_old` — the new budget is never worse than the old one.
* `ImprovedGateGap` — the one remaining proposition: a profile-cleaned packing `y` (profile stage,
  cost `≤ (N4 + 2 N3) θ`, cf. `E17.Cleanup.profile_loss`) on which the physical gate retains
  `(1-u-v) w(y)` up to `ζ n²` (this is where fibre lower bounds after reconstruction are needed).
* `improved_far_loss` — `ImprovedGateGap → x.value - P.gain ≤ 3 (3δ + 1/k₀ + d) n² +
  (N4 + 2 N3) θ + (ζ + 5/6 (u+v)) n²`, through the same downstream algebra
  `PaperIV.RC01DenseAssembly.loss_le_of_retained_round`.
-/

namespace E17.FarBudget

open Finset PaperIV.FarRounding PaperIV.RegularityFormat PaperIV.RC01ResidualCoverage
  PaperIV.DiscardCounts PaperIV.RC01CanonicalSlots PaperIV.RC01K3Pool PaperIV.RC01MixedPatterns
  E17.Cleanup

section General

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α} [DecidableRel G.Adj]

/-- Number of `K₄` profiles (reduced `K₄` patterns). -/
noncomputable def N4 {δ : ℚ} (R : EqualRegularity G δ) : ℕ := (goodK4Slots R).card

/-- Number of triangle profiles (reduced `K₃` patterns). -/
noncomputable def N3 {δ : ℚ} (R : EqualRegularity G δ) : ℕ := (goodK3Slots R).card

/-- The tree's discard count (15.1), in unordered edges. -/
theorem card_discardEdges_budget {δ : ℚ} (hδ : 0 ≤ δ) (R : EqualRegularity G δ) (d : ℚ)
    (hd : 0 ≤ d) {k₀ : ℕ} (hk₀ : 0 < k₀) (hk : k₀ ≤ R.parts.card) :
    ((discardEdges G R (garbage R) d).card : ℚ) ≤
      (3 * δ + 1 / (k₀ : ℚ) + d) * (Fintype.card α : ℚ) ^ 2 := by
  have hcard : ((discardEdges G R (garbage R) d).card : ℚ)
      ≤ ((discardPairs G R (garbage R) d).card : ℚ) := by
    exact_mod_cast card_discardEdges_le R (garbage R) d
  have hpairs : ((discardPairs G R (garbage R) d).card : ℚ)
      ≤ (3 * δ + 1 / (k₀ : ℚ) + d) * (Fintype.card α : ℚ) ^ 2 := by
    rw [discardPairs]
    exact card_discards_le hδ R d hd hk₀ hk (garbage R) (card_garbage_le R)
  linarith

/-- **B7, copy part (improved C.2 budget).** R3-cleaning the discarded edges costs at most
`3 (3δ + 1/k₀ + d) n²` (the tree's C.2 loss charges `5 (3δ + 1/k₀ + d) n²`), and the cleaned
packing carries no weight on any copy using a discarded edge. -/
theorem improved_copy_budget {δ : ℚ} (hδ : 0 ≤ δ) (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (d : ℚ) (hd : 0 ≤ d) {k₀ : ℕ} (hk₀ : 0 < k₀)
    (hk : k₀ ≤ R.parts.card) :
    x.value - ((r3 (G := G) (discardEdges G R (garbage R) d)).apply x).value ≤
        3 * ((3 * δ + 1 / (k₀ : ℚ) + d) * (Fintype.card α : ℚ) ^ 2) ∧
      ∀ T, ((r3 (G := G) (discardEdges G R (garbage R) d)).apply x).weight T ≠ 0 →
        Disjoint (pairs T) (discardEdges G R (garbage R) d) := by
  refine ⟨?_, fun T hT => r3_avoids x _ hT⟩
  have h := r3_loss x (discardEdges G R (garbage R) d)
  have hB := card_discardEdges_budget hδ R d hd hk₀ hk
  linarith [h.1, h.2]

/-- `|H| = N3 + N4` for the tree's reduced patterns. -/
theorem card_mixedPatterns {δ : ℚ} (R : EqualRegularity G δ) :
    (mixedPatterns R).card = N3 R + N4 R := by
  rw [mixedPatterns, card_union_of_disjoint, card_image_of_injective _ Sum.inl_injective,
    card_image_of_injective _ Sum.inr_injective, N3, N4]
  rw [disjoint_left]
  intro σ h1 h2
  obtain ⟨a, _, rfl⟩ := mem_image.1 h1
  obtain ⟨b, _, hb⟩ := mem_image.1 h2
  cases hb

/-- The improved budget is never worse than the tree's C.2 budget. -/
theorem improved_le_old {δ : ℚ} (R : EqualRegularity G δ) (A θ : ℚ) (hA : 0 ≤ A)
    (hθ : 0 ≤ θ) :
    3 * A + ((N4 R : ℚ) + 2 * N3 R) * θ ≤ 5 * A + 5 * (((mixedPatterns R).card : ℚ) * θ) := by
  rw [card_mixedPatterns]
  push_cast
  have h3 : (0 : ℚ) ≤ N3 R := Nat.cast_nonneg _
  have h4 : (0 : ℚ) ≤ N4 R := Nat.cast_nonneg _
  nlinarith [mul_nonneg h3 hθ, mul_nonneg h4 hθ]

/-- A fractional mixed packing has value at most `(5/6) e(G)`. -/
theorem value_le_edges (x : FracPacking G ℚ) :
    x.value ≤ (5 / 6 : ℚ) * G.edgeFinset.card := by
  have hitem : ∀ K ∈ items G, gainF ℚ K ≤ (5 / 6 : ℚ) * ((pairs K ∩ G.edgeFinset).card : ℚ) := by
    intro K hK
    rw [inter_eq_left.2 (pairs_subset_edgeFinset (mem_items.1 hK)), card_pairs, gainF]
    rcases (mem_items.1 hK).2 with h | h <;> rw [h] <;> norm_num [Nat.choose]
  calc x.value = ∑ K ∈ items G, x.weight K * gainF ℚ K := by
        unfold FracPacking.value; exact sum_congr rfl fun _ _ => by ring
    _ ≤ ∑ K ∈ items G, x.weight K *
          ((fun _ => (5 / 6 : ℚ)) K * ((pairs K ∩ G.edgeFinset).card : ℚ)) :=
        sum_le_sum fun K hK => mul_le_mul_of_nonneg_left (hitem K hK) (x.weight_nonneg K)
    _ = ∑ e ∈ G.edgeFinset, ∑ K ∈ items G, (if e ∈ pairs K then 5 / 6 * x.weight K else 0) :=
        sum_mul_card_inter _ _ _
    _ = ∑ e ∈ G.edgeFinset, 5 / 6 * ∑ K ∈ items G, (if e ∈ pairs K then x.weight K else 0) := by
        refine sum_congr rfl fun e _ => ?_
        rw [mul_sum]; exact sum_congr rfl fun _ _ => by split_ifs <;> ring
    _ ≤ ∑ _e ∈ G.edgeFinset, (5 / 6 : ℚ) * 1 :=
        sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (load_le_one x e) (by norm_num)
    _ = (5 / 6 : ℚ) * G.edgeFinset.card := by rw [sum_const, nsmul_eq_mul]; ring

end General

section Dense

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

theorem value_le_sq (x : FracPacking G ℚ) : x.value ≤ (5 / 6 : ℚ) * (n : ℚ) ^ 2 := by
  refine (value_le_edges x).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have h1 : G.edgeFinset.card ≤ n.choose 2 := by
    simpa using SimpleGraph.card_edgeFinset_le_card_choose_two (G := G)
  have h2 : n.choose 2 ≤ n ^ 2 := by
    rw [Nat.choose_two_right, sq]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  exact_mod_cast h1.trans h2

/-- **The remaining gap of B7, as one proposition.**  There is a packing `y` produced from the
R3-cleaned packing by the profile stage at cost at most `(N4 + 2 N3) θ` (the profile stage is
proved at the profile level by `E17.Cleanup.profile_loss`), on which the physical gate retains
`(1 - u - v) w(y)` up to `ζ n²`.  The second conjunct is what the downstream gate needs from the
cleaned packing: fibre lower bounds after reconstruction. -/
def ImprovedGateGap {δ : ℚ} (R : EqualRegularity G δ) (x : FracPacking G ℚ) (P : Packing G)
    (d θ u v ζ : ℚ) : Prop :=
  ∃ y : FracPacking G ℚ,
    ((r3 (G := G) (discardEdges G R (garbage R) d)).apply x).value - y.value ≤
        ((N4 R : ℚ) + 2 * N3 R) * θ ∧
      (1 - u - v) * y.value - (P.gain : ℚ) ≤ ζ * (n : ℚ) ^ 2

/-- **B7 (gap ⇒ target).** Under `ImprovedGateGap`, the far-branch loss obeys the improved
budget `3 (3δ + 1/k₀ + d) n² + (N4 + 2 N3) θ` plus the gate terms, through the same downstream
algebra `PaperIV.RC01DenseAssembly.loss_le_of_retained_round` used by the tree. -/
theorem improved_far_loss {δ : ℚ} (hδ : 0 ≤ δ) (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (P : Packing G) (d θ u v ζ : ℚ) (hd : 0 ≤ d)
    {k₀ : ℕ} (hk₀ : 0 < k₀) (hk : k₀ ≤ R.parts.card) (huv : 0 ≤ u + v)
    (hgap : ImprovedGateGap R x P d θ u v ζ) :
    x.value - (P.gain : ℚ) ≤
      3 * ((3 * δ + 1 / (k₀ : ℚ) + d) * (n : ℚ) ^ 2) + ((N4 R : ℚ) + 2 * N3 R) * θ +
        (ζ + (5 / 6) * (u + v)) * (n : ℚ) ^ 2 := by
  obtain ⟨y, hprof, hround⟩ := hgap
  have hcopy := (improved_copy_budget hδ R x d hd hk₀ hk).1
  rw [Fintype.card_fin] at hcopy
  exact PaperIV.RC01DenseAssembly.loss_le_of_retained_round huv (by linarith)
    (value_le_sq y) hround

end Dense

end E17.FarBudget
