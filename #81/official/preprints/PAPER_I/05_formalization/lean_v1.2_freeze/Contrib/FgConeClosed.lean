/-
Copyright (c) 2026. Released under Apache 2.0 license.
Draft candidate for Mathlib — extracted and generalized from the Erdős-#81 Paper I
formalization (`FiniteLPDuality.lean`). NOT yet a Mathlib PR: see the TODO notes.

# Closedness of a finitely generated cone (Weyl)

The finitely generated cone `cone{v k} = {∑ k, c k • v k : c ≥ 0}` spanned by a finite
family `v : κ → E` in a real normed space is **closed**. This is the nontrivial half of
the Farkas–Minkowski–Weyl correspondence and the key topological input to the geometric
Farkas lemma / finite LP strong duality.

Mathlib (as of v4.28.0) has `ProperCone` (whose closedness is part of the structure) and
`ProperCone.hyperplane_separation` (geometric Farkas), but **not** the statement that a
*finitely generated* cone is closed. This file supplies it.

## Main results
* `Contrib.simplicial_cone_isClosed` — a cone spanned by a linearly independent finite
  family is closed (image of the closed nonnegative orthant under an injective, hence
  closed-embedding, linear map).
* `Contrib.conic_caratheodory` — conic Carathéodory: every nonnegative combination equals a
  nonnegative combination over a linearly independent subfamily.
* `Contrib.fg_cone_isClosed` — a finitely generated cone is closed (finite union of
  simplicial cones).

## Generalization vs. the source
The Paper I version was stated over `EuclideanSpace ℝ ι`. None of the three proofs uses the
inner product; they are ported here to an arbitrary real normed space `E`
(`[NormedAddCommGroup E] [NormedSpace ℝ E]`), which is the natural Mathlib generality.

## TODO before submitting upstream
* Replace the automation-heavy steps in `conic_caratheodory` (`grind`, `simp +decide`) with
  explicit idiomatic proofs; drop `set_option maxHeartbeats`.
* Integrate with the `ConvexCone` / `PointedCone` API (state closedness of the conic hull as
  a `ConvexCone` rather than an explicit set-builder) and discuss on the Mathlib Zulip.
* Consider generalizing the scalar field beyond `ℝ`.
-/
import Mathlib

open scoped BigOperators

namespace Contrib

variable {κ ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A **simplicial cone** — the nonnegative combinations of a linearly independent finite
family — is closed: it is the image of the closed nonnegative orthant under an injective
(hence closed-embedding) linear map from a finite-dimensional space. -/
lemma simplicial_cone_isClosed [Fintype κ]
    (v : κ → E) (s : Finset κ) (hli : LinearIndepOn ℝ v s) :
    IsClosed {y : E |
      ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ (∀ k ∉ s, c k = 0) ∧ ∑ k ∈ s, c k • v k = y} := by
  classical
  set L : (s → ℝ) →ₗ[ℝ] E :=
    ∑ k : s, LinearMap.smulRight (LinearMap.proj k) (v k) with hL_def
  have hLval : ∀ c : s → ℝ, L c = ∑ k : s, c k • v k := by
    intro c
    simp [hL_def, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    rw [hLval] at hm
    funext k; exact Fintype.linearIndependent_iff.mp hli m hm k
  have hclosedmap : IsClosedMap L :=
    (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot_of_injective hLinj)).isClosedMap
  have hO : IsClosed {c : s → ℝ | ∀ k, 0 ≤ c k} := by
    have : {c : s → ℝ | ∀ k, 0 ≤ c k} = ⋂ k, {c : s → ℝ | 0 ≤ c k} := by ext c; simp
    rw [this]
    exact isClosed_iInter (fun k => isClosed_le continuous_const (continuous_apply k))
  have hclosed := hclosedmap _ hO
  convert hclosed using 1
  ext y
  constructor
  · rintro ⟨c, hc0, hcoff, rfl⟩
    refine ⟨fun k : s => c k, fun k => hc0 _, ?_⟩
    rw [hLval, ← Finset.sum_attach s (fun j => c j • v j)]
    rfl
  · rintro ⟨c, hc0, rfl⟩
    refine ⟨fun j => if h : j ∈ s then c ⟨j, h⟩ else 0, ?_, ?_, ?_⟩
    · intro k; dsimp only; split_ifs with h
      · exact hc0 _
      · exact le_refl 0
    · intro k hk; simp [hk]
    · rw [hLval, ← Finset.sum_attach s (fun j => (if h : j ∈ s then c ⟨j, h⟩ else 0) • v j)]
      apply Finset.sum_congr rfl
      intro k _
      simp [k.2]

set_option maxHeartbeats 2000000 in
/-- **Conic Carathéodory.** Any nonnegative combination of a finite family equals a
nonnegative combination over a linearly independent subfamily with the same value.

TODO: the proof below is ported from the source formalization and leans on `grind` /
`simp +decide`; it should be rewritten in idiomatic style before upstreaming. -/
lemma conic_caratheodory [Fintype κ] [DecidableEq κ]
    (v : κ → E) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k) :
    ∃ (d : κ → ℝ) (s : Finset κ), (∀ k, 0 ≤ d k) ∧ (∀ k ∉ s, d k = 0) ∧
      LinearIndepOn ℝ v s ∧ (∑ k ∈ s, d k • v k) = ∑ k, c k • v k := by
  obtain ⟨s, hs⟩ : ∃ s : Finset κ, (∃ d : κ → ℝ, (∀ k, 0 ≤ d k) ∧ (∀ k ∉ s, d k = 0) ∧ (∑ k ∈ s, d k • v k = ∑ k, c k • v k)) ∧ ∀ t : Finset κ, (∃ d : κ → ℝ, (∀ k, 0 ≤ d k) ∧ (∀ k ∉ t, d k = 0) ∧ (∑ k ∈ t, d k • v k = ∑ k, c k • v k)) → s.card ≤ t.card := by
    apply_rules [ Set.exists_min_image ];
    · exact Set.toFinite _;
    · exact ⟨ Finset.univ, ⟨ c, hc, fun k hk => False.elim <| hk <| Finset.mem_univ _, by simp +decide ⟩ ⟩;
  by_cases h_lin_dep : ¬ LinearIndepOn ℝ v s;
  · obtain ⟨d, hd_nonneg, hd_zero, hd_sum⟩ := hs.left
    obtain ⟨a, ha_nonzero, ha_support, ha_sum⟩ : ∃ a : κ → ℝ, (∃ k ∈ s, a k ≠ 0) ∧ (∀ k ∉ s, a k = 0) ∧ (∑ k ∈ s, a k • v k = 0) ∧ (∃ k ∈ s, a k > 0) := by
      obtain ⟨a, ha_nonzero, ha_sum⟩ : ∃ a : κ → ℝ, (∃ k ∈ s, a k ≠ 0) ∧ (∀ k ∉ s, a k = 0) ∧ (∑ k ∈ s, a k • v k = 0) := by
        rw [ linearIndepOn_iff' ] at h_lin_dep;
        push_neg at h_lin_dep;
        obtain ⟨ t, g, ht, hg, i, hi, hi' ⟩ := h_lin_dep; use fun k => if k ∈ t then g k else 0; simp_all +decide [ Finset.sum_ite ] ;
        exact ⟨ ⟨ i, ht hi, hi, hi' ⟩, fun k hk₁ hk₂ => False.elim <| hk₁ <| ht hk₂, by rw [ Finset.inter_eq_right.mpr ht, hg ] ⟩;
      by_cases h_neg : ∀ k ∈ s, a k ≤ 0;
      · use fun k => -a k;
        simp_all +decide [ neg_smul ];
        exact ha_nonzero.imp fun k hk => ⟨ hk.1, lt_of_le_of_ne ( h_neg k hk.1 ) hk.2 ⟩;
      · exact ⟨ a, ha_nonzero, ha_sum.1, ha_sum.2, by push_neg at h_neg; exact h_neg ⟩;
    obtain ⟨θ, hθ_pos, hθ_min⟩ : ∃ θ > 0, (∀ k ∈ s, d k - θ * a k ≥ 0) ∧ (∃ k ∈ s, d k - θ * a k = 0) := by
      obtain ⟨k₀, hk₀⟩ : ∃ k₀ ∈ s, a k₀ > 0 ∧ ∀ k ∈ s, a k > 0 → d k / a k ≥ d k₀ / a k₀ := by
        have h_min : ∃ k₀ ∈ Finset.filter (fun k => a k > 0) s, ∀ k ∈ Finset.filter (fun k => a k > 0) s, d k / a k ≥ d k₀ / a k₀ := by
          exact Finset.exists_min_image _ _ ⟨ ha_sum.2.choose, Finset.mem_filter.mpr ⟨ ha_sum.2.choose_spec.1, ha_sum.2.choose_spec.2 ⟩ ⟩;
        exact ⟨ h_min.choose, Finset.mem_filter.mp h_min.choose_spec.1 |>.1, Finset.mem_filter.mp h_min.choose_spec.1 |>.2, fun k hk hk' => h_min.choose_spec.2 k ( Finset.mem_filter.mpr ⟨ hk, hk' ⟩ ) ⟩;
      refine' ⟨ d k₀ / a k₀, div_pos ( lt_of_le_of_ne ( hd_nonneg k₀ ) ( Ne.symm _ ) ) hk₀.2.1, _, k₀, hk₀.1, _ ⟩;
      · intro h; simp_all +decide [ ne_of_gt ] ;
        have := hs.2 ( s.erase k₀ ) ( fun k => if k = k₀ then 0 else d k ) ?_ ?_ ?_ <;> simp_all +decide [ Finset.sum_ite, Finset.filter_ne' ];
        · exact Nat.not_le_of_gt ( Nat.pred_lt ( ne_bot_of_gt ( Finset.card_pos.mpr ⟨ k₀, hk₀.1 ⟩ ) ) ) this;
        · exact fun k => by split_ifs <;> simp +decide [ * ] ;
      · intro k hk; by_cases hk' : a k > 0 <;> simp_all +decide [ div_mul_cancel₀ _ ( ne_of_gt _ ) ] ;
        · exact le_div_iff₀ hk' |>.1 ( hk₀.2.2 k hk hk' );
        · exact le_trans ( mul_nonpos_of_nonneg_of_nonpos ( div_nonneg ( hd_nonneg _ ) hk₀.2.1.le ) hk' ) ( hd_nonneg _ );
      · rw [ div_mul_cancel₀ _ hk₀.2.1.ne', sub_self ];
    set t := s.filter (fun k => d k - θ * a k ≠ 0) with ht_def;
    have h_t_support : ∀ k, 0 ≤ d k - θ * a k := by
      exact fun k => if hk : k ∈ s then hθ_min.1 k hk else by simp +decide [ hd_zero k hk, ha_support k hk ] ;
    have h_t_zero : ∀ k ∉ t, d k - θ * a k = 0 := by
      grind
    have h_t_sum : ∑ k ∈ t, (d k - θ * a k) • v k = ∑ k, c k • v k := by
      convert congr_arg ( fun x => x - θ • ∑ k ∈ s, a k • v k ) hd_sum using 1;
      · rw [ Finset.sum_filter_of_ne ];
        · simp +decide [ sub_smul, Finset.smul_sum, Finset.sum_sub_distrib, smul_smul ];
        · exact fun k hk hk' => fun hk'' => hk' <| by rw [ hk'', zero_smul ] ;
      · simp +decide [ ha_sum.1 ];
    contrapose! hs;
    refine' fun h => ⟨ t, ⟨ fun k => d k - θ * a k, h_t_support, h_t_zero, h_t_sum ⟩, _ ⟩;
    refine' Finset.card_lt_card _;
    grind;
  · exact ⟨ hs.1.choose, s, hs.1.choose_spec.1, hs.1.choose_spec.2.1, Classical.not_not.mp h_lin_dep, hs.1.choose_spec.2.2 ⟩

/-- **Weyl.** The finitely generated cone `{∑ k, c k • v k : c ≥ 0}` is closed. -/
lemma fg_cone_isClosed [Fintype κ] [DecidableEq κ] (v : κ → E) :
    IsClosed {y : E | ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ ∑ k, c k • v k = y} := by
  have hset : {y : E | ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ ∑ k, c k • v k = y}
      = ⋃ s : Finset κ, ⋃ (_ : LinearIndepOn ℝ v s),
          {y : E | ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ (∀ k ∉ s, c k = 0) ∧ ∑ k ∈ s, c k • v k = y} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨c, hc0, rfl⟩
      obtain ⟨d, s, hd0, hdoff, hindep, hsum⟩ := conic_caratheodory v c hc0
      exact ⟨s, hindep, d, hd0, hdoff, hsum⟩
    · rintro ⟨s, hindep, c, hc0, hcoff, rfl⟩
      refine ⟨c, hc0, ?_⟩
      rw [← Finset.sum_subset (Finset.subset_univ s)]
      intro k _ hks; rw [hcoff k hks, zero_smul]
  rw [hset]
  exact isClosed_iUnion_of_finite fun s =>
    isClosed_iUnion_of_finite fun h => simplicial_cone_isClosed v s h

end Contrib
