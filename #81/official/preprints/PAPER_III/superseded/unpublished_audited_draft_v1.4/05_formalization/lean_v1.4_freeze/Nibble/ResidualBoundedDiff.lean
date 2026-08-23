/-
# Nibble — M8 bridge : bounded difference of the residual degree under one retained edge

Standalone, Mathlib-only. Turns the M5 locality bound (`residual_deg_change_card_le`, the symmetric
difference of the `v`-edge residual sets) into a bounded-difference statement on the residual DEGREE:
toggling one edge `e` in the retained set `R` changes `deg_residual(v)` by at most the local
coefficient `c_e = ∑_{x ∈ e ∪ support(conflicts)} deg(x)`.

This is the coordinate bounded-difference input `hbd` that `mcdiarmid` consumes, once the retention is
viewed as a product configuration (one bit per edge). Combined with `mcdiarmid_two_sided` it gives the
exponential-tail concentration of the residual degree — replacing the too-weak Chebyshev bound.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Round
import Nibble.BoundedDiff
import Mathlib.Analysis.RCLike.Basic

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- **|card difference| ≤ |symmetric difference|.** -/
theorem abs_card_sub_le_card_symmDiff (A B : Finset V) :
    |(A.card : ℝ) - (B.card : ℝ)| ≤ (((A \ B) ∪ (B \ A)).card : ℝ) := by
  have hdisj : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    exact fun x hx hx' => (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx').1
  have hun : ((A \ B) ∪ (B \ A)).card = (A \ B).card + (B \ A).card :=
    Finset.card_union_of_disjoint hdisj
  have hAB : A.card ≤ B.card + (A \ B).card :=
    (Finset.card_le_card (fun x hx => by
      by_cases hxB : x ∈ B
      · exact Finset.mem_union_left _ hxB
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hxB⟩))).trans
        (Finset.card_union_le _ _)
  have hBA : B.card ≤ A.card + (B \ A).card :=
    (Finset.card_le_card (fun x hx => by
      by_cases hxA : x ∈ A
      · exact Finset.mem_union_left _ hxA
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hxA⟩))).trans
        (Finset.card_union_le _ _)
  rw [hun, abs_le]
  have hAB' : (A.card : ℝ) ≤ (B.card : ℝ) + ((A \ B).card : ℝ) := by exact_mod_cast hAB
  have hBA' : (B.card : ℝ) ≤ (A.card : ℝ) + ((B \ A).card : ℝ) := by exact_mod_cast hBA
  refine ⟨?_, ?_⟩ <;>
    · push_cast
      have h1 : (0 : ℝ) ≤ ((A \ B).card : ℝ) := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ ((B \ A).card : ℝ) := Nat.cast_nonneg _
      linarith

/-- **M8 bridge — residual degree bounded difference under one retained edge.** -/
theorem residualDeg_insert_boundedDiff (H R : Finset (Finset V)) (e : Finset V) (v : V) :
    |(degree (residual H R) v : ℝ) - (degree (residual H (insert e R)) v : ℝ)|
      ≤ (∑ x ∈ (e ∪ support (R.filter (fun g => ¬ Disjoint e g))), degree H x : ℝ) := by
  have hA : degree (residual H R) v
      = ((H.filter (fun f => v ∈ f)).filter (fun f => Disjoint f (covered R))).card := by
    rw [degree, residual, Finset.filter_comm]
  have hB : degree (residual H (insert e R)) v
      = ((H.filter (fun f => v ∈ f)).filter (fun f => Disjoint f (covered (insert e R)))).card := by
    rw [degree, residual, Finset.filter_comm]
  rw [hA, hB]
  refine le_trans (abs_card_sub_le_card_symmDiff _ _) ?_
  exact_mod_cast residual_deg_change_card_le H R e v

/-- **M8 — config-toggle bounded difference (ρ-independent coefficient).** Viewing the retention as a
per-edge bit configuration `ω : Finset V → Bool` (`retained = H.filter (ω · = true)`), toggling the
bit of edge `e` changes `deg_residual(v)` by at most the `R`-independent local coefficient
`c_e = ∑_{x ∈ e ∪ support(H-edges conflicting with e)} deg(x)`. This is exactly the coordinate
bounded-difference hypothesis `hbd` that `mcdiarmid_two_sided_const` consumes. -/
theorem residualDegConfig_boundedDiff (H : Finset (Finset V)) (v : V) (e : Finset V)
    (ω ω' : Finset V → Bool) (hagree : ∀ g, g ≠ e → ω g = ω' g) :
    |(degree (residual H (H.filter (fun g => ω g = true))) v : ℝ)
       - (degree (residual H (H.filter (fun g => ω' g = true))) v : ℝ)|
      ≤ (∑ x ∈ e ∪ support (H.filter (fun g => ¬ Disjoint e g)), degree H x : ℝ) := by
  classical
  set C := (∑ x ∈ e ∪ support (H.filter (fun g => ¬ Disjoint e g)), degree H x : ℝ) with hCdef
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun x _ => Nat.cast_nonneg _)
  have hmono : ∀ R : Finset (Finset V), R ⊆ H →
      (∑ x ∈ e ∪ support (R.filter (fun g => ¬ Disjoint e g)), degree H x : ℝ) ≤ C := by
    intro R hRH
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => Nat.cast_nonneg _)
    refine Finset.union_subset_union_right (fun x hx => ?_)
    rw [support, Finset.mem_biUnion] at hx ⊢
    obtain ⟨f, hf, hxf⟩ := hx
    exact ⟨f, Finset.filter_subset_filter _ hRH hf, hxf⟩
  have hkey : ∀ (S : Finset (Finset V)), S ⊆ H →
      |(degree (residual H S) v : ℝ) - (degree (residual H (insert e S)) v : ℝ)| ≤ C :=
    fun S hSH => le_trans (residualDeg_insert_boundedDiff H S e v) (hmono S hSH)
  by_cases hee : ω e = ω' e
  · have hRR : H.filter (fun g => ω g = true) = H.filter (fun g => ω' g = true) := by
      ext g
      rcases eq_or_ne g e with rfl | hge
      · simp only [Finset.mem_filter, hee]
      · simp only [Finset.mem_filter, hagree g hge]
    rw [hRR]; simpa using hC0
  · by_cases heH : e ∈ H
    · have key : (ω e = false ∧ ω' e = true) ∨ (ω e = true ∧ ω' e = false) := by
        revert hee; cases ω e <;> cases ω' e <;> simp
      rcases key with ⟨h0, hω'e⟩ | ⟨h1, hω'e⟩
      · have hins : H.filter (fun g => ω' g = true)
            = insert e (H.filter (fun g => ω g = true)) := by
          ext g
          simp only [Finset.mem_insert, Finset.mem_filter]
          constructor
          · rintro ⟨hg, hgt⟩
            rcases eq_or_ne g e with rfl | hge
            · exact Or.inl rfl
            · exact Or.inr ⟨hg, by rw [hagree g hge]; exact hgt⟩
          · rintro (rfl | ⟨hg, hgt⟩)
            · exact ⟨heH, hω'e⟩
            · rcases eq_or_ne g e with rfl | hge
              · exact ⟨heH, hω'e⟩
              · exact ⟨hg, by rw [← hagree g hge]; exact hgt⟩
        rw [hins]; exact hkey _ (Finset.filter_subset _ _)
      · have hins : H.filter (fun g => ω g = true)
            = insert e (H.filter (fun g => ω' g = true)) := by
          ext g
          simp only [Finset.mem_insert, Finset.mem_filter]
          constructor
          · rintro ⟨hg, hgt⟩
            rcases eq_or_ne g e with rfl | hge
            · exact Or.inl rfl
            · exact Or.inr ⟨hg, by rw [← hagree g hge]; exact hgt⟩
          · rintro (rfl | ⟨hg, hgt⟩)
            · exact ⟨heH, h1⟩
            · rcases eq_or_ne g e with rfl | hge
              · exact ⟨heH, h1⟩
              · exact ⟨hg, by rw [hagree g hge]; exact hgt⟩
        rw [hins, abs_sub_comm]; exact hkey _ (Finset.filter_subset _ _)
    · have hRR : H.filter (fun g => ω g = true) = H.filter (fun g => ω' g = true) := by
        ext g
        rcases eq_or_ne g e with rfl | hge
        · simp only [Finset.mem_filter]; exact ⟨fun h => absurd h.1 heH, fun h => absurd h.1 heH⟩
        · simp only [Finset.mem_filter, hagree g hge]
      rw [hRR]; simpa using hC0

end Hypergraph
