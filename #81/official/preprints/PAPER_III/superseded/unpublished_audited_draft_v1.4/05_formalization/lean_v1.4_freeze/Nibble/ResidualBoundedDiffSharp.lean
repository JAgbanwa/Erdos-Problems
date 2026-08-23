/-
# Nibble — sharp bounded difference of the residual degree (count coefficient)

Standalone, Mathlib-only. The **sharp** companion of `residualDeg_insert_boundedDiff`. The original
bounds the one-edge change of `deg_residual(v)` by `∑_{x ∈ e ∪ support(conflicts)} deg(x)` — a *sum of
degrees* (≈ r²Δ²), applying the loose `edges_meeting_le` step. That coefficient is too large: summed
over `H` it forces the concentration window `c ≳ √|V|·Δ^2.5 ≫ d`, defeating the nibble.

The genuinely correct coefficient is the **count** of `v`-edges that meet the toggled edge's
neighbourhood — `residual_deg_change_local` already proves the symmetric difference is contained in
that set, so we simply keep the count instead of collapsing it to `∑ deg`. This is `O(deg(v))` and,
after the (separate) codegree sum-estimate `∑_{e∈H} c_e(v)² ≲ deg(v)`, yields `c ≈ √(d log n) ≪ d`.

`residualDeg_insert_boundedDiff_sharp` is the sharp one-edge bound with the count coefficient.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.ResidualBoundedDiff

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- **Sharp one-edge bounded difference (count coefficient).** Toggling one edge `e` into the retained
set `R` changes `deg_residual(v)` by at most the *number of `v`-edges meeting the neighbourhood*
`e ∪ support(conflicts of e in R)` — a count `≤ deg(v)`, not a sum of degrees. Obtained by keeping the
`residual_deg_change_local` containment as a cardinality bound, without the loose `edges_meeting_le`. -/
theorem residualDeg_insert_boundedDiff_sharp (H R : Finset (Finset V)) (e : Finset V) (v : V) :
    |(degree (residual H R) v : ℝ) - (degree (residual H (insert e R)) v : ℝ)|
      ≤ (((H.filter (fun f => v ∈ f)).filter
            (fun f => ¬ Disjoint f (e ∪ support (R.filter (fun g => ¬ Disjoint e g))))).card : ℝ) := by
  have hA : degree (residual H R) v
      = ((H.filter (fun f => v ∈ f)).filter (fun f => Disjoint f (covered R))).card := by
    rw [degree, residual, Finset.filter_comm]
  have hB : degree (residual H (insert e R)) v
      = ((H.filter (fun f => v ∈ f)).filter (fun f => Disjoint f (covered (insert e R)))).card := by
    rw [degree, residual, Finset.filter_comm]
  rw [hA, hB]
  refine le_trans (abs_card_sub_le_card_symmDiff _ _) ?_
  exact_mod_cast Finset.card_le_card (residual_deg_change_local H R e v)

/-- **Sharp config-toggle bounded difference (count coefficient).** Viewing retention as a per-edge
bit configuration `ω : Finset V → Bool`, toggling the bit of `e` changes `deg_residual(v)` by at most
the count of `v`-edges meeting `e ∪ support(H-conflicts of e)` — the `R`-independent, `v`-dependent
*count* coefficient (`≤ deg(v)`), the sharp replacement for `residualDegConfig_boundedDiff`'s
sum-of-degrees. This is the coordinate `hbd` a sharp McDiarmid instantiation consumes; summed as
`∑_{e∈H} c_e(v)²` it is `≲ deg(v)` in low codegree, giving `c ≈ √(d log n) ≪ d`. -/
theorem residualDegConfig_boundedDiff_sharp (H : Finset (Finset V)) (v : V) (e : Finset V)
    (ω ω' : Finset V → Bool) (hagree : ∀ g, g ≠ e → ω g = ω' g) :
    |(degree (residual H (H.filter (fun g => ω g = true))) v : ℝ)
       - (degree (residual H (H.filter (fun g => ω' g = true))) v : ℝ)|
      ≤ (((H.filter (fun f => v ∈ f)).filter
            (fun f => ¬ Disjoint f (e ∪ support (H.filter (fun g => ¬ Disjoint e g))))).card : ℝ) := by
  classical
  set C : ℝ := (((H.filter (fun f => v ∈ f)).filter
        (fun f => ¬ Disjoint f (e ∪ support (H.filter (fun g => ¬ Disjoint e g))))).card : ℝ) with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; exact Nat.cast_nonneg _
  have hmono : ∀ R : Finset (Finset V), R ⊆ H →
      (((H.filter (fun f => v ∈ f)).filter
        (fun f => ¬ Disjoint f (e ∪ support (R.filter (fun g => ¬ Disjoint e g))))).card : ℝ) ≤ C := by
    intro R hRH
    rw [hCdef]
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro f hf
    rw [Finset.mem_filter] at hf ⊢
    obtain ⟨hfbase, hfpred⟩ := hf
    refine ⟨hfbase, ?_⟩
    have hsub : (e ∪ support (R.filter (fun g => ¬ Disjoint e g)))
        ⊆ (e ∪ support (H.filter (fun g => ¬ Disjoint e g))) := by
      apply Finset.union_subset_union_right
      intro x hx
      rw [support, Finset.mem_biUnion] at hx ⊢
      obtain ⟨g, hg, hxg⟩ := hx
      exact ⟨g, Finset.filter_subset_filter _ hRH hg, hxg⟩
    exact fun hd => hfpred (Finset.disjoint_of_subset_right hsub hd)
  have hkey : ∀ (S : Finset (Finset V)), S ⊆ H →
      |(degree (residual H S) v : ℝ) - (degree (residual H (insert e S)) v : ℝ)| ≤ C :=
    fun S hSH => le_trans (residualDeg_insert_boundedDiff_sharp H S e v) (hmono S hSH)
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
