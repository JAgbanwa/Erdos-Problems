/-
# An injection (system of distinct representatives) achieving at least the mean weight

A first-moment / probabilistic-method tool: for a weight `f : A → B → ℝ` with `|A| ≤ |B|`, some
injection `σ : A ↪ B` achieves at least the average over all injections, i.e.
`∑ₐ f a (σ a) ≥ (1/|B|) · ∑ₐ ∑_b f a b`. The proof averages `∑ₐ f a (σ a)` over all embeddings
`A ↪ B` (each value `σ a = b` is equally likely by symmetry) and picks an injection beating the mean.

* `Contrib.Averaging.exists_injection_ge_mean`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib

open Finset

namespace Contrib.Averaging

/-- **Injection above the mean**: if `|A| ≤ |B|`, any weight `f : A → B → ℝ` admits an
injection `σ : A ↪ B` with `Σ_a f a (σ a) ≥ (1/|B|) Σ_a Σ_b f a b`. -/
theorem exists_injection_ge_mean {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (f : A → B → ℝ)
    (hAB : Fintype.card A ≤ Fintype.card B) (hB : 0 < Fintype.card B) :
    ∃ σ : A ↪ B, (1 / (Fintype.card B : ℝ)) * ∑ a, ∑ b, f a b
      ≤ ∑ a, f a (σ a) := by
  revert hAB hB;
  intro hAB hB_pos
  by_contra h_contra
  push_neg at h_contra
  have h_avg : ∑ σ : Function.Embedding A B, ∑ a : A, f a (σ a) = (Fintype.card (Function.Embedding A B) : ℝ) * (1 / Fintype.card B : ℝ) * ∑ a : A, ∑ b : B, f a b := by
    have h_avg : ∀ a : A, ∑ σ : Function.Embedding A B, f a (σ a) = (Fintype.card (Function.Embedding A B) : ℝ) * (1 / Fintype.card B : ℝ) * ∑ b : B, f a b := by
      intro a
      have h_sum_embedding : ∀ b : B, ∑ σ : Function.Embedding A B, (if σ a = b then 1 else 0 : ℝ) = (Fintype.card (Function.Embedding A B) : ℝ) / Fintype.card B := by
        intro b
        have h_sum_embedding : ∀ b₁ b₂ : B, ∑ σ : Function.Embedding A B, (if σ a = b₁ then 1 else 0 : ℝ) = ∑ σ : Function.Embedding A B, (if σ a = b₂ then 1 else 0 : ℝ) := by
          intro b₁ b₂
          have h_sum_embedding : ∑ σ : Function.Embedding A B, (if σ a = b₁ then 1 else 0 : ℝ) = ∑ σ : Function.Embedding A B, (if σ a = b₂ then 1 else 0 : ℝ) := by
            have h_bij : ∃ g : B ≃ B, g b₁ = b₂ := by
              exact ⟨ Equiv.swap b₁ b₂, by simp +decide ⟩
            obtain ⟨ g, hg ⟩ := h_bij
            generalize_proofs at *; (
            apply Finset.sum_bij (fun σ _ => Function.Embedding.mk (fun x => g (σ x)) (by
            exact g.injective.comp σ.injective))
            all_goals generalize_proofs at *;
            · exact fun _ _ => Finset.mem_univ _;
            · simp +decide [ Function.Embedding.ext_iff ];
            · exact fun σ _ => ⟨ Function.Embedding.mk ( fun x => g.symm ( σ x ) ) ( by
                exact fun x y hxy => σ.injective <| by simpa using hxy; ), Finset.mem_univ _, by ext; simp +decide ⟩;
            · simp +decide [ ← hg ])
          generalize_proofs at *; (
          convert h_sum_embedding using 1)
        generalize_proofs at *; (
        have h_sum_embedding : ∑ b : B, ∑ σ : Function.Embedding A B, (if σ a = b then 1 else 0 : ℝ) = (Fintype.card (Function.Embedding A B) : ℝ) := by
          rw [ Finset.sum_comm ] ; aesop;
        generalize_proofs at *; (
        rw [ ← h_sum_embedding, Finset.sum_congr rfl fun x _ => ‹∀ b₁ b₂ : B, ( ∑ σ : Function.Embedding A B, if σ a = b₁ then 1 else 0 : ℝ ) = ∑ σ : Function.Embedding A B, if σ a = b₂ then 1 else 0› x b, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ ( by positivity ) ]))
      generalize_proofs at *; (
      have h_sum_embedding : ∑ σ : Function.Embedding A B, f a (σ a) = ∑ b : B, f a b * ∑ σ : Function.Embedding A B, (if σ a = b then 1 else 0 : ℝ) := by
        simp +decide only [Finset.mul_sum _ _ _];
        rw [ Finset.sum_comm ] ; simp +decide ;
      generalize_proofs at *; (
      simp_all +decide [ div_eq_mul_inv, mul_comm, Finset.mul_sum _ _ _ ];
      rw [ Finset.sum_mul _ _ _ ]))
    generalize_proofs at *; (
    rw [ Finset.sum_comm, Finset.mul_sum _ _ _, Finset.sum_congr rfl fun a ha => h_avg a ])
  generalize_proofs at *; (
  have h_card : Fintype.card (Function.Embedding A B) > 0 := by
    simp +zetaDelta at *;
    exact hAB
  generalize_proofs at *; (
  exact absurd ( Finset.sum_lt_sum_of_nonempty ( Finset.univ_nonempty_iff.mpr ⟨ Classical.choice ( Fintype.card_pos_iff.mp h_card ) ⟩ ) fun σ _ => h_contra σ ) ( by simp +decide [ h_avg, mul_assoc ] )));

end Contrib.Averaging
