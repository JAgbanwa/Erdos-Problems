/-
# BKLO §9 for `r = 2`, `F = K₃`: from column pairs and transversal representatives to all triangles

An edge-disjoint triangle family `𝒯` realises the parity vector of *every* triangle on the vertex
set of the partition as soon as it realises

* every **column pair** `uvec a B + uvec a' B` with `a, a'` in a common part `A` and `B` a part
  (`hpair`), and
* one **transversal representative** for each triple of distinct parts (`hrep`).

This is `BKLO.reach_vecOf_of_pairs_reps`.  Everything here is `sorry`-free.
-/
import BKLO.Section9Vectors

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

private theorem zmod2_chain :
    ∀ u1 u2 u3 u4 q1 q2 q3 q4 q5 q6 : ZMod 2,
      u1 + u2 = q1 + q2 → u2 + u3 = q3 + q4 → u3 + u4 = q5 + q6 →
      u4 + q1 + q2 + q3 + q4 + q5 + q6 = u1 := by decide

/-- **From column pairs and transversal representatives to all triangles.** -/
theorem reach_vecOf_of_pairs_reps {P : Finset (Finset V)} {idx : Finset V → ℕ}
    {𝒯 : Finset (Finset V)} (hfam : IsTriFamily 𝒯)
    (hdisj : ∀ W ∈ P, ∀ W' ∈ P, W ≠ W' → Disjoint W W')
    (hpair : ∀ A ∈ P, ∀ a ∈ A, ∀ a' ∈ A, ∀ B ∈ P,
      Reach P idx 𝒯 (fun x W => uvec a B x W + uvec a' B x W))
    (hrep : ∀ A ∈ P, ∀ B ∈ P, ∀ C ∈ P, A ≠ B → A ≠ C → B ≠ C →
      ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, Reach P idx 𝒯 (vecOf ({a, b, c} : Finset V)))
    (T₀ : Finset V) (hcard : T₀.card = 3) (hsub : T₀ ⊆ P.biUnion id) :
    Reach P idx 𝒯 (vecOf T₀) := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hcard
  obtain ⟨A, hA, ha⟩ : ∃ A ∈ P, a ∈ A := by
    have := hsub (by simp : a ∈ ({a, b, c} : Finset V))
    simpa using Finset.mem_biUnion.1 this
  obtain ⟨B, hB, hb⟩ : ∃ B ∈ P, b ∈ B := by
    have := hsub (by simp : b ∈ ({a, b, c} : Finset V))
    simpa using Finset.mem_biUnion.1 this
  obtain ⟨C, hC, hc⟩ : ∃ C ∈ P, c ∈ C := by
    have := hsub (by simp : c ∈ ({a, b, c} : Finset V))
    simpa using Finset.mem_biUnion.1 this
  by_cases hBC : B = C
  · -- `b` and `c` lie in a common part
    subst hBC
    refine (hpair B hB b hb c hc A hA).congr ?_
    intro W hW x hx
    exact (vecOf_two_in_part hdisj hA hB ha hb hc hab hac hbc hW hx).symm
  · by_cases hAB : A = B
    · -- `a` and `b` lie in a common part
      subst hAB
      refine (hpair A hA a ha b hb C hC).congr ?_
      intro W hW x hx
      rw [triple_swap₂ a b c]
      exact (vecOf_two_in_part hdisj hC hA hc ha hb (Ne.symm hac) (Ne.symm hbc) hab hW hx).symm
    · by_cases hAC : A = C
      · -- `a` and `c` lie in a common part
        subst hAC
        refine (hpair A hA a ha c hc B hB).congr ?_
        intro W hW x hx
        rw [triple_swap₁ a b c]
        exact (vecOf_two_in_part hdisj hB hA hb ha hc (Ne.symm hab) hbc hac hW hx).symm
      · -- three distinct parts
        obtain ⟨a', ha', b', hb', c', hc', hrepR⟩ := hrep A hA B hB C hC hAB hAC hBC
        have h1 := hpair A hA a ha a' ha' B hB
        have h2 := hpair A hA a ha a' ha' C hC
        have h3 := hpair B hB b hb b' hb' A hA
        have h4 := hpair B hB b hb b' hb' C hC
        have h5 := hpair C hC c hc c' hc' A hA
        have h6 := hpair C hC c hc c' hc' B hB
        refine (((((hrepR.add hfam h1).add hfam h2).add hfam h3).add hfam h4).add hfam
          h5).add hfam h6 |>.congr ?_
        intro W hW x hx
        have E1 := vecOf_move hdisj hA hB hC hAB hAC hBC ha ha' hb hc hW x
        have E2 := vecOf_move hdisj hB hA hC (Ne.symm hAB) hBC hAC hb hb' ha' hc hW x
        have E3 := vecOf_move hdisj hC hA hB (Ne.symm hAC) (Ne.symm hBC) hAB hc hc' ha' hb' hW x
        rw [← triple_swap₁ a' b c, ← triple_swap₁ a' b' c] at E2
        rw [← triple_swap₂ a' b' c, ← triple_swap₂ a' b' c'] at E3
        exact zmod2_chain _ _ _ _ _ _ _ _ _ _ E1 E2 E3

end BKLO
