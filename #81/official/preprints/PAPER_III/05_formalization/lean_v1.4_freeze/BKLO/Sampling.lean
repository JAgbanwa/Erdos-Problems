/-
# A moment bound for uniformly random subsets.

The vortex clauses of the §10 interface are statements about *random subsets*: a random level
inherits the density of the set it is chosen from.  The whole probabilistic content needed for
them is packaged here, in purely finite form, as a counting statement about
`Finset.powersetCard`.

The engine is the elementary identity

`∑_{U ∈ powersetCard t A} C(|T ∩ U|, k) = C(|T|, k) · C(|A| - k, t - k)`,

obtained by counting pairs `(U, S)` with `S ⊆ T ∩ U` and `|S| = k`; Markov's inequality applied
to `C(·, k)` then bounds the number of `t`-subsets `U` in which `T` is over-represented by

`(|T| t / ((y + 1 - k)(|A| + 1 - k)))^k · C(|A|, t)`,

which for `k` large is an exponentially small fraction of all `t`-subsets.  Taking `k` a constant
multiple of `log(1/ρ)` gives any polynomial or constant failure fraction `ρ` one wants, which is
all that the vortex needs.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Positivity

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Counting the `t`-subsets containing a fixed set -/

/-- The `t`-subsets of `A` containing a fixed subset `S` correspond to the `(t - |S|)`-subsets of
`A \ S`. -/
theorem card_powersetCard_filter_superset {A S : Finset V} {t : ℕ} (hSA : S ⊆ A)
    (hSt : S.card ≤ t) :
    ((A.powersetCard t).filter (fun U => S ⊆ U)).card = (A.card - S.card).choose (t - S.card) := by
  classical
  have hbij : ((A.powersetCard t).filter (fun U => S ⊆ U)).card
      = ((A \ S).powersetCard (t - S.card)).card := by
    refine Finset.card_bij' (fun U _ => U \ S) (fun W _ => W ∪ S) ?_ ?_ ?_ ?_
    · intro U hU
      obtain ⟨hUA, hUt⟩ := Finset.mem_powersetCard.1 (Finset.mem_filter.1 hU).1
      have hSU : S ⊆ U := (Finset.mem_filter.1 hU).2
      refine Finset.mem_powersetCard.2 ⟨Finset.sdiff_subset_sdiff hUA (Finset.Subset.refl _), ?_⟩
      rw [Finset.card_sdiff_of_subset hSU, hUt]
    · intro W hW
      obtain ⟨hWA, hWt⟩ := Finset.mem_powersetCard.1 hW
      have hWS : Disjoint W S := Finset.disjoint_of_subset_left hWA Finset.sdiff_disjoint
      refine Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨?_, ?_⟩, Finset.subset_union_right⟩
      · exact Finset.union_subset (hWA.trans Finset.sdiff_subset) hSA
      · rw [Finset.card_union_of_disjoint hWS, hWt]
        omega
    · intro U hU
      have hSU : S ⊆ U := (Finset.mem_filter.1 hU).2
      show U \ S ∪ S = U
      rw [Finset.sdiff_union_of_subset hSU]
    · intro W hW
      have hWA := (Finset.mem_powersetCard.1 hW).1
      have hWS : Disjoint W S := Finset.disjoint_of_subset_left hWA Finset.sdiff_disjoint
      show (W ∪ S) \ S = W
      rw [Finset.union_sdiff_cancel_right hWS]
  rw [hbij, Finset.card_powersetCard, Finset.card_sdiff_of_subset hSA]

/-! ### The `k`-th factorial moment of the intersection -/

/-- **The moment identity.**  Counting pairs `(U, S)` with `S ⊆ T ∩ U`, `|S| = k`, in two ways. -/
theorem sum_choose_card_inter {A T : Finset V} (hTA : T ⊆ A) {t k : ℕ} (hkt : k ≤ t) :
    ∑ U ∈ A.powersetCard t, (T ∩ U).card.choose k
      = T.card.choose k * (A.card - k).choose (t - k) := by
  classical
  have hterm : ∀ U ∈ A.powersetCard t,
      (T ∩ U).card.choose k = ((T.powersetCard k).filter (fun S => S ⊆ U)).card := by
    intro U _
    rw [← Finset.card_powersetCard]
    congr 1
    ext S
    simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_inter_iff]
    tauto
  have hcount : ∀ S ∈ T.powersetCard k,
      ((A.powersetCard t).filter (fun U => S ⊆ U)).card = (A.card - k).choose (t - k) := by
    intro S hS
    obtain ⟨hST, hScard⟩ := Finset.mem_powersetCard.1 hS
    rw [card_powersetCard_filter_superset (hST.trans hTA) (by omega), hScard]
  calc ∑ U ∈ A.powersetCard t, (T ∩ U).card.choose k
      = ∑ U ∈ A.powersetCard t, ∑ S ∈ T.powersetCard k, if S ⊆ U then 1 else 0 := by
        refine Finset.sum_congr rfl fun U hU => ?_
        rw [hterm U hU, Finset.card_filter]
    _ = ∑ S ∈ T.powersetCard k, ∑ U ∈ A.powersetCard t, if S ⊆ U then 1 else 0 :=
        Finset.sum_comm
    _ = ∑ S ∈ T.powersetCard k, ((A.powersetCard t).filter (fun U => S ⊆ U)).card := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.card_filter]
    _ = ∑ _S ∈ T.powersetCard k, (A.card - k).choose (t - k) := Finset.sum_congr rfl hcount
    _ = T.card.choose k * (A.card - k).choose (t - k) := by
        rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]

/-! ### The tail bound -/

/-- Markov's inequality for the `k`-th factorial moment: the `t`-subsets in which `T` occupies at
least `y` places are few. -/
theorem card_deviant_mul_choose_le {A T : Finset V} (hTA : T ⊆ A) {t k y : ℕ} (hkt : k ≤ t) :
    ((A.powersetCard t).filter (fun U => y ≤ (T ∩ U).card)).card * y.choose k
      ≤ T.card.choose k * (A.card - k).choose (t - k) := by
  classical
  rw [← sum_choose_card_inter hTA hkt]
  calc ((A.powersetCard t).filter (fun U => y ≤ (T ∩ U).card)).card * y.choose k
      = ∑ _U ∈ (A.powersetCard t).filter (fun U => y ≤ (T ∩ U).card), y.choose k := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ U ∈ (A.powersetCard t).filter (fun U => y ≤ (T ∩ U).card), (T ∩ U).card.choose k :=
        Finset.sum_le_sum fun U hU =>
          Nat.choose_le_choose k (Finset.mem_filter.1 hU).2
    _ ≤ ∑ U ∈ A.powersetCard t, (T ∩ U).card.choose k :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- The same, with the binomial coefficients turned into descending factorials. -/
theorem card_deviant_mul_descFactorial_le {A T : Finset V} (hTA : T ⊆ A) {t k y : ℕ}
    (hkt : k ≤ t) :
    ((A.powersetCard t).filter (fun U => y ≤ (T ∩ U).card)).card
        * (y.descFactorial k * A.card.descFactorial k)
      ≤ (T.card.descFactorial k * t.descFactorial k) * A.card.choose t := by
  classical
  have hmain := card_deviant_mul_choose_le hTA (t := t) (k := k) (y := y) hkt
  have hkey : A.card.choose t * t.descFactorial k
      = A.card.descFactorial k * (A.card - k).choose (t - k) := by
    have h := Nat.choose_mul (n := A.card) (k := t) (s := k) hkt
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
    calc A.card.choose t * (k.factorial * t.choose k)
        = k.factorial * (A.card.choose t * t.choose k) := by ring
      _ = k.factorial * (A.card.choose k * (A.card - k).choose (t - k)) := by rw [h]
      _ = k.factorial * A.card.choose k * (A.card - k).choose (t - k) := by ring
  set N := ((A.powersetCard t).filter (fun U => y ≤ (T ∩ U).card)).card with hN
  calc N * (y.descFactorial k * A.card.descFactorial k)
      = (N * y.choose k) * (k.factorial * A.card.descFactorial k) := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]; ring
    _ ≤ (T.card.choose k * (A.card - k).choose (t - k)) * (k.factorial * A.card.descFactorial k) :=
        Nat.mul_le_mul_right _ hmain
    _ = (k.factorial * T.card.choose k) * (A.card.descFactorial k * (A.card - k).choose (t - k)) :=
        by ring
    _ = (k.factorial * T.card.choose k) * (A.card.choose t * t.descFactorial k) := by
        rw [hkey]
    _ = T.card.descFactorial k * (A.card.choose t * t.descFactorial k) := by
        rw [Nat.descFactorial_eq_factorial_mul_choose T.card k]
    _ = (T.card.descFactorial k * t.descFactorial k) * A.card.choose t := by ring

/-- **The tail bound in usable form.**  If `|T| · t ≤ ρ (y + 1 - k)(|A| + 1 - k)` then at most a
`ρ^k` fraction of the `t`-subsets of `A` meet `T` in `y` or more points. -/
theorem card_deviant_le_pow {A T : Finset V} (hTA : T ⊆ A) {t k y : ℕ} {ρ : ℝ}
    (hkt : k ≤ t) (hky : k ≤ y) (hkA : k ≤ A.card)
    (hratio : (T.card : ℝ) * (t : ℝ) ≤ ρ * (((y + 1 - k : ℕ) : ℝ) * ((A.card + 1 - k : ℕ) : ℝ))) :
    ((((A.powersetCard t).filter (fun U => y ≤ (T ∩ U).card)).card : ℝ))
      ≤ ρ ^ k * (A.card.choose t : ℝ) := by
  classical
  set N := (((A.powersetCard t).filter (fun U => y ≤ (T ∩ U).card)).card : ℕ) with hN
  have hnat := card_deviant_mul_descFactorial_le hTA hkt (y := y)
  have hcast : (N : ℝ) * ((y.descFactorial k : ℝ) * (A.card.descFactorial k : ℝ))
      ≤ ((T.card.descFactorial k : ℝ) * (t.descFactorial k : ℝ)) * (A.card.choose t : ℝ) := by
    exact_mod_cast hnat
  -- lower bounds for the descending factorials in the denominator
  have hy : (((y + 1 - k : ℕ) : ℝ)) ^ k ≤ (y.descFactorial k : ℝ) := by
    exact_mod_cast Nat.pow_sub_le_descFactorial y k
  have hA : (((A.card + 1 - k : ℕ) : ℝ)) ^ k ≤ (A.card.descFactorial k : ℝ) := by
    exact_mod_cast Nat.pow_sub_le_descFactorial A.card k
  have hT : (T.card.descFactorial k : ℝ) ≤ (T.card : ℝ) ^ k := by
    exact_mod_cast Nat.descFactorial_le_pow T.card k
  have ht : (t.descFactorial k : ℝ) ≤ (t : ℝ) ^ k := by
    exact_mod_cast Nat.descFactorial_le_pow t k
  have hypos : (0 : ℝ) < ((y + 1 - k : ℕ) : ℝ) := by
    have : 0 < y + 1 - k := by omega
    exact_mod_cast this
  have hApos : (0 : ℝ) < ((A.card + 1 - k : ℕ) : ℝ) := by
    have : 0 < A.card + 1 - k := by omega
    exact_mod_cast this
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hchoose : (0 : ℝ) ≤ (A.card.choose t : ℝ) := Nat.cast_nonneg _
  -- combine
  have hstep : (N : ℝ) * ((((y + 1 - k : ℕ) : ℝ)) ^ k * (((A.card + 1 - k : ℕ) : ℝ)) ^ k)
      ≤ ((T.card : ℝ) ^ k * (t : ℝ) ^ k) * (A.card.choose t : ℝ) := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hNnn) (le_trans hcast ?_)
    · exact mul_le_mul hy hA (by positivity) (by positivity)
    · exact mul_le_mul_of_nonneg_right (mul_le_mul hT ht (by positivity) (by positivity)) hchoose
  have hpow : ((T.card : ℝ) * (t : ℝ)) ^ k
      ≤ (ρ * (((y + 1 - k : ℕ) : ℝ) * ((A.card + 1 - k : ℕ) : ℝ))) ^ k :=
    pow_le_pow_left₀ (by positivity) hratio k
  have hden : (0 : ℝ) < (((y + 1 - k : ℕ) : ℝ)) ^ k * (((A.card + 1 - k : ℕ) : ℝ)) ^ k := by
    positivity
  rw [← le_div_iff₀ hden] at hstep
  refine le_trans hstep ?_
  rw [div_le_iff₀ hden]
  calc ρ ^ k * (A.card.choose t : ℝ)
      * ((((y + 1 - k : ℕ) : ℝ)) ^ k * (((A.card + 1 - k : ℕ) : ℝ)) ^ k)
      = (ρ * (((y + 1 - k : ℕ) : ℝ) * ((A.card + 1 - k : ℕ) : ℝ))) ^ k
        * (A.card.choose t : ℝ) := by
        rw [mul_pow, mul_pow]; ring
    _ ≥ ((T.card : ℝ) * (t : ℝ)) ^ k * (A.card.choose t : ℝ) :=
        mul_le_mul_of_nonneg_right hpow hchoose
    _ = ((T.card : ℝ) ^ k * (t : ℝ) ^ k) * (A.card.choose t : ℝ) := by rw [mul_pow]

end BKLO
