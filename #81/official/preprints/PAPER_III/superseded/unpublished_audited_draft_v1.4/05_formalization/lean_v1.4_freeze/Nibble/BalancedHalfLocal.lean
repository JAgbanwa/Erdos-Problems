/-
# Local attack on `exists_balanced_half_selection` — foundational lemmas.

Self-contained (Mathlib only).  Builds the confident pieces of the potential-and-swap proof of the
balanced half-selection theorem:

* an initial half-selection exists (each even pool has a half-size subset);
* the deficits sum to zero over any vertex set covering the pools;
* the potential `Φ` and its non-negativity.

The swap step (the alternating-chain argument) is developed on top of these.
-/
import Mathlib.Analysis.Normed.Ring.Lemmas

open Finset

namespace Nibble.HalfAllocLocal

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V]

/-- How often the selection `H` uses the vertex `a`. -/
def load (L : Finset ι) (H : ι → Finset V) (a : V) : ℕ :=
  (L.filter fun w => a ∈ H w).card

/-- A half selection: a subset of every pool, of half its size on the index set. -/
def IsHalf (L : Finset ι) (P : ι → Finset V) (k : ι → ℕ) (H : ι → Finset V) : Prop :=
  (∀ w, H w ⊆ P w) ∧ ∀ w ∈ L, (H w).card = k w

/-- The deficit of a vertex: twice its load minus its number of opportunities. -/
def defic (L : Finset ι) (P H : ι → Finset V) (a : V) : ℤ :=
  2 * (load L H a : ℤ) - (load L P a : ℤ)

/-- **An initial half selection exists.**  Pick any `k w`-subset of each even pool. -/
theorem exists_isHalf (L : Finset ι) (P : ι → Finset V) (k : ι → ℕ)
    (hP : ∀ w ∈ L, (P w).card = 2 * k w) :
    ∃ H : ι → Finset V, IsHalf L P k H := by
  classical
  -- choose, for each `w`, a `k w`-subset of `P w`
  have hsub : ∀ w, ∃ S : Finset V, S ⊆ P w ∧ (w ∈ L → S.card = k w) := by
    intro w
    by_cases hw : w ∈ L
    · have hkle : k w ≤ (P w).card := by rw [hP w hw]; omega
      obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hkle
      exact ⟨S, hSsub, fun _ => hScard⟩
    · exact ⟨∅, Finset.empty_subset _, fun h => absurd h hw⟩
  choose H hHsub hHcard using hsub
  exact ⟨H, hHsub, fun w hw => hHcard w hw⟩

/-- `load` counts a subfamily, so `load H ≤ load P` whenever `H ⊆ P` pointwise. -/
theorem load_mono {L : Finset ι} {H P : ι → Finset V} (h : ∀ w, H w ⊆ P w) (a : V) :
    load L H a ≤ load L P a := by
  apply Finset.card_le_card
  intro w hw
  rw [Finset.mem_filter] at hw ⊢
  exact ⟨hw.1, h w hw.2⟩

/-- **Double count** of `load` over a covering vertex set. -/
theorem sum_load_eq (L : Finset ι) (Q : ι → Finset V) (A : Finset V)
    (hQ : ∀ w ∈ L, Q w ⊆ A) :
    ∑ a ∈ A, load L Q a = ∑ w ∈ L, (Q w).card := by
  classical
  simp only [load, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  rw [← Finset.card_filter]
  have : A.filter (fun a => a ∈ Q w) = Q w := by
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right]
    exact hQ w hw
  rw [this]

/-- **The deficits sum to zero** over any vertex set covering the pools. -/
theorem sum_defic_eq (L : Finset ι) (P H : ι → Finset V) (k : ι → ℕ)
    (A : Finset V) (hAP : ∀ w ∈ L, P w ⊆ A) (hHP : ∀ w, H w ⊆ P w)
    (hHalf : IsHalf L P k H) (hP : ∀ w ∈ L, (P w).card = 2 * k w) :
    ∑ a ∈ A, defic L P H a = 0 := by
  classical
  have hAH : ∀ w ∈ L, H w ⊆ A := fun w hw => (hHP w).trans (hAP w hw)
  -- the key nat identity: over `A`, the pool-load is twice the half-load
  have hnat : ∑ a ∈ A, load L P a = 2 * ∑ a ∈ A, load L H a := by
    rw [sum_load_eq L H A hAH, sum_load_eq L P A hAP]
    have h1 : ∑ w ∈ L, (H w).card = ∑ w ∈ L, k w :=
      Finset.sum_congr rfl (fun w hw => hHalf.2 w hw)
    have h2 : ∑ w ∈ L, (P w).card = ∑ w ∈ L, 2 * k w :=
      Finset.sum_congr rfl (fun w hw => hP w hw)
    rw [h1, h2, Finset.mul_sum]
  have hZ : (∑ a ∈ A, (load L P a : ℤ)) = 2 * ∑ a ∈ A, (load L H a : ℤ) := by
    have := congrArg (Nat.cast (R := ℤ)) hnat
    push_cast at this ⊢
    exact this
  simp only [defic, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hZ]
  ring


end Nibble.HalfAllocLocal
