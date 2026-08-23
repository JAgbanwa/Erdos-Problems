/-
# Nibble — the unconditional greedy bound for fractional matchings

A maximum (hence maximal) matching `M` of an `r`-uniform hypergraph meets every edge, so every
fractional matching `w` satisfies `∑ w ≤ r·|M|`: the weight is carried by the `r|M|` vertices that
`M` covers, each of which carries weight at most `1`.

* `Nibble.exists_matching_sum_le_mul` — the bound, with no hypothesis beyond `r`-uniformity.
* `Nibble.fracNibbleAt_of_one_sub_inv_le` — consequently the `(r, β)`-slice of the (false) target
  statement `Nibble.FracNibbleTheorem` is *true*, unconditionally, for every `β ≥ 1 - 1/r`.

Together with `Nibble.not_fracNibbleAt` (the slice is false for `β < 1/(r+1)`) this brackets the
tolerances for which the statement holds: false below `1/(r+1)`, true from `1 - 1/r` on.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.FracNibbleRefutation

open Finset Hypergraph

namespace Nibble

/-- **A maximum matching meets every edge and carries all the weight.**  For every `r`-uniform
hypergraph and every fractional matching `w` there is a matching `M` with `∑ w ≤ r·|M|`. -/
theorem exists_matching_sum_le_mul {W : Type} [Fintype W] [DecidableEq W]
    (H : Finset (Finset W)) {r : ℕ} (hr : 1 ≤ r) (hunif : IsUniform H r) (w : Finset W → ℝ)
    (hwnn : ∀ T, 0 ≤ w T) (hvle : ∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) :
    ∃ M : Finset (Finset W), IsMatching H M ∧ (∑ T ∈ H, w T) ≤ (r : ℝ) * (M.card : ℝ) := by
  classical
  -- a matching of maximum size
  set 𝒮 := H.powerset.filter (fun M => IsMatching H M) with h𝒮
  have hne : 𝒮.Nonempty := by
    refine ⟨∅, ?_⟩
    rw [h𝒮, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, ⟨Finset.empty_subset _, by simp⟩⟩
  obtain ⟨M, hMS, hsup⟩ := Finset.exists_mem_eq_sup 𝒮 hne Finset.card
  rw [h𝒮, Finset.mem_filter] at hMS
  obtain ⟨-, hM⟩ := hMS
  have hmax : ∀ M' : Finset (Finset W), IsMatching H M' → M'.card ≤ M.card := by
    intro M' hM'
    have hmem : M' ∈ 𝒮 := by
      rw [h𝒮, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hM'.subset, hM'⟩
    rw [← hsup]
    exact Finset.le_sup (f := Finset.card) hmem
  refine ⟨M, hM, ?_⟩
  set S : Finset W := M.biUnion id with hS
  -- every edge meets the covered set `S`
  have hmeets : ∀ T ∈ H, (S.filter (fun v => v ∈ T)).Nonempty := by
    intro T hT
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    have hdisj : ∀ m ∈ M, Disjoint T m := by
      intro m hm
      rw [Finset.disjoint_left]
      intro v hvT hvm
      have hvS : v ∈ S := Finset.mem_biUnion.mpr ⟨m, hm, hvm⟩
      have : v ∈ S.filter (fun v => v ∈ T) := Finset.mem_filter.mpr ⟨hvS, hvT⟩
      rw [hcon] at this
      exact absurd this (Finset.notMem_empty v)
    have hTne : T.Nonempty := by
      rw [← Finset.card_pos, hunif T hT]
      omega
    have hTM : T ∉ M := by
      intro hTM
      obtain ⟨v, hv⟩ := hTne
      exact (Finset.disjoint_left.mp (hdisj T hTM) hv) hv
    have hM' : IsMatching H (insert T M) := by
      refine ⟨Finset.insert_subset hT hM.subset, ?_⟩
      intro e he f hf hef
      rw [Finset.mem_insert] at he hf
      rcases he with rfl | he
      · rcases hf with rfl | hf
        · exact absurd rfl hef
        · exact hdisj f hf
      · rcases hf with rfl | hf
        · exact (hdisj e he).symm
        · exact hM.disjoint e he f hf hef
    have hle := hmax _ hM'
    rw [Finset.card_insert_of_notMem hTM] at hle
    omega
  -- the weight is carried by `S`
  have hkey : (∑ T ∈ H, w T) ≤ ∑ v ∈ S, ∑ T ∈ H.filter (fun T => v ∈ T), w T := by
    have hswap : ∑ v ∈ S, ∑ T ∈ H.filter (fun T => v ∈ T), w T
        = ∑ T ∈ H, ((S.filter (fun v => v ∈ T)).card : ℝ) * w T := by
      calc ∑ v ∈ S, ∑ T ∈ H.filter (fun T => v ∈ T), w T
          = ∑ v ∈ S, ∑ T ∈ H, (if v ∈ T then w T else 0) := by
            exact Finset.sum_congr rfl (fun v _ => by rw [Finset.sum_filter])
        _ = ∑ T ∈ H, ∑ v ∈ S, (if v ∈ T then w T else 0) := Finset.sum_comm
        _ = ∑ T ∈ H, ((S.filter (fun v => v ∈ T)).card : ℝ) * w T := by
            refine Finset.sum_congr rfl (fun T _ => ?_)
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hswap]
    refine Finset.sum_le_sum (fun T hT => ?_)
    have h1 : (1 : ℝ) ≤ ((S.filter (fun v => v ∈ T)).card : ℝ) := by
      have := Finset.card_pos.mpr (hmeets T hT)
      exact_mod_cast this
    nlinarith [hwnn T]
  -- and `S` has at most `r|M|` vertices, each of weight at most `1`
  have hScard : (S.card : ℝ) ≤ (r : ℝ) * (M.card : ℝ) := by
    have h1 : S.card ≤ ∑ m ∈ M, (id m).card := Finset.card_biUnion_le
    have h2 : ∑ m ∈ M, (id m).card = r * M.card := by
      simp only [id_eq]
      rw [Finset.sum_congr rfl (fun m hm => hunif m (hM.subset hm)), Finset.sum_const,
        smul_eq_mul, mul_comm]
    rw [h2] at h1
    exact_mod_cast h1
  calc (∑ T ∈ H, w T) ≤ ∑ v ∈ S, ∑ T ∈ H.filter (fun T => v ∈ T), w T := hkey
    _ ≤ ∑ _v ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hvle v)
    _ = (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (r : ℝ) * (M.card : ℝ) := hScard

/-- **The `(r, β)`-slice of the target statement is unconditionally true for `β ≥ 1 - 1/r`.**  No
codegree or degree hypothesis is used: the greedy bound `∑ w ≤ r·ν` suffices. -/
theorem fracNibbleAt_of_one_sub_inv_le (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 1 - 1 / (r : ℝ) ≤ β) :
    FracNibbleAt r β := by
  have hrpos : (0 : ℝ) < r := by
    have : 0 < r := lt_of_lt_of_le (by norm_num) hr
    exact_mod_cast this
  refine ⟨1, one_pos, 1, one_pos, ?_⟩
  intro W _ _ H w D _ hunif hwnn _ hvle _ _
  obtain ⟨M, hM, hMle⟩ :=
    exists_matching_sum_le_mul H (le_trans (by norm_num) hr) hunif w hwnn hvle
  refine ⟨M, hM, ?_⟩
  have hsumnn : 0 ≤ ∑ T ∈ H, w T := Finset.sum_nonneg (fun T _ => hwnn T)
  have hinv : (1 - β) ≤ 1 / (r : ℝ) := by linarith
  have hstep : (1 - β) * (∑ T ∈ H, w T) ≤ (1 / (r : ℝ)) * (∑ T ∈ H, w T) :=
    mul_le_mul_of_nonneg_right hinv hsumnn
  have hstep2 : (1 / (r : ℝ)) * (∑ T ∈ H, w T) ≤ (1 / (r : ℝ)) * ((r : ℝ) * (M.card : ℝ)) :=
    mul_le_mul_of_nonneg_left hMle (by positivity)
  have hfin : (1 / (r : ℝ)) * ((r : ℝ) * (M.card : ℝ)) = (M.card : ℝ) := by
    field_simp
  linarith

end Nibble
