/-
# Nibble — the complete `r`-uniform hypergraph as a test instance

Standalone, Mathlib-only.  The outer-layer parameter obligations of the nibble assembly are
`∀`-statements over hypergraphs satisfying near-regularity and a codegree bound.  Refuting such an
obligation requires an explicit instance; this file supplies the simplest one, the complete
`r`-uniform hypergraph `completeHG n r = powersetCard r univ` on `Fin n`:

* it is `r`-uniform;
* it is exactly `d`-regular with `d = C(n-1, r-1)` (hence `NearlyRegularMost` with empty exceptional
  set);
* its codegrees are `C(n-2, r-2) = d·(r-1)/(n-1)`, so `CodegreeBounded` holds with any `μ > 0` once
  `n` is large;
* `d ≥ (n-1)/(r-1)`, so both the degree threshold `d₀ ≤ d` and the size condition `|V| ≤ K d²` hold
  for large `n`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Regular
import Nibble.RegularMost
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered

open Finset Hypergraph

namespace Nibble

/-- The number of `r`-subsets of `s` containing a fixed `a`-subset `A` is `(|s|-|A|)` choose
`(r-|A|)`. -/
theorem card_filter_superset_powersetCard {α : Type*} [DecidableEq α] (s A : Finset α) (r : ℕ)
    (hAs : A ⊆ s) (hAr : A.card ≤ r) :
    ((Finset.powersetCard r s).filter (fun e => A ⊆ e)).card
      = (s.card - A.card).choose (r - A.card) := by
  classical
  have hbij : ((Finset.powersetCard r s).filter (fun e => A ⊆ e)).card
      = (Finset.powersetCard (r - A.card) (s \ A)).card := by
    refine Finset.card_bij' (fun e _ => e \ A) (fun t _ => A ∪ t) ?_ ?_ ?_ ?_
    · intro e he
      rw [Finset.mem_filter, Finset.mem_powersetCard] at he
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨he.1.1 hx.1, hx.2⟩
      · rw [Finset.card_sdiff_of_subset he.2, he.1.2]
    · intro t ht
      rw [Finset.mem_powersetCard] at ht
      have hdisj : Disjoint A t := by
        refine Finset.disjoint_left.mpr fun x hx hxt => ?_
        exact (Finset.mem_sdiff.mp (ht.1 hxt)).2 hx
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨?_, ?_⟩, Finset.subset_union_left⟩
      · intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact hAs hx
        · exact (Finset.mem_sdiff.mp (ht.1 hx)).1
      · rw [Finset.card_union_of_disjoint hdisj, ht.2]
        omega
    · intro e he
      rw [Finset.mem_filter] at he
      show A ∪ (e \ A) = e
      rw [Finset.union_sdiff_self_eq_union]
      exact Finset.union_eq_right.mpr he.2
    · intro t ht
      rw [Finset.mem_powersetCard] at ht
      have hdisj : Disjoint A t := by
        refine Finset.disjoint_left.mpr fun x hx hxt => ?_
        exact (Finset.mem_sdiff.mp (ht.1 hxt)).2 hx
      show (A ∪ t) \ A = t
      rw [Finset.union_sdiff_cancel_left hdisj]
  rw [hbij, Finset.card_powersetCard, Finset.card_sdiff_of_subset hAs]

/-- The complete `r`-uniform hypergraph on `Fin n`. -/
def completeHG (n r : ℕ) : Finset (Finset (Fin n)) :=
  Finset.powersetCard r (Finset.univ : Finset (Fin n))

theorem completeHG_isUniform (n r : ℕ) : IsUniform (completeHG n r) r := by
  intro e he
  exact (Finset.mem_powersetCard.mp he).2

/-- Every vertex of the complete `r`-uniform hypergraph has degree `C(n-1, r-1)`. -/
theorem completeHG_degree {n r : ℕ} (hr : 1 ≤ r) (v : Fin n) :
    degree (completeHG n r) v = (n - 1).choose (r - 1) := by
  classical
  have hfilter : (completeHG n r).filter (fun e => v ∈ e)
      = (completeHG n r).filter (fun e => ({v} : Finset (Fin n)) ⊆ e) := by
    refine Finset.filter_congr fun e _ => ?_
    simp [Finset.singleton_subset_iff]
  have hcard := card_filter_superset_powersetCard (Finset.univ : Finset (Fin n))
    ({v} : Finset (Fin n)) r (Finset.subset_univ _) (by simpa using hr)
  rw [degree, hfilter, completeHG]
  simpa using hcard

/-- Two distinct vertices of the complete `r`-uniform hypergraph have codegree `C(n-2, r-2)`. -/
theorem completeHG_codegree {n r : ℕ} (hr : 2 ≤ r) {x y : Fin n} (hxy : x ≠ y) :
    codegree (completeHG n r) x y = (n - 2).choose (r - 2) := by
  classical
  have hpair : ({x, y} : Finset (Fin n)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
  have hfilter : (completeHG n r).filter (fun e => x ∈ e ∧ y ∈ e)
      = (completeHG n r).filter (fun e => ({x, y} : Finset (Fin n)) ⊆ e) := by
    refine Finset.filter_congr fun e _ => ?_
    simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]
  have hcard := card_filter_superset_powersetCard (Finset.univ : Finset (Fin n))
    ({x, y} : Finset (Fin n)) r (Finset.subset_univ _) (by rw [hpair]; exact hr)
  rw [codegree, hfilter, completeHG]
  rw [hpair] at hcard
  simpa using hcard

/-- The degree/codegree identity `(n-1)·C(n-2,r-2) = C(n-1,r-1)·(r-1)`. -/
theorem choose_shift_identity {n r : ℕ} (hr : 2 ≤ r) (hn : 2 ≤ n) :
    (n - 1) * (n - 2).choose (r - 2) = (n - 1).choose (r - 1) * (r - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  have h := Nat.add_one_mul_choose_eq m k
  simpa using h

/-- The complete `r`-uniform hypergraph is exactly `C(n-1,r-1)`-regular, hence majority
near-regular with empty exceptional set. -/
theorem completeHG_nearlyRegularMost {n r : ℕ} (hr : 1 ≤ r) {μ η : ℝ} (hμ : 0 ≤ μ) (hη : 0 ≤ η) :
    NearlyRegularMost (completeHG n r) (((n - 1).choose (r - 1) : ℕ) : ℝ) μ η := by
  refine ⟨∅, by simpa using mul_nonneg hη (Nat.cast_nonneg _), fun v _ => ?_⟩
  rw [completeHG_degree hr v]
  refine ⟨?_, ?_⟩
  · nlinarith [Nat.cast_nonneg (α := ℝ) ((n - 1).choose (r - 1))]
  · nlinarith [Nat.cast_nonneg (α := ℝ) ((n - 1).choose (r - 1))]

/-- **A test instance for the nibble hypotheses.**  For every tolerance `μ > 0`, degree threshold
`d₀ > 0` and size constant `K > 0`, the complete `r`-uniform hypergraph on a suitably large `Fin n`
is `r`-uniform, exactly `d`-regular with `d ≥ d₀`, codegree-bounded by `μ d`, and satisfies the size
condition `|V| ≤ K d²`. -/
theorem exists_complete_instance {r : ℕ} (hr : 2 ≤ r) {μ d₀ K : ℝ}
    (hμ : 0 < μ) (hd₀ : 0 < d₀) (hK : 0 < K) :
    ∃ (n : ℕ) (d : ℝ), 0 < n ∧ 0 < d ∧ d₀ ≤ d ∧ (n : ℝ) ≤ K * d ^ 2 ∧
      IsUniform (completeHG n r) r ∧
      (∀ v : Fin n, (degree (completeHG n r) v : ℝ) = d) ∧
      CodegreeBounded (completeHG n r) (μ * d) := by
  classical
  set n : ℕ := r + 2 + Nat.ceil ((r : ℝ) * d₀) + Nat.ceil ((r : ℝ) / μ)
      + Nat.ceil (2 * (r : ℝ) ^ 2 / K) with hn_def
  set d : ℝ := (((n - 1).choose (r - 1) : ℕ) : ℝ) with hd_def
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hn2 : 2 ≤ n := by omega
  have hnr : r ≤ n := by omega
  have hm : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h1 : 1 ≤ n := by omega
    push_cast [Nat.cast_sub h1]
    ring
  have hb1 : (r : ℝ) * d₀ ≤ (n : ℝ) - 1 := by
    have h1 : ((Nat.ceil ((r : ℝ) * d₀) : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      have h : Nat.ceil ((r : ℝ) * d₀) ≤ n - 1 := by omega
      exact_mod_cast h
    have h2 : (r : ℝ) * d₀ ≤ (Nat.ceil ((r : ℝ) * d₀) : ℕ) := Nat.le_ceil _
    rw [hm] at h1
    linarith only [h1, h2]
  have hb2 : (r : ℝ) / μ ≤ (n : ℝ) - 1 := by
    have h1 : ((Nat.ceil ((r : ℝ) / μ) : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      have h : Nat.ceil ((r : ℝ) / μ) ≤ n - 1 := by omega
      exact_mod_cast h
    have h2 : (r : ℝ) / μ ≤ (Nat.ceil ((r : ℝ) / μ) : ℕ) := Nat.le_ceil _
    rw [hm] at h1
    linarith only [h1, h2]
  have hb3 : 2 * (r : ℝ) ^ 2 / K ≤ (n : ℝ) - 1 := by
    have h1 : ((Nat.ceil (2 * (r : ℝ) ^ 2 / K) : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      have h : Nat.ceil (2 * (r : ℝ) ^ 2 / K) ≤ n - 1 := by omega
      exact_mod_cast h
    have h2 : 2 * (r : ℝ) ^ 2 / K ≤ (Nat.ceil (2 * (r : ℝ) ^ 2 / K) : ℕ) := Nat.le_ceil _
    rw [hm] at h1
    linarith only [h1, h2]
  -- the key identity `(n-1)·C(n-2,r-2) = C(n-1,r-1)·(r-1)`, and `C(n-2,r-2) ≥ 1`
  have hr1R : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    have h1 : 1 ≤ r := by omega
    push_cast [Nat.cast_sub h1]
    ring
  have hid : ((n : ℝ) - 1) * (((n - 2).choose (r - 2) : ℕ) : ℝ) = d * ((r : ℝ) - 1) := by
    have h : ((n - 1 : ℕ) : ℝ) * (((n - 2).choose (r - 2) : ℕ) : ℝ)
        = (((n - 1).choose (r - 1) : ℕ) : ℝ) * ((r - 1 : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) (choose_shift_identity hr hn2)
    rw [hm, hr1R] at h
    rw [hd_def]
    exact h
  have hcpos : (1 : ℝ) ≤ (((n - 2).choose (r - 2) : ℕ) : ℝ) := by
    have h : 0 < (n - 2).choose (r - 2) := Nat.choose_pos (by omega)
    exact_mod_cast h
  have hr1pos : (0 : ℝ) < (r : ℝ) - 1 := by linarith only [hrR]
  have hn1pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith only [this]
  have hdlow : (n : ℝ) - 1 ≤ d * ((r : ℝ) - 1) := by nlinarith only [hid, hcpos, hn1pos]
  have hdpos : 0 < d := by nlinarith only [hid, hcpos, hr1pos, hn1pos]
  refine ⟨n, d, by omega, hdpos, ?_, ?_, completeHG_isUniform n r,
    fun v => by rw [completeHG_degree (by omega) v], ?_⟩
  · -- `d₀ ≤ d`
    nlinarith only [hb1, hdlow, hdpos]
  · -- `|V| ≤ K d²`
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hnle : (n : ℝ) ≤ 2 * ((n : ℝ) - 1) := by linarith only [hnR]
    have hKn : 2 * (r : ℝ) ^ 2 ≤ K * ((n : ℝ) - 1) := by
      rw [div_le_iff₀ hK] at hb3
      linarith only [hb3]
    have hsq : ((n : ℝ) - 1) ^ 2 ≤ (d * ((r : ℝ) - 1)) ^ 2 := by nlinarith
    nlinarith [sq_nonneg ((r : ℝ) - 1), sq_nonneg d]
  · -- codegree bound
    intro x y hxy
    rw [completeHG_codegree hr hxy]
    have hcod : (((n - 2).choose (r - 2) : ℕ) : ℝ) = d * ((r : ℝ) - 1) / ((n : ℝ) - 1) := by
      field_simp at hid ⊢
      linarith only [hid]
    rw [hcod]
    rw [div_le_iff₀ hn1pos]
    have hμn : (r : ℝ) ≤ μ * ((n : ℝ) - 1) := by
      rw [div_le_iff₀ hμ] at hb2
      linarith
    nlinarith

end Nibble
