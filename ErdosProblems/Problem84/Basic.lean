import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Erdős Problem #84 — Basic definitions

Cycle-length spectra and the counting function `spectrumCount`.
-/

namespace ErdosProblem84

open scoped BigOperators
open SimpleGraph Walk

/-- Valid cycle lengths for an `n`-vertex graph. -/
def validLengths (n : ℕ) : Finset ℕ :=
  if _h : 3 ≤ n then Finset.Icc 3 n else ∅

lemma mem_validLengths {n ℓ : ℕ} (hn : 3 ≤ n) :
    ℓ ∈ validLengths n ↔ 3 ≤ ℓ ∧ ℓ ≤ n := by
  simp [validLengths, hn]

lemma card_validLengths (n : ℕ) (hn : 3 ≤ n) : (validLengths n).card = n - 2 := by
  simp [validLengths, hn, Nat.card_Icc]

/-- The cycle-length spectrum of a graph: lengths of simple cycles. -/
noncomputable def cycleSpectrum {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) : Set ℕ :=
  {ℓ | ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = ℓ}

lemma mem_cycleSpectrum {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) {ℓ : ℕ} :
    ℓ ∈ cycleSpectrum G ↔ ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = ℓ := by
  simp [cycleSpectrum]

lemma IsCycle.length_le_card {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    p.length ≤ Fintype.card V := by
  have htail := hp.isPath_tail
  rw [← Walk.length_tail_add_one hp.not_nil]
  exact Nat.succ_le_of_lt htail.length_lt

lemma mem_validLengths_of_mem_cycleSpectrum {n ℓ : ℕ} (hn : 3 ≤ n)
    {G : SimpleGraph (Fin n)} (h : ℓ ∈ cycleSpectrum G) :
    ℓ ∈ validLengths n := by
  rw [mem_validLengths hn]
  obtain ⟨u, p, hp, rfl⟩ := (mem_cycleSpectrum G).1 h
  exact ⟨IsCycle.three_le_length hp, by simpa [Fintype.card_fin] using IsCycle.length_le_card hp⟩

/-- A subset `A` of `{3,…,n}` is *realizable* if some `n`-vertex graph has spectrum `A`. -/
def Realizable (n : ℕ) (A : Set ℕ) : Prop :=
  if _h : 3 ≤ n then
    A ⊆ validLengths n ∧
      ∃ (G : SimpleGraph (Fin n)), cycleSpectrum G = A
  else
    A = ∅

/-- Realizability of a finset of cycle lengths. -/
def RealizableFinset (n : ℕ) (S : Finset ℕ) : Prop :=
  Realizable n (S : Set ℕ)

noncomputable instance (n : ℕ) (S : Finset ℕ) : Decidable (RealizableFinset n S) :=
  Classical.propDecidable _

/-- `f(n)`: the number of distinct realizable cycle-length spectra on `n` vertices. -/
noncomputable def spectrumCount (n : ℕ) : ℕ∞ :=
  if _h : 3 ≤ n then
    ((validLengths n).powerset.filter fun S => RealizableFinset n S).card
  else
    0

lemma RealizableFinset_iff {n : ℕ} (S : Finset ℕ) :
    RealizableFinset n S ↔ Realizable n (S : Set ℕ) := Iff.rfl

/-- Trivial upper bound: at most `2^{n-2}` subsets of `{3,…,n}`. -/
theorem spectrumCount_le (n : ℕ) (hn : 3 ≤ n) :
    spectrumCount n ≤ 2 ^ (n - 2) := by
  unfold spectrumCount
  rw [dif_pos hn]
  exact_mod_cast
    calc
      ((validLengths n).powerset.filter fun S => RealizableFinset n S).card
          ≤ (validLengths n).powerset.card := Finset.card_filter_le _ _
      _ = 2 ^ (validLengths n).card := Finset.card_powerset _
      _ = 2 ^ (n - 2) := by rw [card_validLengths n hn]

/-- The golden ratio `φ = (1 + √5)/2`. -/
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

lemma one_lt_φ : 1 < φ := by
  unfold φ
  have h : Real.sqrt 5 > 2 := by
    have : (2 : ℝ) ^ 2 < 5 := by norm_num
    exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2)).2 this
  linarith

lemma φ_div_sqrt_two_gt_one : φ / Real.sqrt 2 > 1 := by
  unfold φ
  have hφ : (1 + Real.sqrt 5) / 2 > Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 from by norm_num),
      Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 from by norm_num),
      sq_nonneg (Real.sqrt 5 - Real.sqrt 2)]
  rw [gt_iff_lt, lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 from by norm_num)]

end ErdosProblem84
