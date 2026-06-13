import ErdosProblems.Problem84.Basic

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Combinatorial cycle-spectrum formulas (single-hub chords)
-/

namespace ErdosProblem84

open scoped BigOperators

/-- Chord offsets available for odd `n ≥ 5`: `{2,…,(n-1)/2}`. -/
def chordOffsets (n : ℕ) : Finset ℕ :=
  if h : Odd n ∧ 5 ≤ n then Finset.Icc 2 ((n - 1) / 2) else ∅

lemma mem_chordOffsets {n s : ℕ} (hn : Odd n) (h5 : 5 ≤ n) :
    s ∈ chordOffsets n ↔ 2 ≤ s ∧ s ≤ (n - 1) / 2 := by
  simp [chordOffsets, hn, h5]

lemma card_chordOffsets (n : ℕ) (hn : Odd n) (h5 : 5 ≤ n) :
    (chordOffsets n).card = (n - 1) / 2 - 1 := by
  have hn' : 2 ≤ (n - 1) / 2 := by
    rcases hn with ⟨k, rfl⟩
    omega
  simp [chordOffsets, hn, h5, Nat.card_Icc, hn']

/-- Difference-cycle lengths contributed by pairs of chords. -/
def differenceCycles (S : Finset ℕ) : Set ℕ :=
  {d | ∃ s ∈ S, ∃ t ∈ S, s < t ∧ d = t - s + 2}

/-- Expected cycle spectrum from the single-hub chord construction. -/
def chordSpectrum (n : ℕ) (S : Finset ℕ) : Set ℕ :=
  {n} ∪ (S.image (· + 1)) ∪ (S.image fun s => n - s + 1) ∪ differenceCycles S

/-- Long cycle lengths: `(n+1)/2 < ℓ < n`. -/
def longCycleRange (n : ℕ) : Set ℕ :=
  {ℓ | (n + 1) / 2 < ℓ ∧ ℓ < n}

/-- Recover chord offsets from long cycle lengths in the spectrum. -/
def recoverChordSet (n : ℕ) (Cy : Set ℕ) : Set ℕ :=
  {s | n - s + 1 ∈ Cy ∩ longCycleRange n}

lemma map_sub_add_one_injective (n : ℕ) :
    Function.Injective fun s : ℕ => n - s + 1 := by
  intro a b hab
  have hab' : n - a = n - b := by linarith
  have ha : a ≤ n := by omega
  have hb : b ≤ n := by omega
  exact (Nat.sub_right_inj ha hb).mp hab'

lemma longCycleRange_disjoint_short (n : ℕ) (hn : Odd n) (h5 : 5 ≤ n) (s : ℕ)
    (hs : s ∈ chordOffsets n) :
    s + 1 ∉ longCycleRange n := by
  simp only [longCycleRange, Set.mem_setOf_eq, mem_chordOffsets hn h5] at hs ⊢
  rcases hn with ⟨k, rfl⟩
  omega

lemma longCycleRange_disjoint_difference (n : ℕ) (hn : Odd n) (h5 : 5 ≤ n)
    {s t : ℕ} (hs : s ∈ chordOffsets n) (ht : t ∈ chordOffsets n) (hst : s < t) :
    t - s + 2 ∉ longCycleRange n := by
  simp only [longCycleRange, Set.mem_setOf_eq, mem_chordOffsets hn h5] at hs ht ⊢
  rcases hn with ⟨k, rfl⟩
  omega

lemma mem_longCycleRange_of_mem (n : ℕ) (S : Finset ℕ) {s : ℕ} (hs : s ∈ S)
    (hn : Odd n) (h5 : 5 ≤ n) (hS : S ⊆ chordOffsets n) :
    n - s + 1 ∈ longCycleRange n := by
  have hs' := hS hs
  rw [mem_chordOffsets hn h5] at hs'
  simp only [longCycleRange, Set.mem_setOf_eq]
  rcases hn with ⟨k, rfl⟩
  omega

lemma longCycles_chordSpectrum (n : ℕ) (S : Finset ℕ) (hS : S ⊆ chordOffsets n)
    (hn : Odd n) (h5 : 5 ≤ n) :
    chordSpectrum n S ∩ longCycleRange n = (S.image fun s => n - s + 1 : Set ℕ) := by
  ext ℓ
  simp only [chordSpectrum, differenceCycles, longCycleRange, Set.mem_inter_iff,
    Set.mem_union, Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro ⟨hCy, hlong⟩
    rcases hCy with hℓ | ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩ | ⟨s, hs, t, ht, hst, rfl⟩
    · subst hℓ
      rcases hn with ⟨k, rfl⟩
      simp only [longCycleRange, Set.mem_setOf_eq] at hlong
      omega
    · exact (longCycleRange_disjoint_short n hn h5 s (hS hs) hlong).elim
    · exact ⟨s, hs, rfl⟩
    · exact (longCycleRange_disjoint_difference n hn h5 (hS hs) (hS ht) hst hlong).elim
  · intro h
    obtain ⟨s, hs, rfl⟩ := h
    refine ⟨Or.inr (Or.inr (Or.inl ⟨s, hs, rfl⟩)), mem_longCycleRange_of_mem n S hs hn h5 hS⟩

lemma recoverChordSet_chordSpectrum (n : ℕ) (S : Finset ℕ) (hn : Odd n) (h5 : 5 ≤ n)
    (hS : S ⊆ chordOffsets n) :
    recoverChordSet n (chordSpectrum n S) = (S : Set ℕ) := by
  ext s
  simp only [recoverChordSet, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h
    have h' : n - s + 1 ∈ chordSpectrum n S ∩ longCycleRange n := by
      simpa [Set.mem_inter_iff] using h
    rw [longCycles_chordSpectrum n S hS hn h5] at h'
    obtain ⟨s', hs', heq⟩ := h'
    exact (map_sub_add_one_injective n heq).symm ▸ hs'
  · intro hs
    refine ⟨mem_longCycleRange_of_mem n S hs hn h5 hS, ?_⟩
    have h' : n - s + 1 ∈ (S.image fun t => n - t + 1 : Set ℕ) := ⟨s, hs, rfl⟩
    rw [← longCycles_chordSpectrum n S hS hn h5]
    exact h'

theorem chordSpectrum_injectiveOn (n : ℕ) (hn : Odd n) (h5 : 5 ≤ n) :
    Set.InjOn (fun S : Finset ℕ => chordSpectrum n S) ((chordOffsets n).powerset : Set (Finset ℕ)) := by
  intro S hS T hT hspec
  have hS' : S ⊆ chordOffsets n := Finset.mem_powerset.mp hS
  have hT' : T ⊆ chordOffsets n := Finset.mem_powerset.mp hT
  ext s
  have hrec := congrArg (recoverChordSet n) hspec
  rw [recoverChordSet_chordSpectrum n S hn h5 hS',
      recoverChordSet_chordSpectrum n T hn h5 hT'] at hrec
  exact hrec s

end ErdosProblem84
