import Mathlib

/-!
# The round-robin pair family on `Option (ZMod (2n+1))`

This module is a self-contained, purely arithmetic description of the classical
round-robin (circle) one-factorization of the complete graph on `2n+2` vertices,
presented *without* any graph-theoretic packaging: the `2n+2` vertices are
`Option (ZMod (2n+1))`, the colours are `i : ZMod (2n+1)`, and the `n+1` pairs of
colour `i` are indexed by `t : Fin (n+1)`:

* `t = 0` gives the pair `{∞, i}` (with `∞ = none`);
* `t ≠ 0` gives the pair `{i + t, i - t}`.

The four literal facts proved here are exactly what a triangle factorization of a
complete split graph needs:

* `pair_card`          — every pair has two elements;
* `pair_disjoint`      — two pairs of the *same* colour are disjoint (a perfect matching);
* `card_inter_le_one`  — two pairs of *different* colours meet in at most one vertex;
* `exists_mem_pair`    — the pairs of a fixed colour cover all `2n+2` vertices.

Nothing is assumed; `n` is an arbitrary natural number.
-/

namespace PaperIV.RoundRobinPairs

open Finset

variable {n : ℕ}

/-- The colour/residue ring of the round-robin construction. -/
abbrev R (n : ℕ) : Type := ZMod (2 * n + 1)

/-- The first vertex of the `t`-th pair of colour `i`. -/
def fstV (i : R n) (t : Fin (n + 1)) : Option (R n) :=
  if (t : ℕ) = 0 then none else some (i + ((t : ℕ) : R n))

/-- The second vertex of the `t`-th pair of colour `i`. -/
def sndV (i : R n) (t : Fin (n + 1)) : Option (R n) :=
  if (t : ℕ) = 0 then some i else some (i - ((t : ℕ) : R n))

/-- The `t`-th pair of colour `i`, as a literal two-element set. -/
def pair (i : R n) (t : Fin (n + 1)) : Finset (Option (R n)) := {fstV i t, sndV i t}

@[simp] theorem fstV_zero (i : R n) {t : Fin (n + 1)} (ht : (t : ℕ) = 0) :
    fstV i t = none := by simp [fstV, ht]

@[simp] theorem sndV_zero (i : R n) {t : Fin (n + 1)} (ht : (t : ℕ) = 0) :
    sndV i t = some i := by simp [sndV, ht]

theorem fstV_pos (i : R n) {t : Fin (n + 1)} (ht : (t : ℕ) ≠ 0) :
    fstV i t = some (i + ((t : ℕ) : R n)) := by simp [fstV, ht]

theorem sndV_pos (i : R n) {t : Fin (n + 1)} (ht : (t : ℕ) ≠ 0) :
    sndV i t = some (i - ((t : ℕ) : R n)) := by simp [sndV, ht]

@[simp] theorem mem_pair {i : R n} {t : Fin (n + 1)} {x : Option (R n)} :
    x ∈ pair i t ↔ x = fstV i t ∨ x = sndV i t := by simp [pair]

/-! ## Small arithmetic facts in `ZMod (2n+1)` -/

/-- A natural number strictly between `0` and `2n+1` is nonzero in `ZMod (2n+1)`. -/
theorem natCast_ne_zero {a : ℕ} (h0 : a ≠ 0) (hlt : a < 2 * n + 1) :
    ((a : ℕ) : R n) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd
  omega

theorem fin_val_lt {t : Fin (n + 1)} : (t : ℕ) < 2 * n + 1 := by
  have := t.isLt; omega

/-- Two distinct indices in `Fin (n+1)` remain distinct in `ZMod (2n+1)`. -/
theorem natCast_fin_injective {t t' : Fin (n + 1)} (h : ((t : ℕ) : R n) = ((t' : ℕ) : R n)) :
    t = t' := by
  have ht := t.isLt
  have ht' := t'.isLt
  have h1 : ((t : ℕ) : R n).val = ((t' : ℕ) : R n).val := by rw [h]
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h1
  exact Fin.ext h1

/-! ## The four structural facts -/

theorem fstV_ne_sndV (i : R n) (t : Fin (n + 1)) : fstV i t ≠ sndV i t := by
  by_cases ht : (t : ℕ) = 0
  · simp [fstV_zero i ht, sndV_zero i ht]
  · rw [fstV_pos i ht, sndV_pos i ht]
    simp only [ne_eq, Option.some.injEq]
    intro hEq
    have h2 : ((2 * (t : ℕ) : ℕ) : R n) = 0 := by
      push_cast
      linear_combination hEq
    exact natCast_ne_zero (by omega) (by have := t.isLt; omega) h2

theorem pair_card (i : R n) (t : Fin (n + 1)) : (pair i t).card = 2 := by
  rw [pair, Finset.card_insert_of_notMem (by simpa using fstV_ne_sndV i t), Finset.card_singleton]

/-- Two pairs of the same colour are disjoint: the pairs of one colour form a perfect
matching of the `2n+2` vertices. -/
theorem pair_disjoint (i : R n) {t t' : Fin (n + 1)} (h : t ≠ t') :
    Disjoint (pair i t) (pair i t') := by
  have hsum : ∀ a b : Fin (n + 1), (a : ℕ) ≠ 0 → (b : ℕ) ≠ 0 →
      ((a : ℕ) : R n) + ((b : ℕ) : R n) ≠ 0 := by
    intro a b ha hb
    have hA := a.isLt
    have hB := b.isLt
    have : (((a : ℕ) + (b : ℕ) : ℕ) : R n) ≠ 0 := natCast_ne_zero (by omega) (by omega)
    push_cast at this
    exact this
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_pair] at hx hx'
  by_cases ht : (t : ℕ) = 0 <;> by_cases ht' : (t' : ℕ) = 0
  · exact h (Fin.ext (by omega))
  · rw [fstV_zero i ht, sndV_zero i ht] at hx
    rw [fstV_pos i ht', sndV_pos i ht'] at hx'
    rcases hx with rfl | rfl
    · rcases hx' with h1 | h1 <;> exact absurd h1 (by simp)
    · rcases hx' with h1 | h1 <;>
        · simp only [Option.some.injEq] at h1
          refine absurd ?_ (natCast_ne_zero (n := n) (a := (t' : ℕ)) ht' fin_val_lt)
          first
            | linear_combination -h1
            | linear_combination h1
  · rw [fstV_pos i ht, sndV_pos i ht] at hx
    rw [fstV_zero i ht', sndV_zero i ht'] at hx'
    rcases hx' with rfl | rfl
    · rcases hx with h1 | h1 <;> exact absurd h1 (by simp)
    · rcases hx with h1 | h1 <;>
        · simp only [Option.some.injEq] at h1
          refine absurd ?_ (natCast_ne_zero (n := n) (a := (t : ℕ)) ht fin_val_lt)
          first
            | linear_combination h1
            | linear_combination -h1
  · rw [fstV_pos i ht, sndV_pos i ht] at hx
    rw [fstV_pos i ht', sndV_pos i ht'] at hx'
    rcases hx with rfl | rfl <;> rcases hx' with h1 | h1 <;>
      simp only [Option.some.injEq] at h1
    · exact h (natCast_fin_injective (by linear_combination h1))
    · exact absurd (by linear_combination h1 : ((t : ℕ) : R n) + ((t' : ℕ) : R n) = 0)
        (hsum t t' ht ht')
    · exact absurd (by linear_combination -h1 : ((t : ℕ) : R n) + ((t' : ℕ) : R n) = 0)
        (hsum t t' ht ht')
    · exact h (natCast_fin_injective (by linear_combination -h1))

/-- `2` is cancellable in `ZMod (2n+1)`. -/
theorem two_cancel {x y : R n} (h : x + x = y + y) : x = y := by
  have hodd : Odd (2 * n + 1) := ⟨n, by ring⟩
  haveI : NeZero (2 * n + 1) := ⟨by omega⟩
  have h2 : IsUnit (2 : R n) := by
    have : IsUnit ((2 : ℕ) : ZMod (2 * n + 1)) :=
      (ZMod.isUnit_iff_coprime 2 (2 * n + 1)).mpr (Nat.coprime_two_left.mpr hodd)
    simpa using this
  have : (2 : R n) * x = 2 * y := by linear_combination h
  exact h2.mul_left_cancel this

/-- The colour of a pair is determined by any two of its vertices: two pairs of
*different* colours meet in at most one vertex. -/
theorem card_inter_le_one {i i' : R n} (hii : i ≠ i') (t t' : Fin (n + 1)) :
    ((pair i t) ∩ (pair i' t')).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  by_contra hxy
  rw [Finset.mem_inter, mem_pair, mem_pair] at hx hy
  -- the two shared vertices exhaust both pairs, so the pairs coincide as sets
  have hcolour : i = i' := by
    by_cases ht : (t : ℕ) = 0
    · -- the pair of colour `i` is `{∞, i}`; the other must then also contain `∞`
      rw [fstV_zero i ht, sndV_zero i ht] at hx hy
      by_cases ht' : (t' : ℕ) = 0
      · rw [fstV_zero i' ht', sndV_zero i' ht'] at hx hy
        rcases hx.1 with rfl | rfl
        · rcases hy.1 with rfl | rfl
          · exact absurd rfl hxy
          · rcases hy.2 with h1 | h1
            · exact absurd h1 (by simp)
            · simpa using h1
        · rcases hx.2 with h1 | h1
          · exact absurd h1 (by simp)
          · simpa using h1
      · rw [fstV_pos i' ht', sndV_pos i' ht'] at hx hy
        exfalso
        rcases hx.1 with rfl | rfl
        · rcases hx.2 with h1 | h1 <;> exact absurd h1 (by simp)
        · rcases hy.1 with rfl | rfl
          · rcases hy.2 with h1 | h1 <;> exact absurd h1 (by simp)
          · exact hxy rfl
    · by_cases ht' : (t' : ℕ) = 0
      · rw [fstV_pos i ht, sndV_pos i ht] at hx hy
        rw [fstV_zero i' ht', sndV_zero i' ht'] at hx hy
        exfalso
        rcases hx.2 with rfl | rfl
        · rcases hx.1 with h1 | h1 <;> exact absurd h1 (by simp)
        · rcases hy.2 with rfl | rfl
          · rcases hy.1 with h1 | h1 <;> exact absurd h1 (by simp)
          · exact hxy rfl
      · rw [fstV_pos i ht, sndV_pos i ht, fstV_pos i' ht', sndV_pos i' ht'] at hx hy
        -- both pairs are `{i ± t}` and `{i' ± t'}`; two common elements force `2i = 2i'`
        refine two_cancel ?_
        rcases hx.1 with rfl | rfl <;> rcases hy.1 with rfl | rfl <;>
            rcases hx.2 with h2 | h2 <;> rcases hy.2 with h3 | h3 <;>
          simp only [Option.some.injEq] at h2 h3 <;>
          first
            | exact absurd rfl hxy
            | linear_combination h2 + h3
            | exact absurd (congrArg some (h2.trans h3.symm)) hxy
  exact hii hcolour

/-- The `n+1` pairs of a fixed colour cover all `2n+2` vertices. -/
theorem exists_mem_pair (i : R n) (x : Option (R n)) : ∃ t : Fin (n + 1), x ∈ pair i t := by
  haveI : NeZero (2 * n + 1) := ⟨by omega⟩
  match x with
  | none =>
    refine ⟨⟨0, by omega⟩, ?_⟩
    rw [mem_pair]
    exact Or.inl (fstV_zero i rfl).symm
  | some u =>
    by_cases hu : u = i
    · refine ⟨⟨0, by omega⟩, ?_⟩
      rw [mem_pair]
      right
      rw [sndV_zero i rfl, hu]
    · set d : R n := u - i with hd
      have hdne : d ≠ 0 := sub_ne_zero_of_ne hu
      have hval : (d.val : R n) = d := ZMod.natCast_zmod_val d
      have hlt : d.val < 2 * n + 1 := ZMod.val_lt d
      have hpos : d.val ≠ 0 := by
        intro h0
        apply hdne
        rw [← hval, h0, Nat.cast_zero]
      by_cases hsmall : d.val ≤ n
      · refine ⟨⟨d.val, by omega⟩, ?_⟩
        rw [mem_pair]
        left
        rw [fstV_pos i (show ((⟨d.val, by omega⟩ : Fin (n + 1)) : ℕ) ≠ 0 from hpos)]
        simp only [Option.some.injEq]
        show u = i + ((d.val : ℕ) : R n)
        rw [hval, hd]
        ring
      · refine ⟨⟨2 * n + 1 - d.val, by omega⟩, ?_⟩
        rw [mem_pair]
        right
        rw [sndV_pos i (show ((⟨2 * n + 1 - d.val, by omega⟩ : Fin (n + 1)) : ℕ) ≠ 0 from by
          simp only []; omega)]
        simp only [Option.some.injEq]
        show u = i - (((2 * n + 1 - d.val : ℕ) : ℕ) : R n)
        have hsum : ((2 * n + 1 - d.val : ℕ) : R n) + (d.val : R n) = 0 := by
          have : ((2 * n + 1 - d.val : ℕ) : R n) + (d.val : R n)
              = (((2 * n + 1 - d.val) + d.val : ℕ) : R n) := by push_cast; ring
          rw [this]
          have harith : (2 * n + 1 - d.val) + d.val = 2 * n + 1 := by omega
          rw [harith]
          simp [ZMod.natCast_self]
        have : ((2 * n + 1 - d.val : ℕ) : R n) = -d := by
          rw [hval] at hsum
          linear_combination hsum
        rw [this, hd]
        ring

/-- The pairs of a fixed colour cover the whole vertex set. -/
theorem biUnion_pair (i : R n) :
    (Finset.univ : Finset (Fin (n + 1))).biUnion (pair i) = (Finset.univ : Finset (Option (R n))) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
  exact exists_mem_pair i x

end PaperIV.RoundRobinPairs
