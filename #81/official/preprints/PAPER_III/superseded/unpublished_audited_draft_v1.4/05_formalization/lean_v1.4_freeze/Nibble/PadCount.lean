/-
# Nibble — block counting for the padding construction

Elementary counting lemmas for maps of the shape `t ↦ (t % M + c (t / M)) % M`, i.e. maps that
restrict to a *bijection* on every block `[qM, (q+1)M)`.  These are the combinatorial engine behind
the explicit degree-balanced padding hypergraph of `Nibble.PaddedTriangle`.

* `Nibble.blockFun`, `Nibble.blockCount`, `Nibble.intervalCount` — the map and its counting
  functions.
* `Nibble.blockCount_mul` — a whole number of blocks is counted exactly: `count (q*M) = q`.
* `Nibble.blockCount_ge`, `Nibble.blockCount_le` — hence `Y/M ≤ count Y ≤ Y/M + 1`.
* `Nibble.intervalCount_shift` — counting over `[a, a+L)` is counting the shifted range.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.ModEq

open Finset

namespace Nibble

/-- The block map: on the block `[qM, (q+1)M)` it is `s ↦ (s + c q) % M`, a bijection. -/
def blockFun (M : ℕ) (c : ℕ → ℕ) (t : ℕ) : ℕ := (t % M + c (t / M)) % M

/-- The number of `t ∈ [a, b)` with `blockFun M c t = x`. -/
def intervalCount (M : ℕ) (c : ℕ → ℕ) (x a b : ℕ) : ℕ :=
  ((Finset.Ico a b).filter (fun t => blockFun M c t = x)).card

/-- The number of `t < Y` with `blockFun M c t = x`. -/
def blockCount (M : ℕ) (c : ℕ → ℕ) (x Y : ℕ) : ℕ := intervalCount M c x 0 Y

theorem blockCount_eq_filter_range (M : ℕ) (c : ℕ → ℕ) (x Y : ℕ) :
    blockCount M c x Y = ((Finset.range Y).filter (fun t => blockFun M c t = x)).card := by
  rw [blockCount, intervalCount, Finset.range_eq_Ico]

/-- Additivity of the interval count. -/
theorem intervalCount_add (M : ℕ) (c : ℕ → ℕ) (x : ℕ) {a b e : ℕ} (hab : a ≤ b) (hbe : b ≤ e) :
    intervalCount M c x a b + intervalCount M c x b e = intervalCount M c x a e := by
  classical
  rw [intervalCount, intervalCount, intervalCount, ← Finset.card_union_of_disjoint,
    ← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico hab hbe]
  exact Finset.disjoint_filter_filter
    (Finset.Ico_disjoint_Ico_consecutive a b e)

/-- Counting on one block: exactly one `t` in `[qM, (q+1)M)` has `blockFun M c t = x`. -/
theorem intervalCount_block (M : ℕ) (c : ℕ → ℕ) {x : ℕ} (hx : x < M) (q : ℕ) :
    intervalCount M c x (q * M) (q * M + M) = 1 := by
  classical
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le x) hx
  set cq := c q with hcq
  set s₀ := (x + (M - cq % M)) % M with hs₀
  have hs₀lt : s₀ < M := Nat.mod_lt _ hM
  have hs₀eq : (s₀ + cq) % M = x := by
    have h1 : cq % M < M := Nat.mod_lt _ hM
    have h2 : M * (cq / M) + cq % M = cq := Nat.div_add_mod cq M
    have h4 : M * (1 + cq / M) = M + M * (cq / M) := by ring
    have harith : x + (M - cq % M) + cq = x + M * (1 + cq / M) := by omega
    calc (s₀ + cq) % M = (x + (M - cq % M) + cq) % M := by rw [hs₀, Nat.mod_add_mod]
      _ = (x + M * (1 + cq / M)) % M := by rw [harith]
      _ = x % M := by rw [Nat.add_mul_mod_self_left]
      _ = x := Nat.mod_eq_of_lt hx
  have hcancel : ∀ s s' : ℕ, s < M → s' < M → (s + cq) % M = (s' + cq) % M → s = s' := by
    intro s s' hs hs' h
    have hmod : s % M = s' % M := by
      have : (s + cq) ≡ (s' + cq) [MOD M] := h
      exact (Nat.ModEq.add_right_cancel' cq this)
    rw [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hs'] at hmod
    exact hmod
  have hkey : ∀ s, s < M → (blockFun M c (q * M + s) = x ↔ s = s₀) := by
    intro s hs
    have hmod : (q * M + s) % M = s := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hs]
    have hdiv : (q * M + s) / M = q := by
      rw [Nat.mul_comm, Nat.mul_add_div hM, Nat.div_eq_of_lt hs, Nat.add_zero]
    rw [blockFun, hmod, hdiv, ← hcq]
    constructor
    · intro h
      exact hcancel s s₀ hs hs₀lt (by rw [h, hs₀eq])
    · rintro rfl
      exact hs₀eq
  have : (Finset.Ico (q * M) (q * M + M)).filter (fun t => blockFun M c t = x)
      = {q * M + s₀} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      obtain ⟨s, hs, rfl⟩ : ∃ s, s < M ∧ t = q * M + s := ⟨t - q * M, by omega, by omega⟩
      rw [(hkey s hs).mp h3]
    · rintro rfl
      exact ⟨⟨by omega, by omega⟩, (hkey s₀ hs₀lt).mpr rfl⟩
  rw [intervalCount, this, Finset.card_singleton]

/-- A whole number of blocks is counted exactly. -/
theorem blockCount_mul (M : ℕ) (c : ℕ → ℕ) {x : ℕ} (hx : x < M) (q : ℕ) :
    blockCount M c x (q * M) = q := by
  induction q with
  | zero => simp [blockCount, intervalCount]
  | succ q ih =>
    have h1 : blockCount M c x (q * M) + intervalCount M c x (q * M) (q * M + M)
        = blockCount M c x (q * M + M) :=
      intervalCount_add M c x (Nat.zero_le _) (Nat.le_add_right _ _)
    rw [intervalCount_block M c hx q, ih] at h1
    have : (q + 1) * M = q * M + M := by ring
    rw [this, ← h1]

theorem blockCount_mono (M : ℕ) (c : ℕ → ℕ) (x : ℕ) {Y Y' : ℕ} (h : Y ≤ Y') :
    blockCount M c x Y ≤ blockCount M c x Y' := by
  classical
  rw [blockCount_eq_filter_range, blockCount_eq_filter_range]
  exact Finset.card_le_card (Finset.filter_subset_filter _
    (fun t ht => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp ht) h)))

theorem blockCount_ge (M : ℕ) (c : ℕ → ℕ) {x : ℕ} (hx : x < M) (Y : ℕ) :
    Y / M ≤ blockCount M c x Y := by
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le x) hx
  have h1 : Y / M * M ≤ Y := Nat.div_mul_le_self Y M
  calc Y / M = blockCount M c x (Y / M * M) := (blockCount_mul M c hx _).symm
    _ ≤ blockCount M c x Y := blockCount_mono M c x h1

theorem blockCount_le (M : ℕ) (c : ℕ → ℕ) {x : ℕ} (hx : x < M) (Y : ℕ) :
    blockCount M c x Y ≤ Y / M + 1 := by
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le x) hx
  have h1 : Y ≤ (Y / M + 1) * M := by
    have h2 := Nat.div_add_mod Y M
    have h3 := Nat.mod_lt Y hM
    nlinarith only [h2, h3]
  calc blockCount M c x Y ≤ blockCount M c x ((Y / M + 1) * M) := blockCount_mono M c x h1
    _ = Y / M + 1 := blockCount_mul M c hx _

/-- Counting over a shifted range. -/
theorem intervalCount_shift (M : ℕ) (c : ℕ → ℕ) (x a L : ℕ) :
    ((Finset.range L).filter (fun k => blockFun M c (a + k) = x)).card
      = intervalCount M c x a (a + L) := by
  classical
  rw [intervalCount]
  refine Finset.card_bij' (fun k _ => a + k) (fun t _ => t - a) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨Nat.le_add_right _ _, by omega⟩, hk.2⟩
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_Ico] at ht
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [show a + (t - a) = t by omega]
    exact ht.2
  · intro k _
    show a + k - a = k
    omega
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_Ico] at ht
    show a + (t - a) = t
    omega

end Nibble
