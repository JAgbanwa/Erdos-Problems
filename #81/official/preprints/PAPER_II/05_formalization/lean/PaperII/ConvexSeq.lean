import Mathlib

/-!
# Paper II — Discrete convexity core of L2 (Lemma 4.1)

Analytic heart of the clone-class convexity lemma: a real sequence with midpoint convexity on
`{0,…,N}` (`2·f(k+1) ≤ f k + f(k+2)`) attains its maximum over `{0,…,N}` at an endpoint. The graph
family `H_k` of L2 plugs `f k = Φ_τ(H_k)` into this, with midpoint convexity supplied by L1.
-/

open Finset

namespace PaperII

/-- A real sequence whose first differences are nondecreasing (midpoint convexity) is bounded by the
max of its endpoint values over `{0,…,N}`. -/
theorem convexSeq_le_max_endpoints (N : ℕ) (f : ℕ → ℝ)
    (hconv : ∀ k, k + 2 ≤ N → 2 * f (k + 1) ≤ f k + f (k + 2)) :
    ∀ j, j ≤ N → f j ≤ max (f 0) (f N) := by
  set d : ℕ → ℝ := fun i => f (i + 1) - f i with hd
  -- differences are nondecreasing on `[0, N-1]`
  have hstep : ∀ k, k + 2 ≤ N → d k ≤ d (k + 1) := by
    intro k hk; have := hconv k hk; simp only [hd]; linarith
  have hmono : ∀ i j, i ≤ j → j + 1 ≤ N → d i ≤ d j := by
    intro i j
    induction j with
    | zero => intro hij _; interval_cases i; exact le_refl _
    | succ n ih =>
      intro hij hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hij) with h | h
      · exact le_trans (ih (Nat.lt_succ_iff.mp h) (by omega)) (hstep n (by omega))
      · subst h; exact le_refl _
  -- telescoping identity
  have htele : ∀ m : ℕ, ∑ i ∈ range m, d i = f m - f 0 := by
    intro m; simpa [hd] using Finset.sum_range_sub f m
  intro j hj
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0; exact le_max_left _ _
  rcases eq_or_lt_of_le hj with hjN | hjN
  · subst hjN; exact le_max_right _ _
  -- interior `0 < j < N`: bound the two blocks of differences by `d (j-1)`
  have hj1 : j - 1 + 1 = j := by omega
  have hbelow : f j - f 0 ≤ (j : ℝ) * d (j - 1) := by
    rw [← htele j]
    calc ∑ i ∈ range j, d i ≤ ∑ _i ∈ range j, d (j - 1) :=
          Finset.sum_le_sum fun i hi => hmono i (j - 1) (by simp at hi; omega) (by omega)
      _ = (j : ℝ) * d (j - 1) := by rw [Finset.sum_const, card_range]; ring
  have habove : ((N - j : ℕ) : ℝ) * d (j - 1) ≤ f N - f j := by
    have hsplit : ∑ i ∈ range N, d i = (∑ i ∈ range j, d i) + ∑ i ∈ Ico j N, d i := by
      rw [← Finset.sum_range_add_sum_Ico d hj]
    have : ∑ i ∈ Ico j N, d i = f N - f j := by
      have h1 := htele N; have h2 := htele j; rw [hsplit] at h1; linarith
    rw [← this]
    calc ((N - j : ℕ) : ℝ) * d (j - 1)
        = ∑ _i ∈ Ico j N, d (j - 1) := by
          rw [Finset.sum_const, Nat.card_Ico]; ring
      _ ≤ ∑ i ∈ Ico j N, d i :=
          Finset.sum_le_sum fun i hi => by
            rw [Finset.mem_Ico] at hi
            exact hmono (j - 1) i (by omega) (by omega)
  -- combine: `N * f j ≤ (N-j) f 0 + j f N`, a convex combination ≤ max
  have hjN' : (j : ℝ) ≤ N := by exact_mod_cast hj
  have hNj : ((N - j : ℕ) : ℝ) = (N : ℝ) - j := by
    have : j ≤ N := hj; push_cast [Nat.cast_sub this]; ring
  have hkey : (N : ℝ) * f j ≤ ((N : ℝ) - j) * f 0 + (j : ℝ) * f N := by
    rw [hNj] at habove
    nlinarith [hbelow, habove]
  -- convex combination bound
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  rcases le_total (f 0) (f N) with hle | hle
  · have : (N : ℝ) * f j ≤ (N : ℝ) * f N := by
      have : ((N : ℝ) - j) * f 0 + (j : ℝ) * f N ≤ (N : ℝ) * f N := by nlinarith [hjN']
      linarith [hkey]
    have := le_of_mul_le_mul_left this hNpos
    exact le_trans this (le_max_right _ _)
  · have : (N : ℝ) * f j ≤ (N : ℝ) * f 0 := by
      have : ((N : ℝ) - j) * f 0 + (j : ℝ) * f N ≤ (N : ℝ) * f 0 := by nlinarith [hjpos]
      linarith [hkey]
    have := le_of_mu