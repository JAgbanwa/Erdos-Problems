/-
  Paper II — arithmetic corollaries of the extremal value `⌊(2n+1)²/24⌋`.

  These strengthen the paper's Corollary 1.2 (asymptotics) and Proposition 7.1 (residue closed
  form) into named, axiom-clean theorems, and record the series-coherence bound against Paper I.
  All are pure integer arithmetic on the value `(2*n+1)^2 / 24` produced by `theorem_1_2`; they add
  no hypotheses to and do not modify the frozen main development.
-/
import Mathlib.Tactic

namespace PaperII

/-- **#1 — explicit asymptotic (Corollary 1.2, sharpened, cleared of denominators).**
The extremal value `⌊(2n+1)²/24⌋` satisfies `4n²+4n−23 < 24·⌊(2n+1)²/24⌋ ≤ 4n²+4n+1`. Dividing by
`24`, the chordal maximum equals `n²/6 + n/6 + O(1)`; in particular it is `n²/6 + O(n)`. -/
theorem phiTau_max_sandwich (n : ℤ) :
    4 * n ^ 2 + 4 * n - 23 < 24 * ((2 * n + 1) ^ 2 / 24) ∧
      24 * ((2 * n + 1) ^ 2 / 24) ≤ 4 * n ^ 2 + 4 * n + 1 := by
  have hsq : (2 * n + 1) ^ 2 = 4 * n ^ 2 + 4 * n + 1 := by ring
  omega

/-- **#3 — series coherence with Paper I.** For `n ≥ 1`, the exact chordal maximum stays below
Paper I's split-graph upper bound `n²/6 + n/2` (here ×24-cleared as `≤ 4n²+12n`): since split
graphs are chordal, the exact chordal value refines — and lies strictly under — Paper I's bound. -/
theorem phiTau_max_le_paperI_bound (n : ℤ) (hn : 1 ≤ n) :
    24 * ((2 * n + 1) ^ 2 / 24) ≤ 4 * n ^ 2 + 12 * n := by
  have hsq : (2 * n + 1) ^ 2 = 4 * n ^ 2 + 4 * n + 1 := by ring
  omega

/-- `(2n+1)² ≡ 1 (mod 24)`, or `≡ 9` when `3 ∣ (2n+1)`. (Odd squares are `1 mod 24`, except
multiples of `3`, which are `9 mod 24`.) -/
theorem odd_sq_emod_24 (n : ℤ) :
    (2 * n + 1) ^ 2 % 24 = if (3 : ℤ) ∣ (2 * n + 1) then 9 else 1 := by
  obtain ⟨k, r, hr0, hr6, hn⟩ : ∃ k r, 0 ≤ r ∧ r < 6 ∧ n = 6 * k + r :=
    ⟨n / 6, n % 6, Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num), by omega⟩
  subst hn
  have hsq : (2 * (6 * k + r) + 1) ^ 2 = 144 * k ^ 2 + (48 * r + 24) * k + (2 * r + 1) ^ 2 := by
    ring
  rw [hsq]
  interval_cases r <;> split <;> omega

/-- **#2 — exact closed form by residue (Proposition 7.1, standalone).** The extremal value has no
genuine floor: `⌊(2n+1)²/24⌋` is exactly `((2n+1)²−9)/24` when `3 ∣ (2n+1)`, and `((2n+1)²−1)/24`
otherwise, both exact integer divisions. -/
theorem phiTau_max_closed (n : ℤ) :
    (2 * n + 1) ^ 2 / 24 =
      if (3 : ℤ) ∣ (2 * n + 1) then ((2 * n + 1) ^ 2 - 9) / 24 else ((2 * n + 1) ^ 2 - 1) / 24 := by
  have hmod := odd_sq_emod_24 n
  have hdivmod : (2 * n + 1) ^ 2 = 24 * ((2 * n + 1) ^ 2 / 24) + (2 * n + 1) ^ 2 % 24 :=
    (Int.mul_ediv_add_emod _ _).symm
  by_cases h3 : (3 : ℤ) ∣ (2 * n + 1)
  · rw [if_pos h3]; rw [if_pos h3] at hmod; omega
  · rw [if_neg h3]; rw [if_neg h3] at hmod; omega

end PaperII
