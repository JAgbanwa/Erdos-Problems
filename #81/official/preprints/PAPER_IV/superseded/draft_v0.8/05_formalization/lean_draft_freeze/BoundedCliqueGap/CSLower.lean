import BoundedCliqueGap.CSPortFull

/-
`BoundedCliqueGap.CSLower` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# The port-poor lower bound for complete split graphs

`cs_gap_linear_full` (rung G1) is an *upper* bound on the LP value of
`CS(k,s)`.  The flower rung needs the matching *lower* bound on `ν₃`: in the
port-poor regime `s ≤ k` the complete split graph has an edge-disjoint
triangle family using all but `O(k)` of its edges,

  `(C(k,2) + k·s)/3 − 10k ≤ ν₃(CS(Fin k, Fin s))`.

This is the Bose-plus-Vizing construction of `nu3_CS_bose_fin` with the
order rounded to the nearest `3n` (`n` odd) and the port count to the nearest
`6δ`; the hypothesis `s ≤ k` is what keeps the discarded ports down to a
bounded number, so that the loss stays linear in `k`.
-/

namespace BoundedCliqueGap

open Finset

/-- **Port-poor lower bound.**  For `s ≤ k`, the complete split graph
`CS(k,s)` has an edge-disjoint triangle family of size at least
`(C(k,2) + k·s)/3 − 10k`. -/
theorem nu3_CS_portPoor_ge (k s : ℕ) (hs : s ≤ k) :
    ((k : ℚ) * ((k : ℚ) - 1) / 2 + (k : ℚ) * (s : ℚ)) / 3 - 10 * (k : ℚ)
      ≤ (nu3 (CS (Fin k) (Fin s)) : ℚ) := by
  have hnu0 : (0 : ℚ) ≤ (nu3 (CS (Fin k) (Fin s)) : ℚ) := by positivity
  have hkQ : (0 : ℚ) ≤ (k : ℚ) := by positivity
  have hsQ : (0 : ℚ) ≤ (s : ℚ) := by positivity
  have hskQ : (s : ℚ) ≤ (k : ℚ) := by exact_mod_cast hs
  rcases Nat.lt_or_ge k 3 with hksmall | hk3
  · -- at most two clique vertices: the claimed bound is already `≤ 0`
    have hk2 : (k : ℚ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.1 hksmall
    nlinarith
  · -- round the clique size down to `3n` (`n` odd) and the port count down to `6δ`
    obtain ⟨n, hnodd, hn1, hn2⟩ : ∃ n, Odd n ∧ 3 * n ≤ k ∧ k ≤ 3 * n + 5 := by
      rcases Nat.even_or_odd (k / 3) with he | ho
      · rw [Nat.even_iff] at he
        exact ⟨k / 3 - 1, by rw [Nat.odd_iff]; omega, by omega, by omega⟩
      · rw [Nat.odd_iff] at ho
        exact ⟨k / 3, by rw [Nat.odd_iff]; omega, by omega, by omega⟩
    obtain ⟨d, hd1, hd2, hd3⟩ : ∃ d, 2 * d ≤ n - 1 ∧ 6 * d ≤ s ∧ s ≤ 6 * d + 11 :=
      ⟨min (s / 6) ((n - 1) / 2), by omega, by omega, by omega⟩
    have hcore := nu3_CS_bose_fin n d hnodd hd1
    have hmono : nu3 (CS (Fin (3 * n)) (Fin (6 * d))) ≤ nu3 (CS (Fin k) (Fin s)) :=
      nu3_CS_fin_mono (by omega) (by omega)
    have hcoreQ : (3 : ℚ) * n * n + 12 * n * d
        ≤ 2 * (nu3 (CS (Fin (3 * n)) (Fin (6 * d))) : ℚ) + 4 * n := by exact_mod_cast hcore
    have hmonoQ : (nu3 (CS (Fin (3 * n)) (Fin (6 * d))) : ℚ)
        ≤ (nu3 (CS (Fin k) (Fin s)) : ℚ) := by exact_mod_cast hmono
    have h3n : (3 : ℚ) * n ≤ (k : ℚ) := by exact_mod_cast hn1
    have h3n' : (k : ℚ) ≤ 3 * n + 5 := by exact_mod_cast hn2
    have h6d : (6 : ℚ) * d ≤ (s : ℚ) := by exact_mod_cast hd2
    have h6d' : (s : ℚ) ≤ 6 * d + 11 := by exact_mod_cast hd3
    have hn0 : (0 : ℚ) ≤ (n : ℚ) := by positivity
    have hd0 : (0 : ℚ) ≤ (d : ℚ) := by positivity
    -- the two nonlinear estimates
    have h1 : (k : ℚ) * k - 9 * n * n ≤ 30 * n + 25 := by nlinarith
    have h2 : 2 * (k : ℚ) * s - 36 * n * d ≤ 60 * d + 22 * k := by nlinarith
    have h3 : (60 : ℚ) * d ≤ 10 * k := by linarith
    have hk3Q : (3 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk3
    linarith

/-! ## Axiom audit -/

end BoundedCliqueGap
