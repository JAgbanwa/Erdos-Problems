/-
# The cover-down input, repaired.

`BKLO/CoverDownRefutation.lean` shows that the §10 input `CoverDownK3` of `BKLO/InputsVortex.lean`
is false as stated.  Both counterexamples exploit the same omission: the interface asks only that
the *whole* edge set `F` be triangle-divisible, and says nothing about the edge sets induced on the
vortex levels `W'` and `W''`.

* The parity counterexample (`BKLO.not_coverDownK3At_ge_three`) has a vertex `v₀ ∈ W''` of *odd*
  degree inside `W'` — impossible if `F ∩ cliqueEdges W'` is triangle-divisible.
* The counting counterexample (`BKLO.not_coverDownK3At_two`) needs `|W| = 2|W'|`, i.e. the ratio
  `K = 2`; it disappears as soon as the ratio supplied by the input satisfies `2/K < c`, which
  `K ≥ 3` already does.  (`K` is existentially quantified in the interface, so a prover of the
  repaired interface is free to choose `K ≥ 3`.)

The repaired interface below adds exactly the missing divisibility hypotheses on the two levels.
This is faithful to BKLO §10, where the vortex is chosen so that every level induces an
`F`-divisible graph; it is *this* fact that makes the cover-down's parity corrections possible.

`CoverDownK3Div` is a **definition of an interface, not a claim**: nothing here asserts that it
holds.  What is proved here is that it is not vacuous — `coverDownK3Div_hypotheses_realizable`
exhibits, for every ratio `K ≥ 2`, every density `c < 1` and arbitrarily large `|W|`, a
configuration satisfying *all* of its hypotheses, including the two new ones, and with
`F ∩ cliqueEdges W''` nonempty.  In particular the counterexamples of
`BKLO/CoverDownRefutationA.lean` and `BKLO/CoverDownRefutationB.lean` do not apply to it, and the
extra hypotheses have not made the interface unsatisfiable.

Everything here is `sorry`-free.
-/
import BKLO.CoverDownRefutation

open Finset

namespace BKLO

/-- **The repaired cover-down input.**  As `CoverDownK3`, but the edge sets induced on the two
lower levels `W'` and `W''` are required to be triangle-divisible as well.  This is the form in
which BKLO's §10 cover-down lemma is actually available: the vortex is chosen with divisible
levels. -/
def CoverDownK3Div : Prop :=
  ∀ c γ : ℝ, 9 / 10 < c → 0 < γ → ∃ K n₀ : ℕ, 2 ≤ K ∧
    ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
      n₀ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
      K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
      F ⊆ cliqueEdges W → TriDivisible F →
      TriDivisible (F ∩ cliqueEdges W') → TriDivisible (F ∩ cliqueEdges W'') →
      (∀ v ∈ W, c * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn F P ∧
        F \ famEdges P ⊆ cliqueEdges W' ∧
        F ∩ cliqueEdges W'' ⊆ F \ famEdges P ∧
        ∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
          ≤ (edeg (F \ famEdges P) v : ℝ) + γ * (W'.card : ℝ)

variable {V : Type*} [DecidableEq V]

/-- The complete edge set on a vertex set of size `≡ 3 (mod 6)` is triangle-divisible. -/
theorem triDivisible_cliqueEdges_of_card {W : Finset V} {t : ℕ} (h : W.card = 6 * t + 3) :
    TriDivisible (cliqueEdges W) := by
  classical
  constructor
  · intro v
    show Even (edeg (cliqueEdges W) v)
    by_cases hv : v ∈ W
    · rw [edeg_cliqueEdges_of_mem hv, h]
      exact ⟨3 * t + 1, by omega⟩
    · have : (cliqueEdges W).filter (fun e => v ∈ e) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun e he hve => hv ?_
        exact (mem_cliqueEdgesV.1 he).1 v hve
      show Even (edeg (cliqueEdges W) v)
      unfold edeg
      rw [this]
      exact ⟨0, rfl⟩
  · show 3 ∣ (cliqueEdges W).card
    rw [card_cliqueEdges, h]
    have h2 : 2 * ((6 * t + 3).choose 2) = (6 * t + 3) * ((6 * t + 3) - 1) :=
      two_mul_choose_two _
    have e1 : (6 * t + 3) * ((6 * t + 3) - 1) = 36 * t ^ 2 + 30 * t + 6 := by
      have hsub : (6 * t + 3) - 1 = 6 * t + 2 := by omega
      rw [hsub]; ring
    rw [e1] at h2
    omega

/-- **The hypotheses of the repaired input are satisfiable**, for every density `c < 1`, every
ratio `K ≥ 2` and every size threshold `n₀`, with `W''` and `F ∩ cliqueEdges W''` nonempty.  So the
two divisibility hypotheses added to `CoverDownK3` have not made the interface vacuous. -/
theorem coverDownK3Div_hypotheses_realizable {c : ℝ} (hc : c < 1) {K : ℕ} (hK : 2 ≤ K) (n₀ : ℕ) :
    ∃ (N : ℕ) (W W' W'' : Finset (Fin N)) (F : Finset (Sym2 (Fin N))),
      n₀ ≤ W.card ∧ W' ⊆ W ∧ W'' ⊆ W' ∧
      K * W'.card ≤ W.card ∧ W.card ≤ K * K * W'.card ∧ K * W''.card ≤ W'.card ∧
      F ⊆ cliqueEdges W ∧ TriDivisible F ∧
      TriDivisible (F ∩ cliqueEdges W') ∧ TriDivisible (F ∩ cliqueEdges W'') ∧
      (∀ v ∈ W, c * (W.card : ℝ) ≤ (edeg F v : ℝ)) ∧ (F ∩ cliqueEdges W'').Nonempty := by
  classical
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 - c))
  -- the middle level, of size `M ≡ 3 (mod 6)`, is chosen large
  set a : ℕ := n₀ + K + k + 3 with ha
  set M : ℕ := 6 * a + 3 with hM
  -- the top level is the first size `≡ 3 (mod 6)` above `K·M`
  set b : ℕ := (K * M) / 6 + 1 with hb
  set N : ℕ := 6 * b + 3 with hN
  have hM9 : 9 ≤ M := by omega
  have hMK : 3 * K ≤ M := by omega
  have hKM : K * M ≤ N := by
    have h6 : 6 * ((K * M) / 6) + 6 ≥ K * M := by omega
    omega
  have hNle : N ≤ K * M + 9 := by omega
  have hMN : M ≤ N := by
    have : M ≤ K * M := Nat.le_mul_of_pos_left M (by omega)
    omega
  have hKKM : N ≤ K * K * M := by
    have h1 : K * M + K * M ≤ K * (K * M) := by
      have : 2 * (K * M) ≤ K * (K * M) := Nat.mul_le_mul_right _ hK
      omega
    have h2 : 18 ≤ K * M := by
      have : 2 * M ≤ K * M := Nat.mul_le_mul_right _ hK
      omega
    have h3 : K * K * M = K * (K * M) := by ring
    omega
  have hn₀N : n₀ ≤ N := by
    have : M ≤ K * M := Nat.le_mul_of_pos_left M (by omega)
    omega
  have hkN : k ≤ N := by
    have : M ≤ K * M := Nat.le_mul_of_pos_left M (by omega)
    omega
  -- the three nested levels
  have hcardU : (univ : Finset (Fin N)).card = N := by simp
  obtain ⟨W', hW'sub, hW'card⟩ :=
    Finset.exists_subset_card_eq (s := (univ : Finset (Fin N))) (n := M)
      (by rw [hcardU]; exact hMN)
  obtain ⟨W'', hW''sub, hW''card⟩ :=
    Finset.exists_subset_card_eq (s := W') (n := 3) (by rw [hW'card]; omega)
  refine ⟨N, univ, W', W'', cliqueEdges (univ : Finset (Fin N)), ?_, Finset.subset_univ _,
    hW''sub, ?_, ?_, ?_, Finset.Subset.refl _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcardU]; exact hn₀N
  · rw [hcardU, hW'card]; exact hKM
  · rw [hcardU, hW'card]; exact hKKM
  · rw [hW'card, hW''card]; omega
  · exact triDivisible_cliqueEdges_of_card (t := b) (by rw [hcardU])
  · rw [Finset.inter_eq_right.2 (cliqueEdges_mono (Finset.subset_univ _))]
    exact triDivisible_cliqueEdges_of_card (t := a) hW'card
  · rw [Finset.inter_eq_right.2 (cliqueEdges_mono (Finset.subset_univ _))]
    exact triDivisible_cliqueEdges_of_card (t := 0) (by rw [hW''card])
  · intro v _
    rw [edeg_cliqueEdges_of_mem (Finset.mem_univ v), hcardU]
    have h1 : (0 : ℝ) < 1 - c := by linarith only [hc]
    have hNr : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
    have h2 : (1 : ℝ) ≤ (1 - c) * (N : ℝ) := by
      have h3 : 1 / (1 - c) ≤ (N : ℝ) := le_trans hk.le hNr
      rw [div_le_iff₀ h1] at h3
      linarith only [h3]
    have h4 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      have h5 : 1 ≤ N := by omega
      push_cast [Nat.cast_sub h5]
      ring
    rw [h4]
    linarith only [h2]
  · rw [Finset.inter_eq_right.2 (cliqueEdges_mono (Finset.subset_univ _))]
    exact cliqueEdges_nonempty (by omega)

end BKLO
