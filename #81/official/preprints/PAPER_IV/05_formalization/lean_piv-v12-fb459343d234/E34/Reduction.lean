import E33.Assembly
import E34.CycleCount
import E34.SampleBound

/-!
# E34 — from a sampling removal lemma for chordality to an explicit `Nedit`

* `ChordalEasyRemovalWith mS N1` — the sampling form of a removal lemma for chordality with
  explicit sample size `mS ε` and explicit order threshold `N1 ε`: if `G` on `n ≥ N1 ε`
  vertices is `ε`-far from chordal, then at least half of the `mS ε`-subsets induce a
  non-chordal graph.
* `badSets_mul_le` — **L1 + union bound**: under rooted defect `≤ s`,
  `#badSets G m · n ≤ 4·s·m^(m+1)·C(n, m)` for `m ≤ n`.
* `NeditV mS N1 s δ = max (N1 δ) (max (mS δ) (8·s·(mS δ)^(mS δ + 1) + 1))`.
* `editApproxExplicit_of_easyRemoval` — `ChordalEasyRemovalWith mS N1` gives
  `E33.EditApproxExplicit (NeditV mS N1)`.
* `theoremC_of_easyRemoval`, `theoremC_uniform_of_easyRemoval` — Theorem C above
  `E33.Fexp (NeditV mS N1) s`.
-/

namespace E34

open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.FixedL4
  PaperIV.DefectTargetArithmetic

/-- **Sampling removal lemma for chordality** with explicit sample size `mS` and threshold
`N1` (the form of Theorem 1 of de Joannis de Verclos, arXiv:1902.06135, in which the
probability is written as a count of `m`-subsets). -/
def ChordalEasyRemovalWith (mS N1 : ℚ → ℕ) : Prop :=
  ∀ ε : ℚ, 0 < ε → ε ≤ 1 → ∀ n : ℕ, N1 ε ≤ n → ∀ G : SimpleGraph (Fin n),
    (∀ G' : SimpleGraph (Fin n), AlonShapira.IsChordal G' →
      ε * (n : ℚ) ^ 2 ≤ (AlonShapira.editDist G G' : ℚ)) →
      n.choose (mS ε) ≤ 2 * (badSets G (mS ε)).card

/-- **L1 + union bound.** Under rooted defect `≤ s`, for `m ≤ n`:
`#badSets G m · n ≤ 4·s·m^(m+1)·C(n, m)`. -/
theorem badSets_mul_le {n s : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : RootedDefectAt G s) {m : ℕ} (hmn : m ≤ n) :
    (badSets G m).card * n ≤ 4 * s * m ^ (m + 1) * n.choose m := by
  have hU := card_badSets_le G m
  have hk : ∀ k ∈ Icc 4 m,
      AlonShapira.indCopies (SimpleGraph.cycleGraph k) G * (n - k).choose (m - k) * n ≤
        2 * s * n.choose m * (k * m ^ k) := by
    intro k hk
    obtain ⟨hk4, hkm⟩ := mem_Icc.1 hk
    have hL1 := indCopies_cycle_le G hG hk4
    have hr := choose_ratio (n := n) hkm hmn
    have hpow : n ^ (k - 1) * n = n ^ k := by
      rw [← pow_succ]; congr 1; omega
    calc AlonShapira.indCopies (SimpleGraph.cycleGraph k) G * (n - k).choose (m - k) * n
        ≤ 2 * k * s * n ^ (k - 1) * (n - k).choose (m - k) * n :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hL1)
      _ = 2 * k * s * ((n - k).choose (m - k) * (n ^ (k - 1) * n)) := by ring
      _ = 2 * k * s * ((n - k).choose (m - k) * n ^ k) := by rw [hpow]
      _ ≤ 2 * k * s * (n.choose m * m ^ k) := Nat.mul_le_mul_left _ hr
      _ = 2 * s * n.choose m * (k * m ^ k) := by ring
  calc (badSets G m).card * n
      ≤ (∑ k ∈ Icc 4 m, AlonShapira.indCopies (SimpleGraph.cycleGraph k) G *
          (n - k).choose (m - k)) * n := Nat.mul_le_mul_right _ hU
    _ = ∑ k ∈ Icc 4 m, AlonShapira.indCopies (SimpleGraph.cycleGraph k) G *
          (n - k).choose (m - k) * n := by rw [sum_mul]
    _ ≤ ∑ k ∈ Icc 4 m, 2 * s * n.choose m * (k * m ^ k) := sum_le_sum hk
    _ = 2 * s * n.choose m * ∑ k ∈ Icc 4 m, k * m ^ k := by rw [mul_sum]
    _ ≤ 2 * s * n.choose m * (2 * m ^ (m + 1)) := Nat.mul_le_mul_left _ (sum_k_pow_le m)
    _ = 4 * s * m ^ (m + 1) * n.choose m := by ring

/-- Consequently, under rooted defect `≤ s`, fewer than half of the `m`-sets are bad as soon
as `n > 8·s·m^(m+1)` (and `m ≤ n`). -/
theorem badSets_lt_half {n s : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : RootedDefectAt G s) {m : ℕ} (hmn : m ≤ n) (hn : 8 * s * m ^ (m + 1) < n) :
    2 * (badSets G m).card < n.choose m := by
  by_contra hcon
  push_neg at hcon
  have h1 := badSets_mul_le G hG hmn
  have hpos : 0 < n.choose m := Nat.choose_pos hmn
  have : n.choose m * n ≤ 8 * s * m ^ (m + 1) * n.choose m := by
    calc n.choose m * n ≤ 2 * (badSets G m).card * n := Nat.mul_le_mul_right _ hcon
      _ = 2 * ((badSets G m).card * n) := by ring
      _ ≤ 2 * (4 * s * m ^ (m + 1) * n.choose m) := Nat.mul_le_mul_left _ h1
      _ = 8 * s * m ^ (m + 1) * n.choose m := by ring
  have : n ≤ 8 * s * m ^ (m + 1) := by
    rw [mul_comm (n.choose m)] at this
    exact Nat.le_of_mul_le_mul_right this hpos
  omega

/-- The explicit edit threshold obtained from a sampling removal lemma and L1. -/
def NeditV (mS N1 : ℚ → ℕ) (s : ℕ) (δ : ℚ) : ℕ :=
  max (N1 δ) (max (mS δ) (8 * s * mS δ ^ (mS δ + 1) + 1))

/-- The edgeless graph is chordal. -/
theorem bot_isChordal (n : ℕ) : (⊥ : SimpleGraph (Fin n)).IsChordal := by
  apply PaperIV.EditRoute.isChordal_of_noInducedCycle
  intro k hk
  refine ⟨fun e => ?_⟩
  have := e.map_adj_iff.2 (cyc_adj_succ hk ⟨0, by omega⟩)
  exact this

theorem ncard_eq_editDist {n : ℕ} (G G' : SimpleGraph (Fin n)) :
    (symmDiff G.edgeSet G'.edgeSet).ncard = AlonShapira.editDist G G' := by
  classical
  have hset : symmDiff G.edgeSet G'.edgeSet =
      ((symmDiff G.edgeFinset G'.edgeFinset : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))) := by
    rw [Finset.coe_symmDiff, SimpleGraph.coe_edgeFinset, SimpleGraph.coe_edgeFinset]
  rw [hset, Set.ncard_coe_finset, editDist_eq_card]

/-- **Reduction.** A sampling removal lemma for chordality with explicit parameters gives
`EditApproxExplicit` with the explicit threshold `NeditV mS N1`. -/
theorem editApproxExplicit_of_easyRemoval {mS N1 : ℚ → ℕ} (h : ChordalEasyRemovalWith mS N1) :
    E33.EditApproxExplicit (NeditV mS N1) := by
  classical
  intro s δ hδ n hn G inst hG
  have hn1 : N1 δ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : mS δ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : 8 * s * mS δ ^ (mS δ + 1) + 1 ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  rcases le_or_gt δ 1 with hδ1 | hδ1
  · by_contra hno
    push_neg at hno
    have hfar : ∀ G' : SimpleGraph (Fin n), AlonShapira.IsChordal G' →
        δ * (n : ℚ) ^ 2 ≤ (AlonShapira.editDist G G' : ℚ) := by
      intro G' hG'
      have hc : G'.IsChordal := PaperIV.EditRoute.isChordal_of_noInducedCycle G'
        (fun k hk => hG' k (SimpleGraph.cycleGraph k) ⟨hk, rfl⟩)
      have := hno G' hc
      rw [ncard_eq_editDist] at this
      exact this.le
    have hbad := h δ hδ hδ1 n hn1 G hfar
    have hlt := @badSets_lt_half n s G inst hG (mS δ) hn2 (by omega)
    omega
  · refine ⟨⊥, bot_isChordal n, ?_⟩
    have hE : (symmDiff G.edgeSet (⊥ : SimpleGraph (Fin n)).edgeSet).ncard ≤ n ^ 2 := by
      rw [ncard_eq_editDist, editDist_eq_card]
      refine (card_le_card (symmDiff_le_sup (a := G.edgeFinset)
        (b := (⊥ : SimpleGraph (Fin n)).edgeFinset))).trans ((card_union_le _ _).trans ?_)
      have h1 := SimpleGraph.card_edgeFinset_le_card_choose_two (G := G)
      have h2 := SimpleGraph.card_edgeFinset_le_card_choose_two (G := (⊥ : SimpleGraph (Fin n)))
      rw [Fintype.card_fin] at h1 h2
      have h3 : n.choose 2 * 2 ≤ n ^ 2 := by
        rw [Nat.choose_two_right]
        have := Nat.div_mul_le_self (n * (n - 1)) 2
        have : n * (n - 1) ≤ n ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        omega
      omega
    have : ((symmDiff G.edgeSet (⊥ : SimpleGraph (Fin n)).edgeSet).ncard : ℚ) ≤ (n : ℚ) ^ 2 := by
      exact_mod_cast hE
    have hn0 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := by positivity
    nlinarith

/-- **Theorem C, fully explicit relative to a sampling removal lemma.** -/
theorem theoremC_of_easyRemoval {mS N1 : ℚ → ℕ} (h : ChordalEasyRemovalWith mS N1) (s n : ℕ)
    (hn : E33.Fexp (NeditV mS N1) s ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdef : RootedDefectAt G s) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n :=
  E33.theoremC_explicit _ (editApproxExplicit_of_easyRemoval h) s n hn G hdef

/-- **Uniform Theorem C** relative to a sampling removal lemma. -/
theorem theoremC_uniform_of_easyRemoval {mS N1 : ℚ → ℕ} (h : ChordalEasyRemovalWith mS N1)
    (n : ℕ) (h0 : E33.Fmono (NeditV mS N1) 0 ≤ n) :
    ∀ s : ℕ, s ≤ E33.Finv (NeditV mS N1) n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      RootedDefectAt G s →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n :=
  E33.theoremC_uniform _ (editApproxExplicit_of_easyRemoval h) n h0

end E34
