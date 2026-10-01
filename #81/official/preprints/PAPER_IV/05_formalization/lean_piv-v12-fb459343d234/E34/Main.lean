import E34.Params
import E34.Reduction

/-!
# E34 — main results

* `Lemma11Explicit` — **the one remaining named input**: Lemma 11 of
  de Joannis de Verclos, arXiv:1902.06135 (pinned representations are testable), with the
  explicit sample size `m11V ε K = ⌈2^58 (K+1)^15 / ε^12⌉₊`.
* `chordalEasyRemoval_V` — Theorem 1 of the paper (subset form) with the explicit sample size
  `mVq ε` and threshold `N1 = mVq`, from `Lemma11Explicit`.
* `editApproxExplicit_V` — `E33.EditApproxExplicit NeditE` with the explicit closed form
  `NeditE s δ = max (mVq δ) (8·s·(mVq δ)^(mVq δ + 1) + 1)` (up to the harmless `max` with `N1`).
* `theoremC_fully_explicit`, `theoremC_fully_explicit_uniform` — Theorem C above
  `E33.Fexp NeditE s`.
-/

namespace E34

open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.FixedL4
  PaperIV.DefectTargetArithmetic

/-- **Lemma 11 of arXiv:1902.06135 with explicit sample size** `m11V`. -/
def Lemma11Explicit : Prop := Lemma11With m11V

/-- The explicit sample size, as a function of a rational `ε`. -/
noncomputable def mVq (ε : ℚ) : ℕ := mV (ε : ℝ)

theorem two_le_mV {ε : ℝ} (hε0 : 0 < ε) : 2 ≤ mV ε := by
  have hs : 1 ≤ sV ε := by
    unfold sV; rw [Nat.one_le_ceil_iff]; positivity
  have : 1 ≤ qV ε := Nat.one_le_pow _ _ hs
  unfold mV; omega

/-- **Theorem 1 of arXiv:1902.06135** (subset form, explicit parameters) from Lemma 11. -/
theorem chordalEasyRemoval_V (hL : Lemma11Explicit) : ChordalEasyRemovalWith mVq mVq := by
  intro ε hε0 hε1 n hn G hfar
  have hε0' : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε0
  have hε1' : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
  have h2 := two_le_mV hε0'
  have hfar' : ∀ F : SimpleGraph (Fin n), AlonShapira.IsChordal F →
      (ε : ℝ) * (n : ℝ) ^ 2 ≤ (AlonShapira.editDist G F : ℝ) := by
    intro F hF
    have := hfar F hF
    exact_mod_cast this
  exact thm1_of_lemma11 m11V hL ε hε0' hε1' (qV ε) (ellV (qV ε)) (MV ε (qV ε))
    (hM_V _ _) (hcodes_V _) (hq_V hε0' hε1') hn (by unfold mVq at hn; omega) G hfar'

/-- The explicit edit threshold. -/
noncomputable def NeditE : ℕ → ℚ → ℕ := NeditV mVq mVq

/-- **`E33.EditApproxExplicit` with an explicit closed-form threshold**, from Lemma 11. -/
theorem editApproxExplicit_V (hL : Lemma11Explicit) : E33.EditApproxExplicit NeditE :=
  editApproxExplicit_of_easyRemoval (chordalEasyRemoval_V hL)

/-- **Theorem C, fully explicit** (relative to the single named input `Lemma11Explicit`). -/
theorem theoremC_fully_explicit (hL : Lemma11Explicit) (s n : ℕ)
    (hn : E33.Fexp NeditE s ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdef : RootedDefectAt G s) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n :=
  theoremC_of_easyRemoval (chordalEasyRemoval_V hL) s n hn G hdef

/-- **Uniform Theorem C, fully explicit** (relative to `Lemma11Explicit`). -/
theorem theoremC_fully_explicit_uniform (hL : Lemma11Explicit) (n : ℕ)
    (h0 : E33.Fmono NeditE 0 ≤ n) :
    ∀ s : ℕ, s ≤ E33.Finv NeditE n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      RootedDefectAt G s →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n :=
  theoremC_uniform_of_easyRemoval (chordalEasyRemoval_V hL) n h0

end E34
