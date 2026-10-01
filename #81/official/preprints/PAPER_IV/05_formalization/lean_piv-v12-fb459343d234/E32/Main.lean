import E32.Consequences
import E32.FarMargin
import PaperIV.IntegralStability
import PaperIV.RootedDefectZeroChordal

/-!
# E32 — Theorem C′: quantitative stability and classification at every fixed rooted defect

## What is proved unconditionally

* `theoremC_at` — Theorem C (`A4S1.IndepAll.a4Sharp_all_indep`) in the threshold form used here.
* `minDegEditStable_of_retained` — steps 1 (far exclusion with margin, all graphs) and the
  localization of the near branch: the remaining step only has to treat graphs that are
  *simultaneously* of minimum degree `≥ (1/3 − ε) n`, in the near branch, and localized.
* `theoremCPrime_of_retained` — **Theorem C′ (a)–(c) for every `s`, from the one named
  proposition `RetainedTerminalAt s ε γ K N`**, with the explicit constants
  `C_s = max K (2/ε)` in (a) and `C'_s = 1 + 7·C_s` in (b).
* `theoremCPrime_zero` — **Theorem C′ for `s = 0`, unconditionally**, with `C_0 = 16`,
  `C'_0 = 113`, from Paper IV's chordal Theorem 6.1 (`RootedDefectAt G 0 ↔ chordal`).

## The remaining step

`RetainedTerminalAt s ε γ K N` (below) is the retained-account form of the minimum-degree
terminal: the linear edit bound for graphs that satisfy all the terminal hypotheses of
`A4S1.MinDegreeAll.MinDegTerminal s ε` (minimum degree, near branch, localized clique). It is the
analogue of the retained account (5.15a) for the E14-H constructor of Appendix E.1; the existing
constructor proves only `|Q| ≤ Q_s(n)` and discards the slack. `RetainedTerminalStability s`
packages its constants existentially; all constants are explicit functions of them.
-/

namespace E32

open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.DefectComparatorGraph
  PaperIV.DefectTargetArithmetic PaperIV.ExtremalClassification

/-- **The remaining step (retained account at the minimum-degree terminal).** For `n ≥ N`,
every graph of rooted defect `s` that has minimum degree `≥ (1/3 − ε) n`, lies in the near
branch `F₄(G) ≥ n²/6 − ε n²`, carries a localized clique at precision `ε`, and satisfies
`c₄(G) ≥ Q_s(n) − δ` with `0 ≤ δ ≤ γ n²`, has a root `(C, D, H)` with edit distance at most
`K·δ` to `E_s = defSplitGraph C D H`. -/
def RetainedTerminalAt (s : ℕ) (ε γ K : ℚ) (N : ℕ) : Prop :=
  ∀ n, N ≤ n → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj], RootedDefectAt G s →
    (∀ v, ((1 : ℚ) / 3 - ε) * n ≤ (G.degree v : ℚ)) →
    (n : ℝ) ^ 2 / 6 - (ε : ℝ) * (n : ℝ) ^ 2 ≤ PaperIV.VertexCopyGate.F4' G →
    Nonempty (PaperIV.FixedL4.LocalizedClique G ε) →
    ∀ δ : ℚ, 0 ≤ δ → δ ≤ γ * (n : ℚ) ^ 2 →
    (∀ Q : CliquePartition G, Q.OrderAtMost 4 → (defectTarget s n : ℚ) - δ ≤ Q.size) →
      ∃ C D H : Finset (Fin n), IsDefectRoot G s C D H ∧ (rootEdit G C D H : ℚ) ≤ K * δ

/-- The remaining step with its constants quantified. -/
def RetainedTerminalStability (s : ℕ) : Prop :=
  ∃ ε γ K : ℚ, ∃ N : ℕ, 0 < ε ∧ 0 < γ ∧ 0 ≤ K ∧ RetainedTerminalAt s ε γ K N

/-- Theorem C in threshold form. -/
theorem theoremC_at (s : ℕ) : ∃ NC, TheoremCAt s NC := by
  obtain ⟨N, hN⟩ := PaperIV.DefectSharpPublication.rooted_defect_eventual s
  exact ⟨N, fun n hn G _ hG => hN n hn G hG⟩

/-- **Steps 1 and localization.** The remaining step implies edit stability for all graphs of
minimum degree `≥ (1/3 − ε) n`: the far branch is excluded by the margin
(`near_of_small_deficit`) and the near branch is localized
(`PaperIV.EditRoute.fixedL4Localization_unconditional`). -/
theorem minDegEditStable_of_retained {s : ℕ} {ε γ K : ℚ} {N : ℕ} (hε : 0 < ε) (hγ : 0 < γ)
    (h : RetainedTerminalAt s ε γ K N) :
    ∃ γ₁ : ℚ, 0 < γ₁ ∧ ∃ N₁ : ℕ, MinDegEditStable s ε γ₁ K N₁ := by
  classical
  obtain ⟨eta, heta, NL, hNL⟩ := PaperIV.EditRoute.fixedL4Localization_unconditional s ε hε
  set η' : ℚ := min eta ε with hη'
  have hη'pos : 0 < η' := lt_min heta hε
  have h1 : η' ≤ eta := min_le_left _ _
  have h2 : η' ≤ ε := min_le_right _ _
  obtain ⟨Nf, hNf⟩ := near_of_small_deficit s η' hη'pos
  refine ⟨min γ (η' / 4), lt_min hγ (by positivity), N + NL + Nf, ?_⟩
  intro n hn G _ hdef hdeg δ hδ0 hδ hlow
  have hsq : (0 : ℚ) ≤ (n : ℚ) ^ 2 := by positivity
  have hδγ : δ ≤ γ * (n : ℚ) ^ 2 :=
    le_trans hδ (mul_le_mul_of_nonneg_right (min_le_left _ _) hsq)
  have hδη : δ ≤ η' / 4 * (n : ℚ) ^ 2 :=
    le_trans hδ (mul_le_mul_of_nonneg_right (min_le_right _ _) hsq)
  have hnear := hNf n (by omega) G δ hδη (fun Q hQ => hlow Q hQ)
  have hsqR : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have h1R : (η' : ℝ) ≤ (eta : ℝ) := by exact_mod_cast h1
  have h2R : (η' : ℝ) ≤ (ε : ℝ) := by exact_mod_cast h2
  have hnearε : (n : ℝ) ^ 2 / 6 - (ε : ℝ) * (n : ℝ) ^ 2 ≤ PaperIV.VertexCopyGate.F4' G := by
    nlinarith
  obtain ⟨w, hw⟩ := PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum G
  have hF := PaperIV.CertifiedF4Bridge.F4'_eq_edge_sub_certified hw
  have hnearQ : (n : ℚ) ^ 2 / 6 - eta * (n : ℚ) ^ 2 ≤ (G.edgeFinset.card : ℚ) - w := by
    have hR : (n : ℝ) ^ 2 / 6 - (eta : ℝ) * (n : ℝ) ^ 2 ≤
        (((G.edgeFinset.card : ℚ) - w : ℚ) : ℝ) := by
      rw [← hF]; nlinarith
    have h' : ((((n : ℚ) ^ 2 / 6 - eta * (n : ℚ) ^ 2 : ℚ)) : ℝ) ≤
        (((G.edgeFinset.card : ℚ) - w : ℚ) : ℝ) := by
      push_cast at hR ⊢; linarith
    exact_mod_cast h'
  exact h n (by omega) G hdef hdeg hnearε (hNL n (by omega) G hdef w hw hnearQ) δ hδ0 hδγ
    (fun Q hQ => hlow Q hQ)

/-- **Theorem C′ (a)–(c) for every `s`, from the remaining step.** The constants are explicit:
`C_s = max K (2/ε)` and `C'_s = 1 + 7·C_s`. -/
theorem theoremCPrime_of_retained {s : ℕ} {ε γ K : ℚ} {N : ℕ} (hε : 0 < ε) (hγ : 0 < γ)
    (hK : 0 ≤ K) (h : RetainedTerminalAt s ε γ K N) :
    ∃ γ' : ℚ, 0 < γ' ∧ ∃ N' : ℕ,
      TheoremCPrimeAB s γ' (max K (2 / ε)) N' ∧ TheoremCPrimeC s N' := by
  obtain ⟨γ₁, hγ₁, N₁, hmin⟩ := minDegEditStable_of_retained hε hγ h
  obtain ⟨NC, hC⟩ := theoremC_at s
  obtain ⟨N₂, hN₂⟩ := editStable_of_minDeg s hε hγ₁ hK hmin hC
  have hγ' : 0 < min γ₁ (ε / 4) / 2 := by
    have : 0 < min γ₁ (ε / 4) := lt_min hγ₁ (by positivity)
    positivity
  have hA : EditStable s (min γ₁ (ε / 4) / 2) (max K (2 / ε)) N₂ :=
    fun n hn G _ hdef δ hδ0 hδ hlow => hN₂ n hn G hdef δ hδ0 hδ (fun Q hQ => hlow Q hQ)
  refine ⟨min γ₁ (ε / 4) / 2, hγ', N₂ + NC + s + 4, ?_, ?_⟩
  · intro n hn
    exact theoremCPrimeAB_of_editStable hA n (by omega)
  · exact theoremCPrimeC_of_editStable hγ'.le hA hC

/-- **Theorem C′ for every `s`, from `RetainedTerminalStability s`.** -/
theorem theoremCPrime_of_retainedStability {s : ℕ} (h : RetainedTerminalStability s) :
    ∃ γ Cs : ℚ, 0 < γ ∧ 0 ≤ Cs ∧ ∃ N : ℕ, TheoremCPrimeAB s γ Cs N ∧ TheoremCPrimeC s N := by
  obtain ⟨ε, γ, K, N, hε, hγ, hK, hR⟩ := h
  obtain ⟨γ', hγ', N', hAB, hC⟩ := theoremCPrime_of_retained hε hγ hK hR
  exact ⟨γ', max K (2 / ε), hγ', le_trans hK (le_max_left _ _), N', hAB, hC⟩


/-- A δ-free *constructor form* of the remaining step: on the terminal class, some root and some
order-`≤ 4` partition satisfy `|Q| + rootEdit/K ≤ Q_s(n)` (the budget of Appendix E.1 retaining a
linear multiple of the edit distance, as (5.15a) does for chordal graphs). With `K = 0` read as
no retention this is `MinDegTerminal`. -/
def RetainedAccountAt (s : ℕ) (ε K : ℚ) (N : ℕ) : Prop :=
  ∀ n, N ≤ n → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj], RootedDefectAt G s →
    (∀ v, ((1 : ℚ) / 3 - ε) * n ≤ (G.degree v : ℚ)) →
    (n : ℝ) ^ 2 / 6 - (ε : ℝ) * (n : ℝ) ^ 2 ≤ PaperIV.VertexCopyGate.F4' G →
    Nonempty (PaperIV.FixedL4.LocalizedClique G ε) →
      ∃ C D H : Finset (Fin n), IsDefectRoot G s C D H ∧
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
          K * (Q.size : ℚ) + (rootEdit G C D H : ℚ) ≤ K * (defectTarget s n : ℚ)

/-- The constructor form implies the remaining step, for every deficit window. -/
theorem retainedTerminalAt_of_account {s : ℕ} {ε K γ : ℚ} {N : ℕ} (hK : 0 ≤ K)
    (h : RetainedAccountAt s ε K N) : RetainedTerminalAt s ε γ K N := by
  intro n hn G _ hdef hdeg hnear hloc δ _ _ hlow
  obtain ⟨C, D, H, hR, Q, hQ4, hQ⟩ := h n hn G hdef hdeg hnear hloc
  refine ⟨C, D, H, hR, ?_⟩
  have hl := hlow Q hQ4
  have h1 : K * ((defectTarget s n : ℚ) - Q.size) ≤ K * δ :=
    mul_le_mul_of_nonneg_left (by linarith) hK
  nlinarith

/-! ## The case `s = 0`, unconditionally -/

theorem defSplitGraph_empty_adj {V : Type*} [DecidableEq V] (R X : Finset V) (x y : V) :
    (defSplitGraph R ∅ X).Adj x y ↔ (PaperIV.SplitUniformIncidence.splitGraph R X).Adj x y := by
  simp [defSplitGraph_adj_iff, PaperIV.SplitUniformIncidence.splitGraph_adj_iff]

/-- The chordal Theorem 6.1 of Paper IV is statement (a) at `s = 0` with `C_0 = 16`. -/
theorem editStable_zero : ∃ γ : ℚ, 0 < γ ∧ ∃ N : ℕ, EditStable 0 γ 16 N := by
  classical
  obtain ⟨N, hN⟩ := PaperIV.IntegralStability.chordal_linear_stability_sixteen
  refine ⟨PaperIV.IntegralStability.gamma, PaperIV.IntegralStability.gamma_pos, N, ?_⟩
  intro n hn G _ hdef δ hδ0 hδ hlow
  have hch : PaperIV.FarRounding.IsChordal G :=
    (PaperIV.RootedDefectZero.rootedDefect_zero_iff_isChordal).1 hdef
  have hT : defectTarget 0 n = PaperIV.targetSize n := by
    unfold defectTarget; simp; rfl
  obtain ⟨R, hR, hR2, hRout, -, -, -, hdist⟩ := hN n hn G hch δ hδ0 hδ (fun Q hQ => by
    have := hlow Q hQ; rw [hT] at this; exact this)
  refine ⟨R, ∅, univ \ R, ⟨disjoint_empty_right _, disjoint_sdiff, disjoint_empty_left _,
    fun x => by by_cases hx : x ∈ R <;> simp [hx], hR, card_empty, hR2, hRout⟩, ?_⟩
  have hsupp : PaperIV.GraphFamilyDistance.graphEdgeSupport
      (PaperIV.SplitUniformIncidence.splitGraph R (univ \ R)) =
      (defSplitGraph R ∅ (univ \ R)).edgeFinset := by
    rw [PaperIV.GraphFamilyDistance.graphEdgeSupport_eq_edgeFinset]
    exact PaperIV.CliquePartitionTransport.edgeFinset_congr
      (fun x y => (defSplitGraph_empty_adj R (univ \ R) x y).symm)
  rw [hsupp] at hdist
  exact hdist

/-- **Theorem C′ at `s = 0` (chordal graphs), unconditionally**: `C_0 = 16`, `C'_0 = 113`. -/
theorem theoremCPrime_zero :
    ∃ γ : ℚ, 0 < γ ∧ ∃ N : ℕ, TheoremCPrimeAB 0 γ 16 N ∧ TheoremCPrimeC 0 N := by
  obtain ⟨γ, hγ, N, hA⟩ := editStable_zero
  obtain ⟨NC, hC⟩ := theoremC_at 0
  refine ⟨γ, hγ, N + NC + 0 + 4, ?_, theoremCPrimeC_of_editStable hγ.le hA hC⟩
  intro n hn
  exact theoremCPrimeAB_of_editStable hA n (by omega)

/-- The remaining step holds at `s = 0` (a consistency check of its formulation). -/
theorem retainedTerminalStability_zero : RetainedTerminalStability 0 := by
  obtain ⟨γ, hγ, N, hA⟩ := editStable_zero
  exact ⟨1, γ, 16, N, one_pos, hγ, by norm_num,
    fun n hn G _ hdef _ _ _ δ hδ0 hδ hlow => hA n hn G hdef δ hδ0 hδ hlow⟩

end E32
