import E33.LocExplicit
import A4S1.IndepAllMain

/-!
# E33 — Theorem C with a threshold explicit in the defect `s`

Every threshold of the assembly of `A4S1.IndepAll.a4Sharp_all_indep` is made explicit,
**relative to the single existential input** `EditApproxExplicit Nedit` (edit-closeness to
chordal, step (i′), which the formal proof obtains from the Alon–Shapira lemma only in
`∃ N` form):

* `minDegTerminal_explicit s` — the terminal (iv), explicit: `ε_s = epsS s = 10⁻⁴¹ (s+1)⁻⁸`
  and threshold `NTerm s = ⌈10⁵⁰ (s+1)⁸⌉`.
* `near_or_far_explicit` — localization (i) + far regime (ii) + terminal (iv) under a
  minimum-degree hypothesis, above `N0 Nedit s = NLoc + NfarE (etaNF s) + NTerm s + s + 3`.
* `Fexp Nedit s = N₀ + ⌈(N₀² + 1)/ε_s⌉ + 1` (the minimum-degree reduction (iii)), and
  `Fexp_eq : Fexp Nedit s = N₀ + (N₀² + 1)·10⁴¹·(s+1)⁸ + 1`.
* **`theoremC_explicit`**: `∀ s n, Fexp Nedit s ≤ n → ∀ G, RootedDefectAt G s →
  c₄(G) ≤ Q_s(n)`.
* **`theoremC_uniform`**: with `Fmono` the running maximum of `Fexp` and
  `Finv n = max {s ≤ n : Fmono s ≤ n}`, for every `n ≥ Fmono 0` the bound holds for **all**
  `s ≤ Finv n` simultaneously; `le_Finv` shows `Finv n → ∞`.
* `theoremC_uniform_exists`, `a4Sharp_all_E33` — unconditional corollaries (with the
  non-explicit witness of `exists_editApproxExplicit`).
-/

namespace E33

open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.FixedL4
  PaperIV.DefectTargetArithmetic A4S1.IndepAll

/-! ## (iv) the terminal, explicit -/

/-- The minimum-degree terminal with explicit threshold `N`. -/
def MinDegTerminalN (s : ℕ) (eps : ℚ) (N : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    RootedDefectAt G s →
    (∀ v : Fin n, ((1 : ℚ) / 3 - eps) * n ≤ (G.degree v : ℚ)) →
    (n : ℝ) ^ 2 / 6 - (eps : ℝ) * (n : ℝ) ^ 2 ≤ PaperIV.VertexCopyGate.F4' G →
    Nonempty (LocalizedClique G eps) →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n

/-- The explicit terminal threshold `⌈10⁵⁰ (s+1)⁸⌉`. -/
noncomputable def NTerm (s : ℕ) : ℕ := ⌈(10 : ℚ) ^ 50 * ((s : ℚ) + 1) ^ 8⌉₊

/-- **The terminal (iv) with explicit constants** (copy of
`A4S1.IndepAll.minDegTerminal_all_indep`, keeping the witnesses). -/
theorem minDegTerminal_explicit (s : ℕ) : MinDegTerminalN s (epsS s) (NTerm s) := by
  intro n hn G _ hG hdeg _ hL
  obtain ⟨L⟩ := hL
  have hnq : (10 : ℚ) ^ 50 * ((s : ℚ) + 1) ^ 8 ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_fin]; exact (Nat.ceil_le.1 hn)
  have hsz := abs_le.1 L.size_window
  have hmass := L.mass_small
  have h0 : (0 : ℚ) ≤ ((PaperIV.RootVocab.outsideEdges G L.core).card : ℚ) := by positivity
  have h1 : (0 : ℚ) ≤ ((PaperIV.RootVocab.missingIncidences G L.core : ℕ) : ℚ) := by positivity
  have hin : AllInput G L.core s :=
    { rd := hG
      hn := hnq
      deg := by rw [Fintype.card_fin]; exact hdeg
      clique := L.isClique
      size_lo := by rw [Fintype.card_fin]; linarith
      size_hi := by rw [Fintype.card_fin]; linarith
      miss := by rw [← all_missingIncidences_eq, Fintype.card_fin]; linarith
      out := by rw [← all_card_outsideEdges_eq, Fintype.card_fin]; linarith }
  obtain ⟨Q, hQ4, hQ⟩ := hin.partition
  exact ⟨Q, hQ4, by simpa using hQ⟩

theorem epsS_pos' (s : ℕ) : 0 < epsS s := by unfold epsS; positivity

theorem epsS_le_two (s : ℕ) : epsS s ≤ 2 := by
  unfold epsS
  have h : (1 : ℚ) ≤ 10 ^ 41 * ((s : ℚ) + 1) ^ 8 := by
    have : (1 : ℚ) ≤ ((s : ℚ) + 1) ^ 8 := one_le_pow₀ (by linarith [(Nat.cast_nonneg s : (0:ℚ) ≤ s)])
    nlinarith
  rw [div_le_iff₀ (by positivity)]; linarith

/-! ## (i)+(ii)+(iv): the near/far step, explicit -/

/-- The far margin actually used: `min (η_loc(s, ε_s)) ε_s`. -/
def etaNF (s : ℕ) : ℚ := min (etaLoc s (epsS s)) (epsS s)

theorem etaNF_pos (s : ℕ) : 0 < etaNF s :=
  lt_min (etaLoc_pos s (epsS_pos' s)) (epsS_pos' s)

/-- **The explicit `N₀(s)`** of the minimum-degree reduction. -/
noncomputable def N0 (Nedit : ℕ → ℚ → ℕ) (s : ℕ) : ℕ :=
  NLoc Nedit s (epsS s) + E18.NfarE (etaNF s) + NTerm s + s + 3

/-- **The near/far step with explicit threshold `N0 Nedit s`.** -/
theorem near_or_far_explicit (Nedit : ℕ → ℚ → ℕ) (hE : EditApproxExplicit Nedit) (s : ℕ) :
    ∀ n : ℕ, N0 Nedit s ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      RootedDefectAt G s → (∀ v : Fin n, ((1 : ℚ) / 3 - epsS s) * n ≤ (G.degree v : ℚ)) →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n := by
  classical
  have heps := epsS_pos' s
  have hNL := marginLoc_explicit Nedit hE s heps (epsS_le_two s)
  have hNT := minDegTerminal_explicit s
  have hNf := E18.farRegime_allGraphs_explicit (etaNF s) (etaNF_pos s)
  intro n hn G _ hdef hdeg
  unfold N0 at hn
  set eta := etaLoc s (epsS s) with heta
  set eps := epsS s with hepsdef
  have h1 : etaNF s ≤ eta := min_le_left _ _
  have h2 : etaNF s ≤ eps := min_le_right _ _
  by_cases hfar : PaperIV.VertexCopyGate.F4' G <
      (n : ℝ) ^ 2 / 6 - ((etaNF s : ℚ) : ℝ) * (n : ℝ) ^ 2
  · obtain ⟨Q, hQ4, hQs⟩ := hNf n (by omega) G hfar
    exact ⟨Q, hQ4, le_trans hQs (targetSize_le_defectTarget s n (by omega))⟩
  push_neg at hfar
  have hsqR : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have h1R : ((etaNF s : ℚ) : ℝ) ≤ (eta : ℝ) := by exact_mod_cast h1
  have h2R : ((etaNF s : ℚ) : ℝ) ≤ (eps : ℝ) := by exact_mod_cast h2
  have hfarEps : (n : ℝ) ^ 2 / 6 - (eps : ℝ) * (n : ℝ) ^ 2 ≤ PaperIV.VertexCopyGate.F4' G := by
    nlinarith
  obtain ⟨w, hw⟩ := PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum G
  have hF := PaperIV.CertifiedF4Bridge.F4'_eq_edge_sub_certified hw
  have hnear : (n : ℚ) ^ 2 / 6 - eta * (n : ℚ) ^ 2 ≤ (G.edgeFinset.card : ℚ) - w := by
    have hR : (n : ℝ) ^ 2 / 6 - (eta : ℝ) * (n : ℝ) ^ 2 ≤
        (((G.edgeFinset.card : ℚ) - w : ℚ) : ℝ) := by
      rw [← hF]; nlinarith
    have h : ((((n : ℚ) ^ 2 / 6 - eta * (n : ℚ) ^ 2 : ℚ)) : ℝ) ≤
        (((G.edgeFinset.card : ℚ) - w : ℚ) : ℝ) := by
      push_cast at hR ⊢; linarith
    exact_mod_cast h
  exact hNT n (by omega) G hdef hdeg hfarEps (hNL n (by omega) G hdef w hw hnear)

/-! ## (iii) the minimum-degree reduction, explicit, and the final threshold -/

/-- **The explicit threshold of Theorem C at defect `s`**, relative to `Nedit`:
`F(s) = N₀ + ⌈(N₀² + 1)/ε_s⌉ + 1`. -/
noncomputable def Fexp (Nedit : ℕ → ℚ → ℕ) (s : ℕ) : ℕ :=
  N0 Nedit s + ⌈(((N0 Nedit s * N0 Nedit s : ℕ) : ℚ) + 1) / epsS s⌉₊ + 1

/-- Closed form: `F(s) = N₀ + (N₀² + 1) · 10⁴¹ · (s+1)⁸ + 1`. -/
theorem Fexp_eq (Nedit : ℕ → ℚ → ℕ) (s : ℕ) :
    Fexp Nedit s = N0 Nedit s + (N0 Nedit s * N0 Nedit s + 1) * 10 ^ 41 * (s + 1) ^ 8 + 1 := by
  unfold Fexp
  congr 2
  have h : (((N0 Nedit s * N0 Nedit s : ℕ) : ℚ) + 1) / epsS s =
      (((N0 Nedit s * N0 Nedit s + 1) * 10 ^ 41 * (s + 1) ^ 8 : ℕ) : ℚ) := by
    unfold epsS
    push_cast
    field_simp
    norm_num
  rw [h, Nat.ceil_natCast]

/-- **Theorem C with an explicit threshold in `s`** (relative to `EditApproxExplicit`). -/
theorem theoremC_explicit (Nedit : ℕ → ℚ → ℕ) (hE : EditApproxExplicit Nedit) (s n : ℕ)
    (hn : Fexp Nedit s ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdef : RootedDefectAt G s) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n := by
  classical
  have heps := epsS_pos' s
  have hnear := near_or_far_explicit Nedit hE s
  have hN₀ : s + 3 ≤ N0 Nedit s := by unfold N0; omega
  set N₀ := N0 Nedit s with hN₀def
  set K := N₀ * N₀ with hK
  have hall := A4S1.MinDegreeAll.targetK_all heps N₀ hN₀ hnear
  set M : ℕ := ⌈((K : ℚ) + 1) / epsS s⌉₊ with hM
  have hnM : N₀ + M + 1 ≤ n := by
    have : Fexp Nedit s = N₀ + M + 1 := rfl
    omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_cases hlow : ∃ v : Fin (m + 1), G.degree v + K ≤ (m + s + 2) / 3
  · obtain ⟨v, hv⟩ := hlow
    obtain ⟨Q, hQ4, hQ⟩ := A4S1.MinDegreeAll.delete_vertex (hall m) G hdef v
    refine ⟨Q, hQ4, ?_⟩
    rw [A4S1.MinDegreeAll.defectTarget_succ s m (by omega)]
    omega
  push_neg at hlow
  refine hnear (m + 1) (by omega) G hdef (fun v => ?_)
  have h := hlow v
  have h3 : m + 3 ≤ 3 * (G.degree v + K) := by omega
  have h3Q : ((m : ℚ) + 3) ≤ 3 * ((G.degree v : ℚ) + K) := by exact_mod_cast h3
  have hMle : ((K : ℚ) + 1) / epsS s ≤ (M : ℚ) := Nat.le_ceil _
  have hnM' : (M : ℚ) ≤ (m : ℚ) + 1 := by
    have : M ≤ m + 1 := by omega
    exact_mod_cast this
  have hKe : (K : ℚ) + 1 ≤ epsS s * ((m : ℚ) + 1) := by
    have := (div_le_iff₀ heps).1 (hMle.trans hnM')
    linarith
  push_cast
  nlinarith

/-! ## Uniformity in `s` -/

/-- Running maximum of the explicit thresholds (monotone in `s`). -/
noncomputable def Fmono (Nedit : ℕ → ℚ → ℕ) (s : ℕ) : ℕ := (range (s + 1)).sup (Fexp Nedit)

theorem Fexp_le_Fmono (Nedit : ℕ → ℚ → ℕ) (s : ℕ) : Fexp Nedit s ≤ Fmono Nedit s :=
  Finset.le_sup (f := Fexp Nedit) (Finset.mem_range.2 (Nat.lt_succ_self s))

theorem Fmono_mono (Nedit : ℕ → ℚ → ℕ) : Monotone (Fmono Nedit) := by
  intro a b hab
  exact Finset.sup_mono (Finset.range_subset_range.2 (by omega))

/-- The explicit inverse `F⁻¹(n) = max {s ≤ n : Fmono s ≤ n}`. -/
noncomputable def Finv (Nedit : ℕ → ℚ → ℕ) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun s => Fmono Nedit s ≤ n) n

theorem Fmono_Finv_le (Nedit : ℕ → ℚ → ℕ) {n : ℕ} (h0 : Fmono Nedit 0 ≤ n) :
    Fmono Nedit (Finv Nedit n) ≤ n :=
  Nat.findGreatest_spec (P := fun s => Fmono Nedit s ≤ n) (Nat.zero_le n) h0

/-- `F⁻¹(n) → ∞`: every `s` is admissible once `n ≥ max s (Fmono s)`. -/
theorem le_Finv (Nedit : ℕ → ℚ → ℕ) {s n : ℕ} (hs : s ≤ n) (hF : Fmono Nedit s ≤ n) :
    s ≤ Finv Nedit n :=
  Nat.le_findGreatest (P := fun s => Fmono Nedit s ≤ n) hs hF

/-- **Theorem C, uniform in the defect**: for every `n ≥ Fmono 0`, the sharp bound
`c₄(G) ≤ Q_s(n)` holds simultaneously for all `s ≤ F⁻¹(n)`. -/
theorem theoremC_uniform (Nedit : ℕ → ℚ → ℕ) (hE : EditApproxExplicit Nedit) (n : ℕ)
    (h0 : Fmono Nedit 0 ≤ n) :
    ∀ s : ℕ, s ≤ Finv Nedit n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      RootedDefectAt G s →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n := by
  intro s hs G _ hG
  have h1 := Fexp_le_Fmono Nedit s
  have h2 := Fmono_mono Nedit hs
  have h3 := Fmono_Finv_le Nedit h0
  exact theoremC_explicit Nedit hE s n (by omega) G hG

/-- Unconditional uniform statement (the threshold function is explicit in terms of the
witness of `exists_editApproxExplicit`, which itself is not explicit). -/
theorem theoremC_uniform_exists :
    ∃ F : ℕ → ℕ, ∀ s n : ℕ, F s ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      RootedDefectAt G s →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n := by
  obtain ⟨Nedit, hE⟩ := exists_editApproxExplicit
  exact ⟨Fexp Nedit, fun s n hn G _ hG => theoremC_explicit Nedit hE s n hn G hG⟩

/-- Comparison with the fixed-`s` statement: `A4Sharp s` for every `s`. -/
theorem a4Sharp_all_E33 (s : ℕ) : PaperIV.A4AllDefects.A4Sharp s := by
  obtain ⟨F, hF⟩ := theoremC_uniform_exists
  exact ⟨F s, fun n hn G _ hG => hF s n hn G hG⟩

end E33
