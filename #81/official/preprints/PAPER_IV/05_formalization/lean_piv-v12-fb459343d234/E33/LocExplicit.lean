import E33.FarExplicit
import PaperIV.EditRouteUnconditional

/-!
# E33 — explicit localization (step (i)) relative to one existential input

* `EditApproxN s δ N` — every graph of rooted defect `≤ s` and order `n ≥ N` is within
  `δ n²` edits of a chordal graph (the explicit-threshold form of
  `PaperIV.EditRoute.EditApproxAt s δ`).
* **`EditApproxExplicit Nedit`** — the named Prop for the one step of Theorem C that the
  formal proof provides only existentially: `Nedit : ℕ → ℚ → ℕ` is a threshold function
  for edit-closeness to chordal.  `exists_editApproxExplicit` shows it is satisfiable
  (by choice from `PaperIV.EditRoute.editApproxAt_all`, i.e. the formal Alon–Shapira
  lemma plus Lemma K), so it is not vacuous; but that witness is not explicit.
* `MarginLocN s ε η N` — localization with explicit margin `η` and threshold `N`.
* `marginLoc_zero_explicit` — defect `0`, explicit `η₀(ε)` and `N₀(ε)`
  (built on `chordal_linear_stability_explicit`).
* `marginLoc_of_editApproxN` — transfer to defect `s` with threshold `max N₀ N_edit`.
* `marginLoc_explicit` — every defect `s`, every `0 < ε ≤ 2`: explicit margin
  `etaLoc s ε` and threshold `NLoc Nedit s ε = max (N0Of (ε/2)) (Nedit s (deltaLoc s ε))`.
-/

namespace E33

open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.FixedL4
  PaperIV.RootVocab PaperIV.EditRoute

/-- Edit-closeness to chordal at precision `δ` above the explicit order `N`. -/
def EditApproxN (s : ℕ) (δ : ℚ) (N : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    RootedDefectAt G s → ∃ G' : SimpleGraph (Fin n), G'.IsChordal ∧
      (((symmDiff G.edgeSet G'.edgeSet).ncard : ℚ) ≤ δ * (n : ℚ) ^ 2)

/-- **The named Prop for the existential step (i′):** `Nedit s δ` is a threshold for
edit-closeness to chordal at precision `δ`, for every rooted defect `s`. -/
def EditApproxExplicit (Nedit : ℕ → ℚ → ℕ) : Prop :=
  ∀ s : ℕ, ∀ δ : ℚ, 0 < δ → EditApproxN s δ (Nedit s δ)

/-- The named Prop is satisfiable (non-explicitly, by choice from the formal
Alon–Shapira route `PaperIV.EditRoute.editApproxAt_all`). -/
theorem exists_editApproxExplicit : ∃ Nedit : ℕ → ℚ → ℕ, EditApproxExplicit Nedit := by
  classical
  refine ⟨fun s δ => if h : 0 < δ then Classical.choose (editApproxAt_all s δ h) else 0, ?_⟩
  intro s δ hδ n hn G _ hG
  simp only [dif_pos hδ] at hn
  exact Classical.choose_spec (editApproxAt_all s δ hδ) n hn G hG

/-- Localization with explicit margin `eta` and explicit threshold `N`. -/
def MarginLocN (s : ℕ) (eps eta : ℚ) (N : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], RootedDefectAt G s →
    ∀ w : ℚ, CertifiedFractionalOptimum G w →
      (n : ℚ) ^ 2 / 6 - eta * (n : ℚ) ^ 2 ≤ (G.edgeFinset.card : ℚ) - w →
        Nonempty (LocalizedClique G eps)

/-! ## Defect zero -/

/-- The explicit defect-zero margin `η₀(ε) = min (γ/2) (min (ε/32) (ε²/16))`. -/
def eta0Of (eps : ℚ) : ℚ :=
  min (PaperIV.IntegralStability.gamma / 2) (min (eps / 32) (eps ^ 2 / 16))

/-- The explicit defect-zero threshold `N₀(ε) = max stabThreshold ⌈100/(γ ε²)⌉`. -/
noncomputable def N0Of (eps : ℚ) : ℕ :=
  max stabThreshold ⌈(100 : ℚ) / (PaperIV.IntegralStability.gamma * eps ^ 2)⌉₊

theorem eta0Of_pos {eps : ℚ} (heps : 0 < eps) : 0 < eta0Of eps := by
  have := PaperIV.IntegralStability.gamma_pos
  unfold eta0Of; positivity

/-- **Localization at defect `0` with explicit constants** (`0 < ε ≤ 1`). -/
theorem marginLoc_zero_explicit {eps : ℚ} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    MarginLocN 0 eps (eta0Of eps) (N0Of eps) := by
  classical
  have hγ := PaperIV.IntegralStability.gamma_pos
  have hγ1 : PaperIV.IntegralStability.gamma ≤ 1 := by
    norm_num [PaperIV.IntegralStability.gamma, PaperIV.NearH1Calibration.eta]
  obtain ⟨γ, hγdef⟩ : ∃ γ, γ = PaperIV.IntegralStability.gamma := ⟨_, rfl⟩
  rw [← hγdef] at hγ hγ1
  have heta_pos : 0 < eta0Of eps := eta0Of_pos heps
  have heta1 : eta0Of eps ≤ γ / 2 := hγdef ▸ min_le_left _ _
  have heta2 : eta0Of eps ≤ eps / 32 := le_trans (min_le_right _ _) (min_le_left _ _)
  have heta3 : eta0Of eps ≤ eps ^ 2 / 16 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hc_pos : 0 < γ * eps ^ 2 := by positivity
  intro n hn G _ hdef w hw hnear
  have hnNs : stabThreshold ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnM : ⌈(100 : ℚ) / (γ * eps ^ 2)⌉₊ ≤ n := by
    have := le_trans (Nat.le_max_right _ _) hn
    rw [hγdef]; exact this
  have hnQ : (100 : ℚ) / (γ * eps ^ 2) ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hnM)
  have hcn : 100 ≤ γ * eps ^ 2 * n := by
    rw [div_le_iff₀ hc_pos] at hnQ; linarith
  obtain ⟨hδγ, hδmass, hδsize⟩ :=
    calibration_arith heps heps1 hγ hγ1 hcn heta_pos heta1 heta2 heta3
  have hchordal : PaperIV.FarRounding.IsChordal G :=
    PaperIV.RootedDefectZero.isChordal_of_rootedDefect_zero hdef
  have hn0 : (0 : ℚ) ≤ n := by positivity
  have hδ0 : 0 ≤ eta0Of eps * (n : ℚ) ^ 2 + (n : ℚ) / 6 := by positivity
  have hmin : ∀ Q : CliquePartition G, Q.OrderAtMost 4 →
      (PaperIV.targetSize n : ℚ) - (eta0Of eps * (n : ℚ) ^ 2 + (n : ℚ) / 6) ≤ (Q.size : ℚ) := by
    intro Q hQ
    have h1 := size_ge_edge_sub_certified hw Q hQ
    have h2 := PaperIV.targetSize_cast_le_continuous n
    linarith
  obtain ⟨R, hRclique, -, -, hbase, -, hreserve, -⟩ :=
    chordal_linear_stability_explicit n hnNs G hchordal _ hδ0 (hγdef ▸ hδγ) hmin
  have hm0 : (0 : ℚ) ≤ ((outsideEdges G R).card : ℚ) := by positivity
  have hA0 : (0 : ℚ) ≤ (missingIncidences G R : ℚ) := by positivity
  refine ⟨⟨R, hRclique, ?_, ?_⟩⟩
  · have hpar := sq_dev_le_of_targetSize_sub_baseline n (R.card : ℚ)
    have hdev : (R.card : ℚ) - (n : ℚ) / 3 =
        ((R.card : ℚ) - (2 * (n : ℚ) + 1) / 6) + 1 / 6 := by ring
    rw [hdev]
    exact hδsize _ (by linarith)
  · linarith

/-! ## Transfer to defect `s` -/

/-- **Transfer with explicit threshold** (copy of
`PaperIV.EditRoute.fixedL4LocalizationAt_of_editApprox`, keeping `max N₀ N_edit`). -/
theorem marginLoc_of_editApproxN {s : ℕ} {eps eps0 eta0 delta r : ℚ} {N0 NE : ℕ}
    (h0 : MarginLocN 0 eps0 eta0 N0)
    (hr : 0 ≤ r) (hr2 : 2 * ((s : ℚ) + 1) * delta ≤ r ^ 2)
    (hwin : eps0 + 2 * r ≤ eps) (hmass : eps0 + delta + 2 * r ≤ eps)
    (hE : EditApproxN s delta NE) : MarginLocN s eps (eta0 - 4 * delta) (max N0 NE) := by
  classical
  intro n hn G _ hdef w hw hnear
  have hnN0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hnNE : NE ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨G', hch, hsym⟩ := hE n hnNE G hdef
  haveI : DecidableRel G'.Adj := Classical.decRel _
  obtain ⟨w', hw'⟩ := PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum G'
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = (G'.edgeFinset \ G.edgeFinset).card := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = (G.edgeFinset \ G'.edgeFinset).card := ⟨_, rfl⟩
  have hz : (a : ℚ) + (d : ℚ) ≤ delta * (n : ℚ) ^ 2 := by
    have := card_symmDiff_edgeSet G G'
    rw [this, ← ha, ← hd] at hsym
    push_cast at hsym
    linarith
  have ha0 : (0 : ℚ) ≤ (a : ℚ) := by positivity
  have hd0 : (0 : ℚ) ≤ (d : ℚ) := by positivity
  have hF := certified_edit_bound hw hw'
  have hnearG' : (n : ℚ) ^ 2 / 6 - eta0 * (n : ℚ) ^ 2 ≤ (G'.edgeFinset.card : ℚ) - w' := by
    rw [← ha, ← hd] at hF
    nlinarith
  have hdef' : RootedDefectAt G' 0 :=
    PaperIV.RootedDefectZero.rootedDefect_zero_iff_isChordal.2 hch
  obtain ⟨L'⟩ := h0 n hnN0 G' hdef' w' hw' hnearG'
  obtain ⟨C, hCsub, hCcl, nu, hWC, hnu⟩ := clique_of_rootedDefect_of_few_nonedges hdef L'.core
  have hnonE : (nonEdgesIn G L'.core).card ≤ a := by
    rw [ha]; exact card_le_card (nonEdgesIn_subset_added (G := G) L'.isClique)
  have hnuQ : ((nu : ℚ)) ^ 2 ≤ 2 * ((s : ℚ) + 1) * (a : ℚ) := by
    have h1 : nu ^ 2 ≤ 2 * (s + 1) * a := by
      calc nu ^ 2 ≤ nu ^ 2 + (s + 1) * nu := Nat.le_add_right _ _
        _ ≤ 2 * (s + 1) * (nonEdgesIn G L'.core).card := hnu
        _ ≤ 2 * (s + 1) * a := by gcongr
    exact_mod_cast h1
  have hn0 : (0 : ℚ) ≤ (n : ℚ) := by positivity
  have hnu_le : (nu : ℚ) ≤ r * (n : ℚ) := by
    have hsq : ((nu : ℚ)) ^ 2 ≤ (r * (n : ℚ)) ^ 2 := by
      have hs0 : (0 : ℚ) ≤ 2 * ((s : ℚ) + 1) := by positivity
      calc ((nu : ℚ)) ^ 2 ≤ 2 * ((s : ℚ) + 1) * (a : ℚ) := hnuQ
        _ ≤ 2 * ((s : ℚ) + 1) * (delta * (n : ℚ) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hs0; linarith
        _ = (2 * ((s : ℚ) + 1) * delta) * (n : ℚ) ^ 2 := by ring
        _ ≤ r ^ 2 * (n : ℚ) ^ 2 := by
            apply mul_le_mul_of_nonneg_right hr2 (by positivity)
        _ = (r * (n : ℚ)) ^ 2 := by ring
    have hrn : 0 ≤ r * (n : ℚ) := mul_nonneg hr hn0
    by_contra hlt
    push_neg at hlt
    nlinarith
  have hsd : (L'.core \ C).card = L'.core.card - C.card := card_sdiff_of_subset hCsub
  have hCle : C.card ≤ L'.core.card := card_le_card hCsub
  have hsdQ : ((L'.core \ C).card : ℚ) ≤ 2 * (nu : ℚ) := by
    have : (L'.core \ C).card ≤ 2 * nu := by omega
    exact_mod_cast this
  have hCQ : (L'.core.card : ℚ) - 2 * (nu : ℚ) ≤ (C.card : ℚ) := by
    have : L'.core.card ≤ C.card + 2 * nu := hWC
    have : (L'.core.card : ℚ) ≤ (C.card : ℚ) + 2 * (nu : ℚ) := by exact_mod_cast this
    linarith
  have hCleQ : (C.card : ℚ) ≤ (L'.core.card : ℚ) := by exact_mod_cast hCle
  refine ⟨⟨C, hCcl, ?_, ?_⟩⟩
  · have hwin' := L'.size_window
    rw [abs_le] at hwin' ⊢
    have hw2 : (eps0 + 2 * r) * (n : ℚ) ≤ eps * (n : ℚ) := mul_le_mul_of_nonneg_right hwin hn0
    constructor
    · linarith
    · linarith
  · have htr := missingIncidences_add_outsideEdges_le_of_edit (G := G) (G' := G') hCsub
      L'.isClique
    rw [← ha, ← hd, Fintype.card_fin] at htr
    have htrQ : (missingIncidences G C : ℚ) + ((outsideEdges G C).card : ℚ) ≤
        (missingIncidences G' L'.core : ℚ) + ((outsideEdges G' L'.core).card : ℚ) +
          (a : ℚ) + (d : ℚ) + ((L'.core \ C).card : ℚ) * (n : ℚ) := by
      exact_mod_cast htr
    have hmass' := L'.mass_small
    have h3 : ((L'.core \ C).card : ℚ) * (n : ℚ) ≤ 2 * r * (n : ℚ) ^ 2 := by
      calc ((L'.core \ C).card : ℚ) * (n : ℚ) ≤ (2 * (nu : ℚ)) * (n : ℚ) :=
            mul_le_mul_of_nonneg_right hsdQ hn0
        _ ≤ (2 * (r * (n : ℚ))) * (n : ℚ) :=
            mul_le_mul_of_nonneg_right (by linarith) hn0
        _ = 2 * r * (n : ℚ) ^ 2 := by ring
    have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := by positivity
    have hfin : (eps0 + delta + 2 * r) * (n : ℚ) ^ 2 ≤ eps * (n : ℚ) ^ 2 := by
      gcongr
    linarith

/-! ## Calibration: explicit constants at every defect -/

/-- `r(ε) = min (ε/8) (min 1 (η₀(ε/2)/8))`. -/
def rLoc (eps : ℚ) : ℚ := min (eps / 8) (min 1 (eta0Of (eps / 2) / 8))

/-- The edit precision `δ(s, ε) = r(ε)² / (2(s+1))` fed to `Nedit`. -/
def deltaLoc (s : ℕ) (eps : ℚ) : ℚ := rLoc eps ^ 2 / (2 * ((s : ℚ) + 1))

/-- The explicit localization margin `η_loc(s, ε) = η₀(ε/2) − 4 δ(s, ε)`. -/
def etaLoc (s : ℕ) (eps : ℚ) : ℚ := eta0Of (eps / 2) - 4 * deltaLoc s eps

/-- The explicit localization threshold. -/
noncomputable def NLoc (Nedit : ℕ → ℚ → ℕ) (s : ℕ) (eps : ℚ) : ℕ :=
  max (N0Of (eps / 2)) (Nedit s (deltaLoc s eps))

theorem rLoc_pos {eps : ℚ} (heps : 0 < eps) : 0 < rLoc eps := by
  have := eta0Of_pos (eps := eps / 2) (by positivity)
  unfold rLoc; exact lt_min (by positivity) (lt_min one_pos (by positivity))

theorem deltaLoc_pos (s : ℕ) {eps : ℚ} (heps : 0 < eps) : 0 < deltaLoc s eps := by
  have := rLoc_pos heps
  unfold deltaLoc; positivity

theorem deltaLoc_le_rLoc (s : ℕ) {eps : ℚ} (heps : 0 < eps) : deltaLoc s eps ≤ rLoc eps := by
  have hr0 := rLoc_pos heps
  have hr1 : rLoc eps ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hs1 : (0 : ℚ) < 2 * ((s : ℚ) + 1) := by positivity
  have h1 : deltaLoc s eps ≤ rLoc eps ^ 2 := by
    unfold deltaLoc
    rw [div_le_iff₀ hs1]
    have : (0 : ℚ) ≤ (s : ℚ) := by positivity
    nlinarith [sq_nonneg (rLoc eps)]
  nlinarith

theorem etaLoc_pos (s : ℕ) {eps : ℚ} (heps : 0 < eps) : 0 < etaLoc s eps := by
  have hr3 : rLoc eps ≤ eta0Of (eps / 2) / 8 := le_trans (min_le_right _ _) (min_le_right _ _)
  have := deltaLoc_le_rLoc s heps
  have := deltaLoc_pos s heps
  unfold etaLoc; linarith

theorem etaLoc_le (s : ℕ) {eps : ℚ} (heps : 0 < eps) : etaLoc s eps ≤ eps := by
  have h1 : eta0Of (eps / 2) ≤ eps / 2 / 32 := le_trans (min_le_right _ _) (min_le_left _ _)
  have := deltaLoc_pos s heps
  unfold etaLoc; linarith

/-- **Explicit localization at every rooted defect**, relative to `EditApproxExplicit`. -/
theorem marginLoc_explicit (Nedit : ℕ → ℚ → ℕ) (hE : EditApproxExplicit Nedit) (s : ℕ)
    {eps : ℚ} (heps : 0 < eps) (heps2 : eps ≤ 2) :
    MarginLocN s eps (etaLoc s eps) (NLoc Nedit s eps) := by
  have hr0 := rLoc_pos heps
  have hr1 : rLoc eps ≤ eps / 8 := min_le_left _ _
  have hr3 : rLoc eps ≤ eta0Of (eps / 2) / 8 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hdle := deltaLoc_le_rLoc s heps
  have hdpos := deltaLoc_pos s heps
  have hs1 : (0 : ℚ) < 2 * ((s : ℚ) + 1) := by positivity
  have hdr2 : 2 * ((s : ℚ) + 1) * deltaLoc s eps = rLoc eps ^ 2 := by
    unfold deltaLoc; field_simp
  exact marginLoc_of_editApproxN (marginLoc_zero_explicit (by positivity) (by linarith))
    hr0.le hdr2.le (by linarith) (by linarith) (hE s _ hdpos)

end E33
