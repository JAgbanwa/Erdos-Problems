/-
# The §10.12 assembly from the *corrected* §7.2/§9.3 inputs, and the ρ-window

`BKLO.lemma1012K3'At_of_inputs` (`BKLO/Section1012Assembly.lean`) carries out the proof of BKLO
Lemma 10.12 (`r = 2`, `F = K₃`) in the dense regime from four hypotheses, two of which — the
transcriptions `BKLO.Lemma72K3` and `BKLO.Lemma93K3` — are *false as stated*.  This file repeats
that assembly from the corrected forms, which are **theorems** of this development:

* `BKLO.lemma72K3'_holds : BKLO.Lemma72K3'`   (`BKLO/Section72K3.lean`);
* `BKLO.lemma93K3S_holds : BKLO.Lemma93K3S`   (`BKLO/Section9ParityK3Proof.lean`).

and it leaves the sparsity parameter `ρ` free, isolating the *single* numerical constraint that the
assembly puts on `ρ`, namely the slack inequality of condition (ii) of Lemma 10.10,

  `18 k √ρ³ ≤ ρ/4`.                                                                        (SLACK)

Corollary 10.11 is only ever used at that one pair `(ρ, k)`, so it enters as `Cor1011K3AtRho ρ k`.

## The ρ-window is empty

The point of the parametrisation is that it makes the obstruction to the "ρ-reconciliation"
completely explicit; that arithmetic is in `BKLO/Section1012RhoWindow.lean`.  The codegree-regime
Lemma 10.10 of `BKLO/Section1010Dense.lean` supplies `Cor1011K3AtRho ρ k` only for

  `1/(648 k²) < ρ`                                                                        (REGIME)

(the Cauchy–Schwarz/Corrádi count needs `4 (18k√ρ³)² > 2ρ²`), whereas the §10.12 assembly needs
(SLACK), i.e. `ρ ≤ 1/(5184 k²)`.  `BKLO.rho_window_empty` proves that these two demands are
contradictory — for *every* `ρ`, not just for the candidate `ρ = 1/(625k²)` of
`BKLO/RhoReconcile625.lean`, whose slack is `18k√ρ³ = (18/25)ρ`, nearly three times what (SLACK)
allows.  Moreover `BKLO.slack_lower_bound_of_regime` shows the clash is not an artefact of the
constant `1/4` in (SLACK): under (REGIME) the slack is above `0.7ρ`.  (Informally — this part is
not formalised — the estimates of the assembly cannot afford a slack above `≈ 0.35ρ` in
condition (ii): with `δ ≥ 9/10` two neighbourhoods inside a part meet in `≥ 0.8|W|` vertices,
against the `0.5|W|` demanded by `2`-divisibility, and the `ρ`-random subgraph inherits that
margin; while the greedy codegree count behind (REGIME) needs a slack `> ρ/√2`.)

So the residual input for `Lemma1012K3' (9/10)` is exactly Lemma 10.10 in the *sparse* regime
`ρ ≤ 1/(5184k²)` — the regime where the paper's proof goes through the pseudorandom `K_r`-factor
statements of Lemma 10.7 / Corollary 10.9 — together with the approximate-decomposition threshold
`δ_F^η` (`BKLO.ApproxTriDecompMinDeg (9/10)`).  Everything else is discharged here.
-/
import BKLO.Section1012Assembly
import BKLO.Section1012RhoWindow
import BKLO.Section106Set
import BKLO.Section72K3
import BKLO.Section9ParityK3Proof

open Finset

namespace BKLO


/-! ### The assembly -/

set_option maxHeartbeats 400000 in
/-- **BKLO Lemma 10.12 for `r = 2` (repaired), hard case, from the *corrected* paper inputs and a
free sparsity parameter `ρ`.**

This is `BKLO.lemma1012K3'At_of_inputs` with three changes.

* The parameter `ρ` is no longer fixed to `1/(10000k²)`: it is a parameter, subject to `0 < ρ ≤ ε`
  and to the single numerical constraint the proof makes on it, namely the slack inequality
  `18k√ρ³ ≤ ρ/4` of condition (ii) of Lemma 10.10.
* Lemma 7.2 and Lemma 9.3 are taken in their *corrected* forms `BKLO.Lemma72K3'` and
  `BKLO.Lemma93K3S` — both of which are theorems of this development — instead of the
  false-as-stated `BKLO.Lemma72K3` and `BKLO.Lemma93K3`.
* Corollary 10.11 is only needed at the single triple `(α, ρ, k) = (ε/(16k²), ρ, k)`, so it is
  taken as `BKLO.Cor1011K3AtAlphaRho (ε/(16k²)) ρ k`.  (This is the *only* way the assembly uses
  §10.2; in particular it never needs Corollary 10.11 at an `α` below `2kρ`.) -/
theorem lemma1012K3'At_of_true_inputs_atAlpha {δ ε ρ : ℝ} {k : ℕ}
    (hδ : (9 : ℝ) / 10 ≤ δ) (hk30 : 30 ≤ k) (hε : 0 < ε)
    (hkε : 1 / (k : ℝ) ≤ ε) (hsum : δ + 3 * ε ≤ 1)
    (hρpos : 0 < ρ) (hρε : ρ ≤ ε) (h18 : 18 * (k : ℝ) * Real.sqrt ρ ^ 3 ≤ ρ / 4)
    (h72 : Lemma72K3') (h93 : Lemma93K3S)
    (h1011 : Cor1011K3AtAlphaRho (ε / (16 * (k : ℝ) ^ 2)) ρ k)
    (h106 : Lemma106K3Set δ) :
    Lemma1012K3'At δ k ε := by
  classical
  have hk0 : 0 < k := by omega
  have hkR : (30 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk30
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith only [hkR]
  have hε30 : ε ≤ 1 / 30 := by linarith only [hδ, hsum]
  -- the parameters of the proof: `ρ` as given, `γ = ρ²ε/(1000k²)` and `α = ε/(16k²)`
  have hε13 : ε ≤ 1 / 3 := by linarith only [hε30]
  have hρ1 : ρ < 1 := by linarith only [hδ, hsum, hρε]
  obtain ⟨γ, hγdef⟩ : ∃ g : ℝ, g = ρ ^ 2 * ε / (1000 * (k : ℝ) ^ 2) := ⟨_, rfl⟩
  obtain ⟨α, hαdef⟩ : ∃ a : ℝ, a = ε / (16 * (k : ℝ) ^ 2) := ⟨_, rfl⟩
  have hρ2ρ : ρ ^ 2 ≤ ρ := Lemma1012ParamsGen.rho_sq_le hρpos hρ1.le
  have hγpos : 0 < γ := Lemma1012ParamsGen.gamma_pos hkR hε hρpos hγdef
  have hαpos : 0 < α := Lemma1012Params.alpha_pos hkR hε hαdef
  have hγε4 : γ ≤ ε / 4 := Lemma1012ParamsGen.gamma_le_eps4 hkR hε hρpos hρ1.le hγdef
  have hγk : γ * (k : ℝ) ≤ ρ ^ 2 / 2000 := Lemma1012Params.gamma_mul_k hkR hε hε13 hγdef
  have hγle : γ ≤ ρ ^ 2 / 2000 := Lemma1012ParamsGen.gamma_le hkR hε hε13 hρpos hγdef
  have hαsmall : α ≤ 1 / 1000 := Lemma1012Params.alpha_small hkR hε hε13 hαdef
  have hfinal : 3 * γ + 2 * α ≤ ε / (2 * (k : ℝ) ^ 2) :=
    Lemma1012ParamsGen.final_bound hkR hε hρpos hρ1.le hγdef hαdef
  obtain ⟨n72, H72⟩ := h72 k γ ρ hk0 hγpos hρpos hρ1
  obtain ⟨n93, H93⟩ := h93 k γ hk0 hγpos
  obtain ⟨n11, H11⟩ : Cor1011K3AtAlphaRho α ρ k := by rw [hαdef]; exact h1011
  obtain ⟨n06, H06⟩ := h106 γ ε k hγpos hγε4 hε hε13 hk0 hkε
  refine ⟨max (max n72 n93) (max n11 (max n06 (100 * k ^ 2))), ?_⟩
  intro V _ E G₀ S P hcard hloop hES hev hG₀ hpart
  have hn72 : n72 ≤ S.card := by omega
  have hn93 : n93 ≤ S.card := by omega
  have hn11 : n11 ≤ S.card := by omega
  have hn06 : n06 ≤ S.card := by omega
  have hnbig : 100 * k ^ 2 ≤ S.card := by omega
  set n : ℕ := S.card with hndef
  have hnR : (100 : ℝ) * (k : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hnbig
  set G : Finset (Sym2 V) := E \ G₀ with hGdef
  have hGE : G ⊆ E := Finset.sdiff_subset
  have hGloop : ∀ e ∈ G, ¬ e.IsDiag := fun e he => hloop e (hGE he)
  have hGS : G ⊆ cliqueEdges S := fun e he => hES (hGE he)
  obtain ⟨heqP, hdegG⟩ := hpart
  -- the crossing edges of `G` and of `E` agree, and the inside edges of `G` are those of `E`
  -- outside `G₀`
  have hcrossEG : crossParts G P = crossParts E P := by
    refine Finset.Subset.antisymm (crossParts_mono hGE) fun e he => ?_
    obtain ⟨heE, hnin⟩ := mem_crossParts.1 he
    exact mem_crossParts.2 ⟨Finset.mem_sdiff.2 ⟨heE, fun hc => hnin (mem_insideParts.1 (hG₀ hc)).2⟩,
      hnin⟩
  have hinsideG : insideParts G P = insideParts E P \ G₀ := by
    ext e
    simp only [mem_insideParts, Finset.mem_sdiff, hGdef]
    tauto
  -- sizes of the parts
  have hWlow : ∀ W ∈ P, (n : ℝ) / (k : ℝ) - 1 ≤ (W.card : ℝ) := by
    intro W hW
    have h1 : (n / k : ℕ) ≤ W.card := heqP.size_lower W hW
    have h2 : ((n / k : ℕ) : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast h1
    have h3 : (n : ℝ) < ((n / k : ℕ) : ℝ) * (k : ℝ) + (k : ℝ) := by
      have := Nat.lt_div_mul_add hk0 (a := n)
      exact_mod_cast this
    rw [sub_le_iff_le_add, div_le_iff₀ hkpos]
    linarith only [h3, mul_le_mul_of_nonneg_right h2 hkpos.le]
  have hnW : ∀ W ∈ P, (n : ℝ) ≤ (101 / 100) * (k : ℝ) * (W.card : ℝ) := by
    intro W hW
    have h1 := hWlow W hW
    have h2 : (n : ℝ) - (k : ℝ) ≤ (k : ℝ) * (W.card : ℝ) := by
      have : (k : ℝ) * ((n : ℝ) / (k : ℝ) - 1) ≤ (k : ℝ) * (W.card : ℝ) :=
        mul_le_mul_of_nonneg_left h1 hkpos.le
      rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hkpos)] at this
      linarith
    have h3 : (100 : ℝ) * (k : ℝ) ≤ (n : ℝ) / (k : ℝ) := by
      rw [le_div_iff₀ hkpos]; linarith only [hnR]
    have hWbig : (100 : ℝ) ≤ (W.card : ℝ) := by linarith only [h1, h3, hkR]
    linarith only [h2, mul_le_mul_of_nonneg_left hWbig hkpos.le]
  have hWn : ∀ W ∈ P, (W.card : ℝ) ≤ (n : ℝ) := by
    intro W hW
    exact_mod_cast Finset.card_le_card (heqP.subset_of_mem hW)
  -- an indexing of the parts
  set idx : Finset V → ℕ := partIdx P with hidxdef
  have hidx : ∀ W ∈ P, ∀ W' ∈ P, W ≠ W' → idx W ≠ idx W' :=
    fun W hW W' hW' hne => partIdx_inj hW hW' hne
  -- `γn` is negligible compared with `ρ²|W|`
  have hB1 : ∀ W ∈ P, γ * (n : ℝ) ≤ ρ ^ 2 * (W.card : ℝ) / 1000 := by
    intro W hW
    have hW0 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
    have h1 : γ * (n : ℝ) ≤ γ * ((101 / 100) * (k : ℝ) * (W.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (hnW W hW) hγpos.le
    have h2 : γ * ((101 / 100) * (k : ℝ) * (W.card : ℝ))
        = (101 / 100) * (γ * (k : ℝ)) * (W.card : ℝ) := by ring
    have h3 : (101 / 100) * (γ * (k : ℝ)) * (W.card : ℝ)
        ≤ (101 / 100) * (ρ ^ 2 / 2000) * (W.card : ℝ) := by
      refine mul_le_mul_of_nonneg_right ?_ hW0
      linarith
    linarith only [h1, h2, h3, mul_nonneg (sq_nonneg ρ) hW0]
  -- the density of `G` inside the parts
  have hdense : ∀ x ∈ S, ∀ W ∈ P, (9 / 10 : ℝ) * (W.card : ℝ) ≤ (degTo G x W : ℝ) := by
    intro x hx W hW
    have h1 : (9 / 10 : ℝ) * (W.card : ℝ) ≤ (δ + 3 * ε) * (W.card : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    exact le_trans h1 (hdegG x hx W hW)
  -- an edge from an earlier part into `W` is a crossing edge
  have hcrossnb : ∀ W ∈ P, ∀ x ∈ beforeParts P idx W, ∀ X : Finset (Sym2 V),
      nbhdIn (crossParts X P) x W = nbhdIn X x W := by
    intro W hW x hx X
    obtain ⟨W', hW', hlt, hxW'⟩ := mem_beforeParts.1 hx
    have hne : W ≠ W' := by rintro rfl; exact absurd hlt (lt_irrefl _)
    ext z
    simp only [mem_nbhdIn, mem_crossParts]
    constructor
    · rintro ⟨hz, he, -⟩; exact ⟨hz, he⟩
    · rintro ⟨hz, he⟩
      exact ⟨hz, he, not_inside_of_parts heqP hW hW' hne hxW' hz⟩
  -- **Step 1**: the `K₃`-parity graph
  obtain ⟨Ppar, hPparG, hPpar, hPpardeg⟩ :=
    H93 G S P idx (δ + 3 * ε) hn93 hGloop hGS (by linarith) ⟨heqP, hdegG⟩
  -- **Step 2**: the sparse random subgraph of the crossing edges
  obtain ⟨R, hRsub, hR1, hR2, hR3⟩ :=
    H72 (crossParts (G \ Ppar) P) (insideParts G P) S P hn72
      (fun e he => hGS (Finset.sdiff_subset (crossParts_subset _ _ he)))
      (fun e he => hGS (insideParts_subset _ _ he)) heqP
  have hRG : R ⊆ G := hRsub.trans ((crossParts_subset _ _).trans Finset.sdiff_subset)
  -- **Step 3**: Lemma 10.6 applied to `G' = G - Ppar - R`
  set G' : Finset (Sym2 V) := G \ (Ppar ∪ R) with hG'def
  have hG'G : G' ⊆ G := Finset.sdiff_subset
  have hG'part : IsKDeltaPartition k (δ + ε) P G' S := by
    refine ⟨heqP, fun x hx W hW => ?_⟩
    have hW0 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
    have hbase := hdegG x hx W hW
    have hsplit : degTo G x W ≤ degTo G' x W + degTo (Ppar ∪ R) x W := by
      rw [hG'def]; exact degTo_le_sdiff_add G (Ppar ∪ R) x W
    have hu : degTo (Ppar ∪ R) x W ≤ degTo Ppar x W + degTo R x W := degTo_union_le _ _ _ _
    have hcast : (degTo G x W : ℝ)
        ≤ (degTo G' x W : ℝ) + (degTo Ppar x W : ℝ) + (degTo R x W : ℝ) := by
      have : degTo G x W ≤ degTo G' x W + degTo Ppar x W + degTo R x W := by omega
      exact_mod_cast this
    have hPd : (degTo Ppar x W : ℝ) ≤ γ * (n : ℝ) :=
      le_trans (by exact_mod_cast degTo_le_edeg Ppar x W) (hPpardeg x)
    have hRd := hR1 x W hW
    have hRc : (degTo (crossParts (G \ Ppar) P) x W : ℝ) ≤ (W.card : ℝ) := by
      exact_mod_cast degTo_le_card (crossParts (G \ Ppar) P) x W
    have e3 : ρ * (degTo (crossParts (G \ Ppar) P) x W : ℝ) ≤ ρ * (W.card : ℝ) :=
      mul_le_mul_of_nonneg_left hRc hρpos.le
    have e1 : ρ * (W.card : ℝ) ≤ ε * (W.card : ℝ) := mul_le_mul_of_nonneg_right hρε hW0
    have e2 : ρ ^ 2 * (W.card : ℝ) ≤ ε * (W.card : ℝ) :=
      mul_le_mul_of_nonneg_right (le_trans hρ2ρ hρε) hW0
    have e4 : γ * (W.card : ℝ) ≤ ρ ^ 2 / 2000 * (W.card : ℝ) :=
      mul_le_mul_of_nonneg_right hγle hW0
    have hb1 := hB1 W hW
    linarith
  obtain ⟨H6, hH6sub, hD1dec, hH6cross, hH6in⟩ :=
    H06 G' S P hn06 (fun e he => hGloop e (hG'G he)) (fun e he => hGS (hG'G he)) hG'part
  set D1 : Finset (Sym2 V) := G' \ H6 with hD1def
  have hd1sub : ∀ W₀ : Finset V, edgesIn D1 W₀ ⊆ edgesIn G' W₀ \ edgesIn H6 W₀ := by
    intro W₀ e he
    rw [hD1def, mem_edgesIn] at he
    obtain ⟨hmem, hall⟩ := he
    obtain ⟨hG'm, hH6m⟩ := Finset.mem_sdiff.1 hmem
    exact Finset.mem_sdiff.2 ⟨mem_edgesIn.2 ⟨hG'm, hall⟩, fun hc => hH6m (mem_edgesIn.1 hc).1⟩
  -- the inside-part edges used by the Lemma 10.6 decomposition have small degree
  have hinsD1 : ∀ W₀ ∈ P, ∀ v ∈ W₀, (edeg (insideParts D1 P) v : ℝ) ≤ 2 * γ * (W₀.card : ℝ) := by
    intro W₀ hW₀ v hv
    refine le_trans ?_ (hH6in W₀ hW₀ v)
    exact_mod_cast le_trans (edeg_insideParts_le_edgesIn heqP hW₀ hv) (edeg_mono (hd1sub W₀) v)
  -- **Step 4**: the parity correction
  set Gstar : Finset (Sym2 V) := E \ (D1 ∪ Ppar) with hGstardef
  have hD1G' : D1 ⊆ G' := Finset.sdiff_subset
  have hD1G : D1 ⊆ G := hD1G'.trans hG'G
  have hD1E : D1 ⊆ E := hD1G.trans hGE
  have hPparE : Ppar ⊆ E := hPparG.trans hGE
  have hD1Ppar : Disjoint D1 Ppar := by
    refine Finset.disjoint_left.2 fun e he hePpar => ?_
    have h := hD1G' he
    rw [hG'def] at h
    exact (Finset.mem_sdiff.1 h).2 (Finset.mem_union_left _ hePpar)
  have hGstarEven : EvenDegrees Gstar := by
    rw [hGstardef]
    exact evenDegrees_sdiff (Finset.union_subset hD1E hPparE) hev
      (evenDegrees_union hD1Ppar (evenDegrees_of_triDecomp hD1dec)
        (evenDegrees_of_triDecomp hPpar.1))
  have hGstarDisj : Disjoint Gstar Ppar :=
    Finset.disjoint_left.2 fun e he heP => (Finset.mem_sdiff.1 he).2 (Finset.mem_union_right _ heP)
  have hGstarClique : Gstar ⊆ cliqueEdges (P.biUnion id) := by
    rw [heqP.cover, hGstardef]
    exact fun e he => hES (Finset.sdiff_subset he)
  obtain ⟨P', hP'sub, hD3dec, hP'par⟩ := hPpar.2 Gstar hGstarClique hGstarDisj hGstarEven
  -- **Step 5**: Corollary 10.11 covers the remaining crossing edges
  set Iav : Finset (Sym2 V) := insideParts (G \ (D1 ∪ Ppar)) P with hIavdef
  set Xc : Finset (Sym2 V) := crossParts (Gstar ∪ P') P with hXcdef
  set Hcov : Finset (Sym2 V) := Xc ∪ Iav with hHcovdef
  have hGstarE : Gstar ⊆ E := Finset.sdiff_subset
  have hP'E : P' ⊆ E := hP'sub.trans hPparE
  have hXcE : Xc ⊆ E := (crossParts_subset _ _).trans (Finset.union_subset hGstarE hP'E)
  have hIavG : Iav ⊆ G := (insideParts_subset _ _).trans Finset.sdiff_subset
  have hIavIn : Iav ⊆ insideParts E P :=
    (insideParts_mono (Finset.sdiff_subset.trans hGE) : Iav ⊆ insideParts E P)
  have hHcovE : Hcov ⊆ E := Finset.union_subset hXcE (hIavG.trans hGE)
  have hcrossHcov : crossParts Hcov P = Xc := by
    ext e
    simp only [hHcovdef, hXcdef, mem_crossParts, Finset.mem_union]
    constructor
    · rintro ⟨he | he, hnin⟩
      · exact he
      · exact absurd (mem_insideParts.1 (hIavIn he)).2 hnin
    · intro he
      exact ⟨Or.inl he, he.2⟩
  have hinsideHcov : insideParts Hcov P = Iav := by
    ext e
    simp only [hHcovdef, mem_insideParts, Finset.mem_union]
    constructor
    · rintro ⟨he | he, hin⟩
      · exact absurd hin (mem_crossParts.1 he).2
      · exact he
    · intro he
      exact ⟨Or.inr he, (mem_insideParts.1 (hIavIn he)).2⟩
  have hHcovloop : ∀ e ∈ Hcov, ¬ e.IsDiag := fun e he => hloop e (hHcovE he)
  have hHcovS : Hcov ⊆ cliqueEdges S := fun e he => hES (hHcovE he)
  -- degree bounds in terms of `n = |S|` rather than of `S.card`
  have hPpardegn : ∀ v : V, (edeg Ppar v : ℝ) ≤ γ * (n : ℝ) := by rw [hndef]; exact hPpardeg
  have hH6crossn : ∀ v : V, (edeg (crossParts H6 P) v : ℝ) ≤ γ * (n : ℝ) := by
    rw [hndef]; exact hH6cross
  have hR3n : ∀ (x y : V) (W : Finset V), W ∈ P →
      ρ * (degTo (insideParts G P) y (nbhdIn (crossParts (G \ Ppar) P) x W) : ℝ) - γ * (n : ℝ)
        ≤ (degTo (insideParts G P) y (nbhdIn R x W) : ℝ) := by rw [hndef]; exact hR3
  -- `R` survives in `Gstar`
  have hRGstar : R ⊆ Gstar := by
    intro e he
    rw [hGstardef]
    refine Finset.mem_sdiff.2 ⟨hGE (hRG he), ?_⟩
    intro hc
    rcases Finset.mem_union.1 hc with h | h
    · have h' := hD1G' h
      rw [hG'def] at h'
      exact (Finset.mem_sdiff.1 h').2 (Finset.mem_union_right _ he)
    · have h' : e ∈ G \ Ppar := (crossParts_subset _ _) (hRsub he)
      exact (Finset.mem_sdiff.1 h').2 h
  -- the crossing edges left over are those of `H₆`, of `R`, and of the parity correction
  have hXcsub : Xc ⊆ crossParts H6 P ∪ R ∪ P' := by
    intro e he
    rw [hXcdef] at he
    obtain ⟨hmem, hncross⟩ := mem_crossParts.1 he
    rcases Finset.mem_union.1 hmem with hg | hp
    · rw [hGstardef] at hg
      obtain ⟨heE, hnd⟩ := Finset.mem_sdiff.1 hg
      have heG : e ∈ G :=
        Finset.mem_sdiff.2 ⟨heE, fun hc => hncross (mem_insideParts.1 (hG₀ hc)).2⟩
      by_cases hR : e ∈ R
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hR)
      · have hG'mem : e ∈ G' := by
          rw [hG'def]
          refine Finset.mem_sdiff.2 ⟨heG, ?_⟩
          intro hc
          rcases Finset.mem_union.1 hc with h | h
          · exact hnd (Finset.mem_union_right _ h)
          · exact hR h
        have hH6mem : e ∈ H6 := by
          by_contra hc
          have : e ∈ D1 := by rw [hD1def]; exact Finset.mem_sdiff.2 ⟨hG'mem, hc⟩
          exact hnd (Finset.mem_union_left _ this)
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (mem_crossParts.2 ⟨hH6mem, hncross⟩))
    · exact Finset.mem_union_right _ hp
  -- from an earlier part, `Hcov` and its crossing part have the same neighbourhood in `W`
  have hHcovnb : ∀ W ∈ P, ∀ x ∈ beforeParts P idx W, nbhdIn Hcov x W = nbhdIn Xc x W := by
    intro W hW x hx
    obtain ⟨W', hW', hlt, hxW'⟩ := mem_beforeParts.1 hx
    have hne : W ≠ W' := by rintro rfl; exact absurd hlt (lt_irrefl _)
    ext z
    simp only [mem_nbhdIn]
    constructor
    · rintro ⟨hz, he⟩
      refine ⟨hz, ?_⟩
      rw [hHcovdef] at he
      rcases Finset.mem_union.1 he with h | h
      · exact h
      · rw [hIavdef] at h
        exact absurd (mem_insideParts.1 h).2 (not_inside_of_parts heqP hW hW' hne hxW' hz)
    · rintro ⟨hz, he⟩
      exact ⟨hz, by rw [hHcovdef]; exact Finset.mem_union_left _ he⟩
  -- the crossing degrees into a part are `≈ ρ|W|`
  have hdegXc : ∀ (x : V) (W : Finset V), W ∈ P →
      (degTo Xc x W : ℝ) ≤ ρ * (W.card : ℝ) + γ * (W.card : ℝ) + 2 * (γ * (n : ℝ)) := by
    intro x W hW
    have h1 : degTo Xc x W ≤ degTo (crossParts H6 P ∪ R) x W + degTo P' x W :=
      le_trans (degTo_mono_left hXcsub x W) (degTo_union_le _ _ _ _)
    have h2 : degTo (crossParts H6 P ∪ R) x W ≤ degTo (crossParts H6 P) x W + degTo R x W :=
      degTo_union_le _ _ _ _
    have h3 : (degTo (crossParts H6 P) x W : ℝ) ≤ γ * (n : ℝ) :=
      le_trans (by exact_mod_cast degTo_le_edeg (crossParts H6 P) x W) (hH6crossn x)
    have h4 : (degTo P' x W : ℝ) ≤ γ * (n : ℝ) := by
      refine le_trans ?_ (hPpardegn x)
      exact_mod_cast le_trans (degTo_le_edeg P' x W) (edeg_mono hP'sub x)
    have h5 := hR1 x W hW
    have h6 : (degTo (crossParts (G \ Ppar) P) x W : ℝ) ≤ (W.card : ℝ) := by
      exact_mod_cast degTo_le_card (crossParts (G \ Ppar) P) x W
    have h7 : ρ * (degTo (crossParts (G \ Ppar) P) x W : ℝ) ≤ ρ * (W.card : ℝ) :=
      mul_le_mul_of_nonneg_left h6 hρpos.le
    have hcast : (degTo Xc x W : ℝ)
        ≤ (degTo (crossParts H6 P) x W : ℝ) + (degTo R x W : ℝ) + (degTo P' x W : ℝ) := by
      have : degTo Xc x W ≤ degTo (crossParts H6 P) x W + degTo R x W + degTo P' x W := by omega
      exact_mod_cast this
    linarith
  have cond1 : ∀ W ∈ P, ∀ x ∈ beforeParts P idx W, 2 ∣ degTo Hcov x W := by
    intro W hW x hx
    have h1 : degTo Hcov x W = degTo (Gstar ∪ P') x W := by
      rw [degTo, degTo, hHcovnb W hW x hx, hXcdef, hcrossnb W hW x hx]
    rw [h1]
    exact (hP'par W hW x hx).two_dvd
  have cond2 : ∀ W ∈ P, ∀ x ∈ beforeParts P idx W, ∀ y ∈ nbhdIn Hcov x W,
      (1 / 2 : ℝ) * (degTo Hcov x W : ℝ) + 18 * (k : ℝ) * Real.sqrt ρ ^ 3 * (W.card : ℝ)
        ≤ (degTo Hcov y (nbhdIn Hcov x W) : ℝ) := by
    intro W hW x hx y hy
    have hW0 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
    have hyW : y ∈ W := nbhdIn_subset _ _ _ hy
    have hyS : y ∈ S := heqP.subset_of_mem hW hyW
    obtain ⟨W', hW'P, hlt, hxW'⟩ := mem_beforeParts.1 hx
    have hxS : x ∈ S := heqP.subset_of_mem hW'P hxW'
    -- the left-hand side is `≈ ρ|W|/2`
    have hLHS : (degTo Hcov x W : ℝ) ≤ ρ * (W.card : ℝ) + γ * (W.card : ℝ) + 2 * (γ * (n : ℝ)) := by
      have e1 : degTo Hcov x W = degTo Xc x W := by unfold degTo; rw [hHcovnb W hW x hx]
      rw [e1]; exact hdegXc x W hW
    -- the `R`-neighbourhood of `x` in `W` is available
    have hNeq : nbhdIn Hcov x W = nbhdIn (Gstar ∪ P') x W := by
      rw [hHcovnb W hW x hx, hXcdef, hcrossnb W hW x hx]
    have hNsub : nbhdIn R x W ⊆ nbhdIn Hcov x W := by
      rw [hNeq]
      exact nbhdIn_mono_left (fun e he => Finset.mem_union_left _ (hRGstar he)) x W
    have hIavHcov : Iav ⊆ Hcov := by rw [hHcovdef]; exact Finset.subset_union_right
    have hA : degTo Iav y (nbhdIn R x W) ≤ degTo Hcov y (nbhdIn Hcov x W) :=
      le_trans (degTo_mono_left hIavHcov y _) (degTo_mono_right hNsub y)
    -- the inside-part edges of `G` that neither `D₁` nor the parity graph use are available
    have hIavsub : insideParts G P \ (insideParts D1 P ∪ Ppar) ⊆ Iav := by
      intro e he
      obtain ⟨hin, hnot⟩ := Finset.mem_sdiff.1 he
      obtain ⟨heG, hW''⟩ := mem_insideParts.1 hin
      rw [hIavdef]
      refine mem_insideParts.2 ⟨Finset.mem_sdiff.2 ⟨heG, ?_⟩, hW''⟩
      intro hc
      rcases Finset.mem_union.1 hc with h | h
      · exact hnot (Finset.mem_union_left _ (mem_insideParts.2 ⟨h, hW''⟩))
      · exact hnot (Finset.mem_union_right _ h)
    have hB : degTo (insideParts G P) y (nbhdIn R x W)
        ≤ degTo Iav y (nbhdIn R x W) + edeg (insideParts D1 P ∪ Ppar) y := by
      refine le_trans (degTo_sdiff_ge (insideParts G P) (insideParts D1 P ∪ Ppar) y _) ?_
      exact Nat.add_le_add_right (degTo_mono_left hIavsub y _) _
    have hBd : (edeg (insideParts D1 P ∪ Ppar) y : ℝ) ≤ 2 * γ * (W.card : ℝ) + γ * (n : ℝ) := by
      have h1 : (edeg (insideParts D1 P ∪ Ppar) y : ℝ)
          ≤ (edeg (insideParts D1 P) y : ℝ) + (edeg Ppar y : ℝ) := by
        exact_mod_cast edeg_union_le_sum (insideParts D1 P) Ppar y
      have h2 := hinsD1 W hW y hyW
      have h3 := hPpardegn y
      linarith
    -- the codegree of `y` with the crossing neighbourhood of `x`
    have hAcap : degTo (insideParts G P) y (nbhdIn (crossParts (G \ Ppar) P) x W)
        = (nbhdIn (insideParts G P) y W ∩ nbhdIn (crossParts (G \ Ppar) P) x W).card := by
      unfold degTo
      congr 1
      ext z
      simp only [mem_nbhdIn, Finset.mem_inter]
      constructor
      · rintro ⟨hz, he⟩
        exact ⟨⟨hz.1, he⟩, hz⟩
      · rintro ⟨⟨-, he⟩, hz⟩
        exact ⟨hz, he⟩
    have hDlow : (8 / 10 : ℝ) * (W.card : ℝ) - γ * (n : ℝ)
        ≤ (degTo (insideParts G P) y (nbhdIn (crossParts (G \ Ppar) P) x W) : ℝ) := by
      have hcap := card_inter_nbhd_ge (X := insideParts G P) (x := y)
        (Y := crossParts (G \ Ppar) P) (y := x) (W := W)
      have h1 : (9 / 10 : ℝ) * (W.card : ℝ) ≤ ((nbhdIn (insideParts G P) y W).card : ℝ) := by
        rw [nbhdIn_insideParts_eq hW hyW]
        exact hdense y hyS W hW
      have h2 : (9 / 10 : ℝ) * (W.card : ℝ) - γ * (n : ℝ)
          ≤ ((nbhdIn (crossParts (G \ Ppar) P) x W).card : ℝ) := by
        rw [hcrossnb W hW x hx]
        have h3 : (degTo G x W : ℝ) - (edeg Ppar x : ℝ) ≤ (degTo (G \ Ppar) x W : ℝ) :=
          degTo_sdiff_le G Ppar x W
        have h4 := hdense x hxS W hW
        have h5 := hPpardegn x
        have h6 : (degTo (G \ Ppar) x W : ℝ) = ((nbhdIn (G \ Ppar) x W).card : ℝ) := rfl
        linarith
      rw [hAcap]
      linarith
    have hρmul : ρ * ((8 / 10 : ℝ) * (W.card : ℝ) - γ * (n : ℝ))
        ≤ ρ * (degTo (insideParts G P) y (nbhdIn (crossParts (G \ Ppar) P) x W) : ℝ) :=
      mul_le_mul_of_nonneg_left hDlow hρpos.le
    have hC := hR3n x y W hW
    have hBcast : (degTo (insideParts G P) y (nbhdIn R x W) : ℝ)
        ≤ (degTo Iav y (nbhdIn R x W) : ℝ) + (edeg (insideParts D1 P ∪ Ppar) y : ℝ) := by
      exact_mod_cast hB
    have hAcast : (degTo Iav y (nbhdIn R x W) : ℝ) ≤ (degTo Hcov y (nbhdIn Hcov x W) : ℝ) := by
      exact_mod_cast hA
    -- the numerics
    have t1 : γ * (W.card : ℝ) ≤ ρ ^ 2 / 2000 * (W.card : ℝ) :=
      mul_le_mul_of_nonneg_right hγle hW0
    have t2 := hB1 W hW
    have t3a := mul_le_mul_of_nonneg_left t2 hρpos.le
    have t3b : ρ * (ρ ^ 2 * (W.card : ℝ) / 1000) ≤ ρ ^ 2 * (W.card : ℝ) / 1000 := by
      linarith only [mul_nonneg (mul_nonneg (sq_nonneg ρ) hW0)
        (show (0 : ℝ) ≤ 1 - ρ by linarith only [hρ1])]
    have t4 : ρ ^ 2 * (W.card : ℝ) ≤ ρ * (W.card : ℝ) := mul_le_mul_of_nonneg_right hρ2ρ hW0
    have h18W : 18 * (k : ℝ) * Real.sqrt ρ ^ 3 * (W.card : ℝ) ≤ ρ / 4 * (W.card : ℝ) :=
      mul_le_mul_of_nonneg_right h18 hW0
    linarith
  have cond3 : ∀ W ∈ P, ∀ x ∈ beforeParts P idx W, ∀ x' ∈ beforeParts P idx W, x ≠ x' →
      (codegTo Hcov x x' W : ℝ) ≤ 2 * ρ ^ 2 * (W.card : ℝ) := by
    intro W hW x hx x' hx' hxx'
    have hW0 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
    -- every `Hcov`-neighbour in `W` is an `R`-neighbour or a neighbour in `H₆ ∪ P'`
    have hB : ∀ (z x₀ : V), x₀ ∈ beforeParts P idx W → z ∈ nbhdIn Hcov x₀ W →
        z ∈ nbhdIn R x₀ W ∪ nbhdIn (crossParts H6 P ∪ P') x₀ W := by
      intro z x₀ hx₀ hz
      rw [hHcovnb W hW x₀ hx₀, mem_nbhdIn] at hz
      rcases Finset.mem_union.1 (hXcsub hz.2) with h | h
      · rcases Finset.mem_union.1 h with h' | h'
        · exact Finset.mem_union_right _ (mem_nbhdIn.2 ⟨hz.1, Finset.mem_union_left _ h'⟩)
        · exact Finset.mem_union_left _ (mem_nbhdIn.2 ⟨hz.1, h'⟩)
      · exact Finset.mem_union_right _ (mem_nbhdIn.2 ⟨hz.1, Finset.mem_union_right _ h⟩)
    have hsub : nbhdIn Hcov x W ∩ nbhdIn Hcov x' W ⊆
        (nbhdIn R x W ∩ nbhdIn R x' W) ∪
          (nbhdIn (crossParts H6 P ∪ P') x W ∪ nbhdIn (crossParts H6 P ∪ P') x' W) := by
      intro z hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_inter.1 hz
      rcases Finset.mem_union.1 (hB z x hx hz1) with h1 | h1
      · rcases Finset.mem_union.1 (hB z x' hx' hz2) with h2 | h2
        · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨h1, h2⟩)
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ h2)
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ h1)
    have hcard : codegTo Hcov x x' W ≤ codegTo R x x' W
        + (degTo (crossParts H6 P ∪ P') x W + degTo (crossParts H6 P ∪ P') x' W) := by
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (nbhdIn R x W ∩ nbhdIn R x' W)
        (nbhdIn (crossParts H6 P ∪ P') x W ∪ nbhdIn (crossParts H6 P ∪ P') x' W)
      have h3 := Finset.card_union_le (nbhdIn (crossParts H6 P ∪ P') x W)
        (nbhdIn (crossParts H6 P ∪ P') x' W)
      unfold codegTo degTo
      omega
    have hBd : ∀ x₀ : V, (degTo (crossParts H6 P ∪ P') x₀ W : ℝ) ≤ 2 * (γ * (n : ℝ)) := by
      intro x₀
      have h1 : (degTo (crossParts H6 P ∪ P') x₀ W : ℝ)
          ≤ (degTo (crossParts H6 P) x₀ W : ℝ) + (degTo P' x₀ W : ℝ) := by
        exact_mod_cast degTo_union_le (crossParts H6 P) P' x₀ W
      have h2 : (degTo (crossParts H6 P) x₀ W : ℝ) ≤ γ * (n : ℝ) :=
        le_trans (by exact_mod_cast degTo_le_edeg (crossParts H6 P) x₀ W) (hH6crossn x₀)
      have h3 : (degTo P' x₀ W : ℝ) ≤ γ * (n : ℝ) := by
        refine le_trans ?_ (hPpardegn x₀)
        exact_mod_cast le_trans (degTo_le_edeg P' x₀ W) (edeg_mono hP'sub x₀)
      linarith
    have hcodle : (codegTo (crossParts (G \ Ppar) P) x x' W : ℝ) ≤ (W.card : ℝ) := by
      have : codegTo (crossParts (G \ Ppar) P) x x' W ≤ W.card :=
        Finset.card_le_card ((Finset.inter_subset_left).trans (nbhdIn_subset _ _ _))
      exact_mod_cast this
    have hRcod := hR2 x x' W hxx' hW
    have hRcod2 : ρ ^ 2 * (codegTo (crossParts (G \ Ppar) P) x x' W : ℝ)
        ≤ ρ ^ 2 * (W.card : ℝ) := mul_le_mul_of_nonneg_left hcodle (sq_nonneg ρ)
    have hcardR : (codegTo Hcov x x' W : ℝ) ≤ (codegTo R x x' W : ℝ)
        + ((degTo (crossParts H6 P ∪ P') x W : ℝ) + (degTo (crossParts H6 P ∪ P') x' W : ℝ)) := by
      exact_mod_cast hcard
    have e4 : γ * (W.card : ℝ) ≤ ρ ^ 2 / 2000 * (W.card : ℝ) :=
      mul_le_mul_of_nonneg_right hγle hW0
    have hb1 := hB1 W hW
    have := hBd x
    have := hBd x'
    linarith
  have cond4 : ∀ W ∈ P, ∀ y ∈ W,
      (degTo Hcov y (beforeParts P idx W) : ℝ) ≤ 2 * (k : ℝ) * ρ * (W.card : ℝ) := by
    intro W hW y hy
    have hW0 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
    -- edges from `y ∈ W` to earlier parts are crossing edges
    have hnb : nbhdIn Hcov y (beforeParts P idx W) = nbhdIn Xc y (beforeParts P idx W) := by
      ext z
      simp only [mem_nbhdIn]
      constructor
      · rintro ⟨hz, he⟩
        obtain ⟨W'', hW''P, hlt, hzW''⟩ := mem_beforeParts.1 hz
        have hne : W'' ≠ W := by rintro rfl; exact absurd hlt (lt_irrefl _)
        refine ⟨hz, ?_⟩
        rw [hHcovdef] at he
        rcases Finset.mem_union.1 he with h | h
        · exact h
        · rw [hIavdef] at h
          exact absurd (mem_insideParts.1 h).2 (not_inside_of_parts heqP hW''P hW hne hy hzW'')
      · rintro ⟨hz, he⟩
        exact ⟨hz, by rw [hHcovdef]; exact Finset.mem_union_left _ he⟩
    have h0 : (degTo Hcov y (beforeParts P idx W) : ℝ)
        = ∑ W' ∈ P.filter (fun W' => idx W' < idx W), (degTo Xc y W' : ℝ) := by
      have e1 : degTo Hcov y (beforeParts P idx W) = degTo Xc y (beforeParts P idx W) := by
        unfold degTo; rw [hnb]
      rw [e1, degTo_beforeParts_eq_sum heqP idx Xc y W, Nat.cast_sum]
    have hbound : ∑ W' ∈ P.filter (fun W' => idx W' < idx W), (degTo Xc y W' : ℝ)
        ≤ ∑ W' ∈ P.filter (fun W' => idx W' < idx W),
            ((ρ + γ) * (W'.card : ℝ) + 2 * (γ * (n : ℝ))) := by
      refine Finset.sum_le_sum fun W' hW' => ?_
      have := hdegXc y W' (Finset.mem_filter.1 hW').1
      linarith
    have heval : ∑ W' ∈ P.filter (fun W' => idx W' < idx W),
          ((ρ + γ) * (W'.card : ℝ) + 2 * (γ * (n : ℝ)))
        = (ρ + γ) * (∑ W' ∈ P.filter (fun W' => idx W' < idx W), (W'.card : ℝ))
          + ((P.filter (fun W' => idx W' < idx W)).card : ℝ) * (2 * (γ * (n : ℝ))) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have hsc : ∑ W' ∈ P, W'.card = n := by rw [hndef]; exact sum_card_parts heqP
    have hsumcard : ∑ W' ∈ P.filter (fun W' => idx W' < idx W), (W'.card : ℝ) ≤ (n : ℝ) := by
      have h1 : ∑ W' ∈ P, (W'.card : ℝ) = (n : ℝ) := by exact_mod_cast congrArg Nat.cast hsc
      have h2 : ∑ W' ∈ P.filter (fun W' => idx W' < idx W), (W'.card : ℝ)
          ≤ ∑ W' ∈ P, (W'.card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => Nat.cast_nonneg _)
      linarith
    have hFk : ((P.filter (fun W' => idx W' < idx W)).card : ℝ) ≤ (k : ℝ) := by
      have : (P.filter (fun W' => idx W' < idx W)).card ≤ k := by
        rw [← heqP.card_parts]; exact Finset.card_filter_le _ _
      exact_mod_cast this
    have hprod : (ρ + γ) * (∑ W' ∈ P.filter (fun W' => idx W' < idx W), (W'.card : ℝ))
        ≤ (ρ + γ) * (n : ℝ) := by
      refine mul_le_mul_of_nonneg_left hsumcard ?_
      linarith
    have hFprod : ((P.filter (fun W' => idx W' < idx W)).card : ℝ) * (2 * (γ * (n : ℝ)))
        ≤ (k : ℝ) * (2 * (γ * (n : ℝ))) := by
      refine mul_le_mul_of_nonneg_right hFk ?_
      have hn0' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith only [mul_nonneg hγpos.le hn0']
    -- the numerics
    have f1 := mul_le_mul_of_nonneg_left (hnW W hW) hρpos.le
    have f2 := hB1 W hW
    have f3 := mul_le_mul_of_nonneg_left (hB1 W hW) hkpos.le
    have f4 : ρ ^ 2 * (W.card : ℝ) ≤ ρ * (W.card : ℝ) := mul_le_mul_of_nonneg_right hρ2ρ hW0
    have f5 := mul_le_mul_of_nonneg_left f4 hkpos.le
    have f6 : ρ * (W.card : ℝ) ≤ (k : ℝ) * (ρ * (W.card : ℝ)) := by
      linarith only [mul_nonneg (mul_nonneg hρpos.le hW0)
        (show (0 : ℝ) ≤ (k : ℝ) - 1 by linarith only [hkR])]
    have f7 : γ * (n : ℝ) ≤ ρ * (W.card : ℝ) := by linarith [mul_nonneg hρpos.le hW0]
    linarith
  have cond5 : ∀ W ∈ P, ∀ y ∈ W,
      ((1 : ℝ) / 2 + 2 * α) * (W.card : ℝ) ≤ (degTo Hcov y W : ℝ) := by
    intro W hW y hy
    have hW0 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
    have hyS : y ∈ S := heqP.subset_of_mem hW hy
    have hIavHcov : Iav ⊆ Hcov := by rw [hHcovdef]; exact Finset.subset_union_right
    have h1 : degTo Iav y W ≤ degTo Hcov y W := degTo_mono_left hIavHcov y W
    have h2 : degTo Iav y W = degTo (G \ (D1 ∪ Ppar)) y W := by
      rw [hIavdef]; exact degTo_insideParts_eq hW hy
    have h3 : (degTo G y W : ℝ)
        ≤ (degTo (G \ (D1 ∪ Ppar)) y W : ℝ) + (degTo (D1 ∪ Ppar) y W : ℝ) := by
      exact_mod_cast degTo_le_sdiff_add G (D1 ∪ Ppar) y W
    have h4 : (degTo (D1 ∪ Ppar) y W : ℝ) ≤ (degTo D1 y W : ℝ) + (degTo Ppar y W : ℝ) := by
      exact_mod_cast degTo_union_le D1 Ppar y W
    have h5 : (degTo D1 y W : ℝ) ≤ 2 * γ * (W.card : ℝ) := by
      refine le_trans ?_ (hH6in W hW y)
      exact_mod_cast le_trans (degTo_le_edeg_edgesIn_mem hy) (edeg_mono (hd1sub W) y)
    have h6 : (degTo Ppar y W : ℝ) ≤ γ * (n : ℝ) :=
      le_trans (by exact_mod_cast degTo_le_edeg Ppar y W) (hPpardegn y)
    have h7 := hdense y hyS W hW
    have hb1 := hB1 W hW
    have hρsq1 : ρ ^ 2 ≤ 1 := by nlinarith only [hρpos.le, hρ1]
    have e4 : γ * (W.card : ℝ) ≤ ρ ^ 2 / 2000 * (W.card : ℝ) :=
      mul_le_mul_of_nonneg_right hγle hW0
    have e5 : ρ ^ 2 * (W.card : ℝ) ≤ (W.card : ℝ) := by
      linarith only [mul_le_mul_of_nonneg_right hρsq1 hW0]
    have e6 : 2 * α * (W.card : ℝ) ≤ 2 * (1 / 1000 : ℝ) * (W.card : ℝ) := by
      linarith only [mul_le_mul_of_nonneg_right hαsmall hW0]
    have hcast : (degTo Iav y W : ℝ) ≤ (degTo Hcov y W : ℝ) := by exact_mod_cast h1
    have hcast2 : (degTo Iav y W : ℝ) = (degTo (G \ (D1 ∪ Ppar)) y W : ℝ) := by
      exact_mod_cast congrArg Nat.cast h2
    linarith
  obtain ⟨H0, hH0sub, hD2dec, hH0deg⟩ :=
    H11 Hcov S P idx hn11 hHcovloop hHcovS heqP hidx cond1 cond2 cond3 cond4 cond5
  rw [hinsideHcov] at hH0sub
  rw [hcrossHcov] at hD2dec
  -- **Step 6**: the three triangle-decomposable graphs assemble to `crossParts E P ∪ H`
  have hH0I : H0 ⊆ insideParts E P := hH0sub.trans hIavIn
  have hH0D1 : Disjoint H0 D1 := by
    refine Finset.disjoint_left.2 fun e he heD => ?_
    have h1 : e ∈ G \ (D1 ∪ Ppar) := insideParts_subset _ _ (hH0sub he)
    exact (Finset.mem_sdiff.1 h1).2 (Finset.mem_union_left _ heD)
  have hH0Ppar : Disjoint H0 Ppar := by
    refine Finset.disjoint_left.2 fun e he heD => ?_
    have h1 : e ∈ G \ (D1 ∪ Ppar) := insideParts_subset _ _ (hH0sub he)
    exact (Finset.mem_sdiff.1 h1).2 (Finset.mem_union_right _ heD)
  have hXcD1 : Disjoint Xc D1 := by
    refine Finset.disjoint_left.2 fun e he heD => ?_
    have h1 : e ∈ Gstar ∪ P' := crossParts_subset _ _ he
    rcases Finset.mem_union.1 h1 with h | h
    · exact (Finset.mem_sdiff.1 h).2 (Finset.mem_union_left _ heD)
    · exact (Finset.disjoint_left.1 hD1Ppar) heD (hP'sub h)
  have hXcPpar : Disjoint Xc (Ppar \ P') := by
    refine Finset.disjoint_left.2 fun e he heD => ?_
    have h1 : e ∈ Gstar ∪ P' := crossParts_subset _ _ he
    rcases Finset.mem_union.1 h1 with h | h
    · exact (Finset.mem_sdiff.1 h).2 (Finset.mem_union_right _ (Finset.mem_sdiff.1 heD).1)
    · exact (Finset.mem_sdiff.1 heD).2 h
  have hdec : TriDecomp ((D1 ∪ (Xc ∪ H0)) ∪ (Ppar \ P')) := by
    refine TriDecomp.union ?_ (TriDecomp.union ?_ hD1dec hD2dec) hD3dec
    · refine Finset.disjoint_union_left.2 ⟨?_, ?_⟩
      · exact Finset.disjoint_of_subset_right (Finset.sdiff_subset) hD1Ppar
      · exact Finset.disjoint_union_left.2 ⟨hXcPpar,
          Finset.disjoint_of_subset_right (Finset.sdiff_subset) hH0Ppar⟩
    · exact Finset.disjoint_union_right.2 ⟨hXcD1.symm, hH0D1.symm⟩
  refine ⟨insideParts D1 P ∪ H0 ∪ insideParts (Ppar \ P') P, ?_, ?_, ?_⟩
  · -- the inside-part edges used lie in `insideParts E P \ G₀`
    rw [← hinsideG]
    refine Finset.union_subset (Finset.union_subset (insideParts_mono hD1G) ?_)
      (insideParts_mono ((Finset.sdiff_subset).trans hPparG))
    exact hH0sub.trans (insideParts_mono (Finset.sdiff_subset))
  · -- the triangle decomposition
    have hset : crossParts E P ∪ (insideParts D1 P ∪ H0 ∪ insideParts (Ppar \ P') P)
        = (D1 ∪ (Xc ∪ H0)) ∪ (Ppar \ P') := by
      have hinsD1 : insideParts D1 P = D1 ∩ insideParts E P := insideParts_eq_inter hD1E
      have hinsPp : insideParts (Ppar \ P') P = (Ppar \ P') ∩ insideParts E P :=
        insideParts_eq_inter ((Finset.sdiff_subset).trans hPparE)
      have hEsplit : crossParts E P ∪ insideParts E P = E := crossParts_union_insideParts E P
      apply Finset.Subset.antisymm
      · intro e he
        rcases Finset.mem_union.1 he with hC | hH
        · by_cases hD : e ∈ D1
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ hD)
          · by_cases hP : e ∈ Ppar
            · by_cases hP' : e ∈ P'
              · refine Finset.mem_union_left _ (Finset.mem_union_right _
                  (Finset.mem_union_left _ ?_))
                exact mem_crossParts.2 ⟨Finset.mem_union_right _ hP', (mem_crossParts.1 hC).2⟩
              · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hP, hP'⟩)
            · refine Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_union_left _ ?_))
              refine mem_crossParts.2 ⟨Finset.mem_union_left _ ?_, (mem_crossParts.1 hC).2⟩
              exact Finset.mem_sdiff.2 ⟨(mem_crossParts.1 hC).1, by
                simp only [Finset.mem_union]; tauto⟩
        · rcases Finset.mem_union.1 hH with hH' | hins
          · rcases Finset.mem_union.1 hH' with hins | hH0
            · rw [hinsD1] at hins
              exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.1 hins).1)
            · exact Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_union_right _ hH0))
          · rw [hinsPp] at hins
            exact Finset.mem_union_right _ (Finset.mem_inter.1 hins).1
      · intro e he
        rcases Finset.mem_union.1 he with h | h
        · rcases Finset.mem_union.1 h with hD | h'
          · have heE : e ∈ E := hD1E hD
            rcases Finset.mem_union.1 (hEsplit ▸ heE) with hC | hI
            · exact Finset.mem_union_left _ hC
            · refine Finset.mem_union_right _ (Finset.mem_union_left _
                (Finset.mem_union_left _ ?_))
              rw [hinsD1]
              exact Finset.mem_inter.2 ⟨hD, hI⟩
          · rcases Finset.mem_union.1 h' with hXc | hH0
            · refine Finset.mem_union_left _ ?_
              have : e ∈ E := hXcE hXc
              exact mem_crossParts.2 ⟨this, (mem_crossParts.1 hXc).2⟩
            · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ hH0))
        · have heE : e ∈ E := hPparE (Finset.mem_sdiff.1 h).1
          rcases Finset.mem_union.1 (hEsplit ▸ heE) with hC | hI
          · exact Finset.mem_union_left _ hC
          · refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
            rw [hinsPp]
            exact Finset.mem_inter.2 ⟨h, hI⟩
    rw [hset]
    exact hdec
  · -- the degree bound
    intro v
    have hcast : (edeg (insideParts D1 P ∪ H0 ∪ insideParts (Ppar \ P') P) v : ℝ)
        ≤ (edeg (insideParts D1 P) v : ℝ) + (edeg H0 v : ℝ)
          + (edeg (insideParts (Ppar \ P') P) v : ℝ) := by
      have h1 := edeg_union_le_sum (insideParts D1 P ∪ H0) (insideParts (Ppar \ P') P) v
      have h2 := edeg_union_le_sum (insideParts D1 P) H0 v
      have h3 : edeg (insideParts D1 P ∪ H0 ∪ insideParts (Ppar \ P') P) v
          ≤ edeg (insideParts D1 P) v + edeg H0 v + edeg (insideParts (Ppar \ P') P) v := by omega
      exact_mod_cast h3
    have hA : (edeg (insideParts D1 P) v : ℝ) ≤ 2 * γ * (n : ℝ) := by
      by_cases hv : ∃ W₀ ∈ P, v ∈ W₀
      · obtain ⟨W₀, hW₀, hvW₀⟩ := hv
        have h1 := hinsD1 W₀ hW₀ v hvW₀
        have h2 : (W₀.card : ℝ) ≤ (n : ℝ) := hWn W₀ hW₀
        linarith only [h1, mul_le_mul_of_nonneg_left h2 hγpos.le]
      · push_neg at hv
        rw [edeg_insideParts_eq_zero hv]
        have hn0' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        push_cast
        linarith only [mul_nonneg hγpos.le hn0']
    have hBd : (edeg H0 v : ℝ) ≤ 2 * α * (n : ℝ) := by rw [hndef]; exact hH0deg v
    have hCd : (edeg (insideParts (Ppar \ P') P) v : ℝ) ≤ γ * (n : ℝ) := by
      refine le_trans ?_ (hPpardegn v)
      exact_mod_cast edeg_mono ((insideParts_subset _ _).trans Finset.sdiff_subset) v
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hfinal hn0
    have hgoal : ε / (2 * (k : ℝ) ^ 2) * (n : ℝ) = ε * (n : ℝ) / (2 * (k : ℝ) ^ 2) := by ring
    linarith only [hcast, hA, hBd, hCd, hmul, hgoal.le, hgoal.ge]

/-- **The §10.12 assembly from the corrected inputs and Corollary 10.11 at the pair `(ρ, k)`.**
This is `BKLO.lemma1012K3'At_of_true_inputs_atAlpha` with the α-quantified form
`BKLO.Cor1011K3AtRho ρ k` of Corollary 10.11; the assembly only ever uses it at
`α = ε/(16k²)`. -/
theorem lemma1012K3'At_of_true_inputs {δ ε ρ : ℝ} {k : ℕ}
    (hδ : (9 : ℝ) / 10 ≤ δ) (hk30 : 30 ≤ k) (hε : 0 < ε)
    (hkε : 1 / (k : ℝ) ≤ ε) (hsum : δ + 3 * ε ≤ 1)
    (hρpos : 0 < ρ) (hρε : ρ ≤ ε) (h18 : 18 * (k : ℝ) * Real.sqrt ρ ^ 3 ≤ ρ / 4)
    (h72 : Lemma72K3') (h93 : Lemma93K3S) (h1011 : Cor1011K3AtRho ρ k)
    (h106 : Lemma106K3Set δ) :
    Lemma1012K3'At δ k ε := by
  have hkR : (30 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk30
  have hαpos : 0 < ε / (16 * (k : ℝ) ^ 2) :=
    Lemma1012Params.alpha_pos hkR hε (rfl : ε / (16 * (k : ℝ) ^ 2) = ε / (16 * (k : ℝ) ^ 2))
  exact lemma1012K3'At_of_true_inputs_atAlpha hδ hk30 hε hkε hsum hρpos hρε h18 h72 h93
    (cor1011K3AtAlphaRho_of_atRho h1011 hαpos) h106

/-! ### Instantiations -/

/-- At `ρ = 1/(10000k²)` the slack inequality (SLACK) holds, with room to spare
(`18k√ρ³ = 0.18ρ ≤ 0.25ρ`). -/
theorem slack_at_ten_thousand {ρ : ℝ} {k : ℕ} (hk30 : 30 ≤ k)
    (hρ : ρ = 1 / (10000 * (k : ℝ) ^ 2)) : 18 * (k : ℝ) * Real.sqrt ρ ^ 3 ≤ ρ / 4 := by
  have hkR : (30 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk30
  have h := Lemma1012Params.eighteen_sqrt hkR hρ
  have hρ0 : 0 < ρ := Lemma1012Params.rho_pos hkR hρ
  rw [h]; linarith only [hρ0]

/-- **Corollary 10.11 in the sparse regime.**  The §10.12 assembly only ever calls Corollary 10.11
at `ρ = 1/(10000k²)` with `30 ≤ k`; this is the precise residual input.  (It is a genuine
restriction of `BKLO.Cor1011K3`: the latter asserts Corollary 10.11 for *every* `0 < ρ < 1`, which
is the range in which the transcription `BKLO.Lemma1010K3` behind it loses the paper's hierarchy
`ρ ≪ 1/k`.)

  (Caveat: this value of `ρ` breaks the paper's hierarchy `ρ ≪ α` at the one place the assembly
  uses Corollary 10.11, `α = ε/(16k²)`: `2kρ = 1/(5000k)` exceeds `α`
  (`BKLO.Lemma1012ParamsHier.two_k_rho_gt_alpha_at_ten_thousand`), so `Cor1011K3Sparse` cannot be
  supplied by the hierarchy-restored `BKLO.Cor1011K3Hier`.  `BKLO/Section1012Hier.lean`
  re-parametrises the assembly at `ρ = ε/(32k³)`, where `2kρ = α`, and derives `Lemma1012K3' (9/10)`
  from `Cor1011K3Hier` instead.) -/
def Cor1011K3Sparse : Prop :=
  ∀ k : ℕ, 30 ≤ k → Cor1011K3AtRho (1 / (10000 * (k : ℝ) ^ 2)) k

theorem cor1011K3Sparse_of_cor1011K3 (h : Cor1011K3) : Cor1011K3Sparse := by
  intro k hk30
  have hk0 : 0 < k := by omega
  have hkR : (30 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk30
  have hρ : (1 : ℝ) / (10000 * (k : ℝ) ^ 2) = 1 / (10000 * (k : ℝ) ^ 2) := rfl
  have hρpos : 0 < 1 / (10000 * (k : ℝ) ^ 2) := Lemma1012Params.rho_pos hkR hρ
  have hρle : (1 : ℝ) / (10000 * (k : ℝ) ^ 2) ≤ 1 / 9000000 := Lemma1012Params.rho_le hkR hρ
  exact cor1011K3AtRho_of_cor1011K3 h hρpos (by linarith) hk0

/-- **The §10.12 hard case from the corrected §7.2 and §9.3 and from Corollary 10.11 in the sparse
regime.**  Lemma 7.2 and Lemma 9.3 are now *theorems* (`BKLO.lemma72K3'_holds`,
`BKLO.lemma93K3S_holds`), so the only remaining hypotheses are Corollary 10.11 at
`ρ = 1/(10000k²)` and Lemma 10.6 on a vertex set. -/
theorem lemma1012K3'At_of_cor1011Sparse {δ ε : ℝ} {k : ℕ}
    (hδ : (9 : ℝ) / 10 ≤ δ) (hk30 : 30 ≤ k) (hε : 0 < ε)
    (hkε : 1 / (k : ℝ) ≤ ε) (hsum : δ + 3 * ε ≤ 1)
    (h1011 : Cor1011K3Sparse) (h106 : Lemma106K3Set δ) :
    Lemma1012K3'At δ k ε := by
  have hkR : (30 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk30
  have hρ : (1 : ℝ) / (10000 * (k : ℝ) ^ 2) = 1 / (10000 * (k : ℝ) ^ 2) := rfl
  have hρpos : 0 < 1 / (10000 * (k : ℝ) ^ 2) := Lemma1012Params.rho_pos hkR hρ
  have hρε : (1 : ℝ) / (10000 * (k : ℝ) ^ 2) ≤ ε := Lemma1012Params.rho_le_eps hkR hkε hρ
  exact lemma1012K3'At_of_true_inputs hδ hk30 hε hkε hsum hρpos hρε
    (slack_at_ten_thousand hk30 hρ) lemma72K3'_holds lemma93K3S_holds (h1011 k hk30) h106

/-- **BKLO Lemma 10.12 for `r = 2` (repaired), `δ ≥ 9/10`, from Corollary 10.11 in the sparse
regime and Lemma 10.6 on a vertex set.** -/
theorem lemma1012K3'_of_cor1011Sparse {δ : ℝ} (hδ : (9 : ℝ) / 10 ≤ δ)
    (h1011 : Cor1011K3Sparse) (h106 : Lemma106K3Set δ) : Lemma1012K3' δ :=
  lemma1012K3'_of_hard_case hδ fun _ _ hk30 hε hkε hsum =>
    lemma1012K3'At_of_cor1011Sparse hδ hk30 hε hkε hsum h1011 h106

/-- **BKLO Lemma 10.12 for `r = 2` (repaired) in the dense regime `δ = 9/10`, from the two
genuinely external inputs.**  Lemma 7.2, Lemma 9.3 and Lemma 10.3 are discharged from the theorems
of this development (`BKLO.lemma72K3'_holds`, `BKLO.lemma93K3S_holds`, `BKLO.lemma103K3_holds`);
what remains is Corollary 10.11 at `ρ = 1/(10000k²)` — i.e. Lemma 10.10 in the sparse regime, the
pseudorandom ingredient of §10.2 — and the approximate-decomposition threshold `δ_F^η`. -/
theorem lemma1012K3'_dense_of_inputs (happ : ApproxTriDecompMinDeg (9 / 10))
    (h1011 : Cor1011K3Sparse) : Lemma1012K3' (9 / 10) :=
  lemma1012K3'_of_cor1011Sparse le_rfl h1011 (lemma106K3Set_dense happ)

/-- The same, from the full Corollary 10.11 and hence from `BKLO.Lemma1010K3`. -/
theorem lemma1012K3'_dense_of_lemma1010 (happ : ApproxTriDecompMinDeg (9 / 10))
    (h1010 : Lemma1010K3) : Lemma1012K3' (9 / 10) :=
  lemma1012K3'_dense_of_inputs happ
    (cor1011K3Sparse_of_cor1011K3 (cor1011K3_of_lemma1010K3 h1010))

end BKLO
