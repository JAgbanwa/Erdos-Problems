/-
# BKLO Lemma 10.12 for `r = 2` (repaired): the proof of pp. 33–34, from the four paper inputs

This file carries out the proof of BKLO Lemma 10.12 (`r = 2`, `F = K₃`) in the dense regime
`9/10 ≤ δ ≤ 1`, from the four ingredients that the paper's proof uses and that are transcribed in
`BKLO/Section1012Defs.lean`:

* `BKLO.Lemma72K3`     — the random sparse subgraph `R` (Lemma 7.2, p. 13);
* `BKLO.Lemma93K3`     — the `F`-parity graph (Lemma 9.3, p. 25);
* `BKLO.Cor1011K3`     — the covering of the crossing edges (Corollary 10.11, p. 32); it is *proved*
  from `BKLO.Lemma1010K3` in `BKLO/Section102K3.lean`;
* `BKLO.Lemma106K3Set` — Lemma 10.6 on a vertex set (p. 28).

The proof is the paper's:

1. take an `F`-parity graph `Ppar ⊆ G` with `Δ(Ppar) ≤ γn` (Lemma 9.3);
2. take a sparse random `R ⊆ G[P] − Ppar` (Lemma 7.2), whose crossing neighbourhoods are dense and
   have small codegrees;
3. apply Lemma 10.6 to `G' = G − Ppar − R`, obtaining `D₁ = G' − H₆` with an `F`-decomposition, whose
   *crossing* leftover `H₆[P]` has maximum degree `≤ γn` and whose inside-part edges have maximum
   degree `≤ 2γ|W|` in each part;
4. the graph `Gstar = E − D₁ − Ppar` is `2`-divisible (both `D₁` and `Ppar` are triangle
   decomposable, hence even), so the parity graph supplies `P' ⊆ Ppar` with `Ppar − P'`
   triangle-decomposable and all degrees `d_{Gstar ∪ P'}(x, Vᵢ)` even;
5. Corollary 10.11 applied to `Hcov = (Gstar ∪ P')[P] ∪ (available inside edges)` covers all the
   remaining crossing edges using inside-part edges of maximum degree `≤ 2αn`.

The union of the three triangle-decomposable graphs of steps 3–5 is exactly `crossParts E P ∪ H`
for `H` the inside-part edges they use, and `Δ(H) ≤ (3γ + 2α)n ≤ εn/(2k²)`.

The parameters are `ρ = 1/(10000k²)`, `γ = ρ²ε/(1000k²)` and `α = ε/(16k²)`, and the threshold
`n₀` is at least `100k²`; that instantiates the paper's hierarchy `1/n ≪ γ ≪ ρ ≪ 1/k ≤ ε`.  The
vacuous range `1 < δ + 3ε` of the repaired statement is disposed of in `BKLO/Section1012Dense.lean`,
which is why the hard case may assume `30 ≤ k` and `δ + 3ε ≤ 1`.

The results are `BKLO.lemma1012K3'At_of_inputs` (the hard case) and `BKLO.lemma1012K3'_of_inputs`
(`Lemma1012K3' δ` for `δ ≥ 9/10`).  Everything here is `sorry`-free; the inputs — Lemma 7.2,
Lemma 9.3, Lemma 10.10 and Lemma 10.6 on a vertex set — are hypotheses.
-/
import BKLO.Section102K3
import BKLO.Section1012Dense
import BKLO.Section1012Tools

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### The numerical hierarchy `1/n ≪ γ ≪ ρ ≪ 1/k ≤ ε`

The proof of Lemma 10.12 below takes `ρ = 1/(10000k²)`, `γ = ρ²ε/(1000k²)` and `α = ε/(16k²)`.
These are the numerical facts about that choice which the proof uses. -/

namespace Lemma1012Params

variable {kk ε ρ γ α : ℝ}

theorem rho_pos (hk : 30 ≤ kk) (hρ : ρ = 1 / (10000 * kk ^ 2)) : 0 < ρ := by
  have : (0 : ℝ) < kk := by linarith only [hk]
  rw [hρ]; positivity

theorem rho_le (hk : 30 ≤ kk) (hρ : ρ = 1 / (10000 * kk ^ 2)) : ρ ≤ 1 / 9000000 := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  rw [hρ]
  apply one_div_le_one_div_of_le (by norm_num)
  nlinarith only [hk]

theorem rho_sq_le (hk : 30 ≤ kk) (hρ : ρ = 1 / (10000 * kk ^ 2)) : ρ ^ 2 ≤ ρ := by
  have h0 : 0 < ρ := rho_pos hk hρ
  have h1 : ρ ≤ 1 / 9000000 := rho_le hk hρ
  nlinarith only [h0, h1]

theorem gamma_pos (hk : 30 ≤ kk) (hε : 0 < ε) (hρ : ρ = 1 / (10000 * kk ^ 2))
    (hγ : γ = ρ ^ 2 * ε / (1000 * kk ^ 2)) : 0 < γ := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  have hρ0 : 0 < ρ := rho_pos hk hρ
  rw [hγ]; positivity

theorem gamma_mul_k (hk : 30 ≤ kk) (hε : 0 < ε) (hε3 : ε ≤ 1 / 3)
    (hγ : γ = ρ ^ 2 * ε / (1000 * kk ^ 2)) : γ * kk ≤ ρ ^ 2 / 2000 := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  have hkey : ε * kk * 2000 ≤ 1000 * kk ^ 2 := by nlinarith only [hε3, hk, hk0]
  rw [hγ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith only [mul_le_mul_of_nonneg_left hkey (sq_nonneg ρ)]

theorem gamma_le (hk : 30 ≤ kk) (hε : 0 < ε) (hε3 : ε ≤ 1 / 3) (hρ : ρ = 1 / (10000 * kk ^ 2))
    (hγ : γ = ρ ^ 2 * ε / (1000 * kk ^ 2)) : γ ≤ ρ ^ 2 / 2000 := by
  have h := gamma_mul_k hk hε hε3 hγ
  have hγ0 : 0 < γ := gamma_pos hk hε hρ hγ
  nlinarith only [h, hγ0, hk]

theorem gamma_le_eps4 (hk : 30 ≤ kk) (hε : 0 < ε) (hρ : ρ = 1 / (10000 * kk ^ 2))
    (hγ : γ = ρ ^ 2 * ε / (1000 * kk ^ 2)) : γ ≤ ε / 4 := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  have hρ0 : 0 < ρ := rho_pos hk hρ
  have hρ1 : ρ ≤ 1 / 9000000 := rho_le hk hρ
  have hρsq : ρ ^ 2 ≤ 1 := by nlinarith only [hρ0.le, hρ1]
  have hkk2 : (900 : ℝ) ≤ kk ^ 2 := by nlinarith only [hk]
  rw [hγ, div_le_iff₀ (by positivity)]
  linarith only [hε.le, mul_le_mul_of_nonneg_right hρsq hε.le,
    mul_le_mul_of_nonneg_left hkk2 (show (0 : ℝ) ≤ 250 * ε by linarith only [hε])]

theorem alpha_pos (hk : 30 ≤ kk) (hε : 0 < ε) (hα : α = ε / (16 * kk ^ 2)) : 0 < α := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  rw [hα]; positivity

theorem alpha_small (hk : 30 ≤ kk) (hε : 0 < ε) (hε3 : ε ≤ 1 / 3)
    (hα : α = ε / (16 * kk ^ 2)) : α ≤ 1 / 1000 := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  rw [hα, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith only [hε3, hk, hk0]

theorem rho_le_eps (hk : 30 ≤ kk) (hkε : 1 / kk ≤ ε) (hρ : ρ = 1 / (10000 * kk ^ 2)) : ρ ≤ ε := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  refine le_trans ?_ hkε
  rw [hρ]
  apply one_div_le_one_div_of_le hk0
  nlinarith only [hk, hk0]

/-- The error term of condition (ii) of Lemma 10.10 is `0.18ρ`. -/
theorem eighteen_sqrt (hk : 30 ≤ kk) (hρ : ρ = 1 / (10000 * kk ^ 2)) :
    18 * kk * Real.sqrt ρ ^ 3 = 18 / 100 * ρ := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  have hs : Real.sqrt ρ = 1 / (100 * kk) := by
    have hsq : ρ = (1 / (100 * kk)) ^ 2 := by rw [hρ]; field_simp; norm_num
    rw [hsq, Real.sqrt_sq (by positivity)]
  rw [hs, hρ]; field_simp; ring

/-- The final degree bound: `3γ + 2α ≤ ε/(2k²)`. -/
theorem final_bound (hk : 30 ≤ kk) (hε : 0 < ε) (hρ : ρ = 1 / (10000 * kk ^ 2))
    (hγ : γ = ρ ^ 2 * ε / (1000 * kk ^ 2)) (hα : α = ε / (16 * kk ^ 2)) :
    3 * γ + 2 * α ≤ ε / (2 * kk ^ 2) := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  have hρ0 : 0 < ρ := rho_pos hk hρ
  have hρ1 : ρ ≤ 1 / 9000000 := rho_le hk hρ
  have hρsq : ρ ^ 2 ≤ 1 := by nlinarith only [hρ0.le, hρ1]
  have hc : (0 : ℝ) < ε / kk ^ 2 := by positivity
  have h1 : γ ≤ ε / kk ^ 2 / 1000 := by
    have he : γ = ρ ^ 2 * (ε / kk ^ 2) / 1000 := by rw [hγ]; field_simp
    have h2 : ρ ^ 2 * (ε / kk ^ 2) ≤ ε / kk ^ 2 := by
      linarith only [mul_le_mul_of_nonneg_right hρsq hc.le]
    rw [he]; linarith only [h2]
  have h2 : α = ε / kk ^ 2 / 16 := by rw [hα]; field_simp
  have h3 : ε / (2 * kk ^ 2) = ε / kk ^ 2 / 2 := by field_simp
  rw [h2, h3]
  linarith only [hc, h1]

end Lemma1012Params

/-! ### Two small lemmas about edges between different parts -/

/-- An edge with one end in a part `W'` and the other in a different part `W` is a crossing edge. -/
theorem not_inside_of_parts {k : ℕ} {P : Finset (Finset V)} {S : Finset V}
    (heq : IsEquitablePartition k P S) {W W' : Finset V} (hW : W ∈ P) (hW' : W' ∈ P)
    (hne : W ≠ W') {x z : V} (hx : x ∈ W') (hz : z ∈ W) :
    ¬ ∃ W'' ∈ P, ∀ v ∈ s(x, z), v ∈ W'' := by
  rintro ⟨W'', hW'', hall⟩
  have h1 : W' = W'' := heq.eq_of_mem hW' hW'' hx (hall x (by simp))
  have h2 : W = W'' := heq.eq_of_mem hW hW'' hz (hall z (by simp))
  exact hne (h2.trans h1.symm)

/-- The inside-part degree of a vertex `v` of the part `W₀` only sees `edgesIn X W₀`. -/
theorem edeg_insideParts_le_edgesIn {k : ℕ} {P : Finset (Finset V)} {S : Finset V}
    (heq : IsEquitablePartition k P S) {X : Finset (Sym2 V)} {W₀ : Finset V} (hW₀ : W₀ ∈ P)
    {v : V} (hv : v ∈ W₀) : edeg (insideParts X P) v ≤ edeg (edgesIn X W₀) v := by
  refine Finset.card_le_card fun e he => ?_
  obtain ⟨heI, hve⟩ := Finset.mem_filter.1 he
  obtain ⟨heX, W, hW, hall⟩ := mem_insideParts.1 heI
  have : W = W₀ := heq.eq_of_mem hW hW₀ (hall v hve) hv
  subst this
  exact Finset.mem_filter.2 ⟨mem_edgesIn.2 ⟨heX, hall⟩, hve⟩

/-- If `v` lies in no part, it has no inside-part edges. -/
theorem edeg_insideParts_eq_zero {P : Finset (Finset V)} {X : Finset (Sym2 V)} {v : V}
    (hv : ∀ W ∈ P, v ∉ W) : edeg (insideParts X P) v = 0 := by
  rw [edeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hve
  obtain ⟨-, W, hW, hall⟩ := mem_insideParts.1 he
  exact hv W hW (hall v hve)

/-! ### An indexing of the parts -/

/-- An injective-on-`P` indexing of the parts, used to order them. -/
noncomputable def partIdx (P : Finset (Finset V)) : Finset V → ℕ := fun W => P.toList.idxOf W

theorem partIdx_inj {P : Finset (Finset V)} {W W' : Finset V} (hW : W ∈ P) (hW' : W' ∈ P)
    (hne : W ≠ W') : partIdx P W ≠ partIdx P W' := by
  intro h
  apply hne
  have hWl : W ∈ P.toList := Finset.mem_toList.2 hW
  have hW'l : W' ∈ P.toList := Finset.mem_toList.2 hW'
  have h1 := List.getElem_idxOf (List.idxOf_lt_length_iff.2 hWl)
  have h2 := List.getElem_idxOf (List.idxOf_lt_length_iff.2 hW'l)
  rw [← h1, ← h2]
  simp [partIdx] at h
  simp [h]

/-! ### The assembly -/

set_option maxHeartbeats 400000 in
/-- **BKLO Lemma 10.12 for `r = 2` (repaired), hard case, from the four paper inputs.** -/
theorem lemma1012K3'At_of_inputs {δ ε : ℝ} {k : ℕ}
    (hδ : (9 : ℝ) / 10 ≤ δ) (hk30 : 30 ≤ k) (hε : 0 < ε)
    (hkε : 1 / (k : ℝ) ≤ ε) (hsum : δ + 3 * ε ≤ 1)
    (h72 : Lemma72K3) (h93 : Lemma93K3) (h1011 : Cor1011K3) (h106 : Lemma106K3Set δ) :
    Lemma1012K3'At δ k ε := by
  classical
  have hk0 : 0 < k := by omega
  have hkR : (30 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk30
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith only [hkR]
  have hε30 : ε ≤ 1 / 30 := by linarith only [hδ, hsum]
  -- the parameters of the proof: `ρ = 1/(10000k²)`, `γ = ρ²ε/(1000k²)`, `α = ε/(16k²)`
  have hε13 : ε ≤ 1 / 3 := by linarith only [hε30]
  obtain ⟨ρ, hρdef⟩ : ∃ r : ℝ, r = 1 / (10000 * (k : ℝ) ^ 2) := ⟨_, rfl⟩
  obtain ⟨γ, hγdef⟩ : ∃ g : ℝ, g = ρ ^ 2 * ε / (1000 * (k : ℝ) ^ 2) := ⟨_, rfl⟩
  obtain ⟨α, hαdef⟩ : ∃ a : ℝ, a = ε / (16 * (k : ℝ) ^ 2) := ⟨_, rfl⟩
  have hρpos : 0 < ρ := Lemma1012Params.rho_pos hkR hρdef
  have hρle : ρ ≤ 1 / 9000000 := Lemma1012Params.rho_le hkR hρdef
  have hρ1 : ρ < 1 := by linarith only [hρle]
  have hρ2ρ : ρ ^ 2 ≤ ρ := Lemma1012Params.rho_sq_le hkR hρdef
  have hγpos : 0 < γ := Lemma1012Params.gamma_pos hkR hε hρdef hγdef
  have hαpos : 0 < α := Lemma1012Params.alpha_pos hkR hε hαdef
  have hγε4 : γ ≤ ε / 4 := Lemma1012Params.gamma_le_eps4 hkR hε hρdef hγdef
  have hγk : γ * (k : ℝ) ≤ ρ ^ 2 / 2000 := Lemma1012Params.gamma_mul_k hkR hε hε13 hγdef
  have hγle : γ ≤ ρ ^ 2 / 2000 := Lemma1012Params.gamma_le hkR hε hε13 hρdef hγdef
  have hαsmall : α ≤ 1 / 1000 := Lemma1012Params.alpha_small hkR hε hε13 hαdef
  have hρε : ρ ≤ ε := Lemma1012Params.rho_le_eps hkR hkε hρdef
  have h18 : 18 * (k : ℝ) * Real.sqrt ρ ^ 3 = 18 / 100 * ρ :=
    Lemma1012Params.eighteen_sqrt hkR hρdef
  have hfinal : 3 * γ + 2 * α ≤ ε / (2 * (k : ℝ) ^ 2) :=
    Lemma1012Params.final_bound hkR hε hρdef hγdef hαdef
  obtain ⟨n72, H72⟩ := h72 k γ ρ hk0 hγpos hρpos hρ1
  obtain ⟨n93, H93⟩ := h93 k γ hk0 hγpos
  obtain ⟨n11, H11⟩ := h1011 α ρ k hαpos hρpos hρ1 hk0
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
    H72 (crossParts (G \ Ppar) P) (insideParts G P) S P hn72 heqP
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
  obtain ⟨P', hP'sub, hD3dec, hP'par⟩ := hPpar.2 Gstar hGstarDisj hGstarEven
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
    rw [h18]
    linarith
  have cond3 : ∀ W ∈ P, ∀ x ∈ beforeParts P idx W, ∀ x' ∈ beforeParts P idx W, x ≠ x' →
      (codegTo Hcov x x' W : ℝ) ≤ 2 * ρ ^ 2 * (W.card : ℝ) := by
    intro W hW x hx x' hx' _
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
    have hRcod := hR2 x x' W hW
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

/-- **BKLO Lemma 10.12 for `r = 2` (repaired), in the dense regime `δ ≥ 9/10`**, from the three
inputs of the paper's proof that are not available in this development: Lemma 7.2 (the random
sparse subgraph), Lemma 9.3 (the `F`-parity graph) and Lemma 10.10 (the random greedy covering),
together with Lemma 10.6 on a vertex set. -/
theorem lemma1012K3'_of_inputs {δ : ℝ} (hδ : (9 : ℝ) / 10 ≤ δ)
    (h72 : Lemma72K3) (h93 : Lemma93K3) (h1010 : Lemma1010K3) (h106 : Lemma106K3Set δ) :
    Lemma1012K3' δ :=
  lemma1012K3'_of_hard_case hδ fun _ _ hk30 hε hkε hsum =>
    lemma1012K3'At_of_inputs hδ hk30 hε hkε hsum h72 h93 (cor1011K3_of_lemma1010K3 h1010) h106

end BKLO
