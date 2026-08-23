/-
# Corollary 10.11 (r=2, F=K3), CODEGREE-regime form

`Cor1011K3Dense` is `BKLO.Cor1011K3` with the extra hypothesis `1/(648 k²) < ρ`, and it is derived
from the codegree-regime Lemma 10.10 (`BKLO.Lemma1010K3Dense`, proved in `Section1010Dense.lean`),
exactly as `BKLO.cor1011K3_of_lemma1010K3` derives `Cor1011K3` from the full `Lemma1010K3`.  This is
the form that the ρ-reconciled §10.12 assembly (parameter `ρ = 1/(625 k²) > 1/(648 k²)`, see
`RhoReconcile625.lean`) can discharge, avoiding the false-as-stated strong `Lemma1010K3`.
-/
import BKLO.Section102K3
import BKLO.Section1010Dense

open Finset

namespace BKLO

def Cor1011K3Dense : Prop :=
  ∀ (α ρ : ℝ) (k : ℕ), 0 < α → 0 < ρ → ρ < 1 → 0 < k → 1 / (648 * (k : ℝ) ^ 2) < ρ → ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (H : Finset (Sym2 V)) (S : Finset V) (P : Finset (Finset V))
      (idx : Finset V → ℕ),
      n₀ ≤ S.card → (∀ e ∈ H, ¬ e.IsDiag) → H ⊆ cliqueEdges S →
      IsEquitablePartition k P S →
      (∀ W ∈ P, ∀ W' ∈ P, W ≠ W' → idx W ≠ idx W') →
      (∀ W ∈ P, ∀ x ∈ beforeParts P idx W, 2 ∣ degTo H x W) →
      (∀ W ∈ P, ∀ x ∈ beforeParts P idx W, ∀ y ∈ nbhdIn H x W,
        (1 / 2 : ℝ) * (degTo H x W : ℝ) + 18 * (k : ℝ) * Real.sqrt ρ ^ 3 * (W.card : ℝ)
          ≤ (degTo H y (nbhdIn H x W) : ℝ)) →
      (∀ W ∈ P, ∀ x ∈ beforeParts P idx W, ∀ x' ∈ beforeParts P idx W, x ≠ x' →
        (codegTo H x x' W : ℝ) ≤ 2 * ρ ^ 2 * (W.card : ℝ)) →
      (∀ W ∈ P, ∀ y ∈ W, (degTo H y (beforeParts P idx W) : ℝ) ≤ 2 * (k : ℝ) * ρ * (W.card : ℝ)) →
      (∀ W ∈ P, ∀ y ∈ W, ((1 : ℝ) / 2 + 2 * α) * (W.card : ℝ) ≤ (degTo H y W : ℝ)) →
      ∃ H₀ : Finset (Sym2 V), H₀ ⊆ insideParts H P ∧
        TriDecomp (crossParts H P ∪ H₀) ∧ ∀ v : V, (edeg H₀ v : ℝ) ≤ 2 * α * (S.card : ℝ)


theorem cor1011K3Dense_of_lemma1010K3Dense (h1010 : Lemma1010K3Dense) : Cor1011K3Dense := by
  intro α ρ k hα hρ hρ1 hk hdense
  obtain ⟨n₀, hn₀⟩ := h1010 α ρ k hα hρ hρ1 hk hdense
  refine ⟨n₀, ?_⟩
  intro V _ H S P idx hcard hloop hHS heq hidx hdvd hmin hcodeg hUdeg hWdeg
  classical
  -- apply Lemma 10.10 to each part
  have hstep : ∀ W ∈ P, ∃ HV : Finset (Sym2 V), HV ⊆ edgesIn H W ∧
      TriDecomp (edgesBtw H (beforeParts P idx W) W ∪ HV) ∧
      ∀ v : V, (edeg HV v : ℝ) ≤ 2 * α * (W.card : ℝ) := by
    intro W hW
    refine hn₀ H S (beforeParts P idx W) W hcard hloop hHS (beforeParts_subset heq idx W)
      (heq.subset_of_mem hW) (disjoint_beforeParts_self heq hW) ?_ (hdvd W hW) (hmin W hW)
      (hcodeg W hW) (hUdeg W hW) (hWdeg W hW)
    -- `|S|/k - 1 ≤ |W|`
    have hlow : (S.card / k : ℕ) ≤ W.card := heq.size_lower W hW
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hdiv : (S.card : ℝ) / (k : ℝ) - 1 ≤ ((S.card / k : ℕ) : ℝ) := by
      have hle : (S.card : ℝ) < ((S.card / k : ℕ) : ℝ) * (k : ℝ) + (k : ℝ) := by
        have h2 : S.card < (S.card / k) * k + k := Nat.lt_div_mul_add hk
        exact_mod_cast h2
      rw [sub_le_iff_le_add, div_le_iff₀ hkpos]
      nlinarith only [hle, hkpos]
    have hcast : ((S.card / k : ℕ) : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hlow
    linarith
  choose! HV hHVsub hHVdec hHVdeg using hstep
  refine ⟨P.biUnion HV, ?_, ?_, ?_⟩
  · -- `H₀ ⊆ insideParts H P`
    intro e he
    obtain ⟨W, hW, heW⟩ := Finset.mem_biUnion.1 he
    exact edgesIn_subset_insideParts hW (hHVsub W hW heW)
  · -- the triangle decomposition
    have hsplit : crossParts H P ∪ P.biUnion HV
        = P.biUnion (fun W => edgesBtw H (beforeParts P idx W) W ∪ HV W) := by
      rw [crossParts_eq_biUnion_edgesBtw heq hHS hloop hidx, ← Finset.biUnion_union]
    rw [hsplit]
    refine TriDecomp.biUnion (fun W hW => hHVdec W hW) ?_
    intro W₁ hW₁ W₂ hW₂ hne
    have hcross₁ : edgesBtw H (beforeParts P idx W₁) W₁ ⊆ crossParts H P :=
      edgesBtw_beforeParts_subset_crossParts heq hW₁
    have hcross₂ : edgesBtw H (beforeParts P idx W₂) W₂ ⊆ crossParts H P :=
      edgesBtw_beforeParts_subset_crossParts heq hW₂
    have hin₁ : HV W₁ ⊆ insideParts H P :=
      (hHVsub W₁ hW₁).trans (edgesIn_subset_insideParts hW₁)
    have hin₂ : HV W₂ ⊆ insideParts H P :=
      (hHVsub W₂ hW₂).trans (edgesIn_subset_insideParts hW₂)
    have hci := disjoint_crossParts_insideParts H P
    refine Finset.disjoint_union_left.2 ⟨?_, ?_⟩ <;>
      refine Finset.disjoint_union_right.2 ⟨?_, ?_⟩
    · exact disjoint_edgesBtw_beforeParts heq hW₁ hW₂ hne
    · exact Finset.disjoint_of_subset_left hcross₁ (Finset.disjoint_of_subset_right hin₂ hci)
    · exact (Finset.disjoint_of_subset_left hcross₂
        (Finset.disjoint_of_subset_right hin₁ hci)).symm
    · exact Finset.disjoint_of_subset_left (hHVsub W₁ hW₁)
        (Finset.disjoint_of_subset_right (hHVsub W₂ hW₂)
          (disjoint_edgesIn_parts heq hW₁ hW₂ hne))
  · -- the degree bound
    intro v
    by_cases hv : ∃ W ∈ P, v ∈ W
    · obtain ⟨W₀, hW₀, hvW₀⟩ := hv
      have hzero : ∀ W ∈ P, W ≠ W₀ → edeg (HV W) v = 0 := by
        intro W hW hne
        have hvW : v ∉ W := fun hc => hne (heq.eq_of_mem hW hW₀ hc hvW₀)
        have := edeg_edgesIn_eq_zero (H := H) hvW
        exact Nat.le_zero.1 (this ▸ edeg_mono (hHVsub W hW) v)
      have hsub : (P.biUnion HV).filter (fun e => v ∈ e) ⊆ (HV W₀).filter (fun e => v ∈ e) := by
        intro e he
        obtain ⟨heB, hve⟩ := Finset.mem_filter.1 he
        obtain ⟨W, hW, heW⟩ := Finset.mem_biUnion.1 heB
        by_cases hWW : W = W₀
        · exact Finset.mem_filter.2 ⟨hWW ▸ heW, hve⟩
        · exfalso
          have h0 := hzero W hW hWW
          rw [edeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
          exact h0 heW hve
      have hle : edeg (P.biUnion HV) v ≤ edeg (HV W₀) v := Finset.card_le_card hsub
      have h1 : (edeg (P.biUnion HV) v : ℝ) ≤ (edeg (HV W₀) v : ℝ) := by exact_mod_cast hle
      have h2 := hHVdeg W₀ hW₀ v
      have h3 : (W₀.card : ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (heq.subset_of_mem hW₀)
      nlinarith [hα.le]
    · push_neg at hv
      have hzero : edeg (P.biUnion HV) v = 0 := by
        rw [edeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he hve
        obtain ⟨W, hW, heW⟩ := Finset.mem_biUnion.1 he
        exact hv W hW ((mem_edgesIn.1 (hHVsub W hW heW)).2 v hve)
      rw [hzero]
      have : (0 : ℝ) ≤ 2 * α * (S.card : ℝ) := by positivity
      simpa using this

end BKLO

