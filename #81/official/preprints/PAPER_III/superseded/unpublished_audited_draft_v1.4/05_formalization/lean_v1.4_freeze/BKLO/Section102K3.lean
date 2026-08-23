/-
# BKLO §10.2 for `r = 2`: Corollary 10.11 from Lemma 10.10

`BKLO/Section1012Defs.lean` transcribes BKLO Lemma 10.10 (p. 32) and Corollary 10.11 (p. 32) for
`r = 2`, `F = K₃`.  The paper deduces the corollary from the lemma by applying the lemma once for
each part `Vᵢ` of the partition, with `U = V_{<i}`.  This file carries that deduction out,
`sorry`-free:

  `BKLO.cor1011K3_of_lemma1010K3 : Lemma1010K3 → Cor1011K3`.

The combinatorial content is the *partition of the crossing edges by their later endpoint*:

  `crossParts H P = ⋃_{W ∈ P} H[V_{<W}, W]`,

a union which is edge-disjoint, so the triangle decompositions produced by Lemma 10.10 for the
individual parts can simply be concatenated (`BKLO.TriDecomp.biUnion`).  The inside-part graphs
`H'_{V}` returned by Lemma 10.10 live in different parts, hence are edge-disjoint from each other
and from every crossing edge, and each vertex lies in only one part, so their union still has
maximum degree `≤ 2α n`.
-/
import BKLO.Section1012Defs

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Parts of a partition -/

/-- Two parts of a partition sharing a vertex are equal. -/
theorem IsEquitablePartition.eq_of_mem {k : ℕ} {P : Finset (Finset V)} {S : Finset V}
    (h : IsEquitablePartition k P S) {W W' : Finset V} (hW : W ∈ P) (hW' : W' ∈ P) {x : V}
    (hx : x ∈ W) (hx' : x ∈ W') : W = W' := by
  by_contra hne
  exact (Finset.disjoint_left.1 (h.pairwise_disjoint W hW W' hW' hne)) hx hx'

/-- Every vertex of `S` lies in a part. -/
theorem IsEquitablePartition.exists_part {k : ℕ} {P : Finset (Finset V)} {S : Finset V}
    (h : IsEquitablePartition k P S) {x : V} (hx : x ∈ S) : ∃ W ∈ P, x ∈ W := by
  rw [← h.cover] at hx
  obtain ⟨W, hW, hxW⟩ := Finset.mem_biUnion.1 hx
  exact ⟨W, hW, hxW⟩

/-- `V_{<i} ⊆ S`. -/
theorem beforeParts_subset {k : ℕ} {P : Finset (Finset V)} {S : Finset V}
    (h : IsEquitablePartition k P S) (idx : Finset V → ℕ) (W : Finset V) :
    beforeParts P idx W ⊆ S := by
  intro x hx
  obtain ⟨W', hW', _, hxW'⟩ := mem_beforeParts.1 hx
  exact h.subset_of_mem hW' hxW'

/-- `V_{<i}` is disjoint from `Vᵢ`. -/
theorem disjoint_beforeParts_self {k : ℕ} {P : Finset (Finset V)} {S : Finset V}
    (h : IsEquitablePartition k P S) {idx : Finset V → ℕ} {W : Finset V} (hW : W ∈ P) :
    Disjoint (beforeParts P idx W) W := by
  refine Finset.disjoint_left.2 fun x hx hxW => ?_
  obtain ⟨W', hW', hlt, hxW'⟩ := mem_beforeParts.1 hx
  rw [h.eq_of_mem hW' hW hxW' hxW] at hlt
  exact lt_irrefl _ hlt

/-! ### The crossing edges, split by their later endpoint -/

section Cross

variable {k : ℕ} {P : Finset (Finset V)} {S : Finset V} {H : Finset (Sym2 V)}
  {idx : Finset V → ℕ}

/-- An edge of `H[V_{<i}, Vᵢ]` is a crossing edge of `P`. -/
theorem edgesBtw_beforeParts_subset_crossParts (heq : IsEquitablePartition k P S)
    {W : Finset V} (hW : W ∈ P) :
    edgesBtw H (beforeParts P idx W) W ⊆ crossParts H P := by
  intro e he
  rw [edgesBtw, Finset.mem_filter] at he
  obtain ⟨heH, a, ha, b, hb, rfl⟩ := he
  obtain ⟨W', hW', hlt, haW'⟩ := mem_beforeParts.1 ha
  refine mem_crossParts.2 ⟨heH, ?_⟩
  rintro ⟨W'', hW'', hall⟩
  have h1 : W' = W'' := heq.eq_of_mem hW' hW'' haW' (hall a (by simp))
  have h2 : W = W'' := heq.eq_of_mem hW hW'' hb (hall b (by simp))
  rw [h1, ← h2] at hlt
  exact lt_irrefl _ hlt

/-- The crossing edges of `P` are covered by the sets `H[V_{<i}, Vᵢ]`. -/
theorem crossParts_subset_biUnion_edgesBtw (heq : IsEquitablePartition k P S)
    (hHS : H ⊆ cliqueEdges S) (hloop : ∀ e ∈ H, ¬ e.IsDiag)
    (hidx : ∀ W ∈ P, ∀ W' ∈ P, W ≠ W' → idx W ≠ idx W') :
    crossParts H P ⊆ P.biUnion (fun W => edgesBtw H (beforeParts P idx W) W) := by
  intro e he
  obtain ⟨heH, hcross⟩ := mem_crossParts.1 he
  have heS : ∀ v ∈ e, v ∈ S := by
    have := mem_cliqueEdgesV.1 (hHS heH)
    exact fun v hv => this.1 v hv
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := by
      intro h; exact hloop _ heH (by simp [Sym2.isDiag_iff_proj_eq, h])
    obtain ⟨Wa, hWa, haWa⟩ := heq.exists_part (heS a (by simp))
    obtain ⟨Wb, hWb, hbWb⟩ := heq.exists_part (heS b (by simp))
    have hne : Wa ≠ Wb := by
      rintro rfl
      exact hcross ⟨Wa, hWa, by rintro v hv; rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption⟩
    have hidxne : idx Wa ≠ idx Wb := hidx Wa hWa Wb hWb hne
    rcases lt_or_gt_of_ne hidxne with hlt | hlt
    · refine Finset.mem_biUnion.2 ⟨Wb, hWb, ?_⟩
      refine Finset.mem_filter.2 ⟨heH, a, mem_beforeParts.2 ⟨Wa, hWa, hlt, haWa⟩, b, hbWb, rfl⟩
    · refine Finset.mem_biUnion.2 ⟨Wa, hWa, ?_⟩
      refine Finset.mem_filter.2 ⟨heH, b, mem_beforeParts.2 ⟨Wb, hWb, hlt, hbWb⟩, a, haWa, ?_⟩
      exact Sym2.eq_swap

/-- The sets `H[V_{<i}, Vᵢ]` are pairwise edge-disjoint. -/
theorem disjoint_edgesBtw_beforeParts (heq : IsEquitablePartition k P S)
    {W₁ W₂ : Finset V} (hW₁ : W₁ ∈ P) (hW₂ : W₂ ∈ P) (hne : W₁ ≠ W₂) :
    Disjoint (edgesBtw H (beforeParts P idx W₁) W₁) (edgesBtw H (beforeParts P idx W₂) W₂) := by
  refine Finset.disjoint_left.2 fun e he₁ he₂ => ?_
  rw [edgesBtw, Finset.mem_filter] at he₁ he₂
  obtain ⟨-, a, ha, b, hb, hab⟩ := he₁
  obtain ⟨-, c, hc, d, hd, hcd⟩ := he₂
  obtain ⟨Wa, hWa, hlta, haWa⟩ := mem_beforeParts.1 ha
  obtain ⟨Wc, hWc, hltc, hcWc⟩ := mem_beforeParts.1 hc
  rw [hab] at hcd
  rcases Sym2.eq_iff.1 hcd.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hne (heq.eq_of_mem hW₁ hW₂ hb hd)
  · -- `b ∈ W₁` and `b ∈ Wc`, `a ∈ Wa` and `a ∈ W₂`
    have h1 : W₁ = Wc := heq.eq_of_mem hW₁ hWc hb hcWc
    have h2 : Wa = W₂ := heq.eq_of_mem hWa hW₂ haWa hd
    rw [← h1] at hltc
    rw [h2] at hlta
    exact absurd hlta (not_lt.2 (le_of_lt hltc))

/-- `crossParts H P = ⋃_{W ∈ P} H[V_{<W}, W]`. -/
theorem crossParts_eq_biUnion_edgesBtw (heq : IsEquitablePartition k P S)
    (hHS : H ⊆ cliqueEdges S) (hloop : ∀ e ∈ H, ¬ e.IsDiag)
    (hidx : ∀ W ∈ P, ∀ W' ∈ P, W ≠ W' → idx W ≠ idx W') :
    crossParts H P = P.biUnion (fun W => edgesBtw H (beforeParts P idx W) W) := by
  apply Finset.Subset.antisymm (crossParts_subset_biUnion_edgesBtw heq hHS hloop hidx)
  intro e he
  obtain ⟨W, hW, heW⟩ := Finset.mem_biUnion.1 he
  exact edgesBtw_beforeParts_subset_crossParts heq hW heW

end Cross

/-! ### Inside-part edge sets -/

/-- Edges inside different parts are distinct. -/
theorem disjoint_edgesIn_parts {k : ℕ} {P : Finset (Finset V)} {S : Finset V}
    (heq : IsEquitablePartition k P S) {H : Finset (Sym2 V)} {W₁ W₂ : Finset V}
    (hW₁ : W₁ ∈ P) (hW₂ : W₂ ∈ P) (hne : W₁ ≠ W₂) :
    Disjoint (edgesIn H W₁) (edgesIn H W₂) := by
  refine Finset.disjoint_left.2 fun e he₁ he₂ => ?_
  rw [mem_edgesIn] at he₁ he₂
  induction e using Sym2.ind with
  | _ x y =>
    exact hne (heq.eq_of_mem hW₁ hW₂ (he₁.2 x (by simp)) (he₂.2 x (by simp)))

/-- A vertex outside `W` has no `edgesIn H W`-edges at it. -/
theorem edeg_edgesIn_eq_zero {H : Finset (Sym2 V)} {W : Finset V} {v : V} (hv : v ∉ W) :
    edeg (edgesIn H W) v = 0 := by
  rw [edeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hve
  exact hv ((mem_edgesIn.1 he).2 v hve)

/-! ### Corollary 10.11 -/

/-- **BKLO Corollary 10.11 for `r = 2`, from Lemma 10.10.**  Apply Lemma 10.10 once per part `W`,
with `U = V_{<W}`; the crossing edges split as `crossParts H P = ⋃_W H[V_{<W}, W]`, an edge-disjoint
union, so the triangle decompositions concatenate. -/
theorem cor1011K3_of_lemma1010K3 (h1010 : Lemma1010K3) : Cor1011K3 := by
  intro α ρ k hα hρ hρ1 hk
  obtain ⟨n₀, hn₀⟩ := h1010 α ρ k hα hρ hρ1 hk
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
