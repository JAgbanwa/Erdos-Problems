import PaperIV.FixedL4LocalizationAllEps
import PaperIV.CertifiedOptimumExistence
import PaperIV.RootedDefectZeroChordal
import PaperIV.EditRouteCliqueRecovery

/-!
# E7: fixed-`L = 4` localization at every rooted defect from edit-closeness to chordal

This module replaces the deletion bridge of `PaperIV.DefectChordalApproxTransfer` by
**edit-closeness** (additions and deletions) to a chordal graph.

* `EditApproxAt s δ` — the only unproved input, stated as a hypothesis and never proved:
  every large graph of rooted defect `≤ s` is within `δ n²` edits of a chordal graph.
  (Mathematically it follows from the Alon–Shapira removal theorem for hereditary
  properties together with Lemma B, `noBlowup_of_rootedDefect`; that derivation is
  *not* formalized here.)
* `certified_edit_bound` (Lemma F) — `e(G') - w' ≥ e(G) - w - 4|A| - |D|` for the certified
  mixed `K₃/K₄` optima of two graphs, `A` the added and `D` the deleted edges.
* `missingIncidences_add_outsideEdges_le_of_edit` — the transport of the localization
  output from a clique `A'` of `G'` to a sub-clique `C ⊆ A'` of `G`:
  `D_C(G) + e_G(V∖C) ≤ D_{A'}(G') + e_{G'}(V∖A') + |A| + |D| + |A'∖C|·n`.
  This is sharper than the `2z + 2|A'∖C|·n` of the plan.
* `fixedL4LocalizationAt_of_editApprox` (one precision) and
  `fixedL4Localization_of_editApprox` (all precisions): the assembly, with Lemma C
  (`clique_of_rootedDefect_of_few_nonedges`) recovering a real clique of `G`.
-/

namespace PaperIV.EditRoute

open Finset
open PaperIV.FarRounding
open PaperIV.RootedSimplicialDefect
open PaperIV.RootVocab
open PaperIV.FixedL4

/-! ## 0. The hypothesis -/

/-- **Edit-closeness to chordal (hypothesis, not proved here).**  Every large graph of
rooted defect `≤ s` is within `δ n²` edge edits (additions plus deletions) of a chordal
graph on the same vertex set. -/
def EditApproxAt (s : ℕ) (delta : ℚ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    RootedDefectAt G s → ∃ G' : SimpleGraph (Fin n), G'.IsChordal ∧
      (((symmDiff G.edgeSet G'.edgeSet).ncard : ℚ) ≤ delta * (n : ℚ) ^ 2)

/-! ## 1. Lemma F: the certified optimum under edits -/

section LemmaF

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G G' : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel G'.Adj]

/-- A packing of `G'` restricted to the items that are also items of `G`. -/
noncomputable def restrictPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (x' : FracPacking G' ℚ) : FracPacking G ℚ where
  weight K := if K ∈ items G' then x'.weight K else 0
  weight_nonneg K := by
    split_ifs
    · exact x'.weight_nonneg K
    · exact le_rfl
  capacity e he := by
    by_cases heG' : e ∈ G'.edgeFinset
    · have hnn : ∀ K, 0 ≤ (if e ∈ pairs K then
          (if K ∈ items G' then x'.weight K else 0) else 0) := by
        intro K; split_ifs <;> first | exact x'.weight_nonneg K | exact le_rfl
      calc ∑ K ∈ items G, (if e ∈ pairs K then
              (if K ∈ items G' then x'.weight K else 0) else 0)
          ≤ ∑ K ∈ items G ∪ items G', (if e ∈ pairs K then
              (if K ∈ items G' then x'.weight K else 0) else 0) :=
            sum_le_sum_of_subset_of_nonneg subset_union_left (fun K _ _ => hnn K)
        _ = ∑ K ∈ items G', (if e ∈ pairs K then
              (if K ∈ items G' then x'.weight K else 0) else 0) := by
            refine (sum_subset subset_union_right ?_).symm
            intro K _ hK
            simp [hK]
        _ = ∑ K ∈ items G', (if e ∈ pairs K then x'.weight K else 0) :=
            sum_congr rfl fun K hK => by simp [hK]
        _ ≤ 1 := x'.capacity e heG'
    · have : ∀ K ∈ items G, (if e ∈ pairs K then
          (if K ∈ items G' then x'.weight K else 0) else 0) = 0 := by
        intro K _
        by_cases hK : K ∈ items G'
        · have : e ∉ pairs K := fun hmem =>
            heG' (pairs_subset_edgeFinset (mem_items.1 hK) hmem)
          simp [this]
        · simp [hK]
      rw [sum_congr rfl this]
      simp

omit [Fintype V] [DecidableEq V] [DecidableRel G'.Adj] in
theorem gainF_le_five {K : Finset V} (h : IsItem G' K) : gainF ℚ K ≤ 5 := by
  rcases h.2 with h3 | h3 <;> rw [gainF, h3] <;> norm_num [Nat.choose]

/-- Restricting to the items of `G` loses at most `5` per added edge. -/
theorem value_le_restrict_add (x' : FracPacking G' ℚ) :
    x'.value ≤ (restrictPacking G x').value + 5 * ((G'.edgeFinset \ G.edgeFinset).card : ℚ) := by
  classical
  set Aset := G'.edgeFinset \ G.edgeFinset with hAset
  have hres : (restrictPacking G x').value =
      ∑ K ∈ items G', gainF ℚ K * (if K ∈ items G then x'.weight K else 0) := by
    rw [FracPacking.value]
    simp only [restrictPacking, mul_ite, mul_zero]
    rw [← sum_filter, ← sum_filter, filter_mem_eq_inter, filter_mem_eq_inter, inter_comm]
  have hsplit : x'.value = (restrictPacking G x').value +
      ∑ K ∈ items G', gainF ℚ K * (if K ∈ items G then 0 else x'.weight K) := by
    rw [hres, FracPacking.value, ← sum_add_distrib]
    refine sum_congr rfl fun K _ => ?_
    split_ifs <;> ring
  have hpt : ∀ K ∈ items G', gainF ℚ K * (if K ∈ items G then 0 else x'.weight K) ≤
      5 * ∑ a ∈ Aset, (if a ∈ pairs K then x'.weight K else 0) := by
    intro K hK
    have hnn : 0 ≤ ∑ a ∈ Aset, (if a ∈ pairs K then x'.weight K else 0) :=
      sum_nonneg fun a _ => by split_ifs <;> first | exact x'.weight_nonneg K | exact le_rfl
    by_cases hKG : K ∈ items G
    · simp only [hKG, if_true, mul_zero]
      linarith
    · simp only [hKG, if_false]
      have hitem := mem_items.1 hK
      have hnot : ¬ ∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b := fun h =>
        hKG (mem_items.2 ⟨h, hitem.2⟩)
      push_neg at hnot
      obtain ⟨a, ha, b, hb, hab, hnadj⟩ := hnot
      have hmemA : s(a, b) ∈ Aset := by
        rw [hAset, mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset]
        exact ⟨hitem.1 a ha b hb hab, hnadj⟩
      have hmemK : s(a, b) ∈ pairs K := mk_mem_pairs.2 ⟨ha, hb, hab⟩
      have hsingle : x'.weight K ≤ ∑ a ∈ Aset, (if a ∈ pairs K then x'.weight K else 0) := by
        have := single_le_sum (f := fun a => if a ∈ pairs K then x'.weight K else 0)
          (fun a _ => by
            show 0 ≤ (if a ∈ pairs K then x'.weight K else 0)
            split_ifs <;> first | exact x'.weight_nonneg K | exact le_rfl) hmemA
        simpa [hmemK] using this
      calc gainF ℚ K * x'.weight K ≤ 5 * x'.weight K :=
            mul_le_mul_of_nonneg_right (gainF_le_five hitem) (x'.weight_nonneg K)
        _ ≤ _ := by linarith
  have hloss : ∑ K ∈ items G', gainF ℚ K * (if K ∈ items G then 0 else x'.weight K) ≤
      5 * (Aset.card : ℚ) := by
    calc _ ≤ ∑ K ∈ items G', 5 * ∑ a ∈ Aset, (if a ∈ pairs K then x'.weight K else 0) :=
          sum_le_sum hpt
      _ = 5 * ∑ a ∈ Aset, ∑ K ∈ items G', (if a ∈ pairs K then x'.weight K else 0) := by
          rw [← mul_sum, sum_comm]
      _ ≤ 5 * ∑ _a ∈ Aset, (1 : ℚ) := by
          gcongr with a ha
          exact x'.capacity a (mem_sdiff.1 ha).1
      _ = 5 * (Aset.card : ℚ) := by simp
  linarith

/-- **Lemma F (the certified optimum under edits).**  With `A = E(G') \ E(G)` added and
`D = E(G) \ E(G')` deleted, `e(G') - w' ≥ e(G) - w - 4|A| - |D|`. -/
theorem certified_edit_bound {w w' : ℚ} (hw : CertifiedFractionalOptimum G w)
    (hw' : CertifiedFractionalOptimum G' w') :
    (G.edgeFinset.card : ℚ) - w - 4 * ((G'.edgeFinset \ G.edgeFinset).card : ℚ)
      - ((G.edgeFinset \ G'.edgeFinset).card : ℚ) ≤ (G'.edgeFinset.card : ℚ) - w' := by
  obtain ⟨x', -, hx', -⟩ := hw'
  have h1 := value_le_restrict_add (G := G) x'
  have h2 := certified_isOptimum hw (restrictPacking G x')
  have hc1 := card_sdiff_add_card_inter G'.edgeFinset G.edgeFinset
  have hc2 := card_sdiff_add_card_inter G.edgeFinset G'.edgeFinset
  rw [inter_comm] at hc2
  have hc1' : ((G'.edgeFinset \ G.edgeFinset).card : ℚ) +
      ((G'.edgeFinset ∩ G.edgeFinset).card : ℚ) = (G'.edgeFinset.card : ℚ) := by
    exact_mod_cast hc1
  have hc2' : ((G.edgeFinset \ G'.edgeFinset).card : ℚ) +
      ((G'.edgeFinset ∩ G.edgeFinset).card : ℚ) = (G.edgeFinset.card : ℚ) := by
    exact_mod_cast hc2
  rw [hx'] at h1
  linarith

end LemmaF

/-! ## 2. Transport of the localization output under edits -/

section Transport

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G G' : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel G'.Adj]

/-- Inside a clique of `G'`, every non-edge of `G` is an added edge. -/
theorem nonEdgesIn_subset_added {A' : Finset V} (hA' : G'.IsClique (A' : Set V)) :
    nonEdgesIn G A' ⊆ G'.edgeFinset \ G.edgeFinset := by
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    simp only [nonEdgesIn, mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at he
    rw [mem_sdiff]
    exact ⟨SimpleGraph.mem_edgeFinset.2 (hA' (mem_coe.2 he.1.1) (mem_coe.2 he.1.2) he.2.1),
      he.2.2⟩

/-- Missing incidences of the sub-clique `C` in `G` are those of `A'` in `G'`, plus added
edges. -/
theorem missingIncidences_le_of_edit {A' C : Finset V} (hC : C ⊆ A')
    (hA' : G'.IsClique (A' : Set V)) :
    missingIncidences G C ≤ missingIncidences G' A' + (G'.edgeFinset \ G.edgeFinset).card := by
  classical
  set T : V → Finset V := fun x =>
    (outsideVertices C).filter (fun y => G'.Adj x y ∧ ¬ G.Adj x y) with hT
  have hcol : ∀ x ∈ C, (missingColumn G C x).card ≤
      (missingColumn G' A' x).card + (T x).card := by
    intro x hx
    refine le_trans (card_le_card ?_) (card_union_le _ _)
    intro y hy
    simp only [missingColumn, mem_filter, mem_outsideVertices] at hy
    by_cases hG' : G'.Adj x y
    · exact mem_union_right _ (by simp [hT, hy.1, hy.2, hG'])
    · have hyA : y ∉ A' := by
        intro hyA
        exact hG' (hA' (mem_coe.2 (hC hx)) (mem_coe.2 hyA) (fun h => hy.1 (h ▸ hx)))
      exact mem_union_left _ (by simp [missingColumn, hyA, hG'])
  have hsum1 : ∑ x ∈ C, (missingColumn G' A' x).card ≤ missingIncidences G' A' :=
    sum_le_sum_of_subset_of_nonneg hC (fun _ _ _ => Nat.zero_le _)
  have hsum2 : ∑ x ∈ C, (T x).card ≤ (G'.edgeFinset \ G.edgeFinset).card := by
    rw [← card_sigma]
    refine card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
    · intro p hp
      rw [mem_coe, mem_sigma] at hp
      simp only [hT, mem_filter, mem_outsideVertices] at hp
      rw [mem_coe, mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset]
      exact ⟨hp.2.2.1, hp.2.2.2⟩
    · intro p hp q hq hpq
      rw [mem_coe, mem_sigma] at hp hq
      simp only [hT, mem_filter, mem_outsideVertices] at hp hq
      simp only at hpq
      rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Sigma.ext h1 (heq_of_eq h2)
      · exact absurd (h1 ▸ hp.1) hq.2.1
  calc missingIncidences G C = ∑ x ∈ C, (missingColumn G C x).card := rfl
    _ ≤ ∑ x ∈ C, ((missingColumn G' A' x).card + (T x).card) := sum_le_sum hcol
    _ = _ + _ := sum_add_distrib
    _ ≤ _ := add_le_add hsum1 hsum2

/-- Edges outside `C` in `G` are edges outside `A'` in `G'`, deleted edges, or edges at a
vertex of `A' \ C`. -/
theorem card_outsideEdges_le_of_edit {A' C : Finset V} :
    (outsideEdges G C).card ≤ (outsideEdges G' A').card +
      (G.edgeFinset \ G'.edgeFinset).card + (A' \ C).card * Fintype.card V := by
  classical
  have hsub : outsideEdges G C ⊆ (outsideEdges G' A' ∪ (G.edgeFinset \ G'.edgeFinset)) ∪
      (A' \ C).biUnion (fun v => G.incidenceFinset v) := by
    intro e he
    have he' := he
    simp only [outsideEdges, mem_filter] at he'
    by_cases hA : e.toFinset ⊆ outsideVertices A'
    · by_cases hG' : e ∈ G'.edgeFinset
      · exact mem_union_left _ (mem_union_left _ (by
          simp only [outsideEdges, mem_filter]; exact ⟨hG', hA⟩))
      · exact mem_union_left _ (mem_union_right _ (mem_sdiff.2 ⟨he'.1, hG'⟩))
    · rw [not_subset] at hA
      obtain ⟨v, hv, hvA⟩ := hA
      rw [mem_outsideVertices, not_not] at hvA
      have hvC : v ∉ C := mem_outsideVertices.1 (he'.2 hv)
      refine mem_union_right _ (mem_biUnion.2 ⟨v, mem_sdiff.2 ⟨hvA, hvC⟩, ?_⟩)
      rw [SimpleGraph.incidenceFinset, Set.mem_toFinset]
      exact ⟨SimpleGraph.mem_edgeFinset.1 he'.1, Sym2.mem_toFinset.1 hv⟩
  calc (outsideEdges G C).card
      ≤ ((outsideEdges G' A' ∪ (G.edgeFinset \ G'.edgeFinset)) ∪
          (A' \ C).biUnion (fun v => G.incidenceFinset v)).card := card_le_card hsub
    _ ≤ (outsideEdges G' A' ∪ (G.edgeFinset \ G'.edgeFinset)).card +
          ((A' \ C).biUnion (fun v => G.incidenceFinset v)).card := card_union_le _ _
    _ ≤ ((outsideEdges G' A').card + (G.edgeFinset \ G'.edgeFinset).card) +
          ∑ v ∈ A' \ C, (G.incidenceFinset v).card :=
        add_le_add (card_union_le _ _) card_biUnion_le
    _ ≤ ((outsideEdges G' A').card + (G.edgeFinset \ G'.edgeFinset).card) +
          ∑ _v ∈ A' \ C, Fintype.card V := by
        gcongr with v
        rw [SimpleGraph.card_incidenceFinset_eq_degree]
        exact (G.degree_lt_card_verts v).le
    _ = _ := by rw [sum_const, smul_eq_mul]

/-- **Transport of the localization mass** (step 5 of the plan, with sharper constants). -/
theorem missingIncidences_add_outsideEdges_le_of_edit {A' C : Finset V} (hC : C ⊆ A')
    (hA' : G'.IsClique (A' : Set V)) :
    missingIncidences G C + (outsideEdges G C).card ≤
      missingIncidences G' A' + (outsideEdges G' A').card +
        (G'.edgeFinset \ G.edgeFinset).card + (G.edgeFinset \ G'.edgeFinset).card +
          (A' \ C).card * Fintype.card V := by
  have h1 := missingIncidences_le_of_edit (G := G) hC hA'
  have h2 := card_outsideEdges_le_of_edit (G := G) (G' := G') (A' := A') (C := C)
  omega

end Transport

/-! ## 3. Assembly -/

/-- The localization statement at defect `s`, precision `ε` and an **explicit** margin `η`;
`FixedL4LocalizationAt s ε` is exactly `∃ η > 0, MarginLocalizationAt s ε η`. -/
def MarginLocalizationAt (s : ℕ) (eps eta : ℚ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], RootedDefectAt G s →
      ∀ w : ℚ, CertifiedFractionalOptimum G w →
        (n : ℚ) ^ 2 / 6 - eta * (n : ℚ) ^ 2 ≤ (G.edgeFinset.card : ℚ) - w →
          Nonempty (LocalizedClique G eps)

theorem fixedL4LocalizationAt_iff_margin {s : ℕ} {eps : ℚ} :
    FixedL4LocalizationAt s eps ↔ ∃ eta : ℚ, 0 < eta ∧ MarginLocalizationAt s eps eta :=
  Iff.rfl

theorem card_symmDiff_edgeSet {n : ℕ} (G G' : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    [DecidableRel G'.Adj] :
    (symmDiff G.edgeSet G'.edgeSet).ncard =
      (G.edgeFinset \ G'.edgeFinset).card + (G'.edgeFinset \ G.edgeFinset).card := by
  classical
  have hset : symmDiff G.edgeSet G'.edgeSet =
      (((G.edgeFinset \ G'.edgeFinset) ∪ (G'.edgeFinset \ G.edgeFinset) :
        Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))) := by
    ext e
    simp [Set.mem_symmDiff]
  rw [hset, Set.ncard_coe_finset, card_union_of_disjoint]
  exact disjoint_sdiff_sdiff

/-- **Assembly, one precision.**  Let the defect-`0` localization hold at precision `ε₀`
with margin `η₀`, and let every large graph of rooted defect `≤ s` be `δ n²`-edit-close
to chordal.  If `4δ < η₀`, `2(s+1)δ ≤ r²` with `r ≥ 0`, `ε₀ + 2r ≤ ε` and
`ε₀ + δ + 2r ≤ ε`, then the fixed-`L = 4` localization holds at defect `s` and precision
`ε` (with margin `η₀ - 4δ`). -/
theorem fixedL4LocalizationAt_of_editApprox {s : ℕ} {eps eps0 eta0 delta r : ℚ}
    (h0 : MarginLocalizationAt 0 eps0 eta0) (hdeta : 4 * delta < eta0)
    (hr : 0 ≤ r) (hr2 : 2 * ((s : ℚ) + 1) * delta ≤ r ^ 2)
    (hwin : eps0 + 2 * r ≤ eps) (hmass : eps0 + delta + 2 * r ≤ eps)
    (hE : EditApproxAt s delta) : FixedL4LocalizationAt s eps := by
  classical
  obtain ⟨N0, hN0⟩ := h0
  obtain ⟨NE, hNE⟩ := hE
  refine ⟨eta0 - 4 * delta, by linarith, max N0 NE, ?_⟩
  intro n hn G _ hdef w hw hnear
  have hnN0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hnNE : NE ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨G', hch, hsym⟩ := hNE n hnNE G hdef
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
  -- Lemma F: `G'` is near-extremal with margin `η₀`
  have hF := certified_edit_bound hw hw'
  have hnearG' : (n : ℚ) ^ 2 / 6 - eta0 * (n : ℚ) ^ 2 ≤ (G'.edgeFinset.card : ℚ) - w' := by
    rw [← ha, ← hd] at hF
    nlinarith
  -- the defect-zero localization in the chordal graph `G'`
  have hdef' : RootedDefectAt G' 0 :=
    PaperIV.RootedDefectZero.rootedDefect_zero_iff_isChordal.2 hch
  obtain ⟨L'⟩ := hN0 n hnN0 G' hdef' w' hw' hnearG'
  -- Lemma C: a real clique of `G` inside the core of `L'`
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
  -- bookkeeping on `|A' \ C|`
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

/-- **Assembly, all precisions.**  If every large graph of rooted defect `≤ s` is
`δ n²`-edit-close to chordal for **every** `δ > 0`, then `FixedL4Localization s`. -/
theorem fixedL4Localization_of_editApprox (s : ℕ)
    (hE : ∀ delta : ℚ, 0 < delta → EditApproxAt s delta) : FixedL4Localization s := by
  intro eps heps
  obtain ⟨eta0, heta0, h0⟩ := fixedL4Localization_defectZero (eps / 2) (by positivity)
  set r : ℚ := min (eps / 8) (min 1 (eta0 / 8)) with hr
  have hr0 : 0 < r := lt_min (by positivity) (lt_min one_pos (by positivity))
  have hr1 : r ≤ eps / 8 := min_le_left _ _
  have hr2 : r ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hr3 : r ≤ eta0 / 8 := le_trans (min_le_right _ _) (min_le_right _ _)
  set delta : ℚ := r ^ 2 / (2 * ((s : ℚ) + 1)) with hdelta
  have hs1 : (0 : ℚ) < 2 * ((s : ℚ) + 1) := by positivity
  have hdpos : 0 < delta := by positivity
  have hdr2 : 2 * ((s : ℚ) + 1) * delta = r ^ 2 := by
    rw [hdelta]; field_simp
  have hdle : delta ≤ r := by
    have h1 : delta ≤ r ^ 2 := by
      rw [hdelta, div_le_iff₀ hs1]
      have : (0 : ℚ) ≤ (s : ℚ) := by positivity
      nlinarith [sq_nonneg r]
    nlinarith
  exact fixedL4LocalizationAt_of_editApprox (s := s) (eps0 := eps / 2) (eta0 := eta0)
    (delta := delta) (r := r) h0 (by linarith) hr0.le hdr2.le (by linarith)
    (by linarith) (hE delta hdpos)

end PaperIV.EditRoute
