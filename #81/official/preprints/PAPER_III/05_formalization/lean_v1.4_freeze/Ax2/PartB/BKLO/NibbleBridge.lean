/-
  Part B — bridge from AX2's `Sym2` triangle-decomposition vocabulary to the
  edge-set `nibble` vocabulary used by the Yuster/AX1 gap lemmas.
-/
import Ax2.PartB.BKLO.ApproxFromPacking
import Nibble.AX1Reduction
import Nibble.YusterBridgeFrac
import Nibble.YusterBridgePacking
import Nibble.YusterNu3

open Finset SimpleGraph
open scoped Classical

namespace Ax2.BKLO

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pair_subset_iff_sym2_mem_triEdges {t : Finset V} {a b : V} (hab : a ≠ b) :
    ({a, b} : Finset V) ⊆ t ↔ s(a, b) ∈ Ax2.triEdges t := by
  constructor
  · intro hsub
    unfold Ax2.triEdges
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mk_mem_sym2_iff]
      exact ⟨hsub (by simp), hsub (by simp)⟩
    · rwa [Sym2.mk_isDiag_iff]
  · intro hmem
    unfold Ax2.triEdges at hmem
    rw [Finset.mem_filter] at hmem
    rw [Finset.mk_mem_sym2_iff] at hmem
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hmem.1.1
    · exact hmem.1.2

lemma edgeFinset_sym2_to_cliqueFinset_two (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : V} (hab : a ≠ b) (he : s(a, b) ∈ G.edgeFinset) :
    ({a, b} : Finset V) ∈ G.cliqueFinset 2 := by
  rw [SimpleGraph.mem_cliqueFinset_iff]
  constructor
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · contradiction
    · rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    · rw [adj_comm]
      rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    · contradiction
  · exact Finset.card_pair hab

lemma cliqueFinset_two_subset_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    {e : Finset V} (he : e ∈ G.cliqueFinset 2) :
    ∀ {a b : V}, e = {a, b} → s(a, b) ∈ G.edgeFinset := by
  intro a b heq
  rw [SimpleGraph.mem_cliqueFinset_iff] at he
  have hab : a ≠ b := by
    have hcard : ({a, b} : Finset V).card = 2 := by rw [← heq, he.2]
    exact fun h => by subst h; simp at hcard
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact he.1 (by rw [heq]; simp) (by rw [heq]; simp) hab

lemma fractional_to_triangleFracPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfrac : FractionalTriangleDecomp G) :
    ∃ w : Finset V → ℝ, Nibble.YusterE.IsTriangleFracPacking G w ∧
      (∑ t ∈ G.cliqueFinset 3, w t) = (G.edgeFinset.card : ℝ) / 3 := by
  classical
  obtain ⟨w0, hw0, hcov⟩ := hfrac
  let w : Finset V → ℝ := fun t => if G.IsNClique 3 t then w0 t else 0
  have hcov' : ∀ e ∈ G.edgeFinset,
      (∑ t ∈ G.cliqueFinset 3, if e ∈ Ax2.triEdges t then w t else 0) = 1 := by
    intro e he
    convert hcov e he using 1
    apply Finset.sum_congr rfl
    intro t ht
    have hclq : G.IsNClique 3 t := SimpleGraph.mem_cliqueFinset_iff.mp ht
    simp [w, hclq]
  refine ⟨w, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro t
      by_cases ht : G.IsNClique 3 t
      · simp [w, ht, hw0]
      · simp [w, ht]
    · intro t ht0
      by_cases ht : G.IsNClique 3 t
      · exact ht
      · simp [w, ht] at ht0
    · intro e hecard
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hecard
      by_cases heG : s(a, b) ∈ G.edgeFinset
      · have hsum := hcov' s(a, b) heG
        rw [Finset.sum_filter]
        have hEq :
            (∑ t ∈ G.cliqueFinset 3, (if ({a, b} : Finset V) ⊆ t then w t else 0)) =
              ∑ t ∈ G.cliqueFinset 3, (if s(a, b) ∈ Ax2.triEdges t then w t else 0) := by
          apply Finset.sum_congr rfl
          intro t ht
          by_cases hsub : ({a, b} : Finset V) ⊆ t
          · have hmem : s(a, b) ∈ Ax2.triEdges t :=
              (pair_subset_iff_sym2_mem_triEdges hab).mp hsub
            simp [hsub, hmem]
          · have hmem : s(a, b) ∉ Ax2.triEdges t := by
              intro h
              exact hsub ((pair_subset_iff_sym2_mem_triEdges hab).mpr h)
            simp [hsub, hmem]
        rw [hEq]
        exact le_of_eq hsum
      · have hempty : (G.cliqueFinset 3).filter (fun t => ({a, b} : Finset V) ⊆ t) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro t ht
          intro hsub
          have hclq : G.IsNClique 3 t := SimpleGraph.mem_cliqueFinset_iff.mp ht
          exact heG (by
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
            exact hclq.1 (hsub (by simp)) (hsub (by simp)) hab)
        simp [hempty]
  · have hsum := fractional_weight_sum G w hcov'
    simpa [w] using hsum

lemma nu3star_ge_of_fractional (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfrac : FractionalTriangleDecomp G) :
    (G.edgeFinset.card : ℝ) / 3 ≤ Nibble.YusterE.nu3star G := by
  obtain ⟨w, hw, hsum⟩ := fractional_to_triangleFracPacking G hfrac
  rw [Nibble.YusterE.nu3star_eq_triangleFrac_sSup G]
  rw [← hsum]
  apply le_csSup
  · obtain ⟨B, hB⟩ := Nibble.YusterE.nu3star_bddAbove G
    refine ⟨B, ?_⟩
    rintro x ⟨w, hw, rfl⟩
    obtain ⟨hpack, hsum'⟩ := Nibble.YusterE.triangleFracPacking_to_fracPacking G hw
    rw [← hsum']
    exact hB ⟨_, hpack, rfl⟩
  · exact ⟨w, hw, rfl⟩

lemma edgeDisjoint_of_trianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    {P : Finset (Finset V)} (hP : Nibble.YusterE.IsTrianglePacking G P) :
    EdgeDisjoint P := by
  intro t ht u hu hne
  rw [Finset.disjoint_left]
  intro e het heu
  induction e using Sym2.ind with
  | _ a b =>
      have hab : a ≠ b := by
        have hnot : ¬ Sym2.IsDiag s(a, b) := by
          have h := het
          unfold Ax2.triEdges at h
          rw [Finset.mem_filter] at h
          exact h.2
        rwa [Sym2.mk_isDiag_iff] at hnot
      have ht_sub : ({a, b} : Finset V) ⊆ t :=
        (pair_subset_iff_sym2_mem_triEdges hab).mpr het
      have hu_sub : ({a, b} : Finset V) ⊆ u :=
        (pair_subset_iff_sym2_mem_triEdges hab).mpr heu
      have hpair_inter : ({a, b} : Finset V) ⊆ t ∩ u := by
        intro x hx
        exact Finset.mem_inter.mpr ⟨ht_sub hx, hu_sub hx⟩
      have htwo : 2 ≤ (t ∩ u).card := by
        have hcard : ({a, b} : Finset V).card = 2 := Finset.card_pair hab
        rw [← hcard]
        exact Finset.card_le_card hpair_inter
      have hone := hP.2 (Finset.mem_coe.mpr ht) (Finset.mem_coe.mpr hu) hne
      omega

theorem approx_of_packing_nsq (G : SimpleGraph V) [DecidableRel G.Adj] {β : ℝ}
    {P : Finset (Finset V)} (hP : ∀ t ∈ P, G.IsNClique 3 t) (hPd : EdgeDisjoint P)
    (hleft : (G.edgeFinset.card : ℝ) - ((coveredEdges P).card : ℝ)
      ≤ β * (Fintype.card V : ℝ) ^ 2) :
    ∃ L : Finset (Sym2 V), L ⊆ G.edgeFinset ∧
      (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 ∧ ApproxTriangleDecomp G L := by
  classical
  have hsub : coveredEdges P ⊆ G.edgeFinset := coveredEdges_subset_edgeFinset G hP
  refine ⟨G.edgeFinset \ coveredEdges P, Finset.sdiff_subset, ?_, ?_⟩
  · have hadd : (G.edgeFinset \ coveredEdges P).card + (coveredEdges P).card = G.edgeFinset.card :=
      Finset.card_sdiff_add_card_eq_card hsub
    have hLR : ((G.edgeFinset \ coveredEdges P).card : ℝ)
        = (G.edgeFinset.card : ℝ) - ((coveredEdges P).card : ℝ) := by
      have hc : ((G.edgeFinset \ coveredEdges P).card : ℝ) + ((coveredEdges P).card : ℝ)
          = (G.edgeFinset.card : ℝ) := by exact_mod_cast hadd
      linarith
    rw [hLR]
    exact hleft
  · refine ⟨P, hP, hPd, ?_⟩
    ext x
    simp only [Finset.mem_sdiff]
    constructor
    · intro hx
      exact ⟨hsub hx, fun h => h.2 hx⟩
    · rintro ⟨hx, hx2⟩
      by_contra h
      exact hx2 ⟨hx, h⟩

theorem approx_of_fractional_of_nibbleGap (hgap : Nibble.AX1.NibbleGapHyp) (β : ℝ)
    (hβ : 0 < β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → FractionalTriangleDecomp G →
        ∃ L : Finset (Sym2 V), L ⊆ G.edgeFinset ∧
          (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 ∧ ApproxTriangleDecomp G L := by
  classical
  obtain ⟨n₀, hn₀⟩ := hgap (β / 3) (by positivity)
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hn hfrac
  have hstar := nu3star_ge_of_fractional G hfrac
  have hgapG := hn₀ V G hn
  obtain ⟨M, hM, hMcard⟩ := Nibble.YusterE.nu3_achieved G
  obtain ⟨P, hPpack, hPcardM⟩ := Nibble.YusterE.matching_gives_trianglePacking G hM
  have hPd : EdgeDisjoint P := edgeDisjoint_of_trianglePacking G hPpack
  have hcovCardNat : (coveredEdges P).card = 3 * P.card :=
    coveredEdges_card G hPpack.1 hPd
  have hPcardNu : P.card = Nibble.YusterE.nu3 G := by rw [hPcardM, hMcard]
  have hcovCard : ((coveredEdges P).card : ℝ) = 3 * (Nibble.YusterE.nu3 G : ℝ) := by
    rw [hcovCardNat, hPcardNu]
    norm_num
  have hthird :
      (G.edgeFinset.card : ℝ) / 3 - (Nibble.YusterE.nu3 G : ℝ)
        ≤ (β / 3) * (Fintype.card V : ℝ) ^ 2 := by
    linarith
  have hleft : (G.edgeFinset.card : ℝ) - ((coveredEdges P).card : ℝ)
      ≤ β * (Fintype.card V : ℝ) ^ 2 := by
    rw [hcovCard]
    nlinarith
  exact approx_of_packing_nsq G hPpack.1 hPd hleft

end Ax2.BKLO
