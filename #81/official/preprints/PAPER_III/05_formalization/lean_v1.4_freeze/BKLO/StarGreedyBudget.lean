/-
# The greedy star decomposition, with the budget as an explicit hypothesis

`BKLO.exists_triDecomp_of_budget` isolates the combinatorial engine behind BKLO Lemma 10.3 (proved
in `BKLO/Section10Lemma103.lean`): if

* every apex neighbourhood `N_H(x,W)`, `x ∈ U`, is even,
* `H[N_H(x,W)]` has minimum degree at least `|N_H(x,W)|/2 + d`,
* every `v ∈ W` satisfies `2 d_H(v,U) ≤ d`,

then the greedy sweep produces `H_V ⊆ H[W]` such that `H[U,W] ∪ H_V` is triangle-decomposable and
`Δ_{H_V}(v) ≤ 2 d_H(v,U)` for every vertex `v`.

The point of stating it this way is that the *conclusion* is the sharp degree bound
`Δ_{H_V}(v) ≤ 2 d_H(v,U)` (compare `BKLO.degTo_le_edeg_of_triDecomp`, which gives the matching
lower bound `d_H(v,U) ≤ Δ_{H_V}(v)`), so the same engine serves both Lemma 10.3 (`d = γ|W|`) and
the regime of Lemma 10.10 in which the codegree hypothesis bounds `d_H(v,U)`.

Everything here is `sorry`-free.
-/
import BKLO.Section10Lemma103

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-- **The greedy star decomposition.**  Under an even-neighbourhood hypothesis, a minimum-degree
hypothesis with slack `d` and the budget `2 d_H(v,U) ≤ d`, the apex stars decompose `H[U,W] ∪ H_V`
for an `H_V ⊆ H[W]` with `Δ_{H_V}(v) ≤ 2 d_H(v,U)`. -/
theorem exists_triDecomp_of_budget {H : Finset (Sym2 V)} {U W : Finset V} {d : ℕ}
    (hloop : ∀ e ∈ H, ¬ e.IsDiag) (hUW : Disjoint U W)
    (hEven : ∀ x ∈ U, Even (nbhdIn H x W).card)
    (hmindeg : ∀ x ∈ U, ∀ v ∈ nbhdIn H x W,
      (nbhdIn H x W).card / 2 + d ≤ edeg (edgesIn H (nbhdIn H x W)) v)
    (hbud : ∀ v ∈ W, 2 * degTo H v U ≤ d) :
    ∃ HV : Finset (Sym2 V), HV ⊆ edgesIn H W ∧
      TriDecomp (edgesBtw H U W ∪ HV) ∧ ∀ v : V, edeg HV v ≤ 2 * degTo H v U := by
  classical
  obtain ⟨Mx, hgood, hpair⟩ := exists_greedy_matchings hloop hUW hEven hmindeg hbud
  -- `H_V` is the union of the matchings, an edge set inside `W`
  have hHVsub : U.biUnion (fun x => famEdges (Mx x)) ⊆ edgesIn H W := by
    intro e he
    obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.1 he
    obtain ⟨f, hf, hef⟩ := Finset.mem_biUnion.1 (by rwa [famEdges] at hex)
    exact edgesIn_mono (nbhdIn_subset H x W) ((hgood x hx).edges f hf hef)
  -- the star union is exactly `H[U,W] ∪ H_V`
  have hSeq : U.biUnion (fun x => famEdges (starTriangles x (Mx x)))
      = edgesBtw H U W ∪ U.biUnion (fun x => famEdges (Mx x)) := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro e he
      obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.1 he
      obtain ⟨tri, htri, hetri⟩ := Finset.mem_biUnion.1 (by rwa [famEdges] at hex)
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 (by rwa [starTriangles] at htri)
      obtain ⟨hmem, hnd⟩ := mem_cliqueEdgesV.1 hetri
      by_cases hxe : x ∈ e
      · refine Finset.mem_union_left _ ?_
        obtain ⟨qq, rfl⟩ := Sym2.mem_iff_exists.1 hxe
        have hq : qq ∈ insert x f := hmem qq (by simp)
        have hqx : qq ≠ x := by
          intro hc
          rw [Sym2.isDiag_iff_proj_eq] at hnd
          exact hnd hc.symm
        have hqf : qq ∈ f := (Finset.mem_insert.1 hq).resolve_left hqx
        have hqN : qq ∈ nbhdIn H x W := (hgood x hx).subset f hf hqf
        rw [mem_nbhdIn] at hqN
        exact Finset.mem_filter.2 ⟨hqN.2, x, hx, qq, hqN.1, rfl⟩
      · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨x, hx, ?_⟩)
        refine Finset.mem_biUnion.2 ⟨f, hf, mem_cliqueEdgesV.2 ⟨?_, hnd⟩⟩
        intro z hz
        rcases Finset.mem_insert.1 (hmem z hz) with hzx | hzf
        · exact absurd (hzx ▸ hz) hxe
        · exact hzf
    · intro e he
      rcases Finset.mem_union.1 he with he | he
      · obtain ⟨heH, a, haU, b, hbW, rfl⟩ := Finset.mem_filter.1 he
        have hbN : b ∈ nbhdIn H a W := mem_nbhdIn.2 ⟨hbW, heH⟩
        obtain ⟨f, hf, hbf⟩ := (hgood a haU).covers b hbN
        refine Finset.mem_biUnion.2 ⟨a, haU, Finset.mem_biUnion.2
          ⟨insert a f, Finset.mem_image_of_mem _ hf, mem_cliqueEdgesV.2 ⟨?_, ?_⟩⟩⟩
        · intro z hz
          rcases Sym2.mem_iff.1 hz with rfl | rfl
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem hbf
        · rw [Sym2.isDiag_iff_proj_eq]
          intro hc
          have hab : a = b := hc
          exact (Finset.disjoint_left.1 hUW haU) (by rw [hab]; exact hbW)
      · obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.1 he
        obtain ⟨f, hf, hef⟩ := Finset.mem_biUnion.1 (by rwa [famEdges] at hex)
        exact Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_biUnion.2
          ⟨insert x f, Finset.mem_image_of_mem _ hf,
            cliqueEdges_mono (Finset.subset_insert x f) hef⟩⟩
  refine ⟨U.biUnion (fun x => famEdges (Mx x)), hHVsub, ?_, ?_⟩
  · rw [← hSeq]
    exact triDecomp_biUnion_starTriangles (fun x hx => (hgood x hx).matching) hpair
  · intro v
    by_cases hvW : v ∈ W
    · have hvU : ∀ x ∈ U, v ≠ x := fun x hx hc => (Finset.disjoint_left.1 hUW hx) (hc ▸ hvW)
      have h1 : edeg (U.biUnion (fun x => famEdges (Mx x))) v
          ≤ edeg (U.biUnion (fun x => famEdges (starTriangles x (Mx x)))) v :=
        edeg_mono (by rw [hSeq]; exact Finset.subset_union_right) v
      have h2 := edeg_biUnion_starTriangles_le_two_degTo (H := H) (W := W)
        (fun x hx => (hgood x hx).matching) hvU (fun x hx e he => (hgood x hx).subset e he)
      exact le_trans h1 h2
    · have hzero : edeg (U.biUnion (fun x => famEdges (Mx x))) v = 0 := by
        unfold edeg
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he hve
        exact hvW ((mem_edgesIn.1 (hHVsub he)).2 v hve)
      rw [hzero]
      exact Nat.zero_le _

end BKLO
