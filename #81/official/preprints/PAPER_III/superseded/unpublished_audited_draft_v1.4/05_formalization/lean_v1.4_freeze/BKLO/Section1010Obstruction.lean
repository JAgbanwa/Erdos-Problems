/-
# The apex-degree obstruction for BKLO Lemma 10.10 (`r = 2`)

Lemma 10.10 asks for a subgraph `H'_V ⊆ H[V]` such that `H[U,V] ∪ H'_V` has a triangle
decomposition and `Δ(H'_V) ≤ 2α|V|`.  This file proves the *lower* bound that any such `H'_V`
must satisfy:

  `d_H(y, U) ≤ Δ_{H'_V}(y)`  for every `y ∈ V`.

The reason is structural and has nothing to do with the hypotheses of Lemma 10.10.  In
`H[U,V] ∪ H'_V` there are no edges inside `U`, so every triangle of a decomposition either lies
inside `V` or has exactly one apex `x ∈ U` and one edge `{y,z}` inside `V`.  Hence the `d_H(y,U)`
edges from `y` to `U` are covered by `d_H(y,U)` *distinct* triangles, each of which spends one
edge of `H'_V` at `y`.

This is the counting behind `BKLO.exists_triDecomp_of_budget` being sharp, and it is the reason
why BKLO's hierarchy `ρ ≪ α, 1/k` is *needed* in Lemma 10.10: hypothesis (iv) allows
`d_H(y,U) = 2kρ|V|`, so the conclusion `Δ(H'_V) ≤ 2α|V|` is only possible when `kρ ≲ α`.

Everything here is `sorry`-free.
-/
import BKLO.Section1012Defs
import Mathlib.Data.Finset.Functor

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- In `H[U,W] ∪ HV` with `HV ⊆ H[W]` and `U`, `W` disjoint there is no edge with both ends in
`U`. -/
theorem not_mem_of_both_mem_U {H HV : Finset (Sym2 V)} {U W : Finset V} (hUW : Disjoint U W)
    (hHV : HV ⊆ edgesIn H W) {a b : V} (ha : a ∈ U) (hb : b ∈ U) :
    s(a, b) ∉ edgesBtw H U W ∪ HV := by
  intro hmem
  rcases Finset.mem_union.1 hmem with h | h
  · obtain ⟨-, c, hc, d, hd, hcd⟩ := Finset.mem_filter.1 h
    rcases Sym2.eq_iff.1 hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (Finset.disjoint_left.1 hUW hb) hd
    · exact (Finset.disjoint_left.1 hUW ha) hd
  · exact (Finset.disjoint_left.1 hUW ha) ((mem_edgesIn.1 (hHV h)).2 a (by simp))

/-- **The apex-degree obstruction.**  If `H[U,W] ∪ HV` has a triangle decomposition, with
`HV ⊆ H[W]` and `U`, `W` disjoint, then every `w ∈ W` has at least `d_H(w,U)` edges of `HV` at
it. -/
theorem degTo_le_edeg_of_triDecomp {H HV : Finset (Sym2 V)} {U W : Finset V}
    (hUW : Disjoint U W) (hHV : HV ⊆ edgesIn H W)
    (hdec : TriDecomp (edgesBtw H U W ∪ HV)) {w : V} (hw : w ∈ W) :
    degTo H w U ≤ edeg HV w := by
  classical
  obtain ⟨P, hcard3, hdisj, hedges⟩ := hdec
  have hsubG : ∀ t ∈ P, cliqueEdges t ⊆ edgesBtw H U W ∪ HV := by
    intro t ht
    rw [← hedges]
    exact Finset.subset_biUnion_of_mem cliqueEdges ht
  -- for every apex `a` at `w`, a triangle `{a, w, z a}` with `s(w, z a) ∈ HV`
  have key : ∀ a ∈ nbhdIn H w U, ∃ (z : V) (t : Finset V), t ∈ P ∧ a ∈ t ∧ w ∈ t ∧ z ∈ t ∧
      z ≠ w ∧ z ≠ a ∧ s(w, z) ∈ HV := by
    intro a ha
    rw [mem_nbhdIn] at ha
    obtain ⟨haU, haH⟩ := ha
    have haw : a ≠ w := fun hc => (Finset.disjoint_left.1 hUW haU) (hc ▸ hw)
    have hedge : s(a, w) ∈ edgesBtw H U W ∪ HV := by
      refine Finset.mem_union_left _ (Finset.mem_filter.2 ⟨?_, a, haU, w, hw, rfl⟩)
      rw [Sym2.eq_swap] at haH
      exact haH
    rw [← hedges, famEdges, Finset.mem_biUnion] at hedge
    obtain ⟨t, ht, hat⟩ := hedge
    obtain ⟨hmem, -⟩ := mem_cliqueEdgesV.1 hat
    have hat' : a ∈ t := hmem a (by simp)
    have hwt : w ∈ t := hmem w (by simp)
    -- a third vertex of the triangle
    have hcard : ({a, w} : Finset V) ⊆ t := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hat'
      · rw [Finset.mem_singleton] at hx; exact hx ▸ hwt
    have hlt : ({a, w} : Finset V).card < t.card := by
      rw [hcard3 t ht, Finset.card_insert_of_notMem (by simpa using haw), Finset.card_singleton]
      omega
    obtain ⟨z, hzt, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({a, w} : Finset V)) (t := t) hlt
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    obtain ⟨hza, hzw⟩ := hz
    -- the edge `{w, z}` lies in `HV`
    have hwz : s(w, z) ∈ edgesBtw H U W ∪ HV := by
      refine hsubG t ht (mem_cliqueEdgesV.2 ⟨?_, ?_⟩)
      · intro x hx
        rcases Sym2.mem_iff.1 hx with rfl | rfl
        · exact hwt
        · exact hzt
      · rw [Sym2.isDiag_iff_proj_eq]
        exact fun hc => hzw hc.symm
    have hwzHV : s(w, z) ∈ HV := by
      rcases Finset.mem_union.1 hwz with h | h
      · obtain ⟨-, c, hc, d, hd, hcd⟩ := Finset.mem_filter.1 h
        rcases Sym2.eq_iff.1 hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd hw (Finset.disjoint_left.1 hUW hc)
        · -- `z ∈ U`, but then the edge `{a,z}` of the triangle would join two vertices of `U`
          exact absurd (hsubG t ht (mem_cliqueEdgesV.2 ⟨by
              intro x hx
              rcases Sym2.mem_iff.1 hx with rfl | rfl
              · exact hat'
              · exact hzt, by
              rw [Sym2.isDiag_iff_proj_eq]
              exact fun hc => hza hc.symm⟩))
            (not_mem_of_both_mem_U hUW hHV haU hc)
      · exact h
    exact ⟨z, t, ht, hat', hwt, hzt, hzw, hza, hwzHV⟩
  choose! z tri htri hatri hwtri hztri hzw hza hHVz using key
  -- `a ↦ s(w, z a)` is injective on the apices at `w`
  have hinj : Set.InjOn (fun a => s(w, z a)) (nbhdIn H w U) := by
    intro a ha b hb hab
    by_contra hne
    have hzab : z a = z b := by
      rcases Sym2.eq_iff.1 hab with ⟨-, h⟩ | ⟨h1, h2⟩
      · exact h
      · exact absurd h2 (hzw a ha)
    have haU : a ∈ U := (mem_nbhdIn.1 ha).1
    have hbU : b ∈ U := (mem_nbhdIn.1 hb).1
    by_cases hsame : tri a = tri b
    · -- the two apices lie in the same triangle, giving an edge inside `U`
      refine not_mem_of_both_mem_U hUW hHV haU hbU (hsubG (tri a) (htri a ha)
        (mem_cliqueEdgesV.2 ⟨?_, ?_⟩))
      · intro x hx
        rcases Sym2.mem_iff.1 hx with hx | hx
        · exact hx ▸ hatri a ha
        · rw [hx, hsame]; exact hatri b hb
      · rw [Sym2.isDiag_iff_proj_eq]; exact hne
    · -- distinct triangles cannot share the edge `{w, z a}`
      have h1 : s(w, z a) ∈ cliqueEdges (tri a) := by
        refine mem_cliqueEdgesV.2 ⟨?_, ?_⟩
        · intro x hx
          rcases Sym2.mem_iff.1 hx with rfl | rfl
          · exact hwtri a ha
          · exact hztri a ha
        · rw [Sym2.isDiag_iff_proj_eq]; exact fun hc => hzw a ha hc.symm
      have h2 : s(w, z a) ∈ cliqueEdges (tri b) := by
        rw [hzab]
        refine mem_cliqueEdgesV.2 ⟨?_, ?_⟩
        · intro x hx
          rcases Sym2.mem_iff.1 hx with rfl | rfl
          · exact hwtri b hb
          · exact hztri b hb
        · rw [Sym2.isDiag_iff_proj_eq]; exact fun hc => hzw b hb hc.symm
      exact (Finset.disjoint_left.1 (hdisj _ (htri a ha) _ (htri b hb) hsame) h1) h2
  calc degTo H w U = ((nbhdIn H w U).image (fun a => s(w, z a))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ edeg HV w := by
        refine Finset.card_le_card ?_
        intro e he
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 he
        exact Finset.mem_filter.2 ⟨hHVz a ha, by simp⟩

end BKLO
