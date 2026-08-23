/-
# Star + matching → edge-disjoint triangles (the atomic step of BKLO Lemma 10.3, r = 2)

BKLO's degree-reduction lemma (Lemma 10.3) reduces the maximum degree of a triangle-decomposition
remainder by, for each apex `x`, choosing a **perfect matching** `M` in the neighbourhood
`N_H(x, V)` (a `K_r`-factor with `r = 2`, existing by Dirac's theorem — our
`BKLO.perfectMatchingDirac_holds`) and forming the triangles `{x, a, b}` for `{a,b} ∈ M`.

This file proves, `sorry`-free, the atomic combinatorial fact that makes that step work: if `M` is a
matching (pairwise vertex-disjoint edges) avoiding `x`, the triangles `insert x e` for `e ∈ M` are
pairwise **edge-disjoint** and each has three vertices, so their edge union — the star of `x` to the
matched vertices together with `M` itself — is triangle-decomposable.

This is the per-apex building block of the greedy loop of Lemma 10.3; the loop assembles these across
all apices `x ∈ U`, with the edge bookkeeping supplied separately.

Everything here is `sorry`-free.
-/
import BKLO.Transformer
import BKLO.TransportV

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- A `Finset (Finset V)` is a **matching** avoiding `x`: every member is a `2`-element set, the
members are pairwise disjoint, and none contains `x`. -/
structure IsMatchingAvoiding (M : Finset (Finset V)) (x : V) : Prop where
  card_two : ∀ e ∈ M, e.card = 2
  pairwise_disjoint : (M : Set (Finset V)).Pairwise Disjoint
  avoids : ∀ e ∈ M, x ∉ e

/-- The triangles of the star at `x` over a matching `M`: `{x} ∪ e` for each edge `e ∈ M`. -/
def starTriangles (x : V) (M : Finset (Finset V)) : Finset (Finset V) :=
  M.image (insert x)

/-- Each star triangle has exactly three vertices. -/
theorem card_starTriangle {x : V} {M : Finset (Finset V)} (h : IsMatchingAvoiding M x)
    {t : Finset V} (ht : t ∈ starTriangles x M) : t.card = 3 := by
  rw [starTriangles, Finset.mem_image] at ht
  obtain ⟨e, he, rfl⟩ := ht
  rw [Finset.card_insert_of_notMem (h.avoids e he), h.card_two e he]

/-- **The star triangles over a matching are pairwise edge-disjoint.**  Two triangles `{x,a,b}` and
`{x,c,d}` from disjoint matching edges share only `x`, hence no edge. -/
theorem starTriangles_pairwise_edgeDisjoint {x : V} {M : Finset (Finset V)}
    (h : IsMatchingAvoiding M x) :
    ∀ t ∈ starTriangles x M, ∀ t' ∈ starTriangles x M, t ≠ t' →
      Disjoint (cliqueEdges t) (cliqueEdges t') := by
  intro t ht t' ht' htt'
  rw [starTriangles, Finset.mem_image] at ht ht'
  obtain ⟨e, he, rfl⟩ := ht
  obtain ⟨f, hf, rfl⟩ := ht'
  have hef : e ≠ f := fun h' => htt' (by rw [h'])
  have hd : Disjoint e f := h.pairwise_disjoint he hf hef
  -- every vertex shared by `insert x e` and `insert x f` is `x`
  have hmem : ∀ z, z ∈ insert x e → z ∈ insert x f → z = x := by
    intro z hze hzf
    rcases Finset.mem_insert.1 hze with h1 | h1
    · exact h1
    · rcases Finset.mem_insert.1 hzf with h2 | h2
      · exact h2
      · exact absurd (Finset.disjoint_left.1 hd h1) (fun hcon => hcon h2)
  -- a common edge would have both endpoints in that intersection, hence be diagonal
  refine Finset.disjoint_left.2 ?_
  intro g
  induction g using Sym2.ind with
  | _ a b =>
    intro hge hgf
    obtain ⟨hg_e, hgnd⟩ := mem_cliqueEdgesV.1 hge
    obtain ⟨hg_f, -⟩ := mem_cliqueEdgesV.1 hgf
    apply hgnd
    have ha : a ∈ insert x e := hg_e a (by simp)
    have hb : b ∈ insert x e := hg_e b (by simp)
    have ha' : a ∈ insert x f := hg_f a (by simp)
    have hb' : b ∈ insert x f := hg_f b (by simp)
    rw [Sym2.isDiag_iff_proj_eq]
    exact (hmem a ha ha').trans (hmem b hb hb').symm

/-- **The star of `x` over a matching is triangle-decomposable.**  Its natural triangle family
`starTriangles x M` is an edge-disjoint family of triangles, so the edge set it spans — the star
edges from `x` to the matched vertices together with the matching `M` — has a triangle decomposition.
This is the atomic decomposable unit the greedy loop of BKLO Lemma 10.3 produces at each apex. -/
theorem triDecomp_famEdges_starTriangles {x : V} {M : Finset (Finset V)}
    (h : IsMatchingAvoiding M x) :
    TriDecomp (famEdges (starTriangles x M)) :=
  ⟨starTriangles x M, fun _ ht => card_starTriangle h ht,
    starTriangles_pairwise_edgeDisjoint h, rfl⟩

end BKLO
