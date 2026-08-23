/-
  Part B (Phase 2) — modelling the absorbing gadget, and a NEGATIVE RESULT that corrects it.

  We first model the naive atomic absorber — a **switcher** for a single target edge `e`: an
  edge-disjoint triangle family avoiding `e` that can be *re-decomposed* to additionally cover
  exactly `e` (the toggle).

  KEY FINDING (`Switcher.elim`, proved sorry-free): this naive model is **uninhabited**. An
  edge-disjoint triangle family always covers a multiple of 3 edges, so a toggle adding exactly
  one edge would force `3a = 3b + 1` — impossible. Consequently the atomic absorber cannot
  toggle a *single* edge; it must absorb a `3`-divisible unit. This refutes the naive
  `switcher_exists` interface (it would have been a FALSE `sorry`), and pins down the shape the
  real transformer must have — exactly the kind of information a hand attempt surfaces that a
  farm would not.

  Also proved sorry-free: the quantified common-neighbour bound (`card_common_neighbors_ge`)
  and that every edge lies in a triangle under high min-degree — genuine bricks for the (yet
  to be correctly modelled) transformer.
-/
import Ax2.PartB.BKLO.Absorber

namespace Ax2.BKLO

open SimpleGraph Finset Ax2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A **switcher** for a target edge `e`: an edge-disjoint triangle family of `G` that does
not cover `e`, but admits an alternative decomposition covering exactly its own edges together
with `e`. This "toggle" is the atom of the absorption method. -/
structure Switcher (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) where
  tris : Finset (Finset V)
  isClique : ∀ t ∈ tris, G.IsNClique 3 t
  edgeDisjoint : EdgeDisjoint tris
  avoids : e ∉ coveredEdges tris
  toggle : ∃ tris' : Finset (Finset V), (∀ t ∈ tris', G.IsNClique 3 t) ∧ EdgeDisjoint tris' ∧
    coveredEdges tris' = insert e (coveredEdges tris)

/-- Edges covered by a 3-clique: exactly three. -/
theorem triEdges_card_of_isNClique (G : SimpleGraph V) [DecidableRel G.Adj] {t : Finset V}
    (ht : G.IsNClique 3 t) : (triEdges t).card = 3 := by
  rw [triEdges, Finset.sym2_eq_image, Sym2.filter_image_mk_not_isDiag, Sym2.card_image_offDiag]
  simp [SimpleGraph.IsNClique.card_eq ht]

/-- An edge-disjoint family of 3-cliques covers exactly `3 · (number of triangles)` edges. -/
theorem coveredEdges_card (G : SimpleGraph V) [DecidableRel G.Adj] {P : Finset (Finset V)}
    (hP : ∀ t ∈ P, G.IsNClique 3 t) (hPd : EdgeDisjoint P) :
    (coveredEdges P).card = 3 * P.card := by
  rw [coveredEdges, Finset.card_biUnion (fun t ht u hu hne => hPd t ht u hu hne)]
  rw [Finset.sum_congr rfl (fun t ht => triEdges_card_of_isNClique G (hP t ht))]
  simp [mul_comm]

/-- **FINDING (not an axiom): the single-edge `Switcher` model is uninhabited.** The toggle
would make an edge-disjoint triangle family cover exactly one more edge, i.e. `3·a = 3·b + 1`,
impossible. Hence the atomic absorber cannot toggle a *single* edge — it must absorb a
`3`-divisible unit. This refutes the naive `switcher_exists` interface. -/
theorem Switcher.elim (G : SimpleGraph V) [DecidableRel G.Adj] {e : Sym2 V}
    (S : Switcher G e) : False := by
  obtain ⟨tris', hcl', hd', hcov'⟩ := S.toggle
  have h1 : (coveredEdges S.tris).card = 3 * S.tris.card := coveredEdges_card G S.isClique S.edgeDisjoint
  have h2 : (coveredEdges tris').card = 3 * tris'.card := coveredEdges_card G hcl' hd'
  have h3 : (coveredEdges tris').card = (coveredEdges S.tris).card + 1 := by
    rw [hcov', Finset.card_insert_of_notMem S.avoids]
  omega

/-- **Local brick (b), quantified.** The number of common neighbours of `x` and `y` is at
least `deg x + deg y − n`. A switcher construction consumes *many* common neighbours, so this
counting lower bound (not just nonemptiness) is the useful form. -/
theorem card_common_neighbors_ge (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    G.degree x + G.degree y - Fintype.card V ≤ (G.neighborFinset x ∩ G.neighborFinset y).card := by
  have hunion : (G.neighborFinset x ∪ G.neighborFinset y).card ≤ Fintype.card V := by
    rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
  have hadd := Finset.card_union_add_card_inter (G.neighborFinset x) (G.neighborFinset y)
  rw [G.card_neighborFinset_eq_degree x, G.card_neighborFinset_eq_degree y] at hadd
  omega

/-- **Local brick (b).** If the endpoints of an edge have degrees summing to more than `n`,
they have a common neighbour. -/
theorem exists_common_neighbor (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V}
    (h : Fintype.card V < G.degree x + G.degree y) :
    (G.neighborFinset x ∩ G.neighborFinset y).Nonempty := by
  rw [← Finset.card_pos]
  have := card_common_neighbors_ge G x y
  omega

/-- **Local brick (b), triangle form.** An edge whose endpoint degrees sum to more than `n`
lies in a triangle. A genuine, sorry-free sub-fact of AC-1 (`switcher_exists`). -/
theorem exists_triangle_of_adj (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V}
    (hxy : G.Adj x y) (h : Fintype.card V < G.degree x + G.degree y) :
    ∃ z, G.IsNClique 3 ({x, y, z} : Finset V) := by
  obtain ⟨z, hz⟩ := exists_common_neighbor G h
  rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at hz
  exact ⟨z, (SimpleGraph.is3Clique_triple_iff).2 ⟨hxy, hz.1, hz.2⟩⟩

end Ax2.BKLO
