/-
  Part B (Phase 2) — BKLO transfer, interfaces + top-level assembly.

  The monolithic transfer is split into named interfaces (each a `sorry` TARGET), composed by
  `bklo_transfer_assembled` into the exact statement of the Phase-1 axiom
  `Ax2.bklo_kthree_transfer`. Filling every interface (and removing the small assembly `sorry`s)
  would de-axiomatize Part B.

  Interfaces (see `../../ROUTE`-style notes in the module docstrings):
  * B-I  `approx_of_fractional`      — fractional ⇒ approximate decomposition (nibble/Haxell–Rödl)
  * B-II₁ `reserve_absorber`         — high min-degree ⇒ absorber + residual with δ ≥ 9n/10
  * B-II₂ (inside `TriangleAbsorber`) — absorber completes a small divisible leftover
  * B-III `leftover_divisible`       — the leftover of a triangle-divisible graph is 3-divisible
  * B-fin `exact_of_cover`           — two edge-disjoint families partitioning E(G) ⇒ exact decomp
-/
import Ax2.PartB.BKLO.Defs
import Ax2.PartB.BKLO.ApproxFromPacking
import Ax2.PartB.BKLO.NibbleBridge
import Ax2.PartB.BKLO.Absorber
import Ax2.PartB.BKLO.Parity

namespace Ax2.BKLO

open SimpleGraph Finset Ax2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **B-I (nibble / Haxell–Rödl).** A fractional triangle decomposition yields, for any target
density `β > 0`, an approximate integral decomposition whose leftover has `≤ β·n²` edges.
(Engine: the Rödl nibble, project `nibble`.) NOTE: reduces to the integral-packing existence
`ν₃ ≥ (1-β)·e(G)/3` via the proved `approx_of_packing` (Ax2.PartB.BKLO.ApproxFromPacking, which
sits ABOVE this module); the remaining content is exactly that nibble packing existence. -/
theorem approx_of_fractional_asymptotic (hgap : Nibble.AX1.NibbleGapHyp) (β : ℝ)
    (hβ : 0 < β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → FractionalTriangleDecomp G →
        ∃ L : Finset (Sym2 V), L ⊆ G.edgeFinset ∧
          (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 ∧ ApproxTriangleDecomp G L :=
  approx_of_fractional_of_nibbleGap hgap β hβ


/-- **B-III (divisibility bookkeeping).** In a triangle-divisible graph, the leftover of an
approximate decomposition has a number of edges divisible by 3 (each triangle removes 3 edges,
and `3 ∣ e(G)`). -/
theorem leftover_divisible (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdiv : TriangleDivisible G) {L : Finset (Sym2 V)} (hLsub : L ⊆ G.edgeFinset)
    (hL : ApproxTriangleDecomp G L) : 3 ∣ L.card := by
  rcases hL with ⟨P, hP, hdis, hcov⟩
  have htri : ∀ t ∈ P, (triEdges t).card = 3 := by
    intro t ht
    rw [triEdges, Finset.sym2_eq_image]
    rw [Sym2.filter_image_mk_not_isDiag, Sym2.card_image_offDiag]
    simp [SimpleGraph.IsNClique.card_eq (hP t ht)]
  have hpw : (↑P : Set (Finset V)).PairwiseDisjoint triEdges := by
    intro t ht u hu hne
    exact hdis t ht u hu hne
  have hcardcov : (coveredEdges P).card = 3 * P.card := by
    rw [coveredEdges, Finset.card_biUnion hpw]
    calc
      ∑ u ∈ P, (triEdges u).card = ∑ _u ∈ P, 3 := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [htri t ht]
      _ = 3 * P.card := by simp [Nat.mul_comm]
  have hsum := Finset.card_sdiff_add_card_eq_card hLsub
  rw [← hcov, hcardcov] at hsum
  rcases hdiv.1 with ⟨k, hk⟩
  refine ⟨k - P.card, ?_⟩
  omega

/-- **B-III′ (leftover has even degrees).** The leftover of an approximate decomposition of a
triangle-divisible graph has every vertex-degree even: `deg_L(v) = deg_G(v) − deg_covered(v)`,
both even (the graph is triangle-divisible, the covered part is triangle-covered). This is the
even-degree half of triangle-divisibility that `TriangleAbsorber` now (correctly) requires. -/
theorem leftover_even_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdiv : TriangleDivisible G) {L : Finset (Sym2 V)} (hLsub : L ⊆ G.edgeFinset)
    (hL : ApproxTriangleDecomp G L) (v : V) :
    Even ((L.filter (fun e => v ∈ e)).card) := by
  classical
  obtain ⟨P, hPcl, hPd, hPcov⟩ := hL
  have hP3 : ∀ t ∈ P, t.card = 3 := fun t ht => (hPcl t ht).card_eq
  have hpar := coveredEdges_degree_even P hP3 hPd v
  have hsplit : (G.edgeFinset.filter (fun e => v ∈ e)).card
      = ((coveredEdges P).filter (fun e => v ∈ e)).card
        + (L.filter (fun e => v ∈ e)).card := by
    rw [hPcov, ← Finset.card_union_of_disjoint]
    · congr 1
      ext e
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨he, hv⟩
        by_cases hLe : e ∈ L
        · exact Or.inr ⟨hLe, hv⟩
        · exact Or.inl ⟨⟨he, hLe⟩, hv⟩
      · rintro (⟨⟨he, _⟩, hv⟩ | ⟨hLe, hv⟩)
        · exact ⟨he, hv⟩
        · exact ⟨hLsub hLe, hv⟩
    · rw [Finset.disjoint_left]
      intro e h1 h2
      rw [Finset.mem_filter, Finset.mem_sdiff] at h1
      rw [Finset.mem_filter] at h2
      exact h1.1.2 h2.1
  have hdeg : (G.edgeFinset.filter (fun e => v ∈ e)).card = G.degree v := by
    rw [← G.incidenceFinset_eq_filter, G.card_incidenceFinset_eq_degree]
  have hGeven : Even (((coveredEdges P).filter (fun e => v ∈ e)).card
      + (L.filter (fun e => v ∈ e)).card) := by
    rw [← hsplit, hdeg]; exact hdiv.2 v
  exact (Nat.even_add.mp hGeven).mp hpar

/-- **B-fin (partition ⇒ exact decomposition).** Two edge-disjoint triangle families whose edge
sets are disjoint and cover all of `E(G)` assemble into an (integral) triangle decomposition. -/
theorem exact_of_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    {P Q : Finset (Finset V)} (hP : ∀ t ∈ P, G.IsNClique 3 t) (hQ : ∀ t ∈ Q, G.IsNClique 3 t)
    (hPd : EdgeDisjoint P) (hQd : EdgeDisjoint Q)
    (hdisj : Disjoint (coveredEdges P) (coveredEdges Q))
    (hcov : coveredEdges P ∪ coveredEdges Q = G.edgeFinset) :
    TriangleDecomposable G := by
  refine ⟨P ∪ Q, ?_, ?_⟩
  · intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact hP t ht
    · exact hQ t ht
  · intro e he
    have hecov : e ∈ coveredEdges P ∪ coveredEdges Q := by
      rw [hcov]
      exact he
    rcases Finset.mem_union.mp hecov with heP | heQ
    · simp only [coveredEdges, Finset.mem_biUnion] at heP
      rcases heP with ⟨t, htP, het⟩
      refine ⟨t, ⟨Finset.mem_union_left Q htP, het⟩, ?_⟩
      intro t' ht'
      rcases ht' with ⟨ht'union, het'⟩
      rcases Finset.mem_union.mp ht'union with ht'P | ht'Q
      · by_contra hne
        have hd := hPd t htP t' ht'P (Ne.symm hne)
        exact (Finset.disjoint_left.mp hd) het het'
      · have hePc : e ∈ coveredEdges P := by
          simp only [coveredEdges, Finset.mem_biUnion]
          exact ⟨t, htP, het⟩
        have heQc : e ∈ coveredEdges Q := by
          simp only [coveredEdges, Finset.mem_biUnion]
          exact ⟨t', ht'Q, het'⟩
        exact False.elim ((Finset.disjoint_left.mp hdisj) hePc heQc)
    · simp only [coveredEdges, Finset.mem_biUnion] at heQ
      rcases heQ with ⟨t, htQ, het⟩
      refine ⟨t, ⟨Finset.mem_union_right P htQ, het⟩, ?_⟩
      intro t' ht'
      rcases ht' with ⟨ht'union, het'⟩
      rcases Finset.mem_union.mp ht'union with ht'P | ht'Q
      · have hePc : e ∈ coveredEdges P := by
          simp only [coveredEdges, Finset.mem_biUnion]
          exact ⟨t', ht'P, het'⟩
        have heQc : e ∈ coveredEdges Q := by
          simp only [coveredEdges, Finset.mem_biUnion]
          exact ⟨t, htQ, het⟩
        exact False.elim ((Finset.disjoint_left.mp hdisj) hePc heQc)
      · by_contra hne
        have hd := hQd t htQ t' ht'Q (Ne.symm hne)
        exact (Finset.disjoint_left.mp hd) het het'

/-- A 3-clique of a subgraph (fewer edges) is a 3-clique of the ambient graph. -/
theorem isNClique_of_le {G G' : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (hle : G'.edgeFinset ⊆ G.edgeFinset) {t : Finset V} (ht : G'.IsNClique 3 t) :
    G.IsNClique 3 t := by
  refine ⟨?_, ht.2⟩
  intro a ha b hb hab
  have h' : G'.Adj a b := ht.1 ha hb hab
  have hmem : s(a, b) ∈ G.edgeFinset :=
    hle (by rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact h')
  rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hmem

end Ax2.BKLO
