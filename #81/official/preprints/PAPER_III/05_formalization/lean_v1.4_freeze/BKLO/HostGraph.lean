/-
# The host graph induced on a finite vertex set.

The `§5` embedding machinery (`BKLO.exists_embedding`, `BKLO.exists_placement`) is stated for a
`SimpleGraph` on a `Fintype`.  The bounded-leftover absorber, like the rest of the §10 vocabulary,
works with an edge set `E : Finset (Sym2 V)` over an arbitrary vertex type together with a finite
vertex set `S : Finset V`.  This file bridges the two: `hostGraph T S` is the graph on the subtype
`↥S` whose edges are the edges of `T`, and its degrees, minimum degree and common neighbourhoods
are related to the edge degrees of `T`.
-/
import BKLO.MapTransport
import BKLO.Embedding

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- The graph on `↥S` whose adjacency is given by the edge set `T`. -/
def hostGraph (T : Finset (Sym2 V)) (S : Finset V) : SimpleGraph {x // x ∈ S} where
  Adj a b := a ≠ b ∧ s((a : V), (b : V)) ∈ T
  symm := by
    intro a b h
    exact ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩
  loopless := ⟨fun a h => h.1 rfl⟩

instance hostGraph_decidableRel (T : Finset (Sym2 V)) (S : Finset V) :
    DecidableRel (hostGraph T S).Adj :=
  fun a b => decidable_of_iff (a ≠ b ∧ s((a : V), (b : V)) ∈ T) Iff.rfl

theorem hostGraph_edge_mem {T : Finset (Sym2 V)} {S : Finset V} {e : Sym2 {x // x ∈ S}}
    (he : e ∈ (hostGraph T S).edgeFinset) : Sym2.map (fun a : {x // x ∈ S} => (a : V)) e ∈ T := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    simpa using he.2

/-- Every vertex of the host graph has degree at least its edge degree in `T`. -/
theorem edeg_le_hostGraph_degree {T : Finset (Sym2 V)} {S : Finset V} (hT : T ⊆ cliqueEdges S)
    (a : {x // x ∈ S}) : edeg T (a : V) ≤ (hostGraph T S).degree a := by
  classical
  set g : Sym2 V → V := fun e => if h : (a : V) ∈ e then Sym2.Mem.other' h else (a : V) with hg
  have hspec : ∀ e ∈ T.filter (fun e => (a : V) ∈ e),
      s((a : V), g e) = e ∧ g e ∈ S ∧ g e ≠ (a : V) := by
    intro e he
    obtain ⟨heT, hae⟩ := Finset.mem_filter.1 he
    have hgdef : g e = Sym2.Mem.other' hae := by simp [hg, dif_pos hae]
    have hs : s((a : V), g e) = e := by rw [hgdef]; exact Sym2.other_spec' hae
    have hmem : g e ∈ e := by rw [hgdef]; exact Sym2.other_mem' hae
    have hcl := mem_cliqueEdgesV.1 (hT heT)
    refine ⟨hs, hcl.1 _ hmem, ?_⟩
    intro hcon
    refine hcl.2 ?_
    rw [← hs, hcon]
    simp
  have himg : (T.filter (fun e => (a : V) ∈ e)).image g
      ⊆ ((hostGraph T S).neighborFinset a).image (fun b : {x // x ∈ S} => (b : V)) := by
    intro w hw
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨hs, hS, hne⟩ := hspec e he
    refine Finset.mem_image.2 ⟨⟨g e, hS⟩, ?_, rfl⟩
    rw [SimpleGraph.mem_neighborFinset]
    refine ⟨?_, ?_⟩
    · intro hcon
      exact hne (congrArg Subtype.val hcon).symm
    · simpa [hs] using (Finset.mem_filter.1 he).1
  have hinj : Set.InjOn g (T.filter (fun e => (a : V) ∈ e)) := by
    intro e he e' he' heq
    have h1 := (hspec e he).1
    have h2 := (hspec e' he').1
    rw [← h1, ← h2, heq]
  calc edeg T (a : V) = ((T.filter (fun e => (a : V) ∈ e)).image g).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (((hostGraph T S).neighborFinset a).image (fun b : {x // x ∈ S} => (b : V))).card :=
        Finset.card_le_card himg
    _ = (hostGraph T S).degree a := by
        rw [Finset.card_image_of_injective _ Subtype.val_injective]
        rfl

/-- A lower bound on the size of common neighbourhoods in the host graph, in the form needed by
the greedy embedding: if every vertex of `S` has `T`-degree at least `(9/10)|S|` then every set of
at most `9` vertices has at least `|S|/10` common neighbours. -/
theorem card_commonNbrs_host {T : Finset (Sym2 V)} {S : Finset V} (hT : T ⊆ cliqueEdges S)
    (hne : S.Nonempty) (hdeg : ∀ v ∈ S, 9 * S.card ≤ 10 * edeg T v)
    (Q : Finset {x // x ∈ S}) (hQ : Q.card ≤ 9) :
    S.card ≤ 10 * (commonNbrs (hostGraph T S) Q).card := by
  classical
  have hcardS : Fintype.card {x // x ∈ S} = S.card := Fintype.card_coe S
  have : Nonempty {x // x ∈ S} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hmin : 9 * S.card ≤ 10 * (hostGraph T S).minDegree := by
    have hall : ∀ a : {x // x ∈ S}, (9 * S.card + 9) / 10 ≤ (hostGraph T S).degree a := by
      intro a
      have h1 := edeg_le_hostGraph_degree hT a
      have h2 := hdeg (a : V) a.2
      omega
    have := SimpleGraph.le_minDegree_of_forall_le_degree (G := hostGraph T S)
      ((9 * S.card + 9) / 10) hall
    omega
  have hbase := card_commonNbrs_ge (hostGraph T S) Q
  rw [hcardS] at hbase
  have hmindeg_le : (hostGraph T S).minDegree ≤ S.card := by
    have := SimpleGraph.minDegree_le_degree (hostGraph T S) ⟨hne.choose, hne.choose_spec⟩
    have hd := (hostGraph T S).degree_lt_card_verts ⟨hne.choose, hne.choose_spec⟩
    omega
  have hmul : Q.card * (S.card - (hostGraph T S).minDegree)
      ≤ 9 * (S.card - (hostGraph T S).minDegree) := Nat.mul_le_mul_right _ hQ
  omega

end BKLO
