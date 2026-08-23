/-
# Nibble — why the two "cheap" routes to `DenseGlobalSmallLeftover` cannot work

`Nibble.DenseGlobalSmallLeftover` asks for an `o(|V|²)`-leftover triangle packing at the Dross
density `9|V| ≤ 10 δ(G)`, while the library's unconditional nibble output
`Nibble.dense_approx_global` only delivers its leftover in the near-complete band
`δ(G) ≥ θ|V|` with `θ = 1 − μ/2` close to `1`.  Two routes suggest themselves for bridging the gap.
This file refutes both, concretely.

## Route (c): "clean up to a near-complete induced subgraph"

`Nibble.multipartite k m` is the complete `k`-partite graph with parts of size `m`
(vertices `Fin k × Fin m`, adjacency `p.1 ≠ q.1`).  For `k = 10` it sits exactly on the Dross
density (`Nibble.multipartite_ten_dross`), and

* `Nibble.multipartite_ten_no_dense_induced` — **every** nonempty vertex subset `S` contains a
  vertex whose induced degree is at most `(9/10)|S|`.  So no induced subgraph, of any size, ever
  enters the near-complete band `θ > 9/10`: passing to induced subgraphs cannot buy density.

## Route (a): "iterate the nibble on the residual graph"

* `Nibble.matching_eq_empty_of_cliqueFree` — in a triangle-free graph the *only* matching of the
  edge-type triangle hypergraph is the empty one;
* `Nibble.multipartite_two_cliqueFree`, `Nibble.multipartite_two_leftover` — the complete bipartite
  graph `K_{m,m}` is triangle-free and every matching there leaves the *full*
  `uncoveredTot = |V|²/2` incidence count.

Leftover graphs are triangle-free by `Nibble.no_free_triangle` (a potential-minimal matching leaves
no triangle with three uncovered edges), and `K_{m,m}` is exactly the extremal leftover behind the
`1/2` wall of `Nibble.dense_uncoveredAt_le_half`.  Re-running any triangle-packing theorem on such a
residual gains *nothing*, since it contains no triangle at all — and the residual carries no density
hypothesis to feed back into `Nibble.dense_approx_global`.

Together with `Nibble.not_nibbleBandFifth` (route (b): the general band-`1/5` nibble is false), the
three obvious routes are closed, and the remaining content of `DenseGlobalSmallLeftover` is a
genuinely global input (a near-perfect fractional triangle decomposition at density `9/10`).

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DenseTriangleNibbleDegProof

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

/-! ### The complete multipartite graph -/

/-- The complete `k`-partite graph with parts of size `m`. -/
def multipartite (k m : ℕ) : SimpleGraph (Fin k × Fin m) where
  Adj p q := p.1 ≠ q.1
  symm := fun _ _ h => h.symm
  loopless := ⟨fun _ h => h rfl⟩

instance (k m : ℕ) : DecidableRel (multipartite k m).Adj :=
  fun p q => inferInstanceAs (Decidable (p.1 ≠ q.1))

@[simp] theorem multipartite_adj {k m : ℕ} (p q : Fin k × Fin m) :
    (multipartite k m).Adj p q ↔ p.1 ≠ q.1 := Iff.rfl

theorem card_multipartite_vtx (k m : ℕ) : Fintype.card (Fin k × Fin m) = k * m := by
  simp

/-- The fibre of a first coordinate has `m` elements. -/
theorem card_fibre (k m : ℕ) (i : Fin k) :
    ((Finset.univ : Finset (Fin k × Fin m)).filter (fun q => q.1 = i)).card = m := by
  classical
  have h : ((Finset.univ : Finset (Fin k × Fin m)).filter (fun q => q.1 = i))
      = ({i} : Finset (Fin k)) ×ˢ (Finset.univ : Finset (Fin m)) := by
    ext ⟨a, b⟩; simp [eq_comm]
  rw [h, Finset.card_product, Finset.card_singleton, Finset.card_univ, Fintype.card_fin, one_mul]

/-- Every vertex of the complete `k`-partite graph has degree `(k − 1)m`. -/
theorem multipartite_degree (k m : ℕ) (p : Fin k × Fin m) :
    (multipartite k m).degree p = k * m - m := by
  classical
  have hdeg : (multipartite k m).degree p
      = ((Finset.univ : Finset (Fin k × Fin m)).filter (fun q => ¬ (q.1 = p.1))).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext q
    simp [SimpleGraph.mem_neighborFinset, ne_comm]
  have hnot : ((Finset.univ : Finset (Fin k × Fin m)).filter (fun q => ¬ (q.1 = p.1)))
      = (Finset.univ : Finset (Fin k × Fin m))
        \ ((Finset.univ : Finset (Fin k × Fin m)).filter (fun q => q.1 = p.1)) :=
    Finset.filter_not _ _
  rw [hdeg, hnot, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
    card_multipartite_vtx, card_fibre]

/-- The complete `10`-partite graph sits exactly on the Dross density `9|V| ≤ 10 δ(G)`. -/
theorem multipartite_ten_dross (m : ℕ) (hm : 0 < m) :
    9 * Fintype.card (Fin 10 × Fin m) ≤ 10 * (multipartite 10 m).minDegree := by
  have hne : Nonempty (Fin 10 × Fin m) := ⟨⟨⟨0, by omega⟩, ⟨0, hm⟩⟩⟩
  have hmin : 9 * m ≤ (multipartite 10 m).minDegree := by
    refine SimpleGraph.le_minDegree_of_forall_le_degree _ _ (fun v => ?_)
    rw [multipartite_degree]
    omega
  rw [card_multipartite_vtx]
  omega

/-! ### Route (c) is closed: no induced subgraph is near-complete -/

/-- **Route (c) refuted.**  In the complete `10`-partite graph every nonempty vertex set `S` has a
vertex whose induced degree is at most `(9/10)|S|`; so no induced subgraph — of any size — reaches
the near-complete band `δ ≥ θ|S|` with `θ > 9/10` required by `Nibble.dense_approx_global`. -/
theorem multipartite_ten_no_dense_induced (m : ℕ) {S : Finset (Fin 10 × Fin m)} (hS : S.Nonempty) :
    ∃ v ∈ S, 10 * (S.filter (fun u => (multipartite 10 m).Adj v u)).card ≤ 9 * S.card := by
  classical
  have hsum : S.card = ∑ i : Fin 10, (S.filter (fun q => q.1 = i)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ x.1)
  -- pigeonhole: some part carries at least a tenth of `S`
  obtain ⟨i, -, hi⟩ : ∃ i ∈ (Finset.univ : Finset (Fin 10)), S.card ≤ 10 * (S.filter
      (fun q => q.1 = i)).card := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∑ i : Fin 10, (S.filter (fun q => q.1 = i)).card * 10
        ≤ ∑ _i : Fin 10, (S.card - 1) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      have := hcon i hi
      omega
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
    have hs10 : (∑ i : Fin 10, (S.filter (fun q => q.1 = i)).card) * 10
        = ∑ i : Fin 10, (S.filter (fun q => q.1 = i)).card * 10 := by
      rw [Finset.sum_mul]
    have hpos : 1 ≤ S.card := Finset.card_pos.mpr hS
    omega
  have hne : (S.filter (fun q => q.1 = i)).Nonempty := by
    rw [← Finset.card_pos]
    have hpos : 1 ≤ S.card := Finset.card_pos.mpr hS
    omega
  obtain ⟨v, hv⟩ := hne
  obtain ⟨hvS, hvi⟩ := Finset.mem_filter.mp hv
  refine ⟨v, hvS, ?_⟩
  -- the neighbours of `v` inside `S` avoid `v`'s own part
  have hsub : S.filter (fun u => (multipartite 10 m).Adj v u) ⊆ S \ S.filter (fun q => q.1 = i) := by
    intro u hu
    obtain ⟨huS, hadj⟩ := Finset.mem_filter.mp hu
    rw [Finset.mem_sdiff]
    refine ⟨huS, fun hmem => ?_⟩
    have hui : u.1 = i := (Finset.mem_filter.mp hmem).2
    rw [multipartite_adj] at hadj
    exact hadj (by rw [hvi, hui])
  have hcard : (S.filter (fun u => (multipartite 10 m).Adj v u)).card
      ≤ S.card - (S.filter (fun q => q.1 = i)).card := by
    refine le_trans (Finset.card_le_card hsub) ?_
    rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  omega

/-- Real-valued form of `Nibble.multipartite_ten_no_dense_induced`. -/
theorem multipartite_ten_no_dense_induced_real (m : ℕ) {θ : ℝ} (hθ : 9 / 10 < θ)
    {S : Finset (Fin 10 × Fin m)} (hS : S.Nonempty) :
    ∃ v ∈ S, ((S.filter (fun u => (multipartite 10 m).Adj v u)).card : ℝ) < θ * (S.card : ℝ) := by
  obtain ⟨v, hvS, hv⟩ := multipartite_ten_no_dense_induced m hS
  refine ⟨v, hvS, ?_⟩
  have hR : 10 * ((S.filter (fun u => (multipartite 10 m).Adj v u)).card : ℝ)
      ≤ 9 * (S.card : ℝ) := by exact_mod_cast hv
  have hpos : (0 : ℝ) < (S.card : ℝ) := by
    have : 0 < S.card := Finset.card_pos.mpr hS
    exact_mod_cast this
  nlinarith only [hθ, hR, hpos]

/-! ### Route (a) is closed: a triangle-free residual admits no triangle at all -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- In a triangle-free graph the edge-type triangle hypergraph is empty. -/
theorem triangleHypergraphSub_eq_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.CliqueFree 3) : triangleHypergraphSub G = ∅ := by
  rw [triangleHypergraphSub, SimpleGraph.cliqueFinset_eq_empty_iff.mpr h, Finset.image_empty]

/-- **In a triangle-free graph every triangle packing is empty.** -/
theorem matching_eq_empty_of_cliqueFree (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.CliqueFree 3) {M : Finset (Finset (EdgeV G))}
    (hM : IsMatching (triangleHypergraphSub G) M) : M = ∅ := by
  rw [← Finset.subset_empty, ← triangleHypergraphSub_eq_empty G h]
  exact hM.subset

/-- Each graph edge at `v` is an uncovered hypergraph vertex of the empty packing, so the empty
packing leaves at least `deg v` uncovered hypergraph vertices at `v`. -/
theorem degree_le_card_uncoveredAt_empty (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v ≤ (uncoveredAt G ∅ v).card := by
  classical
  have hinj : Set.InjOn (fun u => ({v, u} : Finset V)) (G.neighborFinset v) := by
    intro u hu u' hu' heq
    have hne : u ≠ v := (G.ne_of_adj (SimpleGraph.mem_neighborFinset .. |>.mp hu)).symm
    have hne' : u' ≠ v := (G.ne_of_adj (SimpleGraph.mem_neighborFinset .. |>.mp hu')).symm
    have heq' : ({v, u} : Finset V) = {v, u'} := heq
    have hmem : u ∈ ({v, u'} : Finset V) := heq' ▸ (by simp : u ∈ ({v, u} : Finset V))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact absurd h hne
    · exact h
  have hcardL : ((G.neighborFinset v).image (fun u => ({v, u} : Finset V))).card = G.degree v := by
    rw [Finset.card_image_of_injOn hinj, SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : (G.neighborFinset v).image (fun u => ({v, u} : Finset V))
      ⊆ (uncoveredAt G ∅ v).image Subtype.val := by
    intro e he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
    have hadj : G.Adj v u := (SimpleGraph.mem_neighborFinset ..).mp hu
    refine Finset.mem_image.mpr ⟨edgeE G hadj, ?_, rfl⟩
    rw [uncoveredAt, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simp, by simp⟩
  calc G.degree v = ((G.neighborFinset v).image (fun u => ({v, u} : Finset V))).card := hcardL.symm
    _ ≤ ((uncoveredAt G ∅ v).image Subtype.val).card := Finset.card_le_card hsub
    _ ≤ (uncoveredAt G ∅ v).card := Finset.card_image_le

/-! ### The complete bipartite leftover -/

/-- The complete bipartite graph `K_{m,m}` is triangle-free. -/
theorem multipartite_two_cliqueFree (m : ℕ) : (multipartite 2 m).CliqueFree 3 := by
  intro t ht
  have hcard : t.card = 3 := ht.card_eq
  have hlt : (Finset.univ : Finset (Fin 2)).card < t.card := by
    rw [Finset.card_univ, Fintype.card_fin, hcard]; omega
  obtain ⟨x, hx, y, hy, hxy, hfst⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt (fun a _ => Finset.mem_univ a.1)
  exact (ht.isClique hx hy hxy) hfst

/-- **Route (a) refuted.**  In `K_{m,m}` every matching of the edge-type triangle hypergraph is
empty, and the uncovered incidence count is the full `|V|²/2`: iterating a triangle-packing theorem
on a triangle-free residual gains nothing. -/
theorem multipartite_two_leftover (m : ℕ) {M : Finset (Finset (EdgeV (multipartite 2 m)))}
    (hM : IsMatching (triangleHypergraphSub (multipartite 2 m)) M) :
    M = ∅ ∧ (1 / 2) * (Fintype.card (Fin 2 × Fin m) : ℝ) ^ 2
      ≤ (uncoveredTot (multipartite 2 m) M : ℝ) := by
  classical
  have hMe : M = ∅ := matching_eq_empty_of_cliqueFree _ (multipartite_two_cliqueFree m) hM
  refine ⟨hMe, ?_⟩
  subst hMe
  have hdeg : ∀ p : Fin 2 × Fin m, (multipartite 2 m).degree p = m := by
    intro p; rw [multipartite_degree]; omega
  have hsum : 2 * m * m ≤ uncoveredTot (multipartite 2 m) ∅ := by
    calc 2 * m * m = ∑ _p : Fin 2 × Fin m, m := by
          rw [Finset.sum_const, Finset.card_univ, card_multipartite_vtx, smul_eq_mul]
      _ ≤ ∑ p : Fin 2 × Fin m, unDeg (multipartite 2 m) ∅ p :=
          Finset.sum_le_sum (fun p _ => by
            have h := degree_le_card_uncoveredAt_empty (multipartite 2 m) p
            rw [hdeg p] at h
            exact h)
      _ = uncoveredTot (multipartite 2 m) ∅ := rfl
  have hsumR : (2 * m * m : ℝ) ≤ (uncoveredTot (multipartite 2 m) ∅ : ℝ) := by
    exact_mod_cast hsum
  have hcard : (Fintype.card (Fin 2 × Fin m) : ℝ) = 2 * m := by
    rw [card_multipartite_vtx]; push_cast; ring
  rw [hcard]
  linarith only [hsumR]

end Nibble
