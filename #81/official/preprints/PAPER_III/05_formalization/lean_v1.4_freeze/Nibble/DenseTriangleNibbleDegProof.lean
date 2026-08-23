/-
# Nibble — swap-stable triangle packings and the per-vertex leftover bound

This file attacks the residual `Nibble.DenseTriangleNibbleDeg` of `Nibble.DenseApproxDeg` by a
purely combinatorial *local-improvement* (swap) argument.

The engine is an explicit description of the hyperedges of the edge-type triangle hypergraph
`Nibble.YusterE.triangleHypergraphSub` (`Nibble.triE`), two local moves on a matching — adding a
triangle all of whose edges are uncovered, and swapping a packing triangle `{a,b,z}` for a triangle
`{v,a,b}` through a vertex `v` with two uncovered star edges — and the potential
`Nibble.uncoveredPot M = ∑_v |uncoveredAt G M v|²`, which strictly decreases along an improving
move.

* `Nibble.no_free_triangle` — a potential-minimal matching leaves no triangle with three uncovered
  edges (so the leftover graph is triangle-free);
* `Nibble.swap_stability` — if `v` has two uncovered star edges `va`, `vb` and `ab ∈ E(G)`, then the
  packing triangle covering `ab` has a third vertex `z` with `|uncovered star at v| ≤
  |uncovered star at z| + 2`;
* `Nibble.dense_uncoveredAt_le` — **the unconditional output**: at the Dross density
  `9|V| ≤ 10 δ(G)`, on at least `20` vertices, some edge-disjoint triangle family leaves at most
  `(3/5)|V|` uncovered edges at every vertex;
* `Nibble.denseTriangleNibbleDeg_of_three_fifths_le` — hence the residual
  `Nibble.DenseTriangleNibbleDeg` holds for every `β ≥ 3/5`;
* `Nibble.DenseTriangleNibbleDegSmall`, `Nibble.denseTriangleNibbleDeg_of_small` — the remaining,
  strictly narrower residual (the same statement for `β < 3/5`), and the machine-checked reduction
  of `Nibble.DenseTriangleNibbleDeg` to it.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DenseApproxDeg

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Cardinalities of filtered small sets -/

theorem card_filter_pair {α : Type*} [DecidableEq α] {p q : α} (hpq : p ≠ q)
    (r : α → Prop) [DecidablePred r] :
    (({p, q} : Finset α).filter r).card = (if r p then 1 else 0) + (if r q then 1 else 0) := by
  rw [Finset.filter_insert, Finset.filter_singleton]
  by_cases hp : r p <;> by_cases hq : r q <;>
    simp [hp, hq, Finset.card_insert_of_notMem, hpq]

theorem card_filter_singleton {α : Type*} [DecidableEq α] (p : α)
    (r : α → Prop) [DecidablePred r] :
    (({p} : Finset α).filter r).card = if r p then 1 else 0 := by
  rw [Finset.filter_singleton]
  by_cases h : r p <;> simp [h]

theorem card_filter_triple {α : Type*} [DecidableEq α] {p q s : α} (hpq : p ≠ q) (hps : p ≠ s)
    (hqs : q ≠ s) (r : α → Prop) [DecidablePred r] :
    (({p, q, s} : Finset α).filter r).card
      = (if r p then 1 else 0) + (if r q then 1 else 0) + (if r s then 1 else 0) := by
  have h2 : (({q, s} : Finset α).filter r).card
      = (if r q then 1 else 0) + (if r s then 1 else 0) := card_filter_pair hqs r
  rw [Finset.filter_insert]
  by_cases hp : r p
  · have hnot : p ∉ ({q, s} : Finset α).filter r := by simp [Finset.mem_filter, hpq, hps]
    rw [if_pos hp, Finset.card_insert_of_notMem hnot, h2, if_pos hp]
    omega
  · rw [if_neg hp, h2, if_neg hp]
    omega

/-! ### Edges and triangles of the edge-type hypergraph, explicitly -/

/-- An adjacent pair, as a vertex of the edge-type triangle hypergraph. -/
def edgeE (G : SimpleGraph V) [DecidableRel G.Adj] {u w : V} (h : G.Adj u w) : EdgeV G :=
  ⟨{u, w}, by
    rw [SimpleGraph.mem_cliqueFinset_iff]
    refine ⟨by simpa using SimpleGraph.isClique_pair.mpr (fun _ => h), ?_⟩
    rw [Finset.card_insert_of_notMem (by simp [h.ne]), Finset.card_singleton]⟩

@[simp] theorem edgeE_val (G : SimpleGraph V) [DecidableRel G.Adj] {u w : V} (h : G.Adj u w) :
    (edgeE G h).val = {u, w} := rfl

theorem mem_edgeE_val (G : SimpleGraph V) [DecidableRel G.Adj] {u w x : V} (h : G.Adj u w) :
    x ∈ (edgeE G h).val ↔ x = u ∨ x = w := by simp

theorem edgeE_comm (G : SimpleGraph V) [DecidableRel G.Adj] {u w : V} (h : G.Adj u w) :
    edgeE G h.symm = edgeE G h := by
  apply Subtype.ext
  simp [Finset.pair_comm]

theorem edgeE_eq_iff (G : SimpleGraph V) [DecidableRel G.Adj] {u w u' w' : V} (h : G.Adj u w)
    (h' : G.Adj u' w') : edgeE G h = edgeE G h' ↔ ({u, w} : Finset V) = {u', w'} := by
  rw [Subtype.ext_iff]; simp

theorem edgeE_ne_of_notMem (G : SimpleGraph V) [DecidableRel G.Adj] {u w u' w' : V}
    (h : G.Adj u w) (h' : G.Adj u' w') (hx : u ∉ ({u', w'} : Finset V)) :
    edgeE G h ≠ edgeE G h' := by
  intro heq
  exact hx ((edgeE_eq_iff G h h').mp heq ▸ (Finset.mem_insert_self u {w}))

theorem edgeE_ne_of_notMem' (G : SimpleGraph V) [DecidableRel G.Adj] {u w u' w' : V}
    (h : G.Adj u w) (h' : G.Adj u' w') (hx : w ∉ ({u', w'} : Finset V)) :
    edgeE G h ≠ edgeE G h' := by
  intro heq
  refine hx ((edgeE_eq_iff G h h').mp heq ▸ ?_)
  simp

/-- Every hypergraph vertex at `v` is the edge from `v` to some neighbour. -/
theorem exists_other_endpoint (G : SimpleGraph V) [DecidableRel G.Adj] {E : EdgeV G} {v : V}
    (hv : v ∈ E.val) : ∃ w : V, ∃ h : G.Adj v w, E = edgeE G h := by
  have hcl := SimpleGraph.mem_cliqueFinset_iff.mp E.property
  obtain ⟨a, b, hab, hE⟩ := Finset.card_eq_two.mp hcl.card_eq
  have hadj : G.Adj a b := hcl.isClique (by rw [hE]; simp) (by rw [hE]; simp) hab
  rw [hE] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact ⟨b, hadj, Subtype.ext (by rw [hE]; rfl)⟩
  · exact ⟨a, hadj.symm, Subtype.ext (by rw [hE, edgeE_val, Finset.pair_comm])⟩

omit [Fintype V] in
/-- The three `2`-subsets of a triple. -/
theorem powersetCard_two_triple {x y z : V} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ({x, y, z} : Finset V).powersetCard 2 = {{x, y}, {y, z}, {x, z}} := by
  ext s
  simp only [Finset.mem_powersetCard, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hsub, hcard⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    have ha := hsub (Finset.mem_insert_self a {b})
    have hb := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      simp_all [Finset.pair_comm]
  · have h1 : ({x, y} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
    have h2 : ({y, z} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
    have h3 : ({x, z} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hxz]), Finset.card_singleton]
    rintro (rfl | rfl | rfl) <;> refine ⟨?_, by assumption⟩ <;> intro t ht <;> simp at ht ⊢ <;>
      tauto

/-- The hyperedge of the triangle `{x, y, z}`: its three edges. -/
def triE (G : SimpleGraph V) [DecidableRel G.Adj] {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hxz : G.Adj x z) : Finset (EdgeV G) :=
  {edgeE G hxy, edgeE G hyz, edgeE G hxz}

theorem mem_triE (G : SimpleGraph V) [DecidableRel G.Adj] {x y z : V} (hxy : G.Adj x y)
    (hyz : G.Adj y z) (hxz : G.Adj x z) {E : EdgeV G} :
    E ∈ triE G hxy hyz hxz ↔ E = edgeE G hxy ∨ E = edgeE G hyz ∨ E = edgeE G hxz := by
  simp [triE]

/-- The explicit hyperedge is the one the hypergraph is built from. -/
theorem triE_eq_subtype (G : SimpleGraph V) [DecidableRel G.Adj] {x y z : V} (hxy : G.Adj x y)
    (hyz : G.Adj y z) (hxz : G.Adj x z) :
    triE G hxy hyz hxz =
      ((({x, y, z} : Finset V).powersetCard 2).subtype (· ∈ G.cliqueFinset 2)) := by
  ext E
  rw [Finset.mem_subtype, powersetCard_two_triple hxy.ne hyz.ne hxz.ne, mem_triE]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl) <;> simp [edgeE]
  · rintro (h | h | h)
    · exact Or.inl (Subtype.ext (by simpa using h))
    · exact Or.inr (Or.inl (Subtype.ext (by simpa using h)))
    · exact Or.inr (Or.inr (Subtype.ext (by simpa using h)))

theorem triE_mem_hypergraph (G : SimpleGraph V) [DecidableRel G.Adj] {x y z : V} (hxy : G.Adj x y)
    (hyz : G.Adj y z) (hxz : G.Adj x z) :
    triE G hxy hyz hxz ∈ triangleHypergraphSub G := by
  rw [mem_triangleHypergraphSub_iff]
  exact ⟨{x, y, z}, SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩,
    triE_eq_subtype G hxy hyz hxz⟩

/-- **Every hyperedge containing a given edge is the triangle over a third vertex.** -/
theorem exists_third_vertex (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V} (hab : G.Adj a b)
    {T : Finset (EdgeV G)} (hT : T ∈ triangleHypergraphSub G) (hmem : edgeE G hab ∈ T) :
    ∃ z : V, ∃ hbz : G.Adj b z, ∃ haz : G.Adj a z,
      z ≠ a ∧ z ≠ b ∧ T = triE G hab hbz haz := by
  obtain ⟨t, ht, rfl⟩ := (mem_triangleHypergraphSub_iff G).mp hT
  rw [Finset.mem_subtype, Finset.mem_powersetCard] at hmem
  have hsub : ({a, b} : Finset V) ⊆ t := hmem.1
  have hcard2 : ({a, b} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hab.ne]), Finset.card_singleton]
  have hcard1 : (t \ ({a, b} : Finset V)).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, ht.card_eq, hcard2]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard1
  have hzt : z ∈ t ∧ z ∉ ({a, b} : Finset V) := by
    have hmem' : z ∈ t \ ({a, b} : Finset V) := by rw [hz]; simp
    exact Finset.mem_sdiff.mp hmem'
  have hza : z ≠ a := by intro h; exact hzt.2 (by simp [h])
  have hzb : z ≠ b := by intro h; exact hzt.2 (by simp [h])
  have hteq : t = ({a, b, z} : Finset V) := by
    have hu := Finset.union_sdiff_of_subset hsub
    rw [hz] at hu
    rw [← hu]
    ext x; simp
  have haz : G.Adj a z :=
    ht.isClique (by rw [hteq]; simp) (by rw [hteq]; simp) (fun h => hza h.symm)
  have hbz : G.Adj b z :=
    ht.isClique (by rw [hteq]; simp) (by rw [hteq]; simp) (fun h => hzb h.symm)
  exact ⟨z, hbz, haz, hza, hzb, by rw [triE_eq_subtype G hab hbz haz, hteq]⟩

/-! ### The uncovered stars under the two local moves -/

/-- `E` is uncovered by the family `M`. -/
def UncE (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset (EdgeV G)))
    (E : EdgeV G) : Prop := ∀ T ∈ M, E ∉ T

theorem mem_uncoveredAt (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} {v : V} {E : EdgeV G} :
    E ∈ uncoveredAt G M v ↔ v ∈ E.val ∧ UncE G M E := by
  simp [uncoveredAt, UncE]

theorem uncoveredAt_insert (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset (EdgeV G))) (P : Finset (EdgeV G)) (v : V) :
    uncoveredAt G (insert P M) v = uncoveredAt G M v \ P := by
  ext E
  simp only [mem_uncoveredAt, Finset.mem_sdiff, UncE, Finset.mem_insert, forall_eq_or_imp]
  tauto

theorem uncoveredAt_erase (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : ∀ T ∈ M, ∀ T' ∈ M, T ≠ T' → Disjoint T T')
    {T : Finset (EdgeV G)} (hT : T ∈ M) (v : V) :
    uncoveredAt G (M.erase T) v = uncoveredAt G M v ∪ T.filter (fun E => v ∈ E.val) := by
  ext E
  simp only [mem_uncoveredAt, Finset.mem_union, Finset.mem_filter, UncE, Finset.mem_erase]
  constructor
  · rintro ⟨hv, h⟩
    by_cases hE : E ∈ T
    · exact Or.inr ⟨hE, hv⟩
    · refine Or.inl ⟨hv, fun T' hT' hmem => ?_⟩
      by_cases hTT : T' = T
      · exact hE (hTT ▸ hmem)
      · exact h T' ⟨hTT, hT'⟩ hmem
  · rintro (⟨hv, h⟩ | ⟨hE, hv⟩)
    · exact ⟨hv, fun T' hT' => h T' hT'.2⟩
    · refine ⟨hv, fun T' hT' hmem => ?_⟩
      exact Finset.disjoint_left.mp (hM T' hT'.2 T hT hT'.1) hmem hE

/-! ### The potential -/

/-- The uncovered star size of `M` at `v`. -/
def unDeg (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset (EdgeV G))) (v : V) : ℕ :=
  (uncoveredAt G M v).card

/-- The potential `∑_v |uncoveredAt G M v|²`, which strictly decreases along improving moves. -/
def uncoveredPot (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset (EdgeV G))) : ℕ :=
  ∑ v : V, (unDeg G M v) ^ 2

/-- The total number of uncovered incidences `∑_v |uncoveredAt G M v|`, i.e. twice the number of
uncovered edges.  Both local moves leave it unchanged or decrease it. -/
def uncoveredTot (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset (EdgeV G))) : ℕ :=
  ∑ v : V, unDeg G M v

/-- A matching minimising the potential among those with at most `K` uncovered incidences.  Taking
`K` maximal (e.g. the value at the empty matching) this is an unrestricted minimiser. -/
theorem exists_min_pot_within (G : SimpleGraph V) [DecidableRel G.Adj] (K : ℕ)
    {M₀ : Finset (Finset (EdgeV G))} (hM₀ : IsMatching (triangleHypergraphSub G) M₀)
    (hK : uncoveredTot G M₀ ≤ K) :
    ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
      uncoveredTot G M ≤ K ∧
      ∀ M' : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M' →
        uncoveredTot G M' ≤ uncoveredTot G M → uncoveredPot G M ≤ uncoveredPot G M' := by
  classical
  set S : Finset (Finset (Finset (EdgeV G))) :=
    (Finset.univ : Finset (Finset (Finset (EdgeV G)))).filter
      (fun M => IsMatching (triangleHypergraphSub G) M ∧ uncoveredTot G M ≤ K) with hS
  have hne : S.Nonempty := by
    refine ⟨M₀, ?_⟩
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hM₀, hK⟩
  obtain ⟨M, hM, hmin⟩ := S.exists_min_image (uncoveredPot G) hne
  obtain ⟨-, hMmatch, hMtot⟩ := Finset.mem_filter.mp hM
  refine ⟨M, hMmatch, hMtot, fun M' hM' hle => hmin M' ?_⟩
  rw [hS, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hM', le_trans hle hMtot⟩

/-- A matching minimising the potential exists. -/
theorem exists_min_pot (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
      ∀ M' : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M' →
        uncoveredTot G M' ≤ uncoveredTot G M → uncoveredPot G M ≤ uncoveredPot G M' := by
  classical
  have hM₀ : IsMatching (triangleHypergraphSub G) (∅ : Finset (Finset (EdgeV G))) :=
    ⟨Finset.empty_subset _, fun e he => absurd he (Finset.notMem_empty e)⟩
  obtain ⟨M, hM, -, hmin⟩ :=
    exists_min_pot_within G (uncoveredTot G (∅ : Finset (Finset (EdgeV G)))) hM₀ le_rfl
  exact ⟨M, hM, hmin⟩

/-! ### The two local moves -/

theorem isMatching_insert (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    {P : Finset (EdgeV G)} (hP : P ∈ triangleHypergraphSub G) (hfree : ∀ E ∈ P, UncE G M E) :
    IsMatching (triangleHypergraphSub G) (insert P M) := by
  refine ⟨Finset.insert_subset hP hM.subset, ?_⟩
  intro T hT T' hT' hne
  rw [Finset.mem_insert] at hT hT'
  rcases hT with rfl | hT
  · rcases hT' with rfl | hT'
    · exact absurd rfl hne
    · rw [Finset.disjoint_left]
      exact fun E hE hE' => hfree E hE T' hT' hE'
  · rcases hT' with rfl | hT'
    · rw [Finset.disjoint_right]
      exact fun E hE hE' => hfree E hE T hT hE'
    · exact hM.disjoint T hT T' hT' hne

theorem isMatching_swap (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    {T P : Finset (EdgeV G)} (hT : T ∈ M) (hP : P ∈ triangleHypergraphSub G)
    (hfree : ∀ E ∈ P, E ∈ T ∨ UncE G M E) :
    IsMatching (triangleHypergraphSub G) (insert P (M.erase T)) := by
  have hsub : M.erase T ⊆ M := Finset.erase_subset _ _
  have hkey : ∀ T' ∈ M.erase T, Disjoint P T' := by
    intro T' hT'
    rw [Finset.disjoint_left]
    intro E hE hE'
    rcases hfree E hE with hin | hunc
    · exact Finset.disjoint_left.mp
        (hM.disjoint T hT T' (hsub hT') (fun h => (Finset.mem_erase.mp hT').1 h.symm)) hin hE'
    · exact hunc T' (hsub hT') hE'
  refine ⟨Finset.insert_subset hP (hsub.trans hM.subset), ?_⟩
  intro A hA B hB hne
  rw [Finset.mem_insert] at hA hB
  rcases hA with rfl | hA
  · rcases hB with rfl | hB
    · exact absurd rfl hne
    · exact hkey B hB
  · rcases hB with rfl | hB
    · exact (hkey A hA).symm
    · exact hM.disjoint A (hsub hA) B (hsub hB) hne

/-- The bookkeeping identity for a swap: the uncovered star at `u` loses the members of the new
hyperedge `P` and gains those of the removed hyperedge `T`. -/
theorem card_swap_step (G : SimpleGraph V) [DecidableRel G.Adj] {M : Finset (Finset (EdgeV G))}
    (hM : IsMatching (triangleHypergraphSub G) M) {P T : Finset (EdgeV G)} (hT : T ∈ M) (u : V) :
    unDeg G (insert P (M.erase T)) u + ((uncoveredAt G M u) ∩ P).card
        + ((T.filter (fun E => u ∈ E.val)) ∩ P).card
      = unDeg G M u + (T.filter (fun E => u ∈ E.val)).card := by
  classical
  set X := uncoveredAt G M u with hX
  set Y := T.filter (fun E => u ∈ E.val) with hY
  have hdisj : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro E hEX hEY
    rw [hX, mem_uncoveredAt] at hEX
    rw [hY, Finset.mem_filter] at hEY
    exact hEX.2 T hT hEY.1
  have hune : uncoveredAt G (insert P (M.erase T)) u = (X ∪ Y) \ P := by
    rw [uncoveredAt_insert, uncoveredAt_erase G hM.disjoint hT]
  have hinter : (X ∪ Y) ∩ P = (X ∩ P) ∪ (Y ∩ P) := Finset.union_inter_distrib_right X Y P
  have hdisj2 : Disjoint (X ∩ P) (Y ∩ P) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hdisj)
  have hcard1 : ((X ∪ Y) \ P).card + ((X ∪ Y) ∩ P).card = (X ∪ Y).card :=
    Finset.card_sdiff_add_card_inter _ _
  have hcard2 : (X ∪ Y).card = X.card + Y.card := Finset.card_union_of_disjoint hdisj
  have hcard3 : ((X ∪ Y) ∩ P).card = (X ∩ P).card + (Y ∩ P).card := by
    rw [hinter, Finset.card_union_of_disjoint hdisj2]
  have hgoal : unDeg G (insert P (M.erase T)) u = ((X ∪ Y) \ P).card := by rw [unDeg, hune]
  have hgoal2 : unDeg G M u = X.card := by rw [unDeg, ← hX]
  rw [hgoal, hgoal2]
  omega

/-- **No free triangle.**  A potential-minimal matching leaves no triangle with all three edges
uncovered. -/
theorem no_free_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    (hmin : ∀ M' : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M' →
      uncoveredTot G M' ≤ uncoveredTot G M → uncoveredPot G M ≤ uncoveredPot G M')
    {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : G.Adj x z)
    (h1 : UncE G M (edgeE G hxy)) (h2 : UncE G M (edgeE G hyz)) (h3 : UncE G M (edgeE G hxz)) :
    False := by
  classical
  set P := triE G hxy hyz hxz with hPdef
  have hPH : P ∈ triangleHypergraphSub G := triE_mem_hypergraph G hxy hyz hxz
  have hfree : ∀ E ∈ P, UncE G M E := by
    intro E hE
    rw [hPdef, mem_triE] at hE
    rcases hE with rfl | rfl | rfl <;> assumption
  have hM' : IsMatching (triangleHypergraphSub G) (insert P M) := isMatching_insert G hM hPH hfree
  have hle : ∀ u : V, unDeg G (insert P M) u ≤ unDeg G M u := by
    intro u
    rw [unDeg, unDeg, uncoveredAt_insert]
    exact Finset.card_le_card Finset.sdiff_subset
  have hlt : unDeg G (insert P M) x < unDeg G M x := by
    rw [unDeg, unDeg, uncoveredAt_insert]
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr ?_)
    refine ⟨edgeE G hxy, ?_, ?_⟩
    · rw [mem_uncoveredAt]
      exact ⟨by simp, h1⟩
    · simp only [Finset.mem_sdiff, not_and, not_not]
      intro _
      rw [hPdef, mem_triE]
      exact Or.inl rfl
  have htot : uncoveredTot G (insert P M) ≤ uncoveredTot G M :=
    Finset.sum_le_sum (fun i _ => hle i)
  have hpot : uncoveredPot G (insert P M) < uncoveredPot G M :=
    Finset.sum_lt_sum (fun i _ => Nat.pow_le_pow_left (hle i) 2)
      ⟨x, Finset.mem_univ x, Nat.pow_lt_pow_left hlt (by norm_num)⟩
  exact absurd (hmin _ hM' htot) (by omega)

/-- **Swap stability.**  If `v` has two uncovered star edges `va`, `vb` with `ab ∈ E(G)`, then the
packing triangle covering `ab` has a third vertex `z` whose uncovered star is almost as large as
that of `v`. -/
theorem swap_stability (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    (hmin : ∀ M' : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M' →
      uncoveredTot G M' ≤ uncoveredTot G M → uncoveredPot G M ≤ uncoveredPot G M')
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b) (hab : G.Adj a b)
    (h1 : UncE G M (edgeE G hva)) (h2 : UncE G M (edgeE G hvb))
    {T : Finset (EdgeV G)} (hT : T ∈ M) (hmem : edgeE G hab ∈ T) :
    ∃ z : V, ∃ hbz : G.Adj b z, ∃ haz : G.Adj a z,
      z ≠ a ∧ z ≠ b ∧ T = triE G hab hbz haz ∧ unDeg G M v ≤ unDeg G M z + 2 := by
  classical
  obtain ⟨z, hbz, haz, hza, hzb, hTeq⟩ := exists_third_vertex G hab (hM.subset hT) hmem
  have hzv : z ≠ v := by
    rintro rfl
    have hmem' : edgeE G haz ∈ T := by rw [hTeq, mem_triE]; exact Or.inr (Or.inr rfl)
    have heq : edgeE G haz = edgeE G hva := by
      rw [edgeE_eq_iff]; exact Finset.pair_comm a z
    exact h1 T hT (heq ▸ hmem')
  have hvane : v ≠ a := hva.ne
  have hvbne : v ≠ b := hvb.ne
  have habne : a ≠ b := hab.ne
  have hvz : v ≠ z := Ne.symm hzv
  refine ⟨z, hbz, haz, hza, hzb, hTeq, ?_⟩
  set P := triE G hva hab hvb with hPdef
  have hPH : P ∈ triangleHypergraphSub G := triE_mem_hypergraph G hva hab hvb
  have habcov : ¬ UncE G M (edgeE G hab) := fun h => h T hT hmem
  have hfree : ∀ E ∈ P, E ∈ T ∨ UncE G M E := by
    intro E hE
    rw [hPdef, mem_triE] at hE
    rcases hE with rfl | rfl | rfl
    · exact Or.inr h1
    · exact Or.inl hmem
    · exact Or.inr h2
  have hM' : IsMatching (triangleHypergraphSub G) (insert P (M.erase T)) :=
    isMatching_swap G hM hT hPH hfree
  -- distinctness of the six edges involved
  have d1 : edgeE G hva ≠ edgeE G hvb :=
    edgeE_ne_of_notMem' G hva hvb (by simp [Ne.symm hvane, habne])
  have d2 : edgeE G hbz ≠ edgeE G hva := edgeE_ne_of_notMem' G hbz hva (by simp [hzv, hza])
  have d3 : edgeE G hbz ≠ edgeE G hab := edgeE_ne_of_notMem' G hbz hab (by simp [hza, hzb])
  have d4 : edgeE G hbz ≠ edgeE G hvb := edgeE_ne_of_notMem' G hbz hvb (by simp [hzv, hzb])
  have d5 : edgeE G haz ≠ edgeE G hva := edgeE_ne_of_notMem' G haz hva (by simp [hzv, hza])
  have d6 : edgeE G haz ≠ edgeE G hab := edgeE_ne_of_notMem' G haz hab (by simp [hza, hzb])
  have d7 : edgeE G haz ≠ edgeE G hvb := edgeE_ne_of_notMem' G haz hvb (by simp [hzv, hzb])
  have d8 : edgeE G hbz ≠ edgeE G haz :=
    edgeE_ne_of_notMem G hbz haz (by simp [habne.symm, hbz.ne])
  -- the three ingredients of the bookkeeping identity
  have hXP : ∀ u : V, uncoveredAt G M u ∩ P
      = ({edgeE G hva, edgeE G hvb} : Finset (EdgeV G)).filter (fun E => u ∈ E.val) := by
    intro u
    ext E
    simp only [Finset.mem_inter, mem_uncoveredAt, hPdef, mem_triE, Finset.mem_filter,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hu, hunc⟩, (rfl | rfl | rfl)⟩
      · exact ⟨Or.inl rfl, hu⟩
      · exact absurd hunc habcov
      · exact ⟨Or.inr rfl, hu⟩
    · rintro ⟨(rfl | rfl), hu⟩
      · exact ⟨⟨hu, h1⟩, Or.inl rfl⟩
      · exact ⟨⟨hu, h2⟩, Or.inr (Or.inr rfl)⟩
  have hTP : T ∩ P = {edgeE G hab} := by
    ext E
    rw [hTeq]
    simp only [Finset.mem_inter, mem_triE, hPdef, Finset.mem_singleton]
    constructor
    · rintro ⟨(rfl | rfl | rfl), (h | h | h)⟩
      · rfl
      · rfl
      · rfl
      · exact absurd h d2
      · exact absurd h d3
      · exact absurd h d4
      · exact absurd h d5
      · exact absurd h d6
      · exact absurd h d7
    · rintro rfl
      exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩
  have hYP : ∀ u : V, ((T.filter (fun E => u ∈ E.val)) ∩ P).card
      = (if u ∈ (edgeE G hab).val then 1 else 0) := by
    intro u
    rw [Finset.filter_inter, hTP, card_filter_singleton]
  have hXPcard : ∀ u : V, (uncoveredAt G M u ∩ P).card
      = (if u ∈ (edgeE G hva).val then 1 else 0) + (if u ∈ (edgeE G hvb).val then 1 else 0) := by
    intro u
    rw [hXP u, card_filter_pair d1]
  have hYcard : ∀ u : V, (T.filter (fun E => u ∈ E.val)).card
      = (if u ∈ (edgeE G hab).val then 1 else 0) + (if u ∈ (edgeE G hbz).val then 1 else 0)
        + (if u ∈ (edgeE G haz).val then 1 else 0) := by
    intro u
    rw [hTeq, triE, card_filter_triple (Ne.symm d3) (Ne.symm d6) d8]
  have hstep : ∀ u : V, unDeg G (insert P (M.erase T)) u + (uncoveredAt G M u ∩ P).card
      + ((T.filter (fun E => u ∈ E.val)) ∩ P).card
      = unDeg G M u + (T.filter (fun E => u ∈ E.val)).card :=
    fun u => card_swap_step G hM (P := P) hT u
  -- the degree changes: `−2` at `v`, `+2` at `z`, nothing elsewhere
  have hdv : unDeg G (insert P (M.erase T)) v + 2 = unDeg G M v := by
    have h := hstep v
    rw [hXPcard v, hYP v, hYcard v] at h
    simp only [edgeE_val, Finset.mem_insert, Finset.mem_singleton, hvane, hvbne, hvz,
      or_false, if_true, if_false] at h
    omega
  have hdz : unDeg G (insert P (M.erase T)) z = unDeg G M z + 2 := by
    have h := hstep z
    rw [hXPcard z, hYP z, hYcard z] at h
    simp only [edgeE_val, Finset.mem_insert, Finset.mem_singleton, hza, hzb, hzv,
      or_false, or_true, if_true, if_false] at h
    omega
  have hkey : ∀ u : V, u ≠ v → u ≠ z →
      unDeg G (insert P (M.erase T)) u = unDeg G M u := by
    intro u huv huz
    have h := hstep u
    rw [hXPcard u, hYP u, hYcard u] at h
    by_cases hua : u = a
    · subst hua
      simp only [edgeE_val, Finset.mem_insert, Finset.mem_singleton, Ne.symm hvane, habne,
        Ne.symm hza, or_false, or_true, if_true, if_false] at h
      omega
    · by_cases hub : u = b
      · subst hub
        simp only [edgeE_val, Finset.mem_insert, Finset.mem_singleton, Ne.symm hvbne,
          Ne.symm habne, Ne.symm hzb, or_false, or_true, if_true,
          if_false] at h
        omega
      · simp only [edgeE_val, Finset.mem_insert, Finset.mem_singleton, huv, hua, hub, huz,
          if_false, or_self] at h
        omega
  -- comparing potentials
  have hsplit : ∀ f : V → ℕ,
      ∑ u : V, f u = ∑ u ∈ (Finset.univ \ ({v, z} : Finset V)), f u
        + ∑ u ∈ ({v, z} : Finset V), f u :=
    fun f => (Finset.sum_sdiff (Finset.subset_univ _)).symm
  have heqsum : ∑ u ∈ (Finset.univ \ ({v, z} : Finset V)),
        (unDeg G (insert P (M.erase T)) u) ^ 2
      = ∑ u ∈ (Finset.univ \ ({v, z} : Finset V)), (unDeg G M u) ^ 2 := by
    refine Finset.sum_congr rfl (fun u hu => ?_)
    have hu' := Finset.mem_sdiff.mp hu
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu'
    rw [hkey u hu'.2.1 hu'.2.2]
  have heqsum' : ∑ u ∈ (Finset.univ \ ({v, z} : Finset V)),
        unDeg G (insert P (M.erase T)) u
      = ∑ u ∈ (Finset.univ \ ({v, z} : Finset V)), unDeg G M u := by
    refine Finset.sum_congr rfl (fun u hu => ?_)
    have hu' := Finset.mem_sdiff.mp hu
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu'
    rw [hkey u hu'.2.1 hu'.2.2]
  have htot : uncoveredTot G (insert P (M.erase T)) = uncoveredTot G M := by
    simp only [uncoveredTot, hsplit, heqsum', Finset.sum_pair hvz]
    omega
  have hle := hmin _ hM' (le_of_eq htot)
  simp only [uncoveredPot, hsplit, heqsum, Finset.sum_pair hvz] at hle
  rw [← hdv, hdz] at hle
  have hkeyle : unDeg G (insert P (M.erase T)) v ≤ unDeg G M z := by linarith only [hle]
  omega

/-! ### The uncovered neighbourhood -/

open scoped Classical in
/-- The vertices joined to `v` by an uncovered edge. -/
noncomputable def unNbr (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset (EdgeV G)))
    (v : V) : Finset V :=
  Finset.univ.filter (fun w => ∃ h : G.Adj v w, UncE G M (edgeE G h))

theorem mem_unNbr (G : SimpleGraph V) [DecidableRel G.Adj] {M : Finset (Finset (EdgeV G))}
    {v w : V} : w ∈ unNbr G M v ↔ ∃ h : G.Adj v w, UncE G M (edgeE G h) := by
  classical
  simp only [unNbr, Finset.mem_filter, Finset.mem_univ, true_and]

theorem card_unNbr (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset (EdgeV G)))
    (v : V) : (unNbr G M v).card = unDeg G M v := by
  classical
  rw [unDeg]
  refine Finset.card_bij (fun w hw => edgeE G ((mem_unNbr G).mp hw).choose) ?_ ?_ ?_
  · intro w hw
    rw [mem_uncoveredAt]
    exact ⟨by simp, ((mem_unNbr G).mp hw).choose_spec⟩
  · intro w hw w' hw' heq
    have hadj := ((mem_unNbr G).mp hw).choose
    have hpair := (edgeE_eq_iff G ((mem_unNbr G).mp hw).choose ((mem_unNbr G).mp hw').choose).mp heq
    have hmem : w ∈ ({v, w'} : Finset V) := by rw [← hpair]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact absurd rfl hadj.ne
    · rfl
  · intro E hE
    rw [mem_uncoveredAt] at hE
    obtain ⟨w, hadj, rfl⟩ := exists_other_endpoint G hE.1
    exact ⟨w, (mem_unNbr G).mpr ⟨hadj, hE.2⟩, rfl⟩

/-! ### The per-vertex bound at the Dross density -/

/-- **The core counting step.**  At density `9|V| ≤ 10 δ(G)`, for a potential-minimal matching and
a vertex `v₀` with a non-empty uncovered star there is a set `B` of vertices whose uncovered stars
are all within `2` of that of `v₀`, and which is almost as large as the star of `v₀`:
`10|star(v₀)| ≤ 10|B| + |V|`.

Indeed, pick a neighbour `a` of `v₀` along an uncovered edge.  For each `b` in the uncovered star
of `v₀` adjacent to `a` — of which there are at least `|star(v₀)| + δ(G) − |V|` — the edge `ab` must
be covered, since otherwise `v₀ a b` would be a triangle with three uncovered edges; and swap
stability makes the third vertex of the packing triangle covering `ab` a member of `B`.  Distinct
`b`'s give distinct third vertices, since two packing triangles cannot share the edge `az`. -/
theorem exists_large_star_set (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree)
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    (hmin : ∀ M' : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M' →
      uncoveredTot G M' ≤ uncoveredTot G M → uncoveredPot G M ≤ uncoveredPot G M')
    (v₀ : V) (hD : 0 < unDeg G M v₀) :
    ∃ B : Finset V, (∀ z ∈ B, unDeg G M v₀ ≤ unDeg G M z + 2) ∧
      10 * unDeg G M v₀ ≤ 10 * B.card + Fintype.card V := by
  classical
  set n := Fintype.card V with hn
  set D := unDeg G M v₀ with hD'
  have hAcard : (unNbr G M v₀).card = D := card_unNbr G M v₀
  obtain ⟨a, ha⟩ : (unNbr G M v₀).Nonempty := by rw [← Finset.card_pos, hAcard]; omega
  obtain ⟨hva, huva⟩ := (mem_unNbr G).mp ha
  set B := Finset.univ.filter (fun x => D ≤ unDeg G M x + 2) with hB
  refine ⟨B, fun z hz => ?_, ?_⟩
  · rw [hB, Finset.mem_filter] at hz
    exact hz.2
  set S := (unNbr G M v₀) ∩ G.neighborFinset a with hS
  have hScard : D + G.degree a ≤ S.card + n := by
    have h1 : S.card + (unNbr G M v₀ ∪ G.neighborFinset a).card
        = (unNbr G M v₀).card + (G.neighborFinset a).card := by
      rw [hS]; exact Finset.card_inter_add_card_union _ _
    have h2 : (unNbr G M v₀ ∪ G.neighborFinset a).card ≤ n := by
      rw [hn, ← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    rw [hAcard] at h1
    have h3 : (G.neighborFinset a).card = G.degree a := rfl
    omega
  have hex : ∀ b : V, ∃ z : V, b ∈ S →
      (D ≤ unDeg G M z + 2) ∧ z ≠ a ∧ z ≠ b ∧
      ∃ (hab : G.Adj a b) (hbz : G.Adj b z) (haz : G.Adj a z), triE G hab hbz haz ∈ M := by
    intro b
    by_cases hb : b ∈ S
    · rw [hS, Finset.mem_inter] at hb
      obtain ⟨hbA, hbN⟩ := hb
      obtain ⟨hv0b, hu_v0b⟩ := (mem_unNbr G).mp hbA
      have hab : G.Adj a b := by rwa [SimpleGraph.mem_neighborFinset] at hbN
      have hcov : ¬ UncE G M (edgeE G hab) := fun hu =>
        no_free_triangle G hM hmin hva hab hv0b huva hu hu_v0b
      simp only [UncE, not_forall, not_not] at hcov
      obtain ⟨T, hT, hmemT⟩ := hcov
      obtain ⟨z, hbz, haz, hza, hzb, hTeq, hle⟩ :=
        swap_stability G hM hmin hva hv0b hab huva hu_v0b hT hmemT
      exact ⟨z, fun _ => ⟨hle, hza, hzb, hab, hbz, haz, hTeq ▸ hT⟩⟩
    · exact ⟨a, fun h => absurd h hb⟩
  choose f hf using hex
  have hmaps : ∀ b ∈ S, f b ∈ B := by
    intro b hb
    rw [hB, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hf b hb).1⟩
  have hinj : Set.InjOn f S := by
    intro b hb b' hb' heq
    obtain ⟨-, hza, hzb, hab, hbz, haz, hTmem⟩ := hf b hb
    have hb'data := hf b' hb'
    rw [← heq] at hb'data
    obtain ⟨-, hza', hzb', hab', hb'z, haz', hT'mem⟩ := hb'data
    have hazmem : edgeE G haz ∈ triE G hab hbz haz := by
      rw [mem_triE]; exact Or.inr (Or.inr rfl)
    have hazmem' : edgeE G haz ∈ triE G hab' hb'z haz' := by
      rw [mem_triE]; exact Or.inr (Or.inr rfl)
    have hTT : triE G hab hbz haz = triE G hab' hb'z haz' := by
      by_contra hne'
      exact Finset.disjoint_left.mp (hM.disjoint _ hTmem _ hT'mem hne') hazmem hazmem'
    have hmem' : edgeE G hab' ∈ triE G hab hbz haz := by
      rw [hTT, mem_triE]; exact Or.inl rfl
    rw [mem_triE] at hmem'
    rcases hmem' with h | h | h
    · have hpair := (edgeE_eq_iff G hab' hab).mp h
      have hb'mem : b' ∈ ({a, b} : Finset V) := by rw [← hpair]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb'mem
      rcases hb'mem with rfl | rfl
      · exact absurd rfl hab'.ne'
      · rfl
    · have hpair := (edgeE_eq_iff G hab' hbz).mp h
      have hamem : a ∈ ({b, f b} : Finset V) := by rw [← hpair]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hamem
      rcases hamem with rfl | rfl
      · exact absurd rfl hab.ne
      · exact absurd rfl hza
    · have hpair := (edgeE_eq_iff G hab' haz).mp h
      have hb'mem : b' ∈ ({a, f b} : Finset V) := by rw [← hpair]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb'mem
      rcases hb'mem with rfl | rfl
      · exact absurd rfl hab'.ne'
      · exact absurd rfl hzb'
  have hSB : S.card ≤ B.card := Finset.card_le_card_of_injOn f hmaps hinj
  have hdeg : 9 * n ≤ 10 * G.degree a :=
    le_trans hdense (Nat.mul_le_mul_left 10 (SimpleGraph.minDegree_le_degree G a))
  omega

/-- **The unconditional per-vertex leftover bound.**  Every graph with `9|V| ≤ 10 δ(G)` has an
edge-disjoint family of triangles whose uncovered star at every vertex has at most
`(11|V| + 20)/20` edges — so at most `(11/20 + o(1))|V|` edges. -/
theorem dense_uncoveredAt_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) :
    ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
      ∀ v : V, 20 * (uncoveredAt G M v).card ≤ 11 * Fintype.card V + 20 := by
  classical
  obtain ⟨M, hM, hmin⟩ := exists_min_pot G
  refine ⟨M, hM, ?_⟩
  set n := Fintype.card V with hn
  intro v
  have hne : (Finset.univ : Finset V).Nonempty := ⟨v, Finset.mem_univ v⟩
  obtain ⟨v₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (unDeg G M) hne
  set D := unDeg G M v₀ with hD
  have hkey : 20 * D ≤ 11 * n + 20 := by
    by_contra hcon
    push_neg at hcon
    have hAcard : (unNbr G M v₀).card = D := card_unNbr G M v₀
    have hDpos : 0 < D := by omega
    obtain ⟨B, hBdeg, hBcard⟩ := exists_large_star_set G hdense hM hmin v₀ hDpos
    by_cases hcase : ∃ z' ∈ unNbr G M v₀, D ≤ unDeg G M z' + 2
    · -- some vertex of the uncovered star of `v₀` also has a large uncovered star: the two stars
      -- are disjoint, since the leftover carries no triangle
      obtain ⟨z', hz'A, hz'B⟩ := hcase
      obtain ⟨hvz', huvz'⟩ := (mem_unNbr G).mp hz'A
      have hdisj : Disjoint (unNbr G M v₀) (unNbr G M z') := by
        rw [Finset.disjoint_left]
        intro w hw hw'
        obtain ⟨hv0w, hu1⟩ := (mem_unNbr G).mp hw
        obtain ⟨hz'w, hu2⟩ := (mem_unNbr G).mp hw'
        exact no_free_triangle G hM hmin hvz' hz'w hv0w huvz' hu2 hu1
      have hcards : (unNbr G M v₀).card + (unNbr G M z').card ≤ n := by
        rw [← Finset.card_union_of_disjoint hdisj, hn, ← Finset.card_univ]
        exact Finset.card_le_card (Finset.subset_univ _)
      rw [hAcard, card_unNbr] at hcards
      omega
    · -- otherwise the uncovered star of `v₀` avoids `B`, which is large by the core counting
      push_neg at hcase
      have hdisj : Disjoint (unNbr G M v₀) B := by
        rw [Finset.disjoint_left]
        intro w hw hwB
        have h1 := hcase w hw
        have h2 := hBdeg w hwB
        omega
      have hun := Finset.card_union_of_disjoint hdisj
      have hle : (unNbr G M v₀ ∪ B).card ≤ n := by
        rw [hn, ← Finset.card_univ]
        exact Finset.card_le_card (Finset.subset_univ _)
      rw [hAcard] at hun
      omega
  have hvle : unDeg G M v ≤ D := hmax v (Finset.mem_univ v)
  show 20 * unDeg G M v ≤ 11 * n + 20
  omega

/-- **Conditional sharpening.**  If some matching leaves at most `K` uncovered incidences
(`∑_v |uncoveredAt v| ≤ K`, i.e. at most `K/2` uncovered edges), then some matching whose uncovered
stars all have size `d` satisfies the quadratic bound `(10d − |V|)·(d − 2) ≤ 10K`; so a global
leftover bound of `o(|V|²)` forces every star down to `(1/10 + o(1))|V|` — the barrier of the swap
argument being the independence number `|V| − δ(G)`. -/
theorem dense_uncoveredAt_quadratic (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) (K : ℕ)
    {M₀ : Finset (Finset (EdgeV G))} (hM₀ : IsMatching (triangleHypergraphSub G) M₀)
    (hK : uncoveredTot G M₀ ≤ K) :
    ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
      uncoveredTot G M ≤ K ∧
      ∀ v : V, (10 * (uncoveredAt G M v).card) * ((uncoveredAt G M v).card)
        ≤ 10 * K + Fintype.card V * ((uncoveredAt G M v).card) + 20 * (uncoveredAt G M v).card := by
  classical
  obtain ⟨M, hM, hMK, hmin⟩ := exists_min_pot_within G K hM₀ hK
  refine ⟨M, hM, hMK, fun v => ?_⟩
  show (10 * unDeg G M v) * (unDeg G M v)
    ≤ 10 * K + Fintype.card V * unDeg G M v + 20 * unDeg G M v
  rcases le_or_gt (unDeg G M v) 2 with hsmall | hbig
  · nlinarith only [hsmall]
  · obtain ⟨B, hBdeg, hBcard⟩ := exists_large_star_set G hdense hM hmin v (by omega)
    obtain ⟨e, he⟩ : ∃ e : ℕ, unDeg G M v = e + 2 := ⟨unDeg G M v - 2, by omega⟩
    -- every member of `B` has an uncovered star of size at least `|star(v)| − 2`
    have hsum : ∑ z ∈ B, unDeg G M z ≤ uncoveredTot G M :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hlow : B.card * e ≤ ∑ z ∈ B, unDeg G M z := by
      calc B.card * e = ∑ _z ∈ B, e := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ z ∈ B, unDeg G M z := Finset.sum_le_sum (fun z hz => by
            have := hBdeg z hz
            omega)
    have hBK : B.card * e ≤ K := le_trans (le_trans hlow hsum) hMK
    have hmul : (10 * unDeg G M v) * e ≤ (10 * B.card + Fintype.card V) * e :=
      Nat.mul_le_mul_right e hBcard
    have hexp : (10 * B.card + Fintype.card V) * e
        = 10 * (B.card * e) + Fintype.card V * e := by ring
    have hK10 : 10 * (B.card * e) ≤ 10 * K := Nat.mul_le_mul_left 10 hBK
    have hcard_e : Fintype.card V * e ≤ Fintype.card V * unDeg G M v :=
      Nat.mul_le_mul_left _ (by omega)
    calc (10 * unDeg G M v) * (unDeg G M v)
        = (10 * unDeg G M v) * e + 20 * unDeg G M v := by rw [he]; ring
      _ ≤ (10 * B.card + Fintype.card V) * e + 20 * unDeg G M v := by omega
      _ = 10 * (B.card * e) + Fintype.card V * e + 20 * unDeg G M v := by rw [hexp]
      _ ≤ 10 * K + Fintype.card V * unDeg G M v + 20 * unDeg G M v := by omega

/-- **The residual holds for every `β > 11/20`.** -/
theorem denseTriangleNibbleDeg_of_eleven_twentieths_lt {β : ℝ} (hβ : 11 / 20 < β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) := by
  have hpos : 0 < 20 * β - 11 := by linarith only [hβ]
  refine ⟨⌈(20 : ℝ) / (20 * β - 11)⌉₊, ?_⟩
  intro V _ _ G _ hV hdense
  obtain ⟨M, hM, hbound⟩ := dense_uncoveredAt_le G hdense
  refine ⟨M, hM, fun v => ?_⟩
  have h1 : (20 : ℝ) * ((uncoveredAt G M v).card : ℝ) ≤ 11 * (Fintype.card V : ℝ) + 20 := by
    exact_mod_cast hbound v
  have h2 : (20 : ℝ) / (20 * β - 11) ≤ (Fintype.card V : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hV)
  have h3 : (20 : ℝ) ≤ (Fintype.card V : ℝ) * (20 * β - 11) := (div_le_iff₀ hpos).mp h2
  linarith only [h1, h3]

/-- **The residual holds for `β ≥ 3/5`.** -/
theorem denseTriangleNibbleDeg_of_three_fifths_le {β : ℝ} (hβ : 3 / 5 ≤ β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) := by
  exact denseTriangleNibbleDeg_of_eleven_twentieths_lt (by linarith)

/-- **The narrowed residual**: the statement of `Nibble.DenseTriangleNibbleDeg` for small `β`. -/
def DenseTriangleNibbleDegSmall : Prop :=
  ∀ β : ℝ, 0 < β → β ≤ 11 / 20 → ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ)

/-- **Machine-checked reduction**: the full residual follows from the narrowed one. -/
theorem denseTriangleNibbleDeg_of_small (h : DenseTriangleNibbleDegSmall) :
    DenseTriangleNibbleDeg := by
  intro β hβ
  rcases le_or_gt β (11 / 20) with hle | hgt
  · exact h β hβ hle
  · exact denseTriangleNibbleDeg_of_eleven_twentieths_lt hgt

end Nibble
