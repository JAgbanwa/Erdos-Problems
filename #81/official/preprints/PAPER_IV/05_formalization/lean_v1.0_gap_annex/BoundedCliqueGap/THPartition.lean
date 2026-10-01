import BoundedCliqueGap.MTLift
import BoundedCliqueGap.TResidual
import BoundedCliqueGap.TTree

/-
`BoundedCliqueGap.THPartition` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# TH1 — the support partition of a hub packing, and the per-node holed-clique bound

Lane TH works on the interface `TreeHubGapFull` (`BoundedCliqueGap.MTLift`), the only
remaining gate of the universal consumer `chordal_gap_linear_of_treeHubGapFull`.

This module carries the *packing-side* accounting of the clique-tree recursion.
Fix a subtree representation `IsSubtreeRep par rt sub` and its hub graph
`treeHubGraph sub S0 t`.  Then:

* `thHoledClique_gap` — a **general, unconditional** gap bound for a *holed
  clique*: a graph which is complete on `A ∪ B` with all edges inside the hole
  `B` removed has `value ≤ ν₃ + 10·|A|`.  This is `hubGraph_hole_gap`
  (`shell_gap_full_no_ports` behind it) transported along an enumeration of
  `A ∪ B`, so that it can be applied to any presented copy of a holed clique.

* `treePiece_isHoledClique` — the `j`-th piece of the hub graph *is* such a
  holed clique, with `A = treeOwn j` and `B = treeHole j`; hence
  `thPiece_gap : value ≤ ν₃(piece j) + 10·|treeOwn j|`.

* `thNode` — the node of a hub triangle (the `sup` of the roots, i.e. `triNode`
  of `BoundedCliqueGap.TTree` read off the finset), and the anatomy at that node: every
  vertex is `own` or `hole` (`th_own_or_hole`), at least one is `own`
  (`th_exists_own`, this uses `∀ x ∈ S0, rt x = 0`), and two `own` vertices
  already make the triangle a triangle of the node's piece
  (`th_clean_of_two_own`).  Consequently every hub triangle is either
  **clean** — a triangle of exactly one piece — or **foreign** — one `own`
  vertex and two `hole` vertices, its hole–hole edge being owned at a strict
  ancestor (`treeFlower_foreign_edge_ancestor`).

* `th_value_eq_sum_add_foreign` — the exact split of the LP value:
  `value = ∑_j value(part j) + foreignMass`, the sum being over the nodes.

* **`th_value_le_nu3_add_foreign`** — the master reduction of the lane:
  `value ≤ ν₃(hub) + 10·(n − |S₀|) + foreignMass`, unconditional.
  All accounting is on the packing side: the pieces are pairwise edge-disjoint
  (`treePiece_disjoint`), so their packing numbers add inside `ν₃` by
  `nu3_sum_le_of_edgeDisjoint`; no dual telescope is used anywhere.

`BoundedCliqueGap/THForeign.lean` estimates the foreign mass, and
`BoundedCliqueGap/THObstruction.lean` shows machine-checked that it cannot be estimated
linearly in general — the honest position of the lane.

No `sorry`, no new axioms, no `native_decide`; `#print axioms` at the end.
-/

namespace BoundedCliqueGap

open Finset

/-! ## A general holed clique -/

section HoledClique

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `G` is a *holed clique* with support `A ∪ B` and hole `B`: complete on
`A ∪ B`, except that no two hole vertices are adjacent. -/
def IsHoledClique (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∀ u v, G.Adj u v ↔ (u ≠ v ∧ u ∈ A ∪ B ∧ v ∈ A ∪ B ∧ ¬ (u ∈ B ∧ v ∈ B))

/-- **The holed-clique gap, unconditionally.**  A holed clique with `|A|`
non-hole vertices has integrality gap at most `10·|A|`.  This is
`hubGraph_hole_gap` — i.e. `shell_gap_full_no_ports` — moved along an
enumeration of `A ∪ B`. -/
theorem thHoledClique_gap {G : SimpleGraph V} {A B : Finset V}
    (hdisj : Disjoint A B) (hG : IsHoledClique G A B) (F : FracPacking G) :
    F.value ≤ (nu3 G : ℚ) + 10 * (A.card : ℚ) := by
  classical
  set s : Finset V := A ∪ B with hs
  set f : Fin s.card → V := fun i => ((s.equivFin.symm i : s) : V) with hf
  have hfmem : ∀ i, f i ∈ s := fun i => (s.equivFin.symm i).2
  have hfinj : Function.Injective f := by
    intro i i' h
    have : s.equivFin.symm i = s.equivFin.symm i' := Subtype.ext h
    simpa using congrArg s.equivFin this
  have hfsurj : ∀ u ∈ s, ∃ i, f i = u := by
    intro u hu
    exact ⟨s.equivFin ⟨u, hu⟩, by simp [hf]⟩
  set S0 : Finset (Fin s.card) := univ.filter (fun i => f i ∈ B) with hS0
  have himg : S0.image f = B := by
    ext u
    simp only [Finset.mem_image, hS0, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hu
      obtain ⟨i, hi⟩ := hfsurj u (by rw [hs]; exact Finset.mem_union_right _ hu)
      exact ⟨i, by rw [hi]; exact hu, hi⟩
  have hS0card : S0.card = B.card := by
    rw [← himg, Finset.card_image_of_injective _ hfinj]
  have hscard : s.card = A.card + B.card := by
    rw [hs, Finset.card_union_of_disjoint hdisj]
  have hkey : s.card - S0.card = A.card := by omega
  have hadj : ∀ a b, G.Adj (f a) (f b) ↔ (hubGraph S0 (∅ : Finset (Finset (Fin s.card)))).Adj a b := by
    intro a b
    rw [hG (f a) (f b), hubGraph_adj]
    constructor
    · rintro ⟨hne, -, -, hnb⟩
      refine ⟨fun hc => hne (by rw [hc]), ?_, by simp⟩
      rintro ⟨ha, hb⟩
      exact hnb ⟨(Finset.mem_filter.1 ha).2, (Finset.mem_filter.1 hb).2⟩
    · rintro ⟨hne, hnb, -⟩
      refine ⟨fun hc => hne (hfinj hc), hfmem a, hfmem b, ?_⟩
      rintro ⟨ha, hb⟩
      exact hnb ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩⟩
  have hsupp : ∀ u v, G.Adj u v → ∃ a, f a = u := by
    intro u v huv
    exact hfsurj u ((hG u v).1 huv).2.1
  have h := gap_transfer_embed (G := hubGraph S0 (∅ : Finset (Finset (Fin s.card)))) (H := G)
    f hfinj hadj hsupp (10 * ((s.card - S0.card : ℕ) : ℚ))
    (fun F0 => hubGraph_hole_gap S0 F0) F
  rwa [hkey] at h

end HoledClique

/-! ## The pieces of a hub graph are holed cliques -/

section Pieces

variable {n t : ℕ} {par : ℕ → ℕ} {rt : Fin n → ℕ} {sub : Fin n → Finset ℕ}
  {S0 : Finset (Fin n)}

/-- The vertex set of the `j`-th piece, split into the own part and the hole. -/
lemma treePiece_isHoledClique (j : ℕ) :
    IsHoledClique (treePiece sub rt S0 t j)
      ((treeOwn rt S0 j).image (Sum.inl : Fin n → Fin n ⊕ Fin t))
      ((treeHole sub rt S0 j).image (Sum.inl : Fin n → Fin n ⊕ Fin t)) := by
  classical
  intro u v
  constructor
  · intro hadj
    match u, v with
    | Sum.inl a, Sum.inl b =>
      obtain ⟨hne, hcase⟩ := (treePiece_adj_inl_inl sub rt S0).1 hadj
      have hne' : (Sum.inl a : Fin n ⊕ Fin t) ≠ Sum.inl b := by simpa using hne
      have hdisj := treeOwn_disjoint_treeHole (sub := sub) (rt := rt) (S0 := S0) j
      rw [Finset.disjoint_left] at hdisj
      rcases hcase with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · refine ⟨hne', Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha), ?_, ?_⟩
        · rcases hb with hb | hb
          · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb)
          · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb)
        · rintro ⟨hA, -⟩
          obtain ⟨a', ha', ha''⟩ := Finset.mem_image.1 hA
          cases ha''
          exact hdisj ha ha'
      · refine ⟨hne', ?_, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb), ?_⟩
        · rcases ha with ha | ha
          · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)
          · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha)
        · rintro ⟨-, hB⟩
          obtain ⟨b', hb', hb''⟩ := Finset.mem_image.1 hB
          cases hb''
          exact hdisj hb hb'
    | Sum.inl a, Sum.inr y => exact hadj.elim
    | Sum.inr x, Sum.inl b => exact hadj.elim
    | Sum.inr x, Sum.inr y => exact hadj.elim
  · rintro ⟨hne, hu, hv, hnb⟩
    have hmem : ∀ w : Fin n ⊕ Fin t,
        w ∈ (treeOwn rt S0 j).image (Sum.inl : Fin n → Fin n ⊕ Fin t)
          ∪ (treeHole sub rt S0 j).image (Sum.inl : Fin n → Fin n ⊕ Fin t) →
        ∃ a : Fin n, w = Sum.inl a ∧
          (a ∈ treeOwn rt S0 j ∨ a ∈ treeHole sub rt S0 j) := by
      intro w hw
      rcases Finset.mem_union.1 hw with hw' | hw'
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hw'
        exact ⟨a, rfl, Or.inl ha⟩
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hw'
        exact ⟨a, rfl, Or.inr ha⟩
    obtain ⟨a, rfl, ha⟩ := hmem u hu
    obtain ⟨b, rfl, hb⟩ := hmem v hv
    have hab : a ≠ b := by simpa using hne
    refine (treePiece_adj_inl_inl sub rt S0).2 ⟨hab, ?_⟩
    rcases ha with ha | ha
    · exact Or.inl ⟨ha, hb⟩
    · rcases hb with hb | hb
      · exact Or.inr ⟨hb, Or.inr ha⟩
      · exact absurd ⟨Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb⟩ hnb

/-- **The per-node bound.**  Any fractional packing of the `j`-th piece has
gap at most `10·|treeOwn j|`: the piece is a holed clique whose non-hole part
is exactly the set of vertices the node introduces. -/
theorem thPiece_gap (j : ℕ) (F : FracPacking (treePiece sub rt S0 t j)) :
    F.value ≤ (nu3 (treePiece sub rt S0 t j) : ℚ) + 10 * ((treeOwn rt S0 j).card : ℚ) := by
  classical
  have hdisj : Disjoint ((treeOwn rt S0 j).image (Sum.inl : Fin n → Fin n ⊕ Fin t))
      ((treeHole sub rt S0 j).image (Sum.inl : Fin n → Fin n ⊕ Fin t)) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨a', ha', ha''⟩ := Finset.mem_image.1 hw'
    cases ha''
    have hd := treeOwn_disjoint_treeHole (sub := sub) (rt := rt) (S0 := S0) j
    rw [Finset.disjoint_left] at hd
    exact hd ha ha'
  have h := thHoledClique_gap hdisj (treePiece_isHoledClique (n := n) (t := t)
    (sub := sub) (rt := rt) (S0 := S0) j) F
  rwa [Finset.card_image_of_injective _ (fun x y hxy => by simpa using hxy)] at h

/-- The pieces are subgraphs of the hub graph. -/
lemma treePiece_le_hub (h : IsSubtreeRep par rt sub) (j : ℕ) :
    treePiece sub rt S0 t j ≤ treeHubGraph sub S0 t := by
  rw [treeHubGraph_eq_treeFlower]
  exact treePiece_le h (fun x : Fin t => x) (fun _ : Fin t => (∅ : Finset (Fin n))) j

end Pieces

/-! ## The node of a hub triangle -/

section Anatomy

variable {n t : ℕ} {par : ℕ → ℕ} {rt : Fin n → ℕ} {sub : Fin n → Finset ℕ}
  {S0 : Finset (Fin n)}

/-- The node of a hub triangle, read off the finset: the largest root of its
vertices.  On a triangle `{a,b,c}` this is `triNode rt a b c`. -/
def thNode (rt : Fin n → ℕ) (T : Finset (Fin n ⊕ Fin t)) : ℕ :=
  T.sup (Sum.elim rt (fun _ => 0))

/-- Ports are isolated in the hub graph, so a hub triangle consists of hub
vertices. -/
lemma th_triangle_inl {T : Finset (Fin n ⊕ Fin t)}
    (hT : IsTriangle (treeHubGraph sub S0 t) T) :
    ∀ u ∈ T, ∃ a : Fin n, u = Sum.inl a := by
  intro u hu
  match u with
  | Sum.inl a => exact ⟨a, rfl⟩
  | Sum.inr x =>
    exfalso
    have h1 : 1 < T.card := by rw [hT.1]; norm_num
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 h1
    by_cases hpu : p = Sum.inr x
    · have := hT.2 (Sum.inr x) hu q hq (by rw [← hpu]; exact hpq)
      match q with
      | Sum.inl b => exact this.elim
      | Sum.inr y => exact this.elim
    · have := hT.2 (Sum.inr x) hu p hp (fun hc => hpu hc.symm)
      match p with
      | Sum.inl b => exact this.elim
      | Sum.inr y => exact this.elim

/-- A hub triangle written out: three distinct hub vertices, with the node
given by `triNode`. -/
lemma th_triangle_shape {T : Finset (Fin n ⊕ Fin t)}
    (hT : IsTriangle (treeHubGraph sub S0 t) T) :
    ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      T = {Sum.inl a, Sum.inl b, Sum.inl c} ∧ thNode rt T = triNode rt a b c := by
  obtain ⟨u, v, w, huv, huw, hvw, hTe⟩ := Finset.card_eq_three.1 hT.1
  obtain ⟨a, rfl⟩ := th_triangle_inl hT u (by rw [hTe]; simp)
  obtain ⟨b, rfl⟩ := th_triangle_inl hT v (by rw [hTe]; simp)
  obtain ⟨c, rfl⟩ := th_triangle_inl hT w (by rw [hTe]; simp)
  refine ⟨a, b, c, by simpa using huv, by simpa using huw, by simpa using hvw, hTe, ?_⟩
  rw [thNode, hTe]
  simp [triNode, Finset.sup_insert]

/-- The hub graph is a tree flower, so the Helly witness of `BoundedCliqueGap.TTree`
applies: the node of a hub triangle is a common node of the three subtrees. -/
lemma th_mem_sub (h : IsSubtreeRep par rt sub) {a b c : Fin n}
    (hab : (treeHubGraph sub S0 t).Adj (Sum.inl a) (Sum.inl b))
    (hac : (treeHubGraph sub S0 t).Adj (Sum.inl a) (Sum.inl c))
    (hbc : (treeHubGraph sub S0 t).Adj (Sum.inl b) (Sum.inl c)) :
    triNode rt a b c ∈ sub a ∧ triNode rt a b c ∈ sub b ∧ triNode rt a b c ∈ sub c := by
  refine treeFlower_hub_triangle_at_maxRoot (S0 := S0) (terr := fun x : Fin t => x)
    (sep := fun _ : Fin t => (∅ : Finset (Fin n))) h ?_ ?_ ?_
  · exact hab
  · exact hac
  · exact hbc

/-- The root of a vertex of a hub triangle is at most the triangle's node. -/
lemma th_rt_le_node {T : Finset (Fin n ⊕ Fin t)} {a : Fin n} (ha : Sum.inl a ∈ T) :
    rt a ≤ thNode (t := t) rt T :=
  Finset.le_sup (f := Sum.elim rt (fun _ => 0)) ha

/-- **The node of a hub triangle is a node of every one of its subtrees.** -/
lemma th_node_mem_sub (h : IsSubtreeRep par rt sub) {T : Finset (Fin n ⊕ Fin t)}
    (hT : IsTriangle (treeHubGraph sub S0 t) T) {a : Fin n} (ha : Sum.inl a ∈ T) :
    thNode rt T ∈ sub a := by
  classical
  obtain ⟨p, q, s, hpq, hps, hqs, hTe, hnode⟩ := th_triangle_shape (rt := rt) hT
  have hadj : ∀ x y : Fin n, Sum.inl x ∈ T → Sum.inl y ∈ T → x ≠ y →
      (treeHubGraph sub S0 t).Adj (Sum.inl x) (Sum.inl y) := by
    intro x y hx hy hxy
    exact hT.2 _ hx _ hy (by simpa using hxy)
  have hpT : (Sum.inl p : Fin n ⊕ Fin t) ∈ T := by rw [hTe]; simp
  have hqT : (Sum.inl q : Fin n ⊕ Fin t) ∈ T := by rw [hTe]; simp
  have hsT : (Sum.inl s : Fin n ⊕ Fin t) ∈ T := by rw [hTe]; simp
  obtain ⟨h1, h2, h3⟩ := th_mem_sub h (hadj p q hpT hqT hpq) (hadj p s hpT hsT hps)
    (hadj q s hqT hsT hqs)
  have hmem : a = p ∨ a = q ∨ a = s := by
    have := ha
    rw [hTe] at this
    simpa using this
  rw [hnode]
  rcases hmem with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

/-- **Every vertex of a hub triangle is own or hole at the triangle's node.** -/
lemma th_own_or_hole (h : IsSubtreeRep par rt sub) {T : Finset (Fin n ⊕ Fin t)}
    (hT : IsTriangle (treeHubGraph sub S0 t) T) {a : Fin n} (ha : Sum.inl a ∈ T) :
    a ∈ treeOwn rt S0 (thNode rt T) ∨ a ∈ treeHole sub rt S0 (thNode rt T) := by
  classical
  have hle : rt a ≤ thNode (t := t) rt T := th_rt_le_node ha
  have hmem : thNode rt T ∈ sub a := th_node_mem_sub h hT ha
  by_cases hS : a ∈ S0
  · exact Or.inr ((mem_treeHole sub rt S0).2 ⟨hle, hmem, Or.inl hS⟩)
  · by_cases heq : rt a = thNode (t := t) rt T
    · exact Or.inl ((mem_treeOwn rt S0).2 ⟨heq, hS⟩)
    · exact Or.inr ((mem_treeHole sub rt S0).2 ⟨hle, hmem, Or.inr (lt_of_le_of_ne hle heq)⟩)

/-- **A hub triangle always has an own vertex at its node.**  The vertex
attaining the maximal root is own unless it lies in `S₀`; but the vertices of
`S₀` are rooted at `0`, and two of them are never adjacent, so in that case
another vertex of the triangle is own. -/
lemma th_exists_own (hS0 : ∀ x ∈ S0, rt x = 0)
    {T : Finset (Fin n ⊕ Fin t)} (hT : IsTriangle (treeHubGraph sub S0 t) T) :
    ∃ a : Fin n, Sum.inl a ∈ T ∧ a ∈ treeOwn rt S0 (thNode rt T) := by
  classical
  obtain ⟨p, q, s, hpq, hps, hqs, hTe, hnode⟩ := th_triangle_shape (rt := rt) hT
  have hpT : (Sum.inl p : Fin n ⊕ Fin t) ∈ T := by rw [hTe]; simp
  have hqT : (Sum.inl q : Fin n ⊕ Fin t) ∈ T := by rw [hTe]; simp
  have hsT : (Sum.inl s : Fin n ⊕ Fin t) ∈ T := by rw [hTe]; simp
  have hadj : ∀ x y : Fin n, Sum.inl x ∈ T → Sum.inl y ∈ T → x ≠ y →
      (treeHubGraph sub S0 t).Adj (Sum.inl x) (Sum.inl y) := by
    intro x y hx hy hxy
    exact hT.2 _ hx _ hy (by simpa using hxy)
  -- the vertex attaining the node
  have hmax : rt p = thNode (t := t) rt T ∨ rt q = thNode (t := t) rt T ∨
      rt s = thNode (t := t) rt T := by
    rw [hnode]; exact treeFlower_hub_triangle_own (rt := rt) p q s
  -- a vertex attaining the node and outside `S₀` is own
  have hown : ∀ x : Fin n, rt x = thNode (t := t) rt T → x ∉ S0 →
      x ∈ treeOwn rt S0 (thNode rt T) := by
    intro x hx hxS
    exact (mem_treeOwn rt S0).2 ⟨hx, hxS⟩
  -- if the maximal vertex lies in `S₀` the node is `0`, and a neighbour is own
  have hzero : ∀ x y : Fin n, Sum.inl x ∈ T → Sum.inl y ∈ T → x ≠ y →
      rt x = thNode (t := t) rt T → x ∈ S0 →
      ∃ a : Fin n, Sum.inl a ∈ T ∧ a ∈ treeOwn rt S0 (thNode rt T) := by
    intro x y hx hy hxy hxn hxS
    have hnode0 : thNode (t := t) rt T = 0 := by rw [← hxn]; exact hS0 x hxS
    have hyS : y ∉ S0 := by
      intro hyS
      obtain ⟨-, -, hnot⟩ := hadj x y hx hy hxy
      exact hnot ⟨hxS, hyS⟩
    have hyle : rt y ≤ thNode (t := t) rt T := th_rt_le_node hy
    have hy0 : rt y = thNode (t := t) rt T := by omega
    exact ⟨y, hy, hown y hy0 hyS⟩
  rcases hmax with hm | hm | hm
  · by_cases hS : p ∈ S0
    · exact hzero p q hpT hqT hpq hm hS
    · exact ⟨p, hpT, hown p hm hS⟩
  · by_cases hS : q ∈ S0
    · exact hzero q p hqT hpT (Ne.symm hpq) hm hS
    · exact ⟨q, hqT, hown q hm hS⟩
  · by_cases hS : s ∈ S0
    · exact hzero s p hsT hpT (Ne.symm hps) hm hS
    · exact ⟨s, hsT, hown s hm hS⟩

/-- **Two own vertices already make a hub triangle clean**: it is then a
triangle of its node's piece, because the only edge a piece misses is a
hole–hole edge. -/
lemma th_clean_of_two_own (h : IsSubtreeRep par rt sub) {T : Finset (Fin n ⊕ Fin t)}
    (hT : IsTriangle (treeHubGraph sub S0 t) T) {a b : Fin n} (hab : a ≠ b)
    (haT : Sum.inl a ∈ T) (hbT : Sum.inl b ∈ T)
    (ha : a ∈ treeOwn rt S0 (thNode rt T)) (hb : b ∈ treeOwn rt S0 (thNode rt T)) :
    IsTriangle (treePiece sub rt S0 t (thNode rt T)) T := by
  classical
  refine ⟨hT.1, ?_⟩
  intro u hu v hv huv
  obtain ⟨x, rfl⟩ := th_triangle_inl hT u hu
  obtain ⟨y, rfl⟩ := th_triangle_inl hT v hv
  have hxy : x ≠ y := by simpa using huv
  have hx := th_own_or_hole h hT hu
  have hy := th_own_or_hole h hT hv
  have hdisj := treeOwn_disjoint_treeHole (sub := sub) (rt := rt) (S0 := S0) (thNode rt T)
  rw [Finset.disjoint_left] at hdisj
  rcases hx with hx | hx
  · exact (treePiece_adj_inl_inl sub rt S0).2 ⟨hxy, Or.inl ⟨hx, hy⟩⟩
  · rcases hy with hy | hy
    · exact (treePiece_adj_inl_inl sub rt S0).2 ⟨hxy, Or.inr ⟨hy, Or.inr hx⟩⟩
    · -- both hole: then `x, y` avoid the two own vertices `a, b`, so `T` has
      -- at least four elements
      exfalso
      have hxa : x ≠ a := fun hc => by subst hc; exact hdisj ha hx
      have hxb : x ≠ b := fun hc => by subst hc; exact hdisj hb hx
      have hya : y ≠ a := fun hc => by subst hc; exact hdisj ha hy
      have hyb : y ≠ b := fun hc => by subst hc; exact hdisj hb hy
      have hsub : ({Sum.inl a, Sum.inl b, Sum.inl x, Sum.inl y} :
          Finset (Fin n ⊕ Fin t)) ⊆ T := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact haT
        · exact hbT
        · exact hu
        · exact hv
      have hcard : ({Sum.inl a, Sum.inl b, Sum.inl x, Sum.inl y} :
          Finset (Fin n ⊕ Fin t)).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, Ne.symm hxa, Ne.symm hya]),
          Finset.card_insert_of_notMem (by simp [Ne.symm hxb, Ne.symm hyb]),
          Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
      have := Finset.card_le_card hsub
      rw [hcard, hT.1] at this
      omega

/-- **The shape of a foreign triangle.**  A hub triangle that is not a triangle
of its node's piece has exactly one own vertex; its other two vertices are hole
vertices, and the edge they span is owned at a strict ancestor
(`treeFlower_foreign_edge_ancestor`). -/
lemma th_foreign_shape (h : IsSubtreeRep par rt sub) (hS0 : ∀ x ∈ S0, rt x = 0)
    {T : Finset (Fin n ⊕ Fin t)} (hT : IsTriangle (treeHubGraph sub S0 t) T)
    (hfor : ¬ IsTriangle (treePiece sub rt S0 t (thNode rt T)) T) :
    ∃ a b c : Fin n, b ≠ c ∧ Sum.inl a ∈ T ∧ Sum.inl b ∈ T ∧ Sum.inl c ∈ T ∧
      a ∈ treeOwn rt S0 (thNode rt T) ∧ b ∈ treeHole sub rt S0 (thNode rt T) ∧
      c ∈ treeHole sub rt S0 (thNode rt T) := by
  classical
  obtain ⟨a, haT, ha⟩ := th_exists_own hS0 hT
  obtain ⟨p, q, s, hpq, hps, hqs, hTe, -⟩ := th_triangle_shape (rt := rt) hT
  have hpT : (Sum.inl p : Fin n ⊕ Fin t) ∈ T := by rw [hTe]; simp
  have hqT : (Sum.inl q : Fin n ⊕ Fin t) ∈ T := by rw [hTe]; simp
  have hsT : (Sum.inl s : Fin n ⊕ Fin t) ∈ T := by rw [hTe]; simp
  -- no second own vertex
  have hone : ∀ x : Fin n, Sum.inl x ∈ T → x ≠ a →
      x ∈ treeHole sub rt S0 (thNode rt T) := by
    intro x hx hxa
    rcases th_own_or_hole h hT hx with hxo | hxh
    · exact absurd (th_clean_of_two_own h hT hxa hx haT hxo ha) hfor
    · exact hxh
  have hmem : a = p ∨ a = q ∨ a = s := by
    have := haT; rw [hTe] at this; simpa using this
  rcases hmem with rfl | rfl | rfl
  · exact ⟨a, q, s, hqs, haT, hqT, hsT, ha, hone q hqT (Ne.symm hpq), hone s hsT (Ne.symm hps)⟩
  · exact ⟨a, p, s, hps, haT, hpT, hsT, ha, hone p hpT hpq, hone s hsT (Ne.symm hqs)⟩
  · exact ⟨a, p, q, hpq, haT, hpT, hqT, ha, hone p hpT hps, hone q hqT hqs⟩

/-! ## Clean triangles belong to exactly one node -/

/-- A triangle of a piece has an edge of that piece, with both endpoints in the
triangle. -/
lemma th_piece_edge {j : ℕ} {T : Finset (Fin n ⊕ Fin t)}
    (hT : IsTriangle (treePiece sub rt S0 t j) T) :
    ∃ a b : Fin n, a ≠ b ∧ Sum.inl a ∈ T ∧ Sum.inl b ∈ T ∧
      (treePiece sub rt S0 t j).Adj (Sum.inl a) (Sum.inl b) := by
  have h1 : 1 < T.card := by rw [hT.1]; norm_num
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 h1
  have hadj := hT.2 u hu v hv huv
  match u, v, hu, hv, hadj with
  | Sum.inl a, Sum.inl b, hu, hv, hadj => exact ⟨a, b, by simpa using huv, hu, hv, hadj⟩
  | Sum.inl a, Sum.inr y, _, _, hadj => exact hadj.elim
  | Sum.inr x, Sum.inl b, _, _, hadj => exact hadj.elim
  | Sum.inr x, Sum.inr y, _, _, hadj => exact hadj.elim

/-- A clean triangle determines its node. -/
lemma th_clean_unique {j j' : ℕ} {T : Finset (Fin n ⊕ Fin t)}
    (hj : IsTriangle (treePiece sub rt S0 t j) T)
    (hj' : IsTriangle (treePiece sub rt S0 t j') T) : j = j' := by
  obtain ⟨a, b, hab, haT, hbT, hadj⟩ := th_piece_edge hj
  have hadj' := hj'.2 (Sum.inl a) haT (Sum.inl b) hbT (by simpa using hab)
  rw [treePiece_index hadj, treePiece_index hadj']

/-- The node of a clean triangle is a node of the tree. -/
lemma th_clean_lt {r j : ℕ} (hr : ∀ x, rt x < r) {T : Finset (Fin n ⊕ Fin t)}
    (hj : IsTriangle (treePiece sub rt S0 t j) T) : j < r := by
  obtain ⟨a, b, -, -, -, hadj⟩ := th_piece_edge hj
  rw [treePiece_index hadj]
  have := hr a; have := hr b
  omega

end Anatomy

/-! ## The support partition and the master reduction -/

section Master

variable {n t : ℕ} {par : ℕ → ℕ} {rt : Fin n → ℕ} {sub : Fin n → Finset ℕ}
  {S0 : Finset (Fin n)}

open scoped Classical in
/-- The restriction of a hub packing to the triangles of the `j`-th piece. -/
noncomputable def thPart (F : FracPacking (treeHubGraph sub S0 t)) (rt : Fin n → ℕ) (j : ℕ) :
    FracPacking (treePiece sub rt S0 t j) :=
  F.restrict (fun T => IsTriangle (treePiece sub rt S0 t j) T) (treePiece sub rt S0 t j)
    (fun _ _ hp => hp)

open scoped Classical in
/-- The **foreign mass** of a hub packing: the weight it puts on triangles that
are a triangle of no piece — equivalently (`th_foreign_shape`) on triangles with
two hole vertices at their node, whose hole–hole edge is owned at a strict
ancestor. -/
noncomputable def thForeignMass (sub : Fin n → Finset ℕ) (rt : Fin n → ℕ)
    (S0 : Finset (Fin n)) (t : ℕ) (F : FracPacking (treeHubGraph sub S0 t)) : ℚ :=
  ∑ T ∈ Finset.univ.filter
      (fun T => F.x T ≠ 0 ∧ ∀ j, ¬ IsTriangle (treePiece sub rt S0 t j) T), F.x T

open scoped Classical in
/-- **The exact split of the LP value.**  Every support triangle is a triangle
of at most one piece (`th_clean_unique`), and its node is a node of the tree
(`th_clean_lt`); so the value splits into the per-node values plus the foreign
mass. -/
theorem th_value_eq_sum_add_foreign {r : ℕ} (hr : ∀ x, rt x < r)
    (F : FracPacking (treeHubGraph sub S0 t)) :
    F.value = (∑ j ∈ Finset.range r, (thPart F rt j).value)
      + thForeignMass sub rt S0 t F := by
  classical
  have hpart : ∀ j, (thPart F rt j).value
      = ∑ T ∈ Finset.univ.filter
          (fun T => F.x T ≠ 0 ∧ IsTriangle (treePiece sub rt S0 t j) T), F.x T := by
    intro j
    exact FracPacking.restrict_value F (fun T => IsTriangle (treePiece sub rt S0 t j) T)
      (treePiece sub rt S0 t j) (fun _ _ hp => hp)
  have hclean : (Finset.univ.filter
        (fun T : Finset (Fin n ⊕ Fin t) => F.x T ≠ 0 ∧
          ¬ (∀ j, ¬ IsTriangle (treePiece sub rt S0 t j) T)))
      = (Finset.range r).biUnion (fun j => Finset.univ.filter
          (fun T => F.x T ≠ 0 ∧ IsTriangle (treePiece sub rt S0 t j) T)) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, not_forall, not_not]
    constructor
    · rintro ⟨hx, j, hj⟩
      exact ⟨j, th_clean_lt hr hj, hx, hj⟩
    · rintro ⟨j, -, hx, hj⟩
      exact ⟨hx, j, hj⟩
  have hdisj : ((Finset.range r : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun j => Finset.univ.filter
        (fun T : Finset (Fin n ⊕ Fin t) => F.x T ≠ 0 ∧
          IsTriangle (treePiece sub rt S0 t j) T)) := by
    rintro j - j' - hjj
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro T hT hT'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT hT'
    exact hjj (th_clean_unique hT.2 hT'.2)
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter fun T : Finset (Fin n ⊕ Fin t) => F.x T ≠ 0)
    (fun T => ∀ j, ¬ IsTriangle (treePiece sub rt S0 t j) T) F.x
  have h1 : ((Finset.univ.filter fun T : Finset (Fin n ⊕ Fin t) => F.x T ≠ 0).filter
      (fun T => ∀ j, ¬ IsTriangle (treePiece sub rt S0 t j) T))
      = Finset.univ.filter (fun T => F.x T ≠ 0 ∧
          ∀ j, ¬ IsTriangle (treePiece sub rt S0 t j) T) := by
    ext T; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h2 : ((Finset.univ.filter fun T : Finset (Fin n ⊕ Fin t) => F.x T ≠ 0).filter
      (fun T => ¬ ∀ j, ¬ IsTriangle (treePiece sub rt S0 t j) T))
      = Finset.univ.filter (fun T => F.x T ≠ 0 ∧
          ¬ ∀ j, ¬ IsTriangle (treePiece sub rt S0 t j) T) := by
    ext T; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h1, h2, hclean, Finset.sum_biUnion hdisj] at hsplit
  rw [FracPacking.value, thForeignMass]
  rw [Finset.sum_congr rfl (fun j _ => hpart j)]
  linarith [hsplit]

open scoped Classical in
/-- **The master reduction of lane TH.**  For every subtree representation and
every fractional packing of its hub graph,

  `value ≤ ν₃(hub) + 10·(n − |S₀|) + foreignMass`.

Everything is on the packing side: the value splits over the nodes
(`th_value_eq_sum_add_foreign`), each node's piece is a holed clique of gap
`10·|own|` (`thPiece_gap`), the pieces are pairwise edge-disjoint so their
packing numbers add inside `ν₃` (`nu3_sum_le_of_edgeDisjoint`), and the own
sets add up to `n − |S₀|` (`sum_treeOwn_card`). -/
theorem th_value_le_nu3_add_foreign (h : IsSubtreeRep par rt sub) {r : ℕ}
    (hr : ∀ x, rt x < r) (F : FracPacking (treeHubGraph sub S0 t)) :
    F.value ≤ (nu3 (treeHubGraph sub S0 t) : ℚ) + 10 * ((n - S0.card : ℕ) : ℚ)
      + thForeignMass sub rt S0 t F := by
  classical
  have hnu : ∑ j ∈ Finset.range r, nu3 (treePiece sub rt S0 t j)
      ≤ nu3 (treeHubGraph sub S0 t) := by
    refine nu3_sum_le_of_edgeDisjoint (Finset.range r) (treeHubGraph sub S0 t)
      (fun j => treePiece sub rt S0 t j) (fun j _ => treePiece_le_hub h j) ?_
    rintro j - j' - hjj u v hadj
    exact treePiece_disjoint hjj u v hadj
  have hnuQ : (∑ j ∈ Finset.range r, (nu3 (treePiece sub rt S0 t j) : ℚ))
      ≤ (nu3 (treeHubGraph sub S0 t) : ℚ) := by
    have : ((∑ j ∈ Finset.range r, nu3 (treePiece sub rt S0 t j) : ℕ) : ℚ)
        ≤ (nu3 (treeHubGraph sub S0 t) : ℚ) := by exact_mod_cast hnu
    rwa [Nat.cast_sum] at this
  have hown : (∑ j ∈ Finset.range r, ((treeOwn rt S0 j).card : ℚ))
      = ((n - S0.card : ℕ) : ℚ) := by
    have := sum_treeOwn_card rt S0 r hr
    exact_mod_cast congrArg (fun k : ℕ => (k : ℚ)) this
  have hstep : ∀ j ∈ Finset.range r, (thPart F rt j).value
      ≤ (nu3 (treePiece sub rt S0 t j) : ℚ) + 10 * ((treeOwn rt S0 j).card : ℚ) :=
    fun j _ => thPiece_gap j (thPart F rt j)
  have hsum : (∑ j ∈ Finset.range r, (thPart F rt j).value)
      ≤ (nu3 (treeHubGraph sub S0 t) : ℚ) + 10 * ((n - S0.card : ℕ) : ℚ) := by
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hown]
    linarith [hnuQ]
  rw [th_value_eq_sum_add_foreign hr F]
  linarith

end Master

/-! ## Axiom audit -/

end BoundedCliqueGap
