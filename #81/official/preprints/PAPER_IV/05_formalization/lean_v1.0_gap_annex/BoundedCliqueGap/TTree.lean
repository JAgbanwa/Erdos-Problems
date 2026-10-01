import BoundedCliqueGap.QTree

/-
`BoundedCliqueGap.TTree` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Rung T3 (tree half) — the anatomy of the per-node shell decomposition

The primal lift of rung T3 rests on a structural claim about the hub of a tree
flower, which this module machine-checks in full generality (any subtree
representation `IsSubtreeRep`, any hole, any territories):

* every hub triangle is present at the node `max` of its three subtree roots
  (`treeFlower_hub_triangle_at_maxRoot`) — Helly for subtrees with the witness
  *named*, so that the assignment `triNode` of a triangle to a node is a
  function, symmetric in the three vertices
  (`treeFlower_hub_triangle_node_unique`): **every triangle belongs to exactly
  one node's shell**;
* at that node the maximal vertex is *own* (`treeFlower_hub_triangle_own`) and
  the other two are rooted at or above it (`treeFlower_hub_triangle_le`), so
  the triangle is of type `(o,o,o)`, `(o,o,h)` or `(o,h,h)` and never
  `(h,h,h)`;
* in the `(o,h,h)` case the foreign edge is owned at a **strict ancestor**
  (`treeFlower_foreign_edge_ancestor`), where the same triangle is a *port*
  triangle, its own vertex being the port;
* a hub edge belongs to the pieces of at most **two** nodes
  (`treePiece_node_mem_pair`, `card_pieces_of_edge_le_two`) — this is exactly
  the `card_ports_le_two` hypothesis of the `PortSystem` abstraction that
  `donation_exchange_half` consumes, so the sharing of cross edges between two
  shells is arbitrated by the exchange at credit `1/2`.

What is **not** here is the lift itself.  The shell half of rung T3
(`BoundedCliqueGap/TLift.lean`) shows that the per-shell accounting the lift would feed
this anatomy into is unsatisfiable as it stands (`not_exchangeBudget`), so the
composition is not carried out; the anatomy is banked separately because it is
independent of that obstruction and is what a repaired per-shell accounting
would consume.

The K-lane shell modules and the N/Q-lane tree modules define some Props
twice and cannot be imported into one file, which is the reason this half is a
separate module.
-/

namespace BoundedCliqueGap

open Finset

/-! ## The tree anatomy -/

section TreeAnatomy

variable {n t m : ℕ} {par : ℕ → ℕ} {rt : Fin n → ℕ} {sub : Fin n → Finset ℕ}
  {S0 : Finset (Fin n)} {terr : Fin t → Fin m} {sep : Fin m → Finset (Fin n)}

/-- The node of a hub triangle: the largest of the three subtree roots. -/
def triNode (rt : Fin n → ℕ) (a b c : Fin n) : ℕ := max (rt a) (max (rt b) (rt c))

/-- Two meeting subtrees share the larger root. -/
lemma mem_sub_of_rt_le (h : IsSubtreeRep par rt sub) {a b : Fin n}
    (hmeet : (sub a ∩ sub b).Nonempty) (hle : rt a ≤ rt b) : rt b ∈ sub a := by
  have h1 := (subtree_meet_max_rt h hmeet).1
  rwa [max_eq_right hle] at h1

/-- The maximal vertex of a hub triangle is **own** at the triangle's node. -/
theorem treeFlower_hub_triangle_own (a b c : Fin n) :
    rt a = triNode rt a b c ∨ rt b = triNode rt a b c ∨ rt c = triNode rt a b c := by
  simp only [triNode]
  rcases le_total (rt a) (max (rt b) (rt c)) with h | h
  · rcases le_total (rt b) (rt c) with h' | h'
    · exact Or.inr (Or.inr (by rw [max_eq_right h, max_eq_right h']))
    · exact Or.inr (Or.inl (by rw [max_eq_right h, max_eq_left h']))
  · exact Or.inl (by rw [max_eq_left h])

/-- The other two vertices of a hub triangle are rooted at or above the
triangle's node: at that node they are own or hole, never foreign. -/
theorem treeFlower_hub_triangle_le (a b c : Fin n) :
    rt a ≤ triNode rt a b c ∧ rt b ≤ triNode rt a b c ∧ rt c ≤ triNode rt a b c :=
  ⟨le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _),
    le_trans (le_max_right _ _) (le_max_right _ _)⟩

/-- **The node of a hub triangle is a common node of its three subtrees.**
Helly for subtrees with the witness named: the common node is the largest of
the three roots. -/
theorem treeFlower_hub_triangle_at_maxRoot (h : IsSubtreeRep par rt sub) {a b c : Fin n}
    (hab : (treeFlower sub S0 terr sep).Adj (Sum.inl a) (Sum.inl b))
    (hac : (treeFlower sub S0 terr sep).Adj (Sum.inl a) (Sum.inl c))
    (hbc : (treeFlower sub S0 terr sep).Adj (Sum.inl b) (Sum.inl c)) :
    triNode rt a b c ∈ sub a ∧ triNode rt a b c ∈ sub b ∧ triNode rt a b c ∈ sub c := by
  obtain ⟨-, hab', -⟩ := hab
  obtain ⟨-, hac', -⟩ := hac
  obtain ⟨-, hbc', -⟩ := hbc
  have hba' : (sub b ∩ sub a).Nonempty := by rwa [Finset.inter_comm]
  have hca' : (sub c ∩ sub a).Nonempty := by rwa [Finset.inter_comm]
  have hcb' : (sub c ∩ sub b).Nonempty := by rwa [Finset.inter_comm]
  obtain ⟨hla, hlb, hlc⟩ := treeFlower_hub_triangle_le (rt := rt) a b c
  have key : ∀ x v : Fin n, rt v = triNode rt a b c → rt x ≤ triNode rt a b c →
      (sub x ∩ sub v).Nonempty → triNode rt a b c ∈ sub x := by
    intro x v hv hx hmeet
    have hxv : rt x ≤ rt v := by rw [hv]; exact hx
    have := mem_sub_of_rt_le h hmeet hxv
    rwa [hv] at this
  rcases treeFlower_hub_triangle_own (rt := rt) a b c with hA | hB | hC
  · exact ⟨by rw [← hA]; exact h.rt_mem a, key b a hA hlb hba', key c a hA hlc hca'⟩
  · exact ⟨key a b hB hla hab', by rw [← hB]; exact h.rt_mem b, key c b hB hlc hcb'⟩
  · exact ⟨key a c hC hla hac', key b c hC hlb hbc', by rw [← hC]; exact h.rt_mem c⟩

end TreeAnatomy

/-! ## Axiom audit -/

end BoundedCliqueGap
