import BoundedCliqueGap.NChain

/-
`BoundedCliqueGap.QTree` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Rung Q2 — the TREE FLOWER

The chain flower of rung N1 records hub membership by an *interval* `[lo a, hi a]`
of a path.  A chordal block presents itself not on a path but on a **clique
tree**, and a hub vertex then occupies a *subtree*.  This file carries the whole
N1 machinery over to that setting.

## The shape

The skeleton tree is given by a parent function `par : ℕ → ℕ` with `par j < j`
for `j > 0`, so node `0` is the root and *ancestors have smaller indices*; the
leaf-to-root order is the reverse of the order on `ℕ`.  A hub vertex
`a : Fin n` carries

* its node set `sub a : Finset ℕ` — the subtree of clique-tree nodes whose
  cliques contain `a`, and
* its **root** `rt a`, the node of `sub a` closest to the tree root.

`IsSubtreeRep par rt sub` records exactly that this is a family of subtrees:
`rt a ∈ sub a`, `rt a` is the smallest node of `sub a`, and `sub a` is closed
under `par` above its root.  Two hub vertices are adjacent when their subtrees
meet (and not both lie in the hole `S₀`); territories are attached exactly as
before.

Taking `par j = j - 1` and `sub a = Icc (lo a) (hi a)` gives back the chain
flower (`chainFlower_eq_treeFlower`), so the tree primitive contains all three
earlier ones.

## Helly

`subtree_meet_max_rt` — two subtrees that meet share the *larger* of their two
roots — is the tree analogue of "two intersecting intervals share the larger
left endpoint", and it gives Helly for subtrees
(`treeFlower_hub_triangle_common`): three pairwise adjacent hub vertices all
belong to one clique-tree node, so triangles remain **piece-local** and the
donation mechanism is still hub-local.

## The pieces, the charge, the ceiling

Each hub vertex is charged at its subtree's root: `treeOwn rt S0 j` is
literally `chainOwn` for `lo := rt`, so the charge identity
`sum_treeOwn_card : ∑_j |treeOwn j| = n − |S₀|` is the chain identity, now read
as "each hub vertex is new at exactly one node of the tree".  The hole of the
`j`-th piece is `treeHole` (present at `j`, but rooted strictly above `j`, or in
`S₀`), the piece `treePiece j` carries the edges new at `j`, each hub edge lies
in exactly one piece — the piece of `{a,b}` is `max (rt a) (rt b)`, as in the
chain — and the dual weight is again `chainW`, keyed by `rt`.  The LP ceiling is
`treeFlower_value_le`, with the `1/2`-on-gluing instance
`treeFlower_value_le_half_gluing`.
-/

namespace BoundedCliqueGap

open Finset

section TreeDef

variable {n t m : ℕ}

/-- A family of **subtrees** of the rooted tree given by `par`: `rt a` is the
root of `sub a` (its smallest node), and `sub a` is closed under taking parents
above its root. -/
structure IsSubtreeRep (par : ℕ → ℕ) (rt : Fin n → ℕ) (sub : Fin n → Finset ℕ) : Prop where
  /-- the parent of a non-root node is closer to the root -/
  par_lt : ∀ j, 0 < j → par j < j
  /-- the root of a subtree belongs to it -/
  rt_mem : ∀ a, rt a ∈ sub a
  /-- the root is the node closest to the tree root -/
  rt_min : ∀ a j, j ∈ sub a → rt a ≤ j
  /-- a subtree is closed under parents, above its own root -/
  up : ∀ a j, j ∈ sub a → j ≠ rt a → par j ∈ sub a

/-- The **tree flower**: hub vertices `Fin n`, the vertex `a` occupying the
subtree `sub a` of the clique-tree skeleton; two hub vertices are adjacent when
their subtrees meet and they are not both in the hole `S₀`; the territories are
attached as in the holed flower. -/
def treeFlower (sub : Fin n → Finset ℕ) (S0 : Finset (Fin n)) (terr : Fin t → Fin m)
    (sep : Fin m → Finset (Fin n)) : SimpleGraph (Fin n ⊕ Fin t) where
  Adj u v :=
    match u, v with
    | Sum.inl a, Sum.inl b => a ≠ b ∧ (sub a ∩ sub b).Nonempty ∧ ¬ (a ∈ S0 ∧ b ∈ S0)
    | Sum.inl a, Sum.inr y => a ∈ sep (terr y)
    | Sum.inr x, Sum.inl b => b ∈ sep (terr x)
    | Sum.inr x, Sum.inr y => x ≠ y ∧ terr x = terr y
  symm := by
    intro u v h; cases u <;> cases v
    · refine ⟨Ne.symm h.1, ?_, fun hc => h.2.2 ⟨hc.2, hc.1⟩⟩
      rw [Finset.inter_comm]
      exact h.2.1
    · exact h
    · exact h
    · exact ⟨Ne.symm h.1, h.2.symm⟩
  loopless := by
    constructor; intro u h; cases u
    · exact h.1 rfl
    · exact h.1 rfl

variable (sub : Fin n → Finset ℕ) (S0 : Finset (Fin n)) (terr : Fin t → Fin m)
  (sep : Fin m → Finset (Fin n))

@[simp] lemma treeFlower_adj_inl_inl {a b : Fin n} :
    (treeFlower sub S0 terr sep).Adj (Sum.inl a) (Sum.inl b) ↔
      a ≠ b ∧ (sub a ∩ sub b).Nonempty ∧ ¬ (a ∈ S0 ∧ b ∈ S0) := Iff.rfl

@[simp] lemma treeFlower_adj_inl_inr {a : Fin n} {y : Fin t} :
    (treeFlower sub S0 terr sep).Adj (Sum.inl a) (Sum.inr y) ↔ a ∈ sep (terr y) := Iff.rfl

@[simp] lemma treeFlower_adj_inr_inl {b : Fin n} {x : Fin t} :
    (treeFlower sub S0 terr sep).Adj (Sum.inr x) (Sum.inl b) ↔ b ∈ sep (terr x) := Iff.rfl

/-! ## The chain flower is a tree flower -/

end TreeDef

/-! ## Helly for subtrees -/

section Helly

variable {n : ℕ} {par : ℕ → ℕ} {rt : Fin n → ℕ} {sub : Fin n → Finset ℕ}

/-- **The key tree fact.**  If the subtrees of `a` and `b` share the node `j`
and `a`'s root is the higher one, then `b`'s root already lies in `a`'s
subtree: both roots are ancestors of `j`, and ancestors of a node form a
chain. -/
theorem rt_mem_of_common_node (h : IsSubtreeRep par rt sub) :
    ∀ j : ℕ, ∀ a b : Fin n, j ∈ sub a → j ∈ sub b → rt a ≤ rt b → rt b ∈ sub a := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro a b hja hjb hle
    by_cases hjb' : j = rt b
    · exact hjb' ▸ hja
    · have hbj : rt b ≤ j := h.rt_min b j hjb
      have hjpos : 0 < j := by omega
      have hja' : j ≠ rt a := by
        intro hc
        have : rt b ≤ rt a := hc ▸ hbj
        exact hjb' (by omega)
      exact ih (par j) (h.par_lt j hjpos) a b (h.up a j hja hja') (h.up b j hjb hjb') hle

/-- **Two subtrees that meet share the larger of their roots.** -/
theorem subtree_meet_max_rt (h : IsSubtreeRep par rt sub) {a b : Fin n}
    (hab : (sub a ∩ sub b).Nonempty) :
    max (rt a) (rt b) ∈ sub a ∧ max (rt a) (rt b) ∈ sub b := by
  obtain ⟨j, hj⟩ := hab
  rw [Finset.mem_inter] at hj
  rcases le_total (rt a) (rt b) with hle | hle
  · have h1 : rt b ∈ sub a := rt_mem_of_common_node h j a b hj.1 hj.2 hle
    rw [max_eq_right hle]
    exact ⟨h1, h.rt_mem b⟩
  · have h1 : rt a ∈ sub b := rt_mem_of_common_node h j b a hj.2 hj.1 hle
    rw [max_eq_left hle]
    exact ⟨h.rt_mem a, h1⟩

end Helly

/-! ## The pieces of the tree -/

section TreePieces

variable {n t : ℕ}

/-- The hub vertices **entering the tree at node `j`**: those whose subtree is
rooted at `j`, outside the hole.  This is `chainOwn` read with `lo := rt`: each
hub vertex is charged at its subtree's root. -/
def treeOwn (rt : Fin n → ℕ) (S0 : Finset (Fin n)) (j : ℕ) : Finset (Fin n) :=
  chainOwn rt S0 j

/-- The **hole of the `j`-th piece**: the hub vertices present at node `j` but
rooted strictly above it — the gluing separator — together with the parent
separator `S₀`. -/
def treeHole (sub : Fin n → Finset ℕ) (rt : Fin n → ℕ) (S0 : Finset (Fin n)) (j : ℕ) :
    Finset (Fin n) :=
  univ.filter (fun a => rt a ≤ j ∧ j ∈ sub a ∧ (a ∈ S0 ∨ rt a < j))

variable (sub : Fin n → Finset ℕ) (rt : Fin n → ℕ) (S0 : Finset (Fin n))

@[simp] lemma mem_treeOwn {a : Fin n} {j : ℕ} :
    a ∈ treeOwn rt S0 j ↔ rt a = j ∧ a ∉ S0 := by simp [treeOwn, chainOwn]

@[simp] lemma mem_treeHole {a : Fin n} {j : ℕ} :
    a ∈ treeHole sub rt S0 j ↔ rt a ≤ j ∧ j ∈ sub a ∧ (a ∈ S0 ∨ rt a < j) := by
  simp [treeHole]

lemma treeOwn_disjoint_treeHole (j : ℕ) :
    Disjoint (treeOwn rt S0 j) (treeHole sub rt S0 j) := by
  rw [Finset.disjoint_left]
  intro a ha ha'
  rw [mem_treeOwn] at ha
  rw [mem_treeHole] at ha'
  rcases ha'.2.2 with h | h
  · exact ha.2 h
  · omega

/-- The `j`-th **piece** of the tree hub: the pairs with one endpoint new at
node `j` and the other present at `j`. -/
def treePiece (sub : Fin n → Finset ℕ) (rt : Fin n → ℕ) (S0 : Finset (Fin n)) (t j : ℕ) :
    SimpleGraph (Fin n ⊕ Fin t) where
  Adj u v :=
    match u, v with
    | Sum.inl a, Sum.inl b =>
        a ≠ b ∧ ((a ∈ treeOwn rt S0 j ∧ (b ∈ treeOwn rt S0 j ∨ b ∈ treeHole sub rt S0 j)) ∨
                 (b ∈ treeOwn rt S0 j ∧ (a ∈ treeOwn rt S0 j ∨ a ∈ treeHole sub rt S0 j)))
    | _, _ => False
  symm := by
    intro u v h; cases u <;> cases v
    · exact ⟨Ne.symm h.1, h.2.symm⟩
    · exact h
    · exact h
    · exact h
  loopless := by
    constructor; intro u h; cases u
    · exact h.1 rfl
    · exact h

@[simp] lemma treePiece_adj_inl_inl {j : ℕ} {a b : Fin n} :
    (treePiece sub rt S0 t j).Adj (Sum.inl a) (Sum.inl b) ↔
      a ≠ b ∧ ((a ∈ treeOwn rt S0 j ∧ (b ∈ treeOwn rt S0 j ∨ b ∈ treeHole sub rt S0 j)) ∨
               (b ∈ treeOwn rt S0 j ∧ (a ∈ treeOwn rt S0 j ∨ a ∈ treeHole sub rt S0 j))) :=
  Iff.rfl

variable {sub rt S0}

/-- Every edge of a piece is an edge of the tree flower. -/
lemma treePiece_le {par : ℕ → ℕ} (h : IsSubtreeRep par rt sub) {m : ℕ} (terr : Fin t → Fin m)
    (sep : Fin m → Finset (Fin n)) (j : ℕ) :
    treePiece sub rt S0 t j ≤ treeFlower sub S0 terr sep := by
  intro u v hadj
  cases u with
  | inr x => exact hadj.elim
  | inl a =>
    cases v with
    | inr y => exact hadj.elim
    | inl b =>
      obtain ⟨hne, hcase⟩ := hadj
      have key : ∀ p q : Fin n, p ∈ treeOwn rt S0 j →
          (q ∈ treeOwn rt S0 j ∨ q ∈ treeHole sub rt S0 j) →
          (sub p ∩ sub q).Nonempty ∧ ¬ (p ∈ S0 ∧ q ∈ S0) := by
        intro p q hp hq
        rw [mem_treeOwn] at hp
        have hjp : j ∈ sub p := hp.1 ▸ h.rt_mem p
        have hjq : j ∈ sub q := by
          rcases hq with hq | hq
          · rw [mem_treeOwn] at hq; exact hq.1 ▸ h.rt_mem q
          · rw [mem_treeHole] at hq; exact hq.2.1
        exact ⟨⟨j, Finset.mem_inter.2 ⟨hjp, hjq⟩⟩, fun hc => hp.2 hc.1⟩
      rcases hcase with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · obtain ⟨h1, h2⟩ := key a b hp hq
        exact ⟨hne, h1, h2⟩
      · obtain ⟨h1, h2⟩ := key b a hp hq
        exact ⟨hne, by rwa [Finset.inter_comm], fun hc => h2 ⟨hc.2, hc.1⟩⟩

/-- **Each hub edge lies in exactly one piece** (uniqueness). -/
lemma treePiece_index {j : ℕ} {a b : Fin n}
    (hadj : (treePiece sub rt S0 t j).Adj (Sum.inl a) (Sum.inl b)) : j = max (rt a) (rt b) := by
  obtain ⟨-, hcase⟩ := hadj
  rcases hcase with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [mem_treeOwn] at hp
    rcases hq with hq | hq
    · rw [mem_treeOwn] at hq; omega
    · rw [mem_treeHole] at hq; omega
  · rw [mem_treeOwn] at hp
    rcases hq with hq | hq
    · rw [mem_treeOwn] at hq; omega
    · rw [mem_treeHole] at hq; omega

lemma treePiece_disjoint {j j' : ℕ} (hjj : j ≠ j') (u v : Fin n ⊕ Fin t) :
    (treePiece sub rt S0 t j).Adj u v → ¬ (treePiece sub rt S0 t j').Adj u v := by
  cases u with
  | inr x => intro h; exact h.elim
  | inl a =>
    cases v with
    | inr y => intro h; exact h.elim
    | inl b =>
      intro h1 h2
      exact hjj ((treePiece_index h1).trans (treePiece_index h2).symm)

end TreePieces

/-! ## The charge of the tree adds up -/

section TreeCharge

variable {n : ℕ}

/-- **The charge identity of the tree**: each hub vertex outside the hole is
new at exactly one node — the root of its subtree — so the sizes of the
`treeOwn` sets add up to `n − |S₀|`. -/
theorem sum_treeOwn_card (rt : Fin n → ℕ) (S0 : Finset (Fin n)) (r : ℕ)
    (hr : ∀ a, rt a < r) :
    ∑ j ∈ Finset.range r, (treeOwn rt S0 j).card = n - S0.card :=
  sum_chainOwn_card rt rt S0 r (fun _ => le_rfl) hr

end TreeCharge

/-! ## The dual weight and the LP ceiling of the tree flower -/

section TreeLP

variable {n t m : ℕ} {sub : Fin n → Finset ℕ} {rt : Fin n → ℕ} {S0 : Finset (Fin n)}
  {terr : Fin t → Fin m} {sep : Fin m → Finset (Fin n)} {a g c d : ℚ}

/-- The gluing edge slots of the `j`-th piece: one endpoint new at node `j`,
the other in the piece's hole. -/
noncomputable def treeGlueEdgeSet (sub : Fin n → Finset ℕ) (rt : Fin n → ℕ)
    (S0 : Finset (Fin n)) (t j : ℕ) : Finset (Sym2 (Fin n ⊕ Fin t)) :=
  ((treeOwn rt S0 j) ×ˢ (treeHole sub rt S0 j)).image
    (fun q => s((Sum.inl q.1 : Fin n ⊕ Fin t), Sum.inl q.2))

lemma card_treeGlueEdgeSet_le (j : ℕ) :
    (treeGlueEdgeSet sub rt S0 t j).card
      ≤ (treeOwn rt S0 j).card * (treeHole sub rt S0 j).card := by
  classical
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_product]

end TreeLP

/-! ## Axiom audit -/

end BoundedCliqueGap
