/-
# Nibble — the **3-way coherence gate** of the laminar (dyadic) route to `BlockCoverResidualCoupled`

Three routes to the general-density residual `Nibble.AX1.BlockCoverResidualCoupled` have been
refuted.  The last one — one *portion* of each cluster per density band — was refuted by
`Nibble.AX1.portion_budget_overrun` (`Nibble.BlockCoverPortionBudget`): reserving a **product
region** `R(S) × R(T)` of a cluster pair for the demand of a band costs `f + g ≥ 2√(fg)`, so the
budget the scheme obeys is `∑_π √(a_π) ≤ 1` while the LP only gives `∑_π a_π ≤ 1`.

The divergent route makes all block lengths **dyadic**, so that the intervals a cluster offers are
laminar and each cluster side is a 1-D dyadic packing governed exactly by Kraft's inequality
(`Nibble.AX1.kraft_pack`, `Nibble.KraftPackLocal`) — no `√`-loss on a *side*.  Its open gate is
**3-way coherence**: a member on the cluster triple `(S,T,Y)` uses one `S`-block, of the size pinned
by the *opposite* pair `d(T,Y)`, in **both** of its `S`-rectangles, so the quadtree layouts of the
pairs `(S,T)` and `(S,Y)` have to be compatible; the fear is a coherence conflict in which one
cluster's tree cannot serve two pairs' demands at once.

This file **settles that gate, positively**, by an explicit instance.

## What the objective actually asks for

The covering sum of `Nibble.AX1.BlockCoverResidualCoupled` is, per member,
`(d(U,W)·|A||B| + d(U,X)·|A||C| + d(W,X)·|B||C|)/3`: the sum over the member's three rectangles of
`(density of the cluster pair) × (area of the rectangle)`, divided by `3`
(`Nibble.AX1.member_cover_eq_weighted_area`).  So the objective is a **density-weighted area
functional**: the *shapes* of the rectangles are irrelevant to the value, only the area they cover
in each cluster-pair square counts, and the value is maximal exactly when every pair square is
*exactly tiled*.  A family that tiles every pair square therefore attains the capacity bound
`∑_pairs d(S,T)·|S||T| / 3` of `Nibble.AX1.nu3star_regularityReduced_le_dense_cluster_capacity`,
which dominates `ν₃*`: no loss at all.

## The instance

Four clusters `S, T, U, Z`; the triangle `S,T,U` has density `1`, the three edges to `Z` have
density `1/2`.  Each cluster is cut into `4` slots, each slot into `2` halves — `8` atoms, so a
*full slot* is `2` atoms and a *half* is `1` atom, and with the block scale `τ = 1 slot` the block
size prescribed by a density `d` is exactly `2d` atoms: `2` for `d = 1`, `1` for `d = 1/2`.  The
family (`Nibble.AX1.gateFamily`, 60 members) is

* `12` members on `(S,T,U)`: three full slots, placed by the Klein-group Latin square `u = i ⊕ j`
  off a transversal (the transversal exists because the Sylow 2-subgroup of `ℤ₂ × ℤ₂` is
  non-cyclic — the cyclic group of order `4` has no complete mapping);
* `16` members on `(S,T,Z)`, `16` on `(S,U,Z)`, `16` on `(T,U,Z)`: two halves and one full slot,
  the full `Z`-slot being the *colour* of a proper `4`-edge-colouring of the octahedron `K₂,₂,₂`
  (the gadget the three half-block families form on the halves of one slot of each cluster).

`Nibble.AX1.gate_exact_tiling` says every one of the six cluster-pair squares is covered **exactly
once**, hence (`gate_rect_disjoint`, `gate_rect_cover`) the rectangles are pairwise disjoint and
fill the square, and (`gate_value_eq_capacity`) the family attains the capacity bound exactly.

## Why this settles the gate

At the pair `(S,T)` the demand is `3/4` of the square in shape `(full, full)` and `1/4` in shape
`(half, half)` — a **diagonal**, non-product demand: `gate_product_layout_fails` shows no product
region allocation can serve it (a product would need `f₀g₀ ≥ 3/4` and `f₁g₁ ≥ 1/4` with
`f₀+f₁ ≤ 1`, `g₀+g₁ ≤ 1`, which is impossible; quantitatively `gate_product_layout_serves_le` caps
any product allocation at `13/16` of the demand).  So the instance is *out of reach of the portion
route by a constant factor*, and the coupled quadtree family serves it **exactly**, with the three
cluster trees shared coherently across all six pairs.  The 2-D/quadtree coupling therefore does
**not** force a constant-factor loss: the obstruction found for portions is an artefact of the
product structure, not of the coupling.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Prelude

open Finset

namespace Nibble.AX1

/-! ## 0. The objective is a density-weighted area functional -/

/-- **The covering term of one member is a density-weighted area.**  With block sizes
`|A| = τ·x`, `|B| = τ·y`, `|C| = τ·z` prescribed by the three *opposite* densities
(`x = d(W,X)`, `y = d(U,X)`, `z = d(U,W)`), the covering term
`(d(U,W)|A||B| + d(U,X)|A||C| + d(W,X)|B||C|)/3` of `Nibble.AX1.BlockCoverResidualCoupled` is the
sum over the member's three rectangles of `(pair density) × (rectangle area)`, divided by `3`, and
equals `τ²·xyz`.  Hence the covering objective does not see the *shapes* of the rectangles at all:
it is maximised exactly by families that tile the cluster-pair squares. -/
theorem member_cover_eq_weighted_area (τ x y z : ℝ) :
    (z * (τ * x) * (τ * y) + y * (τ * x) * (τ * z) + x * (τ * y) * (τ * z)) / 3
      = τ ^ 2 * (x * y * z) := by
  ring

/-! ## 1. The model: clusters, atoms, dyadic blocks, members -/

/-- The four clusters of the gate instance. -/
inductive GCl | S | T | U | Z
  deriving DecidableEq, Fintype, Repr

/-- The atoms of one cluster: `4` slots of `2` halves each.  A *full slot* is a pair of atoms, a
*half* is a single atom; the block scale is `τ = 1 slot = 2 atoms`. -/
abbrev GAtom := Fin 8

/-- `2·(the density)` of a cluster pair, as a natural number: the triangle `S,T,U` carries density
`1` (so `2`), the three edges to `Z` carry density `1/2` (so `1`), and a cluster is not joined to
itself.  With `τ = 2` atoms this is exactly the block size in atoms that the pair prescribes for
the *opposite* cluster. -/
def gdens2 : GCl → GCl → ℕ
  | GCl.Z, GCl.Z => 0
  | GCl.Z, _ => 1
  | _, GCl.Z => 1
  | a, b => if a = b then 0 else 2

/-- The full slot `i`: the two atoms `2i`, `2i+1`. -/
def gFullSlot (i : Fin 4) : Finset GAtom := Finset.univ.filter (fun a : GAtom => a.val / 2 = i.val)

/-- The half `h` of the slot `i`: the single atom `2i + h`. -/
def gHalf (i : Fin 4) (h : Fin 2) : Finset GAtom := {(⟨2 * i.val + h.val, by omega⟩ : GAtom)}

/-- A **dyadic block** of a cluster: a full slot or a half of a slot.  The two levels are laminar:
two dyadic blocks are nested or disjoint. -/
def IsGDyadic (s : Finset GAtom) : Prop :=
  (∃ i, s = gFullSlot i) ∨ ∃ i h, s = gHalf i h

instance (s : Finset GAtom) : Decidable (IsGDyadic s) := by unfold IsGDyadic; infer_instance

/-- A **member**: the block it uses in each cluster, `∅` at the clusters it does not meet. -/
def GMem := GCl → Finset GAtom

instance : DecidableEq GMem := by unfold GMem; infer_instance

/-- The clusters a member meets. -/
def gsupport (m : GMem) : Finset GCl := Finset.univ.filter (fun c => (m c).Nonempty)

/-- The rectangle a member occupies in the square of the cluster pair `(c, c')`. -/
def grect (m : GMem) (c c' : GCl) : Finset (GAtom × GAtom) := (m c) ×ˢ (m c')

/-! ## 2. The instance -/

/-- A transversal permutation of the Klein group `ℤ₂ × ℤ₂` (written on `Fin 4` in binary):
`σ` is a permutation and `i ↦ i ⊕ σ i` is again a permutation — a *complete mapping*, which exists
because the Sylow 2-subgroup of `ℤ₂ × ℤ₂` is non-cyclic. -/
def gsig : Fin 4 → Fin 4 := ![0, 2, 3, 1]

/-- `gLam i = i ⊕ gsig i`, the third coordinate of the transversal. -/
def gLam : Fin 4 → Fin 4 := ![0, 3, 1, 2]

/-- The Latin square of the Klein group: `gLat i j = i ⊕ j`. -/
def gLat : Fin 4 → Fin 4 → Fin 4 := ![![0,1,2,3], ![1,0,3,2], ![2,3,0,1], ![3,2,1,0]]

/-- The colour (the `Z`-slot) of a `(S,T,Z)`-member, from the two halves it uses. -/
def gcolST : Fin 2 → Fin 2 → Fin 4 := fun h h' => ![![0,1], ![2,3]] h h'

/-- The colour (the `Z`-slot) of a `(S,U,Z)`-member. -/
def gcolSU : Fin 2 → Fin 2 → Fin 4 := fun h g => ![![3,2], ![0,1]] h g

/-- The colour (the `Z`-slot) of a `(T,U,Z)`-member. -/
def gcolTU : Fin 2 → Fin 2 → Fin 4 := fun h' g => ![![1,3], ![2,0]] h' g

/-- A member from its four blocks. -/
def gmk (s t u z : Finset GAtom) : GMem := fun c =>
  match c with
  | GCl.S => s | GCl.T => t | GCl.U => u | GCl.Z => z

/-- The `12` members on the dense triangle `(S,T,U)`: three full slots, `u = i ⊕ j`, off the
transversal `j = σ i`. -/
def gfamSTU : List GMem :=
  (List.finRange 4).flatMap (fun i =>
    ((List.finRange 4).filter (fun j => j ≠ gsig i)).map (fun j =>
      gmk (gFullSlot i) (gFullSlot j) (gFullSlot (gLat i j)) ∅))

/-- The `16` members on `(S,T,Z)`: the four quarters of each transversal cell of the `(S,T)` grid,
with a full `Z`-slot given by the colouring. -/
def gfamSTZ : List GMem :=
  (List.finRange 4).flatMap (fun i => (List.finRange 2).flatMap (fun h =>
    (List.finRange 2).map (fun h' =>
      gmk (gHalf i h) (gHalf (gsig i) h') ∅ (gFullSlot (gcolST h h')))))

/-- The `16` members on `(S,U,Z)`. -/
def gfamSUZ : List GMem :=
  (List.finRange 4).flatMap (fun i => (List.finRange 2).flatMap (fun h =>
    (List.finRange 2).map (fun g =>
      gmk (gHalf i h) ∅ (gHalf (gLam i) g) (gFullSlot (gcolSU h g)))))

/-- The `16` members on `(T,U,Z)`. -/
def gfamTUZ : List GMem :=
  (List.finRange 4).flatMap (fun i => (List.finRange 2).flatMap (fun h' =>
    (List.finRange 2).map (fun g =>
      gmk ∅ (gHalf (gsig i) h') (gHalf (gLam i) g) (gFullSlot (gcolTU h' g)))))

/-- **The coupled dyadic family**: 60 members, sharing one laminar (two-level) tree per cluster. -/
def gateFamily : List GMem := gfamSTU ++ gfamSTZ ++ gfamSUZ ++ gfamTUZ

/-- How many members of the family cover the cell `x` of the square of the cluster pair `(c, c')`. -/
def gcoverCount (c c' : GCl) (x : GAtom × GAtom) : ℕ :=
  (gateFamily.filter (fun m => x ∈ grect m c c')).length

/-! ## 3. The exact tiling -/

section Tiling

set_option maxHeartbeats 4000000

private theorem gate_tile_ST : ∀ x : GAtom × GAtom, gcoverCount GCl.S GCl.T x = 1 := by decide +kernel

private theorem gate_tile_SU : ∀ x : GAtom × GAtom, gcoverCount GCl.S GCl.U x = 1 := by decide +kernel

private theorem gate_tile_TU : ∀ x : GAtom × GAtom, gcoverCount GCl.T GCl.U x = 1 := by decide +kernel

private theorem gate_tile_SZ : ∀ x : GAtom × GAtom, gcoverCount GCl.S GCl.Z x = 1 := by decide +kernel

private theorem gate_tile_TZ : ∀ x : GAtom × GAtom, gcoverCount GCl.T GCl.Z x = 1 := by decide +kernel

private theorem gate_tile_UZ : ∀ x : GAtom × GAtom, gcoverCount GCl.U GCl.Z x = 1 := by decide +kernel

end Tiling

/-- Swapping the two clusters of a pair swaps the cells. -/
private theorem gcoverCount_symm (c c' : GCl) (a b : GAtom) :
    gcoverCount c c' (a, b) = gcoverCount c' c (b, a) := by
  unfold gcoverCount
  congr 1
  refine List.filter_congr fun m _ => ?_
  simp only [grect, Finset.mem_product, decide_eq_decide]
  exact and_comm

/-- **The gate instance tiles every cluster-pair square exactly**: every cell of every one of the
six squares is covered by exactly one member rectangle. -/
theorem gate_exact_tiling : ∀ c c' : GCl, c ≠ c' → ∀ x : GAtom × GAtom, gcoverCount c c' x = 1 := by
  intro c c' hne x
  obtain ⟨a, b⟩ := x
  cases c
  · cases c'
    · exact absurd rfl hne
    · exact gate_tile_ST (a, b)
    · exact gate_tile_SU (a, b)
    · exact gate_tile_SZ (a, b)
  · cases c'
    · exact (gcoverCount_symm _ _ a b).trans (gate_tile_ST (b, a))
    · exact absurd rfl hne
    · exact gate_tile_TU (a, b)
    · exact gate_tile_TZ (a, b)
  · cases c'
    · exact (gcoverCount_symm _ _ a b).trans (gate_tile_SU (b, a))
    · exact (gcoverCount_symm _ _ a b).trans (gate_tile_TU (b, a))
    · exact absurd rfl hne
    · exact gate_tile_UZ (a, b)
  · cases c'
    · exact (gcoverCount_symm _ _ a b).trans (gate_tile_SZ (b, a))
    · exact (gcoverCount_symm _ _ a b).trans (gate_tile_TZ (b, a))
    · exact (gcoverCount_symm _ _ a b).trans (gate_tile_UZ (b, a))
    · exact absurd rfl hne

/-- The members of the family are pairwise distinct. -/
theorem gate_nodup : gateFamily.Nodup := by decide +kernel

/-- **Disjointness at every pair**: two distinct members of the family have disjoint rectangles in
every cluster-pair square.  This is the disjointness clause of
`Nibble.AX1.BlockCoverResidualCoupled` (`tripleRect` disjointness), in the model. -/
theorem gate_rect_disjoint {c c' : GCl} (hne : c ≠ c') {m m' : GMem}
    (hm : m ∈ gateFamily) (hm' : m' ∈ gateFamily) (hmm : m ≠ m') :
    Disjoint (grect m c c') (grect m' c c') := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp (gate_exact_tiling c c' hne x)
  have h1 : m ∈ gateFamily.filter (fun n => x ∈ grect n c c') :=
    List.mem_filter.mpr ⟨hm, by simpa using hx⟩
  have h2 : m' ∈ gateFamily.filter (fun n => x ∈ grect n c c') :=
    List.mem_filter.mpr ⟨hm', by simpa using hx'⟩
  rw [hz] at h1 h2
  simp only [List.mem_singleton] at h1 h2
  exact hmm (h1.trans h2.symm)

/-- **Covering at every pair**: every cell of every cluster-pair square is met by some member. -/
theorem gate_rect_cover {c c' : GCl} (hne : c ≠ c') (x : GAtom × GAtom) :
    ∃ m ∈ gateFamily, x ∈ grect m c c' := by
  obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp (gate_exact_tiling c c' hne x)
  have hmem : z ∈ gateFamily.filter (fun n => x ∈ grect n c c') := by
    rw [hz]; exact List.mem_singleton_self z
  exact ⟨z, (List.mem_filter.mp hmem).1, by simpa using (List.mem_filter.mp hmem).2⟩

/-! ## 4. The family is a legitimate coupled dyadic family -/

section Shape

set_option maxHeartbeats 1000000

/-- Every block of every member is a dyadic block (a full slot or a half), so the two levels used
in each cluster are laminar. -/
theorem gate_blocks_dyadic : ∀ m ∈ gateFamily, ∀ c : GCl, m c = ∅ ∨ IsGDyadic (m c) := by decide +kernel

/-- Every member meets exactly three clusters. -/
theorem gate_support_card : ∀ m ∈ gateFamily, #(gsupport m) = 3 := by decide +kernel

/-- **The block sizes are pinned by the opposite pair.**  For a member on the cluster triple
`{c, c', c''}`, the block in `c` has exactly `2·d(c',c'')` atoms — i.e. `τ·d(c',c'')` with the block
scale `τ = 1 slot = 2 atoms`, which is the size clause of `Nibble.AX1.IsGridSubTriple`.  In
particular the same `c`-block serves the two rectangles of the member at the pairs `(c,c')` and
`(c,c'')`: **coherence**. -/
theorem gate_sizes_pinned : ∀ m ∈ gateFamily, ∀ c c' c'' : GCl,
    gsupport m = {c, c', c''} → c ≠ c' → c ≠ c'' → c' ≠ c'' →
    #(m c) = gdens2 c' c'' := by decide +kernel

/-- Every member sits on a triangle of the density graph: all three of its pairs are dense. -/
theorem gate_members_on_triangles : ∀ m ∈ gateFamily, ∀ c ∈ gsupport m, ∀ c' ∈ gsupport m,
    c ≠ c' → 0 < gdens2 c c' := by decide +kernel

end Shape

/-! ## 5. The value: the family attains the capacity bound exactly -/

/-- The six cluster pairs. -/
def gpairs : List (GCl × GCl) :=
  [(GCl.S, GCl.T), (GCl.S, GCl.U), (GCl.T, GCl.U), (GCl.S, GCl.Z), (GCl.T, GCl.Z), (GCl.U, GCl.Z)]

/-- Six times the covering value of one member: `∑` over its rectangles of
`(pair density)·(area)`, in the integer normalisation `gdens2 = 2·density` (so this is
`6·∑ d·area/3`). -/
def gmemValue6 (m : GMem) : ℕ :=
  (gpairs.map (fun p => gdens2 p.1 p.2 * (#(m p.1) * #(m p.2)))).sum

/-- Six times the covering value of the family. -/
def gfamValue6 : ℕ := (gateFamily.map gmemValue6).sum

/-- Six times the capacity bound `∑_pairs d(S,T)·|S||T| / 3` of
`Nibble.AX1.nu3star_regularityReduced_le_dense_cluster_capacity`, for this instance: each square
has `8 × 8 = 64` cells. -/
def gcapacity6 : ℕ := (gpairs.map (fun p => gdens2 p.1 p.2 * 64)).sum

section Value

set_option maxHeartbeats 1000000

/-- **The family attains the capacity bound exactly.**  Because every pair square is exactly tiled
and the objective is a density-weighted area functional
(`Nibble.AX1.member_cover_eq_weighted_area`), the covering value of the family equals
`∑_pairs d(S,T)·|S||T| / 3` — the upper bound for `ν₃*` supplied by
`Nibble.AX1.nu3star_regularityReduced_le_dense_cluster_capacity`.  There is **no loss** anywhere. -/
theorem gate_value_eq_capacity : gfamValue6 = gcapacity6 := by decide +kernel

end Value

/-! ## 6. The instance is out of reach of the portion (product region) route -/

/-- The number of member rectangles at the pair `(S,T)` whose two sides are full slots, times the
area `4` of such a rectangle: `48` of the `64` cells, i.e. a `3/4` fraction of the square. -/
def gmassBigST : ℕ :=
  ((gateFamily.filter (fun m => #(m GCl.S) = 2 ∧ #(m GCl.T) = 2)).map
    (fun m => #(m GCl.S) * #(m GCl.T))).sum

/-- The area of the `(S,T)` square carried by rectangles whose two sides are halves: `16` of the
`64` cells, a `1/4` fraction. -/
def gmassSmallST : ℕ :=
  ((gateFamily.filter (fun m => #(m GCl.S) = 1 ∧ #(m GCl.T) = 1)).map
    (fun m => #(m GCl.S) * #(m GCl.T))).sum

section Mass

set_option maxHeartbeats 1000000

/-- **The demand at the pair `(S,T)` is diagonal**: `48/64 = 3/4` of the square is carried by
`(full, full)` rectangles and `16/64 = 1/4` by `(half, half)` rectangles — and nothing by the mixed
shapes.  This is exactly the shape of demand the portion route cannot serve. -/
theorem gate_mass_ST : gmassBigST = 48 ∧ gmassSmallST = 16 := by decide +kernel

end Mass

/-- **The product (portion) allocation cannot serve the demand of the gate instance.**  A portion
scheme gives the level-`ℓ` blocks of a cluster a region of relative size `f ℓ` (`g ℓ` for the other
cluster of the pair) and can only place a shape-`(ℓ,ℓ')` rectangle inside `R(ℓ) × R(ℓ')`, so it
serves the demand `(3/4, 1/4)` only if `3/4 ≤ f 0 * g 0` and `1/4 ≤ f 1 * g 1`.  That is
impossible. -/
theorem gate_product_layout_fails (f g : Fin 2 → ℝ) (hf0 : 0 ≤ f 0) (hf1 : 0 ≤ f 1)
    (hg0 : 0 ≤ g 0) (hg1 : 0 ≤ g 1) (hf : f 0 + f 1 ≤ 1) (hg : g 0 + g 1 ≤ 1)
    (hbig : 3 / 4 ≤ f 0 * g 0) (hsmall : 1 / 4 ≤ f 1 * g 1) : False := by
  have hf0' : f 0 ≤ 1 := by linarith only [hf1, hf]
  have hg0' : g 0 ≤ 1 := by linarith only [hg1, hg]
  have h1 : 3 / 4 ≤ f 0 := by nlinarith only [hf0, hbig, hg0']
  have h2 : 3 / 4 ≤ g 0 := by nlinarith only [hbig, hf0', h1]
  nlinarith only [hg1, hf, hg, hsmall, h1, h2]

/-- **The quantitative version**: whatever portions it reserves, a product allocation serves at
most `13/16` of the `(3/4, 1/4)` demand of the gate instance — a constant-factor loss — while the
coupled quadtree family `Nibble.AX1.gateFamily` serves it exactly (`gate_exact_tiling`). -/
theorem gate_product_layout_serves_le (f g : Fin 2 → ℝ) (hf0 : 0 ≤ f 0) (hf1 : 0 ≤ f 1)
    (hg0 : 0 ≤ g 0) (hg1 : 0 ≤ g 1) (hf : f 0 + f 1 ≤ 1) (hg : g 0 + g 1 ≤ 1) :
    min (3 / 4) (f 0 * g 0) + min (1 / 4) (f 1 * g 1) ≤ 13 / 16 := by
  have hf0' : f 0 ≤ 1 := by linarith only [hf1, hf]
  have hg0' : g 0 ≤ 1 := by linarith only [hg1, hg]
  have hsmall : f 1 * g 1 ≤ (1 - f 0) * (1 - g 0) := by nlinarith only [hg1, hf, hg, hf0']
  have hm1 : min (3 / 4 : ℝ) (f 0 * g 0) ≤ 3 / 4 := min_le_left _ _
  have hm1' : min (3 / 4 : ℝ) (f 0 * g 0) ≤ f 0 * g 0 := min_le_right _ _
  have hm2 : min (1 / 4 : ℝ) (f 1 * g 1) ≤ 1 / 4 := min_le_left _ _
  have hm2' : min (1 / 4 : ℝ) (f 1 * g 1) ≤ (1 - f 0) * (1 - g 0) :=
    le_trans (min_le_right _ _) hsmall
  rcases le_or_gt (f 0) (3 / 4) with ha | ha
  · rcases le_or_gt (g 0) (3 / 4) with hb | hb
    · -- both portions are small: the big class is under-served by `3/16`
      have : f 0 * g 0 ≤ 9 / 16 := by nlinarith only [hg0, ha, hb]
      linarith only [hm1', hm2, this]
    · -- the second portion is large: the small class gets almost nothing
      have h1 : (1 - f 0) * (1 - g 0) ≤ (1 - f 0) / 4 := by nlinarith only [ha, hb]
      have h2 : f 0 * g 0 ≤ f 0 := by nlinarith only [hf0, hg0']
      linarith only [hm1', hm2', ha, h1, h2]
  · rcases le_or_gt (g 0) (3 / 4) with hb | hb
    · have h1 : (1 - f 0) * (1 - g 0) ≤ (1 - g 0) / 4 := by nlinarith only [hg0', ha]
      have h2 : f 0 * g 0 ≤ g 0 := by nlinarith only [hg0, hf0']
      linarith
    · -- both portions are large: the small class gets at most `1/16`
      have h1 : (1 - f 0) * (1 - g 0) ≤ 1 / 16 := by nlinarith
      linarith

/-! ### Axiom check -/

section AxCheck

#print axioms Nibble.AX1.member_cover_eq_weighted_area
#print axioms Nibble.AX1.gate_exact_tiling
#print axioms Nibble.AX1.gate_rect_disjoint
#print axioms Nibble.AX1.gate_rect_cover
#print axioms Nibble.AX1.gate_sizes_pinned
#print axioms Nibble.AX1.gate_value_eq_capacity
#print axioms Nibble.AX1.gate_product_layout_fails
#print axioms Nibble.AX1.gate_product_layout_serves_le

end AxCheck

end Nibble.AX1
