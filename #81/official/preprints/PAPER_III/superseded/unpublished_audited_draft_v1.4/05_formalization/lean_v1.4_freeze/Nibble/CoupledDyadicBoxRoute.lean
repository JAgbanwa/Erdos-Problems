/-
# Nibble — the dyadic **box** route to `BlockCoverResidualCoupled`: what it buys, and where it stops

`Nibble.CoupledDyadicGate` settled the *3-way coherence gate* positively: the laminar (dyadic)
coupling of the three cluster trees of a member does not force a constant-factor loss, and
`Nibble.CoupledDyadicScaled` scales that instance to every granularity.  The next step of the
route was to run the weighted nibble `Nibble.fracNibble_withSlack` on the hypergraph whose
*ground set* is the set of dyadic **boxes** of the cluster-pair grids and whose members are the
coherent triples of boxes, and then to read a family of block sub-triples with pairwise disjoint
`Nibble.AX1.tripleRect`s off the resulting matching.

This file records what that step does and does not give.  Its three groups of results are:

## 1. Dyadic blocks are laminar (`Nibble.AX1.dyBlk_laminar`)

Two dyadic blocks are nested or disjoint.  This is the good news of the dyadic route on a *single*
cluster axis: a one-dimensional dyadic demand is packable exactly up to Kraft's inequality
(`Nibble.AX1.kraft_pack`), with no `√`-loss.

## 2. The translation step of the box route fails (`Nibble.AX1.box_matching_not_rectDisjoint`)

Laminarity is exactly what breaks the *translation back*.  A matching of the box hypergraph is a
family of member-triples **no two of which share a box**; the covering clause of
`Nibble.AX1.BlockCoverResidualCoupled` needs the strictly stronger statement that no two of their
`tripleRect`s *meet*.  Two boxes over the same cluster pair that are not equal can still be nested,
because their *shapes* differ: the box a member puts in the pair `(S,T)` has side lengths
`τ·d(T,Y) × τ·d(S,Y)`, pinned by the two *opposite* densities, so two members with different third
clusters `Y`, `Y'` contribute boxes of different shapes at the same place.
`Nibble.AX1.box_matching_not_rectDisjoint` exhibits two member-triples of dyadic blocks that share
no block at all — a legitimate matching of the box hypergraph — whose rectangles intersect.  The
disjointness lemma the near-uniform proof uses,
`Nibble.AX1.tripleRect_disjoint_of_cells_inter`, needs the matched blocks to sit inside *pairwise
disjoint cells*, which a box matching does not provide.

## 3. The cell (edge-disjoint-triangle) model loses a factor `θ`
(`Nibble.AX1.cellTriangle_LP_gap`)

The obvious repair — keep the ground set of the near-uniform proof, namely the *cells* (slot pairs)
of the cluster-pair grids, so that a matching is an edge-disjoint triangle family of the slot
blow-up and disjointness is automatic — is exact *per triple*
(`Nibble.AX1.cellTriangle_capacity_eq`, `Nibble.AX1.cellTriangle_value_eq_min`: one cell triangle of
type `(x,y,z)` carries exactly `min(1/(xy), 1/(xz), 1/(yz))` members, of total value
`τ²·min(x,y,z)`, which is precisely the single-triple optimum of the density LP), but it charges a
whole cell of the pair `(S,T)` to a member group that may only fill the fraction
`min(x,y,z)/d(S,T)` of it.  `Nibble.AX1.cellTriangle_LP_gap` turns this into a quantitative
refutation: on the instance with `d(S,T) = 1` and `r = ⌈1/θ⌉` further clusters `Z i` with
`d(S,Z i) = d(T,Z i) = θ`, the density LP has value `P` while every cell-model family has value at
most `θ·P`.  So the assembly parallel to
`Nibble.AX1.blockCoverResidualCoupledNearUniform_holds` — one member group per cell triangle —
cannot reach the accuracy `ε` of `Nibble.AX1.BlockCoverResidualCoupled`; it is short by a factor
`θ ≤ ε`, and the geometry of that instance *is* realisable (all boxes there have the same shape),
so the deficit is an artefact of the model, not of the objective.

## 4. Rounding the cluster densities is not available
(`Nibble.AX1.rounded_density_violates_blockShape`)

Independently of all this, the first step of the box route — rounding the kept cluster densities
down to powers of two, so that the prescribed block lengths become dyadic — is not admissible:
`Nibble.AX1.IsGridSubTriple` pins the block lengths to the **true** cluster densities within `1`,
and a round-down costs up to a factor `2` of the length, i.e. `τ·d/2`, which the residual's own
shape clause forbids at every block scale `τ ≥ 9`.  Dyadic block *lengths* are therefore out of
reach; what the route actually needs is not laminarity but *coarse cells*, see 5.

## 5. The 3-way coherence of a cell allocation costs nothing
(`Nibble.AX1.coherent_cellTriangle_count`)

The repair both failures point to is to allocate a single **shape** — equivalently a single third
cluster — to each cell of each cluster-pair grid, the cells being coarse (of a length `C ≫ τ`, so
that tiling a cell by blocks of a prescribed length wastes only an `O(τ/C)` fraction and no dyadic
rounding is needed).  Over such an allocation all boxes of a cell have one shape, so a matching of
the box hypergraph *is* a family with pairwise disjoint rectangles, and — unlike a cell triangle —
one cell serves all the members of its shape, whatever their third cell, so the `θ` of 3 is not
lost either.  The allocation must be coherent along cluster triples, and
`Nibble.AX1.coherent_cellTriangle_count` shows that this costs nothing *for every demand profile at
once*: allocating the cell `(i,j)` by the value of `i + j` in a cyclic group of odd order makes the
number of coherent cell triangles exactly the product of the three allocation sizes.  This is the
general-profile form of what `Nibble.CoupledDyadicGate` settles for one profile.

What is therefore still missing for `Nibble.AX1.BlockCoverResidualCoupled` is the **assembly** over
such an allocation: the cluster LP with the *density* capacities `d(S,T)·|S||T|` that bounds `ν₃*` of the
regularity-reduced graph from above, its rounding to allocation sizes, the verification of the
three hypotheses of `Nibble.fracNibble_withSlack` for the resulting box hypergraph, and the
translation of the matching back into a family of grid sub-triples.  Note that the allocation must
not be a product of per-cluster portions — `Nibble.AX1.portion_budget_overrun`
(`Nibble.BlockCoverPortionBudget`) refutes those by a factor equal to the number of bands — which
is exactly why it is attached to cells and not to slots.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapRectPack

open Finset

namespace Nibble.AX1

/-! ## 1. Dyadic blocks are laminar -/

/-- The dyadic block of length `2 ^ l` at index `t`, as a block of consecutive naturals. -/
def dyBlk (l t : ℕ) : Finset ℕ := Finset.Ico (t * 2 ^ l) ((t + 1) * 2 ^ l)

theorem dyBlk_card (l t : ℕ) : #(dyBlk l t) = 2 ^ l := by
  simp [dyBlk, Nat.card_Ico, Nat.succ_mul]

/-- A dyadic block sits inside the coarser block that contains its index. -/
theorem dyBlk_sub_of_add {l k t t' : ℕ} (h1 : t' * 2 ^ k ≤ t) (h2 : t < (t' + 1) * 2 ^ k) :
    dyBlk l t ⊆ dyBlk (l + k) t' := by
  refine Finset.Ico_subset_Ico ?_ ?_
  · calc t' * 2 ^ (l + k) = (t' * 2 ^ k) * 2 ^ l := by ring
      _ ≤ t * 2 ^ l := Nat.mul_le_mul_right _ h1
  · calc (t + 1) * 2 ^ l ≤ ((t' + 1) * 2 ^ k) * 2 ^ l := Nat.mul_le_mul_right _ h2
      _ = (t' + 1) * 2 ^ (l + k) := by ring

/-- A dyadic block is disjoint from every coarser block that does not contain its index. -/
theorem dyBlk_disj_of_add {l k t t' : ℕ} (h : t < t' * 2 ^ k ∨ (t' + 1) * 2 ^ k ≤ t) :
    Disjoint (dyBlk l t) (dyBlk (l + k) t') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [dyBlk, Finset.mem_Ico] at hx hx'
  rcases h with h | h
  · have hle : (t + 1) * 2 ^ l ≤ t' * 2 ^ (l + k) := by
      calc (t + 1) * 2 ^ l ≤ (t' * 2 ^ k) * 2 ^ l := Nat.mul_le_mul_right _ h
        _ = t' * 2 ^ (l + k) := by ring
    omega
  · have hle : (t' + 1) * 2 ^ (l + k) ≤ t * 2 ^ l := by
      calc (t' + 1) * 2 ^ (l + k) = ((t' + 1) * 2 ^ k) * 2 ^ l := by ring
        _ ≤ t * 2 ^ l := Nat.mul_le_mul_right _ h
    omega

/-- **Dyadic blocks are laminar**: two of them are nested or disjoint.  On one cluster axis this is
what makes the dyadic route lossless (Kraft); across a cluster *pair* it is what makes a matching of
the box hypergraph too weak, see `Nibble.AX1.box_matching_not_rectDisjoint`. -/
theorem dyBlk_laminar (l t l' t' : ℕ) :
    dyBlk l t ⊆ dyBlk l' t' ∨ dyBlk l' t' ⊆ dyBlk l t ∨ Disjoint (dyBlk l t) (dyBlk l' t') := by
  rcases le_total l l' with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rcases lt_trichotomy t (t' * 2 ^ k) with h1 | h1 | h1
    · exact Or.inr (Or.inr (dyBlk_disj_of_add (Or.inl h1)))
    · exact Or.inl (dyBlk_sub_of_add h1.ge (by nlinarith [Nat.two_pow_pos k]))
    · by_cases h2 : t < (t' + 1) * 2 ^ k
      · exact Or.inl (dyBlk_sub_of_add h1.le h2)
      · exact Or.inr (Or.inr (dyBlk_disj_of_add (Or.inr (by omega))))
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rcases lt_trichotomy t' (t * 2 ^ k) with h1 | h1 | h1
    · exact Or.inr (Or.inr (dyBlk_disj_of_add (Or.inl h1)).symm)
    · exact Or.inr (Or.inl (dyBlk_sub_of_add h1.ge (by nlinarith [Nat.two_pow_pos k])))
    · by_cases h2 : t' < (t + 1) * 2 ^ k
      · exact Or.inr (Or.inl (dyBlk_sub_of_add h1.le h2))
      · exact Or.inr (Or.inr (dyBlk_disj_of_add (Or.inr (by omega))).symm)

/-! ## 2. A matching of the box hypergraph does not give disjoint rectangles

The instance: four clusters `S = {0,1}`, `T = {4,5}`, `Y = {8,9}`, `Z = {12,13}`, each cut into one
slot of two atoms, with `d(T,Y) = d(S,Z) = 1` and `d(S,Y) = d(T,Z) = 1/2`, at block scale `τ = 1` slot = 2 atoms.
The member on `(S,T,Y)` then has an `S`-block of length `τ·d(T,Y) = 2` atoms and a `T`-block of
length `τ·d(S,Y) = 1` atom, while the member on `(S,T,Z)` has an `S`-block of length
`τ·d(T,Z) = 1` atom and a `T`-block of length `τ·d(S,Z) = 2` atoms: the two members put boxes of
the two *different* shapes `(1, 1/2)` and `(1/2, 1)` into the square `S × T`.
All six blocks are distinct — the two members share no ground element of the box hypergraph — yet
the two rectangles both contain the vertex pair `(0, 4)`. -/

/-- The vertex set of the instance: four clusters of two atoms each. -/
abbrev BoxV := Fin 16

/-- The `S`-block of the first member: the full slot, of length `τ·d(T,Y) = 2` atoms. -/
def boxA : Finset BoxV := {0, 1}
/-- The `T`-block of the first member: half a slot, of length `τ·d(S,Y) = 1` atom. -/
def boxB : Finset BoxV := {4}
/-- The `Y`-block of the first member. -/
def boxC : Finset BoxV := {8}
/-- The `S`-block of the second member: half a slot, of length `τ·d(T,Z) = 1` atom. -/
def boxA' : Finset BoxV := {0}
/-- The `T`-block of the second member: the full slot, of length `τ·d(S,Z) = 2` atoms. -/
def boxB' : Finset BoxV := {4, 5}
/-- The `Z`-block of the second member. -/
def boxC' : Finset BoxV := {12}

/-- **A matching of the box hypergraph need not give disjoint rectangles.**  The two member-triples
`(boxA, boxB, boxC)` and `(boxA', boxB', boxC')` consist of six pairwise distinct dyadic blocks — so
they share no vertex of the hypergraph whose ground set is the set of boxes, and both may be picked
by `Nibble.fracNibble_withSlack` — but the second `S`-block is *nested* inside the first and the
first `T`-block inside the second, and the two `Nibble.AX1.tripleRect`s meet.

This is the precise point at which step 4 of the box route fails: the hypothesis of
`Nibble.AX1.tripleRect_disjoint_of_cells_inter` (blocks inside pairwise disjoint cells) is not
available, and no weaker consequence of "the matching shares no box" replaces it. -/
theorem box_matching_not_rectDisjoint :
    (({boxA, boxB, boxC} : Finset (Finset BoxV)) ∩ ({boxA', boxB', boxC'} : Finset (Finset BoxV)))
        = ∅ ∧
      boxA' ⊂ boxA ∧ boxB ⊂ boxB' ∧
      ¬ Disjoint (tripleRect boxA boxB boxC) (tripleRect boxA' boxB' boxC') := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  rw [Finset.not_disjoint_iff]
  exact ⟨((0 : BoxV), (4 : BoxV)), by decide, by decide⟩

/-! ## 3. The cell (edge-disjoint-triangle) model: exact per triple, lossy in the aggregate

A *cell* of the pair `(S,T)` is a pair of slots, one of `S` and one of `T`; a *cell triangle* of the
cluster triple `(S,T,Y)` is a triple of slots `(i,j,k)`, which occupies one cell of each of the
three pairs.  Writing `x = d(T,Y)`, `y = d(S,Y)`, `z = d(S,T)` for the three densities and `τ` for
the slot length, the member blocks have relative lengths `x, y, z` inside their slots, so inside one
cell triangle a member is a triple of positions `(u, v, w)` with `u < 1/x`, `v < 1/y`, `w < 1/z`,
and two members of the same cell triangle must differ in **each** of the three coordinate pairs. -/

/-- The positions of the members inside one cell triangle: `A·B` triples with all three pairwise
projections injective. -/
def latinTriples (A B C : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range A ×ˢ Finset.range B).image (fun p => (p.1, p.2, (p.1 + p.2) % C))

theorem latinTriples_card (A B C : ℕ) : #(latinTriples A B C) = A * B := by
  rw [latinTriples, Finset.card_image_of_injective _ (by
    intro p q h
    simp only [Prod.ext_iff] at h
    exact Prod.ext h.1 h.2.1)]
  simp

theorem latinTriples_subset {A B C : ℕ} (hC : 0 < C) :
    latinTriples A B C ⊆ Finset.range A ×ˢ Finset.range B ×ˢ Finset.range C := by
  intro m hm
  simp only [latinTriples, Finset.mem_image, Finset.mem_product, Finset.mem_range] at hm ⊢
  obtain ⟨p, ⟨hp1, hp2⟩, rfl⟩ := hm
  exact ⟨hp1, hp2, Nat.mod_lt _ hC⟩

/-- Distinct members of `latinTriples` differ in their first two coordinates. -/
theorem latinTriples_inj12 {A B C : ℕ} :
    ∀ m ∈ latinTriples A B C, ∀ m' ∈ latinTriples A B C,
      m.1 = m'.1 → m.2.1 = m'.2.1 → m = m' := by
  intro m hm m' hm' h1 h2
  simp only [latinTriples, Finset.mem_image] at hm hm'
  obtain ⟨p, -, rfl⟩ := hm
  obtain ⟨q, -, rfl⟩ := hm'
  simp only at h1 h2
  simp [h1, h2]

/-- Distinct members of `latinTriples` differ in their first and third coordinates. -/
theorem latinTriples_inj13 {A B C : ℕ} (hB : B ≤ C) :
    ∀ m ∈ latinTriples A B C, ∀ m' ∈ latinTriples A B C,
      m.1 = m'.1 → m.2.2 = m'.2.2 → m = m' := by
  intro m hm m' hm' h1 h3
  simp only [latinTriples, Finset.mem_image, Finset.mem_product, Finset.mem_range] at hm hm'
  obtain ⟨p, ⟨-, hp2⟩, rfl⟩ := hm
  obtain ⟨q, ⟨-, hq2⟩, rfl⟩ := hm'
  simp only at h1 h3
  rw [h1] at h3 ⊢
  have hmod : Nat.ModEq C (q.1 + p.2) (q.1 + q.2) := h3
  have h2 : p.2 = q.2 :=
    Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' q.1 hmod)
      (lt_of_lt_of_le hp2 hB) (lt_of_lt_of_le hq2 hB)
  simp [h2]

/-- Distinct members of `latinTriples` differ in their last two coordinates. -/
theorem latinTriples_inj23 {A B C : ℕ} (hA : A ≤ C) :
    ∀ m ∈ latinTriples A B C, ∀ m' ∈ latinTriples A B C,
      m.2.1 = m'.2.1 → m.2.2 = m'.2.2 → m = m' := by
  intro m hm m' hm' h2 h3
  simp only [latinTriples, Finset.mem_image, Finset.mem_product, Finset.mem_range] at hm hm'
  obtain ⟨p, ⟨hp1, -⟩, rfl⟩ := hm
  obtain ⟨q, ⟨hq1, -⟩, rfl⟩ := hm'
  simp only at h2 h3
  rw [h2] at h3 ⊢
  have hmod : Nat.ModEq C (p.1 + q.2) (q.1 + q.2) := h3
  have h1 : p.1 = q.1 :=
    Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' q.2 hmod)
      (lt_of_lt_of_le hp1 hA) (lt_of_lt_of_le hq1 hA)
  simp [h1]

/-- **The capacity of one cell triangle is `min(A·B, A·C, B·C)`.**  Upper bound: any set of member
positions whose three pairwise projections are injective has at most that many elements. -/
theorem cellTriangle_capacity_le {A B C : ℕ} (M : Finset (ℕ × ℕ × ℕ))
    (hM : M ⊆ Finset.range A ×ˢ Finset.range B ×ˢ Finset.range C)
    (h12 : ∀ m ∈ M, ∀ m' ∈ M, m.1 = m'.1 → m.2.1 = m'.2.1 → m = m')
    (h13 : ∀ m ∈ M, ∀ m' ∈ M, m.1 = m'.1 → m.2.2 = m'.2.2 → m = m')
    (h23 : ∀ m ∈ M, ∀ m' ∈ M, m.2.1 = m'.2.1 → m.2.2 = m'.2.2 → m = m') :
    #M ≤ min (A * B) (min (A * C) (B * C)) := by
  have hmem : ∀ m ∈ M, m.1 < A ∧ m.2.1 < B ∧ m.2.2 < C := by
    intro m hm
    have := hM hm
    simpa [Finset.mem_product, Finset.mem_range, and_assoc] using this
  have hAB : #M ≤ A * B := by
    have h := Finset.card_le_card_of_injOn (t := Finset.range A ×ˢ Finset.range B)
      (fun m : ℕ × ℕ × ℕ => (m.1, m.2.1))
      (fun m hm => by
        have h := hmem m hm
        simp [h.1, h.2.1])
      (fun m hm m' hm' h => by
        simp only [Prod.mk.injEq] at h
        exact h12 m hm m' hm' h.1 h.2)
    simpa using h
  have hAC : #M ≤ A * C := by
    have h := Finset.card_le_card_of_injOn (t := Finset.range A ×ˢ Finset.range C)
      (fun m : ℕ × ℕ × ℕ => (m.1, m.2.2))
      (fun m hm => by
        have h := hmem m hm
        simp [h.1, h.2.2])
      (fun m hm m' hm' h => by
        simp only [Prod.mk.injEq] at h
        exact h13 m hm m' hm' h.1 h.2)
    simpa using h
  have hBC : #M ≤ B * C := by
    have h := Finset.card_le_card_of_injOn (t := Finset.range B ×ˢ Finset.range C)
      (fun m : ℕ × ℕ × ℕ => (m.2.1, m.2.2))
      (fun m hm => by
        have h := hmem m hm
        simp [h.2.1, h.2.2])
      (fun m hm m' hm' h => by
        simp only [Prod.mk.injEq] at h
        exact h23 m hm m' hm' h.1 h.2)
    simpa using h
  exact le_min hAB (le_min hAC hBC)

/-- **The capacity of one cell triangle is attained.**  When `C` is the largest of the three
reciprocal densities, `latinTriples A B C` is a set of `min(A·B, A·C, B·C)` member positions with
all three pairwise projections injective. -/
theorem cellTriangle_capacity_eq {A B C : ℕ} (hC : 0 < C) (hA : A ≤ C) (hB : B ≤ C) :
    latinTriples A B C ⊆ Finset.range A ×ˢ Finset.range B ×ˢ Finset.range C ∧
      (∀ m ∈ latinTriples A B C, ∀ m' ∈ latinTriples A B C,
        m.1 = m'.1 → m.2.1 = m'.2.1 → m = m') ∧
      (∀ m ∈ latinTriples A B C, ∀ m' ∈ latinTriples A B C,
        m.1 = m'.1 → m.2.2 = m'.2.2 → m = m') ∧
      (∀ m ∈ latinTriples A B C, ∀ m' ∈ latinTriples A B C,
        m.2.1 = m'.2.1 → m.2.2 = m'.2.2 → m = m') ∧
      #(latinTriples A B C) = min (A * B) (min (A * C) (B * C)) := by
  refine ⟨latinTriples_subset hC, latinTriples_inj12, latinTriples_inj13 hB,
    latinTriples_inj23 hA, ?_⟩
  rw [latinTriples_card]
  have h1 : A * B ≤ A * C := Nat.mul_le_mul_left _ hB
  have h2 : A * B ≤ B * C := by
    calc A * B = B * A := by ring
      _ ≤ B * C := Nat.mul_le_mul_left _ hA
  omega

private theorem min_mul_pos (a b c : ℝ) (hc : 0 ≤ c) : min a b * c = min (a * c) (b * c) := by
  rcases le_total a b with h | h <;> simp [h, mul_le_mul_of_nonneg_right h hc]

/-- **One cell triangle carries exactly the single-triple optimum of the density LP.**  A cell
triangle of a triple with densities `x, y, z` carries `min(1/(xy), 1/(xz), 1/(yz))` members, each of
value `τ²·xyz`; the total is `τ²·min(x,y,z)`, which is exactly the value the density LP allows a
single cluster triple whose three pair capacities are one cell each. -/
theorem cellTriangle_value_eq_min {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    min (1 / (x * y)) (min (1 / (x * z)) (1 / (y * z))) * (x * y * z) = min z (min y x) := by
  rw [min_mul_pos _ _ _ (by positivity), min_mul_pos _ _ _ (by positivity)]
  congr 1
  · field_simp
  · congr 1 <;> field_simp

/-! ### The aggregate gap of the cell model -/

/-- **The cell model is short of the density LP by a factor `θ`.**

The instance has two clusters `S`, `T` with `d(S,T) = 1` and `r` further clusters `Z 0, …, Z (r-1)`
with `d(S, Z i) = d(T, Z i) = θ`.  Write `P` for the number of cells of a cluster pair (the square
of the number of slots) times the value `τ²` of one full cell.

* *(a)* In the **cell model** — the assembly parallel to
  `Nibble.AX1.blockCoverResidualCoupledNearUniform_holds`, where the matching produced by the nibble
  is an edge-disjoint triangle family of the slot blow-up and hence assigns each cell to at most one
  cluster triple — the triple `(S,T,Z i)` has `min(x,y,z) = θ`, so by
  `Nibble.AX1.cellTriangle_value_eq_min` a cell triangle of it is worth `θ·τ²`; with `g i` cells of
  the pair `(S,T)` given to the triple `(S,T,Z i)` and `∑ i, g i ≤ P` the total value is at most
  `θ·P`.
* *(b)* The **density LP** — the relaxation that bounds `ν₃*` of the regularity-reduced graph from
  above (`Nibble.AX1.nu3star_regularityReduced_le_dense_cluster_capacity`), whose constraint at a
  pair is that the total value routed through it is at most `d(pair)` times the pair's area — has
  the feasible point `y i = P / r`, of value `P`, as soon as `r·θ ≥ 1`.

Hence the cell model attains at most the fraction `θ` of the optimum, whereas the covering clause of
`Nibble.AX1.BlockCoverResidualCoupled` allows only an additive `ε·|V|²`.  The geometry of the
instance is not to blame: there all boxes of the pair `(S,T)` have the same shape `θ × θ`, and the
`P/θ` boxes of the `r = 1/θ` triples tile the square `S × T` exactly.  What the cell model forbids
is precisely what that tiling does — letting many members with *different* third clusters share one
cell. -/
theorem cellTriangle_LP_gap {θ P : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hP : 0 < P) {r : ℕ}
    (hr : 1 ≤ (r : ℝ) * θ) :
    (∀ g : ℕ → ℝ, (∀ i, 0 ≤ g i) → (∑ i ∈ Finset.range r, g i) ≤ P →
        (∑ i ∈ Finset.range r, θ * g i) ≤ θ * P) ∧
      (∃ y : ℕ → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ i, y i ≤ θ * P) ∧
        (∑ i ∈ Finset.range r, y i) ≤ 1 * P ∧ (∑ i ∈ Finset.range r, y i) = P) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    rcases lt_or_ge (0 : ℝ) (r : ℝ) with h | h
    · exact h
    · exfalso; nlinarith
  refine ⟨?_, ⟨fun _ => P / (r : ℝ), fun _ => by positivity, ?_, ?_, ?_⟩⟩
  · intro g _ hsum
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsum hθ0.le
  · intro _
    rw [div_le_iff₀ hr0]
    nlinarith
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ (ne_of_gt hr0)]
    linarith
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_div_cancel₀ _ (ne_of_gt hr0)

/-! ## 4. Rounding the cluster densities is not available

Step 1 of the box route rounds every kept cluster density down to a power of two, so that the
prescribed block lengths `τ·d(opposite pair)` become dyadic.  That step is not compatible with the
residual: `Nibble.AX1.IsGridSubTriple` pins the block lengths to the **true** cluster densities,
`|#A − τ·d(W,X)| ≤ 1`, and rounding a density down costs up to a factor `2`, hence up to `τ·d/2` in
the block length — which exceeds `1` as soon as the block scale `τ` is large, and the residual has
to deliver every scale `τ ≥ T₀`. -/

/-- **A block of the size prescribed by the rounded density is not a block of the size prescribed
by the true density.**  For the true density `3/4`, whose round-down to a power of two is `1/2`, no
block length can satisfy both shape clauses once `τ > 8`; the deficit is `τ/4`. -/
theorem rounded_density_violates_blockShape {τ s : ℝ} (hτ : 9 ≤ τ)
    (hs : |s - τ * (1 / 2)| ≤ 1) : ¬ |s - τ * (3 / 4)| ≤ 1 := by
  rw [abs_le] at hs
  intro h
  rw [abs_le] at h
  linarith [hs.1, hs.2, h.1, h.2]

/-! ## 5. The 3-way coherence of a cell allocation costs nothing

The repair that the two failures above point to is a **shape allocation by cells**: cut every
cluster into `p` cells of a length `C` much larger than the block scale `τ` (so that tiling a cell
by blocks of a prescribed length wastes only an `O(τ/C)` fraction of it, which needs no dyadic
rounding), and give every cell `(i,j)` of every cluster-pair grid a single *shape* — equivalently,
a single third cluster `Y`, since the shape a member of the triple `(S,T,Y)` uses at the pair
`(S,T)` is `τ·d(T,Y) × τ·d(S,Y)`.  All boxes over one cell then have one shape, so they are equal or
disjoint, matchings of the box hypergraph *do* give disjoint rectangles, and — unlike a cell
triangle of `Nibble.AX1.cellTriangle_LP_gap` — one cell is shared by all the members with that
shape, whatever their third cell.

The allocation has to be **coherent**: a member on `(S,T,Y)` using the cells `(i,j)`, `(i,k)`,
`(j,k)` of the three pairs needs all three of them allocated to the matching shape.  The theorem
below shows that this constraint costs nothing, for *every* demand profile at once, if the
allocation is made by the **sum rule** `(i,j) ↦ σ(i + j)` in a cyclic group of odd order: the number
of coherent cell triangles is then exactly the product of the three allocation sizes — the count a
uniformly random allocation would give on average, with no correlation loss.  This is the general
form of the 3-way coherence statement that `Nibble.CoupledDyadicGate` settles for one profile. -/

/-- The map `(x,y,z) ↦ (x+y, x+z, y+z)` on a cyclic group. -/
def sumTriple {M : ℕ} (p : ZMod M × ZMod M × ZMod M) : ZMod M × ZMod M × ZMod M :=
  (p.1 + p.2.1, p.1 + p.2.2, p.2.1 + p.2.2)

/-- In a cyclic group of odd order, `2` is invertible. -/
theorem exists_half_of_odd {M : ℕ} (hM : Odd M) : ∃ c : ZMod M, (2 : ZMod M) * c = 1 := by
  obtain ⟨m, hm⟩ := hM
  refine ⟨((m + 1 : ℕ) : ZMod M), ?_⟩
  have hcast : (2 : ZMod M) * ((m + 1 : ℕ) : ZMod M) = ((2 * (m + 1) : ℕ) : ZMod M) := by
    push_cast; ring
  rw [hcast, show 2 * (m + 1) = M + 1 by omega]
  push_cast
  simp

theorem sumTriple_injective {M : ℕ} (hc : ∃ c : ZMod M, (2 : ZMod M) * c = 1) :
    Function.Injective (sumTriple (M := M)) := by
  obtain ⟨c, hc⟩ := hc
  rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ h
  simp only [sumTriple, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hx : x = x' := by
    have h2x : (2 : ZMod M) * x = 2 * x' := by linear_combination h1 + h2 - h3
    linear_combination c * h2x - (x - x') * hc
  refine Prod.ext hx (Prod.ext ?_ ?_)
  · simpa using (by linear_combination h1 - hx : y = y')
  · simpa using (by linear_combination h2 - hx : z = z')

/-- **The sum rule allocates cells with no coherence loss.**  Let the cells of a cluster be indexed
by `ZMod M` with `M` odd, let the cell `(i,j)` of the pair `(S,T)` be allocated according to the
value of `i + j`, and let `A`, `B`, `C` be the sets of values allocated to the shape a fixed
cluster triple needs at its three pairs.  Then the number of *coherent* cell triangles `(i,j,k)` —
those whose three cells are allocated to that triple's shape at all three pairs — is exactly
`#A · #B · #C`, i.e. exactly the fraction `(#A/M)(#B/M)(#C/M)` of all `M³` cell triangles.

Since the allocation sizes are proportional to the LP demand, and since the number of cells per
cluster grows with the size of the host graph while the number of clusters stays bounded by
`SzemerediRegularity.bound`, the supply of coherent cell triangles exceeds the demand by an
arbitrarily large factor: the 3-way coherence constraint is not what obstructs the general-density
residual. -/
theorem coherent_cellTriangle_count {M : ℕ} [NeZero M] (hM : Odd M)
    (A B C : Finset (ZMod M)) :
    #((Finset.univ : Finset (ZMod M × ZMod M × ZMod M)).filter
        (fun p => p.1 + p.2.1 ∈ A ∧ p.1 + p.2.2 ∈ B ∧ p.2.1 + p.2.2 ∈ C))
      = #A * #B * #C := by
  classical
  have hc := exists_half_of_odd hM
  have hbij : Function.Bijective (sumTriple (M := M)) :=
    Finite.injective_iff_bijective.mp (sumTriple_injective hc)
  have hcard : #((Finset.univ : Finset (ZMod M × ZMod M × ZMod M)).filter
        (fun p => p.1 + p.2.1 ∈ A ∧ p.1 + p.2.2 ∈ B ∧ p.2.1 + p.2.2 ∈ C))
      = #(A ×ˢ B ×ˢ C) := by
    refine Finset.card_bij (fun p _ => sumTriple p) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter] at hp
      simp [sumTriple, Finset.mem_product, hp.2.1, hp.2.2.1, hp.2.2.2]
    · intro p _ q _ h
      exact sumTriple_injective hc h
    · intro b hb
      obtain ⟨p, rfl⟩ := hbij.2 b
      refine ⟨p, ?_, rfl⟩
      simp only [Finset.mem_product, sumTriple] at hb
      simp [Finset.mem_filter, hb.1, hb.2.1, hb.2.2]
  rw [hcard]
  simp [Finset.card_product, mul_assoc]

/-! ### Axiom check -/

section AxCheck

#print axioms Nibble.AX1.dyBlk_laminar
#print axioms Nibble.AX1.box_matching_not_rectDisjoint
#print axioms Nibble.AX1.cellTriangle_capacity_le
#print axioms Nibble.AX1.cellTriangle_capacity_eq
#print axioms Nibble.AX1.cellTriangle_value_eq_min
#print axioms Nibble.AX1.cellTriangle_LP_gap
#print axioms Nibble.AX1.rounded_density_violates_blockShape
#print axioms Nibble.AX1.coherent_cellTriangle_count

end AxCheck

end Nibble.AX1
