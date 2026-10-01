import BoundedCliqueGap.DualCeiling

/-
`BoundedCliqueGap.FlowerLP` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Rung I1 — the flower LP ceiling, in every regime

Rung H1 closed the flower only in the regime `s i ≤ p i`, and its report
isolated the missing input: an LP ceiling for the flower that beats `|E|/3`
when a territory is *port-rich* (`p i ≤ s i`), because such a territory
cannot pack its own cross edges — its `ν₃` is only `C(p_i,2)`, far below the
`(C(p_i,2) + p_i s_i)/3` credited by the edge count.

This file supplies that ceiling.  Rather than eliminating the primal variable
split (`A` inside the hub; `B^b_i, B^c_i, B^d_i` for the territory-`i`
triangles with 2, 1, 0 vertices in the hub) by hand, we use the **dual** form,
which is equivalent and much shorter: a nonnegative weight `y` on the edge
slots with `∑_{e ∈ T} y e ≥ 1` for every triangle bounds the LP value by
`∑_{e ∈ E} y e` (`value_le_weight_sum`).  The primal constraint families

```
3A + Σ_i B^b_i ≤ C(κ,2),   2(B^b_i + B^c_i) ≤ p_i s_i,   B^c_i + 3B^d_i ≤ C(p_i,2)
```

are exactly the statement that the following weights are feasible: for a
parameter `h ∈ [1/3, 1]`,

* every hub edge gets `h`;
* a cross edge of a port-rich territory gets `(1-h)/2`, of a port-poor one `1/3`;
* a private edge of a port-rich territory gets `h`, of a port-poor one `1/3`.

Feasibility is a four-line check on the four triangle shapes; the resulting
ceiling `flower_value_le` is `h·C(κ,2) + Σ_i (…)`.  Uniform weights (`h = 1/3`)
reproduce `|E|/3`; `h = 1` charges the whole hub and *nothing* to the cross
edges of the port-rich territories, which is what the port-rich lower bound
`ν₃(CS(p,s)) ≥ C(p,2)` needs.

Combining the ceiling with the three lower bounds already in the project
(`nu3_clique_ge` on the hub, `nu3_CS_ge_choose` on a port-rich territory,
`nu3_CS_portPoor_ge` on a port-poor one) through `nu3_sum_le_of_edgeDisjoint`
gives `flower_gap_dual`:

```
value ≤ ν₃(flower) + 10·(κ + t) + (h - 1/3)·Q + (1 - h)·R,
```

for every `h ∈ [1/3,1]`, where `Q = C(κ,2)` is the hub capacity and
`R = Σ_{i port-rich} (p_i s_i/2 − C(p_i,2))` is the *donation mass*: the cross
capacity of the port-rich territories that their own private edges cannot
absorb.  Optimising over `h` gives the residual term `(2/3)·min(Q, R)`, and
`R = 0` recovers rung H1's theorem with the same constant.  See `REPORT_I.md`
for what the residual term costs and why closing it needs the block-granular
donation.
-/

namespace BoundedCliqueGap

open Finset

/-! ## Vertex bookkeeping for the flower -/

section Split

variable {kappa t : ℕ}

/-- The hub vertices of a vertex set of the flower. -/
def hubVerts (T : Finset (Fin kappa ⊕ Fin t)) : Finset (Fin kappa) :=
  univ.filter (fun a => Sum.inl a ∈ T)

/-- The private vertices of a vertex set of the flower. -/
def privVerts (T : Finset (Fin kappa ⊕ Fin t)) : Finset (Fin t) :=
  univ.filter (fun x => Sum.inr x ∈ T)

@[simp] lemma mem_hubVerts {T : Finset (Fin kappa ⊕ Fin t)} {a : Fin kappa} :
    a ∈ hubVerts T ↔ Sum.inl a ∈ T := by simp [hubVerts]

@[simp] lemma mem_privVerts {T : Finset (Fin kappa ⊕ Fin t)} {x : Fin t} :
    x ∈ privVerts T ↔ Sum.inr x ∈ T := by simp [privVerts]

lemma eq_union_images (T : Finset (Fin kappa ⊕ Fin t)) :
    T = (hubVerts T).image Sum.inl ∪ (privVerts T).image Sum.inr := by
  ext u; cases u with | inl a => simp | inr x => simp

lemma card_hub_add_card_priv (T : Finset (Fin kappa ⊕ Fin t)) :
    (hubVerts T).card + (privVerts T).card = T.card := by
  classical
  conv_rhs => rw [eq_union_images T]
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_image_of_injective _ Sum.inr_injective]
  rw [Finset.disjoint_left]
  rintro u hu hu'
  simp only [Finset.mem_image] at hu hu'
  obtain ⟨a, -, rfl⟩ := hu
  obtain ⟨x, -, hx⟩ := hu'
  exact Sum.inl_ne_inr hx.symm

lemma shape_priv_zero {T : Finset (Fin kappa ⊕ Fin t)} (h3 : T.card = 3)
    (h : (privVerts T).card = 0) :
    ∃ a b c : Fin kappa, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      T = {Sum.inl a, Sum.inl b, Sum.inl c} := by
  have hh : (hubVerts T).card = 3 := by have := card_hub_add_card_priv T; omega
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.1 hh
  have hp : privVerts T = ∅ := Finset.card_eq_zero.1 h
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  rw [eq_union_images T, hset, hp]
  ext u; simp; try tauto

lemma shape_priv_one {T : Finset (Fin kappa ⊕ Fin t)} (h3 : T.card = 3)
    (h : (privVerts T).card = 1) :
    ∃ (a b : Fin kappa) (y : Fin t), a ≠ b ∧ T = {Sum.inl a, Sum.inl b, Sum.inr y} := by
  have hh : (hubVerts T).card = 2 := by have := card_hub_add_card_priv T; omega
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.1 hh
  obtain ⟨y, hy⟩ := Finset.card_eq_one.1 h
  refine ⟨a, b, y, hab, ?_⟩
  rw [eq_union_images T, hset, hy]
  ext u; simp; try tauto

lemma shape_priv_two {T : Finset (Fin kappa ⊕ Fin t)} (h3 : T.card = 3)
    (h : (privVerts T).card = 2) :
    ∃ (a : Fin kappa) (x y : Fin t), x ≠ y ∧ T = {Sum.inl a, Sum.inr x, Sum.inr y} := by
  have hh : (hubVerts T).card = 1 := by have := card_hub_add_card_priv T; omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hh
  obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.1 h
  refine ⟨a, x, y, hxy, ?_⟩
  rw [eq_union_images T, ha, hset]
  ext u; simp; try tauto

lemma shape_priv_three {T : Finset (Fin kappa ⊕ Fin t)} (h3 : T.card = 3)
    (h : (privVerts T).card = 3) :
    ∃ x y z : Fin t, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ T = {Sum.inr x, Sum.inr y, Sum.inr z} := by
  have hh : (hubVerts T).card = 0 := by have := card_hub_add_card_priv T; omega
  obtain ⟨x, y, z, hxy, hxz, hyz, hset⟩ := Finset.card_eq_three.1 h
  have hp : hubVerts T = ∅ := Finset.card_eq_zero.1 hh
  refine ⟨x, y, z, hxy, hxz, hyz, ?_⟩
  rw [eq_union_images T, hset, hp]
  ext u; simp; try tauto

end Split

/-! ## Summing a weight over the three edges of a triangle -/

lemma sum_triEdges_three {V : Type*} [DecidableEq V] (y : Sym2 V → ℚ) {T : Finset V} {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hT : T = {a, b, c}) :
    ∑ e ∈ triEdges T, y e = y s(a, b) + y s(a, c) + y s(b, c) := by
  rw [triEdges_eq_of_card_three hab hac hbc hT]
  rw [Finset.sum_insert (by simp; tauto), Finset.sum_insert (by simp; tauto),
    Finset.sum_singleton]
  ring

/-! ## The dual weight of the flower -/

section FlowerWeight

variable {kappa t m : ℕ}

variable (h : ℚ) (terr : Fin t → Fin m) (S : Fin m → Finset (Fin kappa))

/-! ## The three edge classes of the flower, and the total weight -/

/-- The cross edge slots of territory `i`. -/
noncomputable def crossEdgeSet (terr : Fin t → Fin m) (S : Fin m → Finset (Fin kappa))
    (i : Fin m) : Finset (Sym2 (Fin kappa ⊕ Fin t)) :=
  ((S i) ×ˢ (privSet terr i)).image (fun q => s(Sum.inl q.1, Sum.inr q.2))

lemma card_crossEdgeSet (i : Fin m) :
    (crossEdgeSet terr S i).card = sepCard S i * privCard terr i := by
  classical
  rw [crossEdgeSet, Finset.card_image_of_injective, Finset.card_product]
  · rfl
  · rintro ⟨a, x⟩ ⟨b, y⟩ hq
    simp only [Sym2.eq_iff] at hq
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Sum.inl_injective h1, Sum.inr_injective h2]
    · exact absurd h1 (by simp)

end FlowerWeight

/-! ## Axiom audit -/

end BoundedCliqueGap
