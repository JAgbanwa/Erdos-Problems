/-
  Part B (Phase 2) — instantiating the hub gadget: friendship hub walks.

  `AbsorbCalculus.lean` shows that a config `C = cycEdges v σ` is absorbed by the ear triangles
  of any hub assignment `z` **whose hub edges `Z = hubEdges z σ` are triangle-decomposable**.
  This file supplies such hub assignments in the case where every cycle of the config has length
  divisible by three.

  Index the config by `κ × Fin 3`, the permutation being `triSucc τ`, which walks through the
  three phases of a block and then moves to the next block via `τ`.  Send phase `0` to a common
  centre `c`, phase `1` to `a t` and phase `2` to `b t`.  The hub walk then traverses, for every
  block `t`, the triangle `c — a t — b t — c`: the hub-edge set is the **friendship graph** with
  centre `c` and blades `{a t, b t}`, a disjoint union of `|κ|` triangles, hence decomposable.

  Main results:

  * `triSucc`, `triHub` — the index permutation and the hub assignment;
  * `hubEdges_triHub` — the hub edges are exactly the friendship graph;
  * `triDecomposable_hubEdges_triHub` — the friendship graph is decomposable;
  * `absorbs_cycEdges_of_friendshipHubs` — the resulting absorption, with one reserved ear
    triangle per config edge.
-/
import Ax2.PartB.BKLO.AbsorbCalculus

namespace Ax2.BKLO

open SimpleGraph Finset Ax2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The three-phase index permutation -/

/-- The successor permutation of `κ × Fin 3`: run through the three phases of a block, then move
to the next block via `τ`.  Its cycles are the `τ`-cycles blown up by a factor of three, so the
configs it describes are unions of cycles of length divisible by three. -/
def triSucc {κ : Type*} (τ : Equiv.Perm κ) : Equiv.Perm (κ × Fin 3) where
  toFun := fun p => if p.2 = 2 then (τ p.1, 0) else (p.1, p.2 + 1)
  invFun := fun p => if p.2 = 0 then (τ.symm p.1, 2) else (p.1, p.2 - 1)
  left_inv := by rintro ⟨t, j⟩; fin_cases j <;> simp
  right_inv := by rintro ⟨t, j⟩; fin_cases j <;> simp

variable {κ : Type*}

@[simp] theorem triSucc_zero (τ : Equiv.Perm κ) (t : κ) : triSucc τ (t, 0) = (t, 1) := by
  simp [triSucc]

@[simp] theorem triSucc_one (τ : Equiv.Perm κ) (t : κ) : triSucc τ (t, 1) = (t, 2) := by
  simp [triSucc]

@[simp] theorem triSucc_two (τ : Equiv.Perm κ) (t : κ) : triSucc τ (t, 2) = (τ t, 0) := by
  simp [triSucc]

@[simp] theorem triSucc_symm_zero (τ : Equiv.Perm κ) (t : κ) :
    (triSucc τ).symm (t, 0) = (τ.symm t, 2) := by simp [triSucc]

@[simp] theorem triSucc_symm_one (τ : Equiv.Perm κ) (t : κ) :
    (triSucc τ).symm (t, 1) = (t, 0) := by simp [triSucc]

@[simp] theorem triSucc_symm_two (τ : Equiv.Perm κ) (t : κ) :
    (triSucc τ).symm (t, 2) = (t, 1) := by simp [triSucc]

/-- The hub assignment of a friendship walk: the centre `c` at phase `0`, the blade ends `a t`
and `b t` at phases `1` and `2`. -/
def triHub (c : V) (a b : κ → V) : κ × Fin 3 → V :=
  fun p => if p.2 = 0 then c else if p.2 = 1 then a p.1 else b p.1

variable {c : V} {a b : κ → V}

omit [Fintype V] [DecidableEq V] in
@[simp] theorem triHub_zero (t : κ) : triHub c a b (t, 0) = c := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem triHub_one (t : κ) : triHub c a b (t, 1) = a t := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem triHub_two (t : κ) : triHub c a b (t, 2) = b t := rfl

/-! ### The friendship graph of hub edges -/

section Friendship

variable [Fintype κ] [DecidableEq κ]

/-- The friendship triangles: the blades `{c, a t, b t}` through the common centre `c`. -/
def friendshipTris (c : V) (a b : κ → V) [Fintype κ] : Finset (Finset V) :=
  Finset.univ.image (fun t => ({c, a t, b t} : Finset V))

omit [Fintype V] in
theorem card_inter_le_one_of_subset_singleton {X Y : Finset V} {w : V}
    (h : X ∩ Y ⊆ ({w} : Finset V)) : (X ∩ Y).card ≤ 1 := by
  simpa using Finset.card_le_card h

omit [Fintype V] [DecidableEq κ] in
/-- **The hub walk of a friendship assignment traverses the friendship graph.** -/
theorem hubEdges_triHub (τ : Equiv.Perm κ)
    (hca : ∀ t, c ≠ a t) (hcb : ∀ t, c ≠ b t) (hab : ∀ t, a t ≠ b t) :
    hubEdges (triHub c a b) (triSucc τ) = coveredEdges (friendshipTris c a b) := by
  have htri : ∀ t, triEdges ({c, a t, b t} : Finset V) = {s(c, a t), s(c, b t), s(a t, b t)} :=
    fun t => triEdges_triple (hca t) (hcb t) (hab t)
  rw [coveredEdges, friendshipTris, Finset.image_biUnion]
  ext e
  simp only [mem_hubEdges_iff, Finset.mem_biUnion, Finset.mem_univ, true_and, htri,
    Finset.mem_insert, Finset.mem_singleton]
  have hj : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  constructor
  · rintro ⟨⟨t, j⟩, rfl⟩
    rcases hj j with rfl | rfl | rfl <;>
      simp only [triSucc_symm_zero, triSucc_symm_one, triSucc_symm_two, triHub_zero, triHub_one,
        triHub_two]
    · exact ⟨τ.symm t, Or.inr (Or.inl Sym2.eq_swap)⟩
    · exact ⟨t, Or.inl rfl⟩
    · exact ⟨t, Or.inr (Or.inr rfl)⟩
  · rintro ⟨t, h | h | h⟩
    · exact ⟨(t, 1), by simp [h]⟩
    · refine ⟨(τ t, 0), ?_⟩
      simp only [triSucc_symm_zero, triHub_zero, triHub_two, Equiv.symm_apply_apply]
      rw [h, Sym2.eq_swap]
    · exact ⟨(t, 2), by simp [h]⟩

omit [Fintype V] [DecidableEq κ] in
/-- The blades of a friendship graph are edge-disjoint. -/
theorem edgeDisjoint_friendshipTris (hca : ∀ t, c ≠ a t) (hcb : ∀ t, c ≠ b t)
    (hab : ∀ t s, a t ≠ b s) (hainj : Function.Injective a) (hbinj : Function.Injective b) :
    EdgeDisjoint (friendshipTris c a b) := by
  have hac : ∀ t, a t ≠ c := fun t h => hca t h.symm
  have hbc : ∀ t, b t ≠ c := fun t h => hcb t h.symm
  have hba : ∀ t s, b t ≠ a s := fun t s h => hab s t h.symm
  have haeq : ∀ t s, a t = a s ↔ t = s := fun t s => ⟨fun h => hainj h, fun h => by rw [h]⟩
  have hbeq : ∀ t s, b t = b s ↔ t = s := fun t s => ⟨fun h => hbinj h, fun h => by rw [h]⟩
  intro t₁ ht₁ t₂ ht₂ hne
  simp only [friendshipTris, Finset.mem_image, Finset.mem_univ, true_and] at ht₁ ht₂
  obtain ⟨t, rfl⟩ := ht₁
  obtain ⟨s, rfl⟩ := ht₂
  have hts : t ≠ s := by rintro rfl; exact hne rfl
  refine triEdges_disjoint_of_card_inter_le_one ?_
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hxc : x = c := by
    rcases hx1 with rfl | rfl | rfl <;> rcases hx2 with h | h | h <;> simp_all
  have hyc : y = c := by
    rcases hy1 with rfl | rfl | rfl <;> rcases hy2 with h | h | h <;> simp_all
  rw [hxc, hyc]

omit [Fintype V] [DecidableEq κ] in
/-- **The hub edges of a friendship assignment are decomposable**: they are the disjoint union of
the blades. -/
theorem triDecomposable_hubEdges_triHub (G : SimpleGraph V) [DecidableRel G.Adj]
    (τ : Equiv.Perm κ) (hca : ∀ t, c ≠ a t) (hcb : ∀ t, c ≠ b t) (hab : ∀ t s, a t ≠ b s)
    (hainj : Function.Injective a) (hbinj : Function.Injective b)
    (hfr : ∀ t, G.IsNClique 3 ({c, a t, b t} : Finset V)) :
    TriDecomposable G (hubEdges (triHub c a b) (triSucc τ)) := by
  rw [hubEdges_triHub τ hca hcb (fun t => hab t t)]
  refine TriDecomposable.of_family G ?_ (edgeDisjoint_friendshipTris hca hcb hab hainj hbinj)
  intro t ht
  simp only [friendshipTris, Finset.mem_image, Finset.mem_univ, true_and] at ht
  obtain ⟨s, rfl⟩ := ht
  exact hfr s

omit [Fintype V] [Fintype κ] [DecidableEq κ] in
/-- Distinct indices of a friendship hub walk use distinct hub pairs. -/
theorem card_inter_triHub_pair_le_one (τ : Equiv.Perm κ)
    (hca : ∀ t, c ≠ a t) (hcb : ∀ t, c ≠ b t) (hab : ∀ t s, a t ≠ b s)
    (hainj : Function.Injective a) (hbinj : Function.Injective b) :
    ∀ i j : κ × Fin 3, i ≠ j →
      (({triHub c a b ((triSucc τ).symm i), triHub c a b i} : Finset V) ∩
       ({triHub c a b ((triSucc τ).symm j), triHub c a b j} : Finset V)).card ≤ 1 := by
  have hac : ∀ t, a t ≠ c := fun t h => hca t h.symm
  have hbc : ∀ t, b t ≠ c := fun t h => hcb t h.symm
  have hba : ∀ t s, b t ≠ a s := fun t s h => hab s t h.symm
  have haeq : ∀ t s, a t = a s ↔ t = s := fun t s => ⟨fun h => hainj h, fun h => by rw [h]⟩
  have hbeq : ∀ t s, b t = b s ↔ t = s := fun t s => ⟨fun h => hbinj h, fun h => by rw [h]⟩
  have hj : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  rintro ⟨t, jt⟩ ⟨s, js⟩ hij
  simp only [ne_eq, Prod.mk.injEq, not_and] at hij
  rcases hj jt with rfl | rfl | rfl <;> rcases hj js with rfl | rfl | rfl <;>
    simp only [triSucc_symm_zero, triSucc_symm_one, triSucc_symm_two, triHub_zero, triHub_one,
      triHub_two] <;>
    [ (refine card_inter_le_one_of_subset_singleton (w := c) ?_);
      (refine card_inter_le_one_of_subset_singleton (w := c) ?_);
      (refine card_inter_le_one_of_subset_singleton (w := b (τ.symm t)) ?_);
      (refine card_inter_le_one_of_subset_singleton (w := c) ?_);
      (refine card_inter_le_one_of_subset_singleton (w := c) ?_);
      (refine card_inter_le_one_of_subset_singleton (w := a t) ?_);
      (refine card_inter_le_one_of_subset_singleton (w := b (τ.symm s)) ?_);
      (refine card_inter_le_one_of_subset_singleton (w := a s) ?_);
      (refine card_inter_le_one_of_subset_singleton (w := a t) ?_)] <;>
    · intro x hx
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      rcases h1 with rfl | rfl <;> rcases h2 with h | h <;> simp_all

/-! ### The resulting absorption -/

omit [Fintype V] [DecidableEq κ] in
/-- **A config whose cycles have length divisible by three is absorbed by one reserved triangle
per edge.**  The hubs run through a friendship graph with centre `c` and blades `{a t, b t}`;
the reserved part is the family of ear triangles `{z (σ⁻¹ i), v i, z i}`. -/
theorem localAbsorbable_earTris_triHub (G : SimpleGraph V) [DecidableRel G.Adj]
    (τ : Equiv.Perm κ) (v : κ × Fin 3 → V) (hv : Function.Injective v)
    (hcv : ∀ p, c ≠ v p) (hav : ∀ t p, a t ≠ v p) (hbv : ∀ t p, b t ≠ v p)
    (hca : ∀ t, c ≠ a t) (hcb : ∀ t, c ≠ b t) (hab : ∀ t s, a t ≠ b s)
    (hainj : Function.Injective a) (hbinj : Function.Injective b)
    (hsub : ∀ i, G.IsNClique 3 ({v i, triHub c a b i, v (triSucc τ i)} : Finset V))
    (hear : ∀ i, G.IsNClique 3
      ({triHub c a b ((triSucc τ).symm i), v i, triHub c a b i} : Finset V))
    (hfr : ∀ t, G.IsNClique 3 ({c, a t, b t} : Finset V)) :
    LocalAbsorbable G (earTris v (triHub c a b) (triSucc τ)) (cycEdges v (triSucc τ)) := by
  have hj : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  have hzv : ∀ (i : κ × Fin 3) (p : κ × Fin 3), triHub c a b i ≠ v p := by
    rintro ⟨t, j⟩ p
    rcases hj j with rfl | rfl | rfl
    exacts [hcv p, hav t p, hbv t p]
  have hstep : ∀ i : κ × Fin 3, triHub c a b i ≠ triHub c a b (triSucc τ i) := by
    rintro ⟨t, j⟩
    rcases hj j with rfl | rfl | rfl <;>
      simp only [triSucc_zero, triSucc_one, triSucc_two, triHub_zero, triHub_one, triHub_two]
    exacts [hca t, hab t t, fun h => hcb t h.symm]
  have hfix : ∀ i : κ × Fin 3, triSucc τ i ≠ i := by
    rintro ⟨t, j⟩
    rcases hj j with rfl | rfl | rfl <;>
      simp only [triSucc_zero, triSucc_one, triSucc_two, ne_eq, Prod.mk.injEq, not_and] <;>
      intro _ <;> decide
  have hsq : ∀ i : κ × Fin 3, triSucc τ (triSucc τ i) ≠ i := by
    rintro ⟨t, j⟩
    rcases hj j with rfl | rfl | rfl <;>
      simp only [triSucc_zero, triSucc_one, triSucc_two, ne_eq, Prod.mk.injEq, not_and] <;>
      intro _ <;> decide
  exact localAbsorbable_earTris G hv hzv hstep hfix hsq
    (card_inter_triHub_pair_le_one τ hca hcb hab hainj hbinj) hsub hear
    (triDecomposable_hubEdges_triHub G τ hca hcb hab hainj hbinj hfr)

end Friendship

/-! ### Non-vacuity: a hexagon absorbed in `K₁₁` -/

/-- Six config vertices `0,1,2,3,4,5`, arranged in two blocks of three. -/
def hexV (p : Fin 2 × Fin 3) : Fin 11 := ![![0, 1, 2], ![3, 4, 5]] p.1 p.2

/-- The first blade ends of the two friendship blades. -/
def hexA : Fin 2 → Fin 11 := ![7, 9]

/-- The second blade ends of the two friendship blades. -/
def hexB : Fin 2 → Fin 11 := ![8, 10]

/-- The block permutation: `triSucc hexTau` is a single cycle of length `3 · 2 = 6`. -/
def hexTau : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- The config described by `hexV` and `triSucc hexTau` is the hexagon `0-1-2-3-4-5`. -/
theorem cycEdges_hexV : cycEdges hexV (triSucc hexTau)
    = ({s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 5), s(5, 0)} : Finset (Sym2 (Fin 11))) := by
  decide

/-- The hub walk traverses the friendship graph with centre `6` and blades `{7,8}`, `{9,10}`. -/
theorem hubEdges_hexV : hubEdges (triHub 6 hexA hexB) (triSucc hexTau)
    = ({s(6, 7), s(7, 8), s(8, 6), s(6, 9), s(9, 10), s(10, 6)} : Finset (Sym2 (Fin 11))) := by
  decide

/-- Six reserved ear triangles — one per edge of the hexagon. -/
theorem card_earTris_hexV :
    (earTris hexV (triHub 6 hexA hexB) (triSucc hexTau)).card = 6 := by decide

/-- **The hub gadget really produces absorbers.**  In `K₁₁` the six ear triangles
`{z (σ⁻¹ i), v i, z i}` of the friendship hub walk with centre `6` and blades `{7,8}`, `{9,10}`
locally absorb the hexagon `0-1-2-3-4-5`: their covered edges together with the hexagon carry an
edge-disjoint triangle decomposition. -/
theorem localAbsorbable_hexV :
    LocalAbsorbable (⊤ : SimpleGraph (Fin 11))
      (earTris hexV (triHub 6 hexA hexB) (triSucc hexTau))
      ({s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 5), s(5, 0)} : Finset (Sym2 (Fin 11))) := by
  rw [← cycEdges_hexV]
  refine localAbsorbable_earTris_triHub (⊤ : SimpleGraph (Fin 11)) hexTau hexV (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) ?_ ?_ ?_
  · intro i
    refine SimpleGraph.is3Clique_triple_iff.2 ?_
    revert i
    decide
  · intro i
    refine SimpleGraph.is3Clique_triple_iff.2 ?_
    revert i
    decide
  · intro t
    refine SimpleGraph.is3Clique_triple_iff.2 ?_
    revert t
    decide

end Ax2.BKLO
