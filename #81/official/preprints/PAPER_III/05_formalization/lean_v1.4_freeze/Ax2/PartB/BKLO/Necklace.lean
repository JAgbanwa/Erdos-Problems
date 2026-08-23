/-
  Part B (Phase 2) — hub walks along a **triangle necklace**.

  `AbsorbCalculus.lean` reduces the absorption of a config `C = cycEdges v σ` to the choice of a
  hub assignment `z` whose hub edges `Z = hubEdges z σ` are triangle-decomposable, the reserved
  part being the ear triangles `{z (σ⁻¹ i), v i, z i}` — one per config edge.

  `FriendshipHub.lean` supplies such a hub assignment when every cycle of the config has length
  divisible by three: the hubs run through a friendship graph with a common centre `c`.  That
  gadget has one defect, noted in `HexAbsorber.lean`: the centre `c` has to be adjacent to two
  thirds of the config vertices, so a *single* friendship hub can only serve configs of bounded
  size (at most a hexagon in the regime `δ(G) ≥ (9/10 + ε) n`).

  This file supplies the unbounded replacement: the **triangle necklace**

      `T t = {c t, a t, c (t+1)}`,   `t ∈ ZMod m`,

  a cyclic chain of `m` triangles in which consecutive blades share the single vertex `c (t+1)`.
  It is connected with all degrees even (`4` at the `c`'s, `2` at the `a`'s), so it has an
  Eulerian circuit, and every one of its vertices has **bounded degree** — each hub is adjacent to
  at most four config vertices and four other hubs, eight prescribed neighbours in all, exactly
  the budget the dense regime affords.  A single necklace therefore serves configs of *unbounded*
  size.

  The Eulerian circuit used is the explicit one

      `c 0 — a 0 — c 1 — a 1 — ⋯ — c (m-1) — a (m-1) — c 0 — c 1 — c 2 — ⋯ — c (m-1) — c 0`

  (first the `2m` "outer" edges `c t — a t — c (t+1)`, then the `m` "inner" edges `c t — c (t+1)`),
  encoded by `necklaceHub`.  Note that no Eulerian circuit of a necklace can be aligned with the
  blocks of three positions used by `triSucc`: a block-aligned circuit traverses each blade in
  three consecutive steps and hence returns to its entry vertex, forcing all blades through a
  common vertex — the friendship case.  This is why the index type here is `ZMod (3 * m)`.

  Main results:

  * `necklaceHub`, `necklaceSucc`, `necklaceTris` — the walk, its index permutation, the blades;
  * `hubEdges_necklaceHub` — the hub walk traverses exactly the necklace;
  * `edgeDisjoint_necklaceTris`, `triDecomposable_hubEdges_necklaceHub` — the necklace is a
    disjoint union of `m` triangles, hence decomposable;
  * `card_inter_necklaceHub_pair_le_one` — distinct positions use distinct hub pairs;
  * `localAbsorbable_earTris_necklace`, `localAbsorbable_necklace_of_adj` — **a config which is a
    single cycle of length `3m ≥ 9` is absorbed by its `3m` ear triangles along a necklace**.
-/
import Ax2.PartB.BKLO.FriendshipHub

namespace Ax2.BKLO

open SimpleGraph Finset Ax2

variable {V : Type*} [DecidableEq V]

section Necklace

variable (m : ℕ) [NeZero m]

instance neZero_three_mul : NeZero (3 * m) := ⟨by simpa using NeZero.ne m⟩

/-- The blades of the triangle necklace: the triangles `{c t, a t, c (t+1)}`, `t ∈ ZMod m`.
Consecutive blades share exactly the vertex `c (t+1)`. -/
def necklaceTris (c a : ZMod m → V) : Finset (Finset V) :=
  Finset.univ.image fun t : ZMod m => ({c t, a t, c (t + 1)} : Finset V)

/-- The hub assignment of the necklace walk: positions `2t` and `2t+1` (`t < m`) carry `c t` and
`a t`, positions `2m + t` carry `c t` again.  The resulting closed walk traverses every edge of
the necklace exactly once. -/
def necklaceHub (c a : ZMod m → V) (i : ZMod (3 * m)) : V :=
  if i.val < 2 * m then
    (if i.val % 2 = 0 then c ((i.val / 2 : ℕ) : ZMod m) else a ((i.val / 2 : ℕ) : ZMod m))
  else c (((i.val - 2 * m : ℕ)) : ZMod m)

/-- The successor permutation of the necklace index type: the config is a single cycle of length
`3m`. -/
def necklaceSucc : Equiv.Perm (ZMod (3 * m)) := Equiv.addRight 1

variable {m}

omit [NeZero m] in
@[simp] theorem necklaceSucc_apply (i : ZMod (3 * m)) : necklaceSucc m i = i + 1 := rfl

omit [NeZero m] in
@[simp] theorem necklaceSucc_symm_apply (i : ZMod (3 * m)) :
    (necklaceSucc m).symm i = i - 1 := by
  simp [necklaceSucc, Equiv.addRight, sub_eq_add_neg]

variable {c a : ZMod m → V}

omit [DecidableEq V] [NeZero m] in
/-- The value of the necklace hub assignment at a position given by a natural number. -/
theorem necklaceHub_natCast {k : ℕ} (hk : k < 3 * m) :
    necklaceHub m c a (k : ZMod (3 * m)) =
      if k < 2 * m then (if k % 2 = 0 then c ((k / 2 : ℕ) : ZMod m) else a ((k / 2 : ℕ) : ZMod m))
      else c (((k - 2 * m : ℕ)) : ZMod m) := by
  simp only [necklaceHub, ZMod.val_natCast_of_lt hk]

omit [DecidableEq V] [NeZero m] in
theorem necklaceHub_even {t : ℕ} (ht : t < m) :
    necklaceHub m c a ((2 * t : ℕ) : ZMod (3 * m)) = c (t : ZMod m) := by
  rw [necklaceHub_natCast (by omega), if_pos (by omega), if_pos (by omega)]
  congr 2
  omega

omit [DecidableEq V] [NeZero m] in
theorem necklaceHub_odd {t : ℕ} (ht : t < m) :
    necklaceHub m c a ((2 * t + 1 : ℕ) : ZMod (3 * m)) = a (t : ZMod m) := by
  rw [necklaceHub_natCast (by omega), if_pos (by omega), if_neg (by omega)]
  congr 2
  omega

omit [DecidableEq V] [NeZero m] in
theorem necklaceHub_late {t : ℕ} (ht : t < m) :
    necklaceHub m c a ((2 * m + t : ℕ) : ZMod (3 * m)) = c (t : ZMod m) := by
  rw [necklaceHub_natCast (by omega), if_neg (by omega)]
  congr 2
  omega

omit [DecidableEq V] in
/-- Position `2t+2` carries `c (t+1)`, whether or not the walk has wrapped around. -/
theorem necklaceHub_even_succ {t : ℕ} (ht : t < m) :
    necklaceHub m c a ((2 * t + 2 : ℕ) : ZMod (3 * m)) = c ((t + 1 : ℕ) : ZMod m) := by
  rcases lt_or_ge (t + 1) m with h | h
  · have := necklaceHub_even (c := c) (a := a) h
    rw [show 2 * t + 2 = 2 * (t + 1) by ring]
    exact this
  · have htm : t + 1 = m := by omega
    have h0 : (0 : ℕ) < m := Nat.pos_of_ne_zero (NeZero.ne m)
    have := necklaceHub_late (c := c) (a := a) (t := 0) h0
    rw [show 2 * t + 2 = 2 * m + 0 by omega]
    rw [this, htm]
    simp

omit [DecidableEq V] in
/-- Position `2m + t + 1` carries `c (t+1)`, whether or not the walk has wrapped around. -/
theorem necklaceHub_late_succ {t : ℕ} (ht : t < m) :
    necklaceHub m c a ((2 * m + t + 1 : ℕ) : ZMod (3 * m)) = c ((t + 1 : ℕ) : ZMod m) := by
  rcases lt_or_ge (t + 1) m with h | h
  · have := necklaceHub_late (c := c) (a := a) h
    rw [show 2 * m + t + 1 = 2 * m + (t + 1) by ring]
    exact this
  · have htm : t + 1 = m := by omega
    have h0 : (0 : ℕ) < m := Nat.pos_of_ne_zero (NeZero.ne m)
    have hz : ((2 * m + t + 1 : ℕ) : ZMod (3 * m)) = ((2 * 0 : ℕ) : ZMod (3 * m)) := by
      have : 2 * m + t + 1 = 3 * m := by omega
      rw [this]
      simp
    rw [hz, necklaceHub_even h0, htm]
    simp

/-! ### The hub walk traverses the necklace -/

omit [NeZero m] in
/-- Membership in the edge set of a vertex set. -/
theorem mem_triEdges_pair {T : Finset V} {x y : V} :
    s(x, y) ∈ triEdges T ↔ x ∈ T ∧ y ∈ T ∧ x ≠ y := by
  simp only [triEdges, Finset.mem_filter, Finset.mem_sym2_iff, Sym2.mk_isDiag_iff]
  constructor
  · rintro ⟨h, hne⟩
    exact ⟨h _ (by simp), h _ (by simp), hne⟩
  · rintro ⟨hx, hy, hne⟩
    refine ⟨?_, hne⟩
    intro z hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl <;> assumption

omit [DecidableEq V] [NeZero m] in
/-- In `ZMod m` with `m ≥ 2` no element is its own successor. -/
theorem zmod_succ_ne (hm : 2 ≤ m) (t : ZMod m) : t + 1 ≠ t := by
  intro h
  have h1 : ((1 : ℕ) : ZMod m) = 0 := by push_cast; linear_combination h
  have := (ZMod.natCast_eq_zero_iff 1 m).mp h1
  exact absurd (Nat.le_of_dvd one_pos this) (by omega)

omit [DecidableEq V] [NeZero m] in
/-- In `ZMod m` with `m ≥ 3` no element is its own second successor. -/
theorem zmod_succ_succ_ne (hm : 3 ≤ m) (t : ZMod m) : t + 1 + 1 ≠ t := by
  intro h
  have h1 : ((2 : ℕ) : ZMod m) = 0 := by push_cast; linear_combination h
  have := (ZMod.natCast_eq_zero_iff 2 m).mp h1
  exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)

/-- The hub walk, reindexed: the walk edges are the pairs `z k — z (k+1)`. -/
theorem hubEdges_necklaceSucc (z : ZMod (3 * m) → V) :
    hubEdges z (necklaceSucc m)
      = Finset.univ.image (fun k : ZMod (3 * m) => s(z k, z (k + 1))) := by
  have h : (fun i : ZMod (3 * m) => s(z ((necklaceSucc m).symm i), z i)) ∘ (necklaceSucc m)
      = (fun k : ZMod (3 * m) => s(z k, z (k + 1))) := by
    funext k
    simp
  calc hubEdges z (necklaceSucc m)
      = Finset.univ.image (fun i => s(z ((necklaceSucc m).symm i), z i)) := rfl
    _ = Finset.univ.image ((fun i => s(z ((necklaceSucc m).symm i), z i)) ∘ (necklaceSucc m)) := by
        rw [← Finset.image_image, Finset.image_univ_equiv]
    _ = Finset.univ.image (fun k => s(z k, z (k + 1))) := by rw [h]

omit [DecidableEq V] in
/-- Every position of the necklace walk is of one of three explicit forms, with an explicitly
computed walk edge. -/
theorem necklace_walkEdge_form (k : ZMod (3 * m)) :
    (∃ t : ℕ, t < m ∧ k = ((2 * t : ℕ) : ZMod (3 * m)) ∧
        s(necklaceHub m c a k, necklaceHub m c a (k + 1)) = s(c (t : ZMod m), a (t : ZMod m))) ∨
    (∃ t : ℕ, t < m ∧ k = ((2 * t + 1 : ℕ) : ZMod (3 * m)) ∧
        s(necklaceHub m c a k, necklaceHub m c a (k + 1))
          = s(a (t : ZMod m), c ((t : ZMod m) + 1))) ∨
    (∃ t : ℕ, t < m ∧ k = ((2 * m + t : ℕ) : ZMod (3 * m)) ∧
        s(necklaceHub m c a k, necklaceHub m c a (k + 1))
          = s(c (t : ZMod m), c ((t : ZMod m) + 1))) := by
  obtain ⟨n, hnlt, rfl⟩ : ∃ n : ℕ, n < 3 * m ∧ k = ((n : ℕ) : ZMod (3 * m)) :=
    ⟨k.val, ZMod.val_lt k, (ZMod.natCast_zmod_val k).symm⟩
  have hsucc : ((n : ZMod (3 * m)) + 1) = ((n + 1 : ℕ) : ZMod (3 * m)) := by push_cast; ring
  rcases lt_or_ge n (2 * m) with hlt | hge
  · rcases Nat.even_or_odd n with hev | hodd
    · obtain ⟨t, ht⟩ := hev
      have htm : t < m := by omega
      refine Or.inl ⟨t, htm, by rw [show n = 2 * t by omega], ?_⟩
      rw [hsucc, show n = 2 * t by omega, show 2 * t + 1 = 2 * t + 1 from rfl,
        necklaceHub_even htm, necklaceHub_odd htm]
    · obtain ⟨t, ht⟩ := hodd
      have htm : t < m := by omega
      refine Or.inr (Or.inl ⟨t, htm, by rw [show n = 2 * t + 1 by omega], ?_⟩)
      rw [hsucc, show n = 2 * t + 1 by omega, show 2 * t + 1 + 1 = 2 * t + 2 by ring,
        necklaceHub_odd htm, necklaceHub_even_succ htm]
      push_cast
      rfl
  · obtain ⟨t, htm, rfl⟩ : ∃ t : ℕ, t < m ∧ n = 2 * m + t := ⟨n - 2 * m, by omega, by omega⟩
    refine Or.inr (Or.inr ⟨t, htm, rfl, ?_⟩)
    rw [hsucc, necklaceHub_late htm, necklaceHub_late_succ htm]
    push_cast
    rfl

omit [DecidableEq V] in
/-- Every position of the necklace walk is of one of three explicit forms, with an explicitly
computed hub. -/
theorem necklace_pos_form (k : ZMod (3 * m)) :
    (∃ t : ℕ, t < m ∧ k = ((2 * t : ℕ) : ZMod (3 * m)) ∧
        necklaceHub m c a k = c (t : ZMod m) ∧
        k + 1 = ((2 * t + 1 : ℕ) : ZMod (3 * m))) ∨
    (∃ t : ℕ, t < m ∧ k = ((2 * t + 1 : ℕ) : ZMod (3 * m)) ∧
        necklaceHub m c a k = a (t : ZMod m) ∧
        k + 1 = ((2 * t + 2 : ℕ) : ZMod (3 * m))) ∨
    (∃ t : ℕ, t < m ∧ k = ((2 * m + t : ℕ) : ZMod (3 * m)) ∧
        necklaceHub m c a k = c (t : ZMod m) ∧
        k + 1 = ((2 * m + t + 1 : ℕ) : ZMod (3 * m))) := by
  obtain ⟨n, hnlt, rfl⟩ : ∃ n : ℕ, n < 3 * m ∧ k = ((n : ℕ) : ZMod (3 * m)) :=
    ⟨k.val, ZMod.val_lt k, (ZMod.natCast_zmod_val k).symm⟩
  have hsucc : ((n : ZMod (3 * m)) + 1) = ((n + 1 : ℕ) : ZMod (3 * m)) := by push_cast; ring
  rcases lt_or_ge n (2 * m) with hlt | hge
  · rcases Nat.even_or_odd n with hev | hodd
    · obtain ⟨t, ht⟩ := hev
      have htm : t < m := by omega
      refine Or.inl ⟨t, htm, by rw [show n = 2 * t by omega], ?_, ?_⟩
      · rw [show n = 2 * t by omega, necklaceHub_even htm]
      · rw [hsucc, show n + 1 = 2 * t + 1 by omega]
    · obtain ⟨t, ht⟩ := hodd
      have htm : t < m := by omega
      refine Or.inr (Or.inl ⟨t, htm, by rw [show n = 2 * t + 1 by omega], ?_, ?_⟩)
      · rw [show n = 2 * t + 1 by omega, necklaceHub_odd htm]
      · rw [hsucc, show n + 1 = 2 * t + 2 by omega]
  · obtain ⟨t, htm, rfl⟩ : ∃ t : ℕ, t < m ∧ n = 2 * m + t := ⟨n - 2 * m, by omega, by omega⟩
    exact Or.inr (Or.inr ⟨t, htm, rfl, necklaceHub_late htm, hsucc⟩)

omit [DecidableEq V] [NeZero m] in
/-- Natural numbers below `m` are distinguished by their images in `ZMod m`. -/
theorem natCast_inj_of_lt {t s : ℕ} (ht : t < m) (hs : s < m)
    (h : ((t : ℕ) : ZMod m) = ((s : ℕ) : ZMod m)) : t = s := by
  have h1 : ((t : ℕ) : ZMod m).val = t := ZMod.val_natCast_of_lt ht
  have h2 : ((s : ℕ) : ZMod m).val = s := ZMod.val_natCast_of_lt hs
  rw [← h1, ← h2, h]

section Blades

variable (hm : 3 ≤ m) (hca : ∀ t s : ZMod m, c t ≠ a s) (hc : Function.Injective c)

include hm hca hc

omit [NeZero m] in
/-- The three edges of a blade of the necklace. -/
theorem triEdges_necklaceBlade (t : ZMod m) :
    triEdges ({c t, a t, c (t + 1)} : Finset V)
      = {s(c t, a t), s(c t, c (t + 1)), s(a t, c (t + 1))} :=
  triEdges_triple (hca t t) (fun h => (zmod_succ_ne (m := m) (by omega) t).symm (hc h))
    (fun h => hca (t + 1) t h.symm)

/-- Each walk edge of the necklace hub assignment lies on a blade. -/
theorem walkEdge_mem_coveredEdges (k : ZMod (3 * m)) :
    s(necklaceHub m c a k, necklaceHub m c a (k + 1))
      ∈ coveredEdges (necklaceTris m c a) := by
  have hm0 : 0 < m := by omega
  obtain ⟨n, hnlt, rfl⟩ : ∃ n : ℕ, n < 3 * m ∧ k = ((n : ℕ) : ZMod (3 * m)) :=
    ⟨k.val, ZMod.val_lt k, (ZMod.natCast_zmod_val k).symm⟩
  rw [show ((n : ZMod (3 * m)) + 1) = ((n + 1 : ℕ) : ZMod (3 * m)) by push_cast; ring]
  have key : ∀ t : ZMod m, ∀ e : Sym2 V, e ∈ triEdges ({c t, a t, c (t + 1)} : Finset V) →
      e ∈ coveredEdges (necklaceTris m c a) := by
    intro t e he
    refine Finset.mem_biUnion.mpr ⟨{c t, a t, c (t + 1)}, ?_, he⟩
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩
  rcases lt_or_ge n (2 * m) with hlt | hge
  · rcases Nat.even_or_odd n with hev | hodd
    · obtain ⟨t, ht⟩ := hev
      have htm : t < m := by omega
      rw [show n = 2 * t by omega, show 2 * t + 1 = 2 * t + 1 from rfl,
        necklaceHub_even htm, necklaceHub_odd htm]
      refine key (t : ZMod m) _ ?_
      rw [triEdges_necklaceBlade hm hca hc]
      simp
    · obtain ⟨t, ht⟩ := hodd
      have htm : t < m := by omega
      rw [show n = 2 * t + 1 by omega, show 2 * t + 1 + 1 = 2 * t + 2 by ring,
        necklaceHub_odd htm, necklaceHub_even_succ htm]
      refine key (t : ZMod m) _ ?_
      rw [triEdges_necklaceBlade hm hca hc]
      push_cast
      simp
  · obtain ⟨t, htm, rfl⟩ : ∃ t : ℕ, t < m ∧ n = 2 * m + t := ⟨n - 2 * m, by omega, by omega⟩
    rw [necklaceHub_late htm, necklaceHub_late_succ htm]
    refine key (t : ZMod m) _ ?_
    rw [triEdges_necklaceBlade hm hca hc]
    push_cast
    simp

/-- Every edge of the necklace is traversed by the hub walk. -/
theorem coveredEdges_subset_walkEdges :
    coveredEdges (necklaceTris m c a)
      ⊆ Finset.univ.image
          (fun k : ZMod (3 * m) => s(necklaceHub m c a k, necklaceHub m c a (k + 1))) := by
  have hm0 : 0 < m := by omega
  intro e he
  obtain ⟨T, hT, heT⟩ := Finset.mem_biUnion.mp he
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hT
  set r := t.val with hr
  have hrm : r < m := ZMod.val_lt t
  have hrt : ((r : ℕ) : ZMod m) = t := ZMod.natCast_zmod_val t
  have e1 : s(necklaceHub m c a ((2 * r : ℕ) : ZMod (3 * m)),
      necklaceHub m c a (((2 * r : ℕ) : ZMod (3 * m)) + 1)) = s(c t, a t) := by
    rw [show (((2 * r : ℕ) : ZMod (3 * m)) + 1) = ((2 * r + 1 : ℕ) : ZMod (3 * m)) by
      push_cast; ring, necklaceHub_even hrm, necklaceHub_odd hrm, hrt]
  have e2 : s(necklaceHub m c a ((2 * r + 1 : ℕ) : ZMod (3 * m)),
      necklaceHub m c a (((2 * r + 1 : ℕ) : ZMod (3 * m)) + 1)) = s(a t, c (t + 1)) := by
    rw [show (((2 * r + 1 : ℕ) : ZMod (3 * m)) + 1) = ((2 * r + 2 : ℕ) : ZMod (3 * m)) by
      push_cast; ring, necklaceHub_odd hrm, necklaceHub_even_succ hrm]
    push_cast
    rw [hrt]
  have e3 : s(necklaceHub m c a ((2 * m + r : ℕ) : ZMod (3 * m)),
      necklaceHub m c a (((2 * m + r : ℕ) : ZMod (3 * m)) + 1)) = s(c t, c (t + 1)) := by
    rw [show (((2 * m + r : ℕ) : ZMod (3 * m)) + 1) = ((2 * m + r + 1 : ℕ) : ZMod (3 * m)) by
      push_cast; ring, necklaceHub_late hrm, necklaceHub_late_succ hrm]
    push_cast
    rw [hrt]
  rw [triEdges_necklaceBlade hm hca hc] at heT
  simp only [Finset.mem_insert, Finset.mem_singleton] at heT
  rcases heT with rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, e1⟩
  · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, e3⟩
  · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, e2⟩

/-- **The necklace hub walk traverses exactly the necklace.** -/
theorem hubEdges_necklaceHub :
    hubEdges (necklaceHub m c a) (necklaceSucc m) = coveredEdges (necklaceTris m c a) := by
  rw [hubEdges_necklaceSucc]
  refine Finset.Subset.antisymm ?_ (coveredEdges_subset_walkEdges hm hca hc)
  intro e he
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp he
  exact walkEdge_mem_coveredEdges hm hca hc k

end Blades

/-! ### The necklace is a disjoint union of triangles -/

section Disjoint

variable (hm : 3 ≤ m) (hca : ∀ t s : ZMod m, c t ≠ a s) (hc : Function.Injective c)
  (ha : Function.Injective a)

include hm hca hc ha

omit [NeZero m] in
/-- Two distinct blades of a necklace with at least three blades share at most one vertex. -/
theorem card_inter_necklaceBlade_le_one {t s : ZMod m} (hts : t ≠ s) :
    (({c t, a t, c (t + 1)} : Finset V) ∩ ({c s, a s, c (s + 1)} : Finset V)).card ≤ 1 := by
  rw [Finset.card_le_one]
  have hsucc : ∀ u : ZMod m, u + 1 ≠ u := zmod_succ_ne (by omega)
  have hsucc2 : ∀ u : ZMod m, u + 1 + 1 ≠ u := zmod_succ_succ_ne hm
  -- an element of the intersection is `c t` (only if `t = s + 1`) or `c (t+1)` (only if `t+1 = s`)
  have hmem : ∀ x : V, x ∈ ({c t, a t, c (t + 1)} : Finset V) ∩ ({c s, a s, c (s + 1)} : Finset V) →
      (x = c t ∧ t = s + 1) ∨ (x = c (t + 1) ∧ t + 1 = s) := by
    intro x hx
    rw [Finset.mem_inter] at hx
    obtain ⟨hx1, hx2⟩ := hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
    rcases hx1 with rfl | rfl | rfl
    · rcases hx2 with h | h | h
      · exact absurd (hc h) hts
      · exact absurd h (hca _ _)
      · exact Or.inl ⟨rfl, hc h⟩
    · rcases hx2 with h | h | h
      · exact absurd h.symm (hca _ _)
      · exact absurd (ha h) hts
      · exact absurd h.symm (hca _ _)
    · rcases hx2 with h | h | h
      · exact Or.inr ⟨rfl, hc h⟩
      · exact absurd h (hca _ _)
      · exact absurd (hc h) (fun hh => hts (by rw [← add_left_inj 1, hh]))
  intro x hx y hy
  rcases hmem x hx with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;> rcases hmem y hy with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
  · rfl
  · exact absurd (by rw [h2, ← h1]) (hsucc2 t)
  · exact absurd (by rw [h1, ← h2]) (hsucc2 t)
  · rfl

/-- **The blades of a necklace are edge-disjoint.** -/
theorem edgeDisjoint_necklaceTris : EdgeDisjoint (necklaceTris m c a) := by
  intro T hT U hU hTU
  simp only [necklaceTris, Finset.mem_image, Finset.mem_univ, true_and] at hT hU
  obtain ⟨t, rfl⟩ := hT
  obtain ⟨s, rfl⟩ := hU
  have hts : t ≠ s := by rintro rfl; exact hTU rfl
  exact triEdges_disjoint_of_card_inter_le_one
    (card_inter_necklaceBlade_le_one hm hca hc ha hts)

omit [DecidableEq V] in
/-- **Distinct positions of the necklace walk traverse distinct edges**: the walk is an Eulerian
circuit of the necklace. -/
theorem walkEdge_injective :
    Function.Injective
      (fun k : ZMod (3 * m) => s(necklaceHub m c a k, necklaceHub m c a (k + 1))) := by
  have hs1 : ∀ u : ZMod m, u + 1 ≠ u := zmod_succ_ne (by omega)
  have hs2 : ∀ u : ZMod m, u + 1 + 1 ≠ u := zmod_succ_succ_ne hm
  intro k l hkl
  simp only at hkl
  rcases necklace_walkEdge_form (c := c) (a := a) k with
    ⟨t, htm, rfl, hk⟩ | ⟨t, htm, rfl, hk⟩ | ⟨t, htm, rfl, hk⟩ <;>
    rcases necklace_walkEdge_form (c := c) (a := a) l with
      ⟨s, hsm, rfl, hl⟩ | ⟨s, hsm, rfl, hl⟩ | ⟨s, hsm, rfl, hl⟩ <;>
    rw [hk, hl, Sym2.eq_iff] at hkl
  · rcases hkl with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [natCast_inj_of_lt htm hsm (hc h1)]
    · exact absurd h1 (hca _ _)
  · rcases hkl with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact absurd h1 (hca _ _)
    · exact absurd ((hc h1).symm.trans (ha h2)) (hs1 _)
  · rcases hkl with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact absurd h2.symm (hca _ _)
    · exact absurd h2.symm (hca _ _)
  · rcases hkl with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact absurd h1.symm (hca _ _)
    · have e := hc h2
      rw [ha h1] at e
      exact absurd e (hs1 _)
  · rcases hkl with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [natCast_inj_of_lt htm hsm (ha h1)]
    · exact absurd h1.symm (hca _ _)
  · rcases hkl with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1.symm (hca _ _)
    · exact absurd h1.symm (hca _ _)
  · rcases hkl with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact absurd h2 (hca _ _)
    · exact absurd h1 (hca _ _)
  · rcases hkl with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd h1 (hca _ _)
    · exact absurd h2 (hca _ _)
  · rcases hkl with ⟨h1, -⟩ | ⟨h1, h2⟩
    · rw [natCast_inj_of_lt htm hsm (hc h1)]
    · have e2 := hc h2
      rw [hc h1] at e2
      exact absurd e2 (hs2 _)

/-- **The hub edges of a necklace walk are decomposable**: they are the disjoint union of the
blades. -/
theorem triDecomposable_hubEdges_necklaceHub (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbl : ∀ t : ZMod m, G.IsNClique 3 ({c t, a t, c (t + 1)} : Finset V)) :
    TriDecomposable G (hubEdges (necklaceHub m c a) (necklaceSucc m)) := by
  rw [hubEdges_necklaceHub hm hca hc]
  refine TriDecomposable.of_family G ?_ (edgeDisjoint_necklaceTris hm hca hc ha)
  intro T hT
  simp only [necklaceTris, Finset.mem_image, Finset.mem_univ, true_and] at hT
  obtain ⟨t, rfl⟩ := hT
  exact hbl t

/-! ### The ear triangles of a necklace walk absorb the config -/

omit [NeZero m] hm hca hc ha in
/-- Covered edges are never loops. -/
theorem not_isDiag_of_mem_coveredEdges {P : Finset (Finset V)} {e : Sym2 V}
    (he : e ∈ coveredEdges P) : ¬ e.IsDiag := by
  obtain ⟨T, -, heT⟩ := Finset.mem_biUnion.mp he
  exact (Finset.mem_filter.mp heT).2

omit [NeZero m] hm hca hc ha in
/-- Two pairs spanning different edges meet in at most one vertex. -/
theorem card_inter_pair_le_one_of_sym2_ne {x y x' y' : V} (hxy : x ≠ y)
    (h : s(x, y) ≠ s(x', y')) :
    ((({x, y} : Finset V)) ∩ ({x', y'} : Finset V)).card ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  have hsub : ({x, y} : Finset V) ∩ ({x', y'} : Finset V) ⊆ ({x, y} : Finset V) :=
    Finset.inter_subset_left
  have hcard : ({x, y} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
  have heq : ({x, y} : Finset V) ∩ ({x', y'} : Finset V) = ({x, y} : Finset V) :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hxy' : ({x, y} : Finset V) ⊆ ({x', y'} : Finset V) := by
    rw [← heq]; exact Finset.inter_subset_right
  have hx : x = x' ∨ x = y' := by simpa using hxy' (by simp : x ∈ ({x, y} : Finset V))
  have hy : y = x' ∨ y = y' := by simpa using hxy' (by simp : y ∈ ({x, y} : Finset V))
  refine h ?_
  rcases hx with rfl | rfl
  · rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · rfl
  · rcases hy with rfl | rfl
    · exact Sym2.eq_swap
    · exact absurd rfl hxy

omit ha in
/-- Consecutive hubs of a necklace walk are distinct. -/
theorem necklaceHub_step_ne (k : ZMod (3 * m)) :
    necklaceHub m c a k ≠ necklaceHub m c a (k + 1) := by
  have := not_isDiag_of_mem_coveredEdges (walkEdge_mem_coveredEdges hm hca hc k)
  simpa using this

/-- **Distinct positions of a necklace walk use distinct hub pairs.**  This is the hypothesis
`hpair` of `localAbsorbable_earTris`. -/
theorem card_inter_necklaceHub_pair_le_one (i j : ZMod (3 * m)) (hij : i ≠ j) :
    ((({necklaceHub m c a ((necklaceSucc m).symm i), necklaceHub m c a i} : Finset V)) ∩
      ({necklaceHub m c a ((necklaceSucc m).symm j), necklaceHub m c a j} : Finset V)).card
      ≤ 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by ring⟩
  obtain ⟨l, rfl⟩ : ∃ l, j = l + 1 := ⟨j - 1, by ring⟩
  have hkl : k ≠ l := fun h => hij (by rw [h])
  rw [necklaceSucc_symm_apply, necklaceSucc_symm_apply, add_sub_cancel_right,
    add_sub_cancel_right]
  refine card_inter_pair_le_one_of_sym2_ne (necklaceHub_step_ne hm hca hc k) ?_
  intro h
  exact hkl (walkEdge_injective hm hca hc ha h)

/-- **A single cycle of length `3m ≥ 9` is absorbed by its `3m` ear triangles along a triangle
necklace.**  Unlike the friendship gadget of `FriendshipHub.lean`, every hub of the necklace has
bounded degree: `c t` is adjacent to the four config vertices at the positions `2t`, `2t+1`,
`2m+t`, `2m+t+1` and to the four hubs `a t`, `a (t-1)`, `c (t+1)`, `c (t-1)`, and `a t` only to two
config vertices and two hubs.  Hence a necklace serves configs of unbounded size. -/
theorem localAbsorbable_earTris_necklace (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : ZMod (3 * m) → V) (hv : Function.Injective v)
    (hcv : ∀ (t : ZMod m) (i : ZMod (3 * m)), c t ≠ v i)
    (hav : ∀ (t : ZMod m) (i : ZMod (3 * m)), a t ≠ v i)
    (hsub : ∀ i, G.IsNClique 3
      ({v i, necklaceHub m c a i, v (necklaceSucc m i)} : Finset V))
    (hear : ∀ i, G.IsNClique 3
      ({necklaceHub m c a ((necklaceSucc m).symm i), v i, necklaceHub m c a i} : Finset V))
    (hbl : ∀ t : ZMod m, G.IsNClique 3 ({c t, a t, c (t + 1)} : Finset V)) :
    LocalAbsorbable G (earTris v (necklaceHub m c a) (necklaceSucc m))
      (cycEdges v (necklaceSucc m)) := by
  have hzv : ∀ (i j : ZMod (3 * m)), necklaceHub m c a i ≠ v j := by
    intro i j
    rw [necklaceHub]
    split_ifs
    exacts [hcv _ _, hav _ _, hcv _ _]
  have hstep : ∀ i, necklaceHub m c a i ≠ necklaceHub m c a (necklaceSucc m i) :=
    necklaceHub_step_ne hm hca hc
  have hfix : ∀ i : ZMod (3 * m), necklaceSucc m i ≠ i := zmod_succ_ne (by omega)
  have hsq : ∀ i : ZMod (3 * m), necklaceSucc m (necklaceSucc m i) ≠ i :=
    zmod_succ_succ_ne (by omega)
  exact localAbsorbable_earTris G hv hzv hstep hfix hsq
    (card_inter_necklaceHub_pair_le_one hm hca hc ha) hsub hear
    (triDecomposable_hubEdges_necklaceHub hm hca hc ha G hbl)

/-! ### The necklace gadget in terms of adjacencies -/

omit [DecidableEq V] hm hca hc ha in
/-- Consecutive hubs of a necklace walk are adjacent: every walk edge is a blade edge. -/
theorem necklaceHub_adj_step (G : SimpleGraph V) [DecidableRel G.Adj]
    (hb1 : ∀ t : ZMod m, G.Adj (c t) (a t)) (hb2 : ∀ t : ZMod m, G.Adj (a t) (c (t + 1)))
    (hb3 : ∀ t : ZMod m, G.Adj (c t) (c (t + 1))) (k : ZMod (3 * m)) :
    G.Adj (necklaceHub m c a k) (necklaceHub m c a (k + 1)) := by
  have hpair : ∀ x y u w : V, s(x, y) = s(u, w) → G.Adj u w → G.Adj x y := by
    intro x y u w h hadj
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hadj
    · exact hadj.symm
  rcases necklace_walkEdge_form (c := c) (a := a) k with
    ⟨t, -, -, hk⟩ | ⟨t, -, -, hk⟩ | ⟨t, -, -, hk⟩
  · exact hpair _ _ _ _ hk (hb1 _)
  · exact hpair _ _ _ _ hk (hb2 _)
  · exact hpair _ _ _ _ hk (hb3 _)

/-- **The necklace gadget, in terms of adjacencies.**  A config which is a single cycle of length
`3m ≥ 9` is absorbed by its `3m` ear triangles as soon as: the config is a cycle of `G`, every hub
is adjacent to the two config vertices of its walk position, and the blades are triangles of `G`.
All hub demands are bounded (at most eight prescribed neighbours per hub), independently of the
length of the config. -/
theorem localAbsorbable_necklace_of_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : ZMod (3 * m) → V) (hv : Function.Injective v)
    (hcv : ∀ (t : ZMod m) (i : ZMod (3 * m)), c t ≠ v i)
    (hav : ∀ (t : ZMod m) (i : ZMod (3 * m)), a t ≠ v i)
    (hcyc : ∀ i : ZMod (3 * m), G.Adj (v i) (v (i + 1)))
    (hz1 : ∀ i : ZMod (3 * m), G.Adj (necklaceHub m c a i) (v i))
    (hz2 : ∀ i : ZMod (3 * m), G.Adj (necklaceHub m c a i) (v (i + 1)))
    (hb1 : ∀ t : ZMod m, G.Adj (c t) (a t)) (hb2 : ∀ t : ZMod m, G.Adj (a t) (c (t + 1)))
    (hb3 : ∀ t : ZMod m, G.Adj (c t) (c (t + 1))) :
    LocalAbsorbable G (earTris v (necklaceHub m c a) (necklaceSucc m))
      (cycEdges v (necklaceSucc m)) := by
  refine localAbsorbable_earTris_necklace hm hca hc ha G v hv hcv hav ?_ ?_ ?_
  · intro i
    exact SimpleGraph.is3Clique_triple_iff.2 ⟨(hz1 i).symm, hcyc i, hz2 i⟩
  · intro i
    have hstep := necklaceHub_adj_step (c := c) (a := a) G hb1 hb2 hb3 ((necklaceSucc m).symm i)
    rw [necklaceSucc_symm_apply] at hstep ⊢
    rw [sub_add_cancel] at hstep
    refine SimpleGraph.is3Clique_triple_iff.2 ⟨?_, hstep, (hz1 i).symm⟩
    have := hz2 (i - 1)
    rwa [sub_add_cancel] at this
  · intro t
    exact SimpleGraph.is3Clique_triple_iff.2 ⟨hb1 t, hb3 t, hb2 t⟩

end Disjoint

end Necklace

/-! ### Non-vacuity: a nine-cycle absorbed along a three-blade necklace in `K₁₅` -/

/-- The nine config vertices of a nine-cycle. -/
def necV : ZMod 9 → Fin 15 := ![0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- The three "shared" hubs of the necklace. -/
def necC : ZMod 3 → Fin 15 := ![9, 10, 11]

/-- The three "private" hubs of the necklace. -/
def necA : ZMod 3 → Fin 15 := ![12, 13, 14]

/-- The hub walk of the necklace traverses the three blades `{9,12,10}`, `{10,13,11}`,
`{11,14,9}`. -/
theorem hubEdges_necV :
    hubEdges (necklaceHub 3 necC necA) (necklaceSucc 3)
      = ({s(9, 12), s(12, 10), s(9, 10), s(10, 13), s(13, 11), s(10, 11), s(11, 14), s(14, 9),
          s(11, 9)} : Finset (Sym2 (Fin 15))) := by
  decide

/-- Nine reserved ear triangles — one per edge of the nine-cycle. -/
theorem card_earTris_necV :
    (earTris necV (necklaceHub 3 necC necA) (necklaceSucc 3)).card = 9 := by decide

/-- **The necklace gadget really produces absorbers, for configs beyond the reach of a single
friendship hub.**  In `K₁₅` the nine ear triangles of the necklace walk with blades `{9,12,10}`,
`{10,13,11}`, `{11,14,9}` locally absorb the nine-cycle `0-1-2-3-4-5-6-7-8`.  No hub is adjacent
to more than four config vertices, so — unlike the friendship centre — the same pattern scales to
configs of unbounded length. -/
theorem localAbsorbable_necV :
    LocalAbsorbable (⊤ : SimpleGraph (Fin 15))
      (earTris necV (necklaceHub 3 necC necA) (necklaceSucc 3))
      (cycEdges necV (necklaceSucc 3)) :=
  localAbsorbable_necklace_of_adj (m := 3) (by norm_num) (by decide) (by decide) (by decide)
    (⊤ : SimpleGraph (Fin 15)) necV (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

end Ax2.BKLO
