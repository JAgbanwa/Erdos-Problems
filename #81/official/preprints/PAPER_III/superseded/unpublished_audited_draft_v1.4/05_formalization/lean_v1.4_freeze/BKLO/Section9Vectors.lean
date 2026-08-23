/-
# BKLO §9 for `r = 2`, `F = K₃`: the parity vectors of triangles

The parity vector of an edge set `E` is the family of numbers `d_E(x, W) mod 2`, indexed by the
pairs `(x, W)` with `W` a part of the partition `P` and `x ∈ V_{<W}`.  This file computes the
parity vector of a single triangle and provides the elementary algebra of these vectors:

* `BKLO.vecOf T` — the parity vector of the triangle `T`;
* `BKLO.uvec u W` — the "unit" vector supported on the single coordinate `(u, W)`;
* `BKLO.vecOf_two_in_part` — if two of the three vertices of `T` lie in a common part, the parity
  vector of `T` is, on admissible coordinates, the sum of the two units in the column of the third
  vertex;
* `BKLO.vecOf_move` — replacing one vertex of a transversal triangle by another vertex of the same
  part changes the parity vector by two "column" pairs.

Everything here is `sorry`-free.
-/
import BKLO.ParityFamily

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The parity vector of a triangle -/

/-- The parity vector of the triangle `T`: `(x, W) ↦ d_{K(T)}(x, W) mod 2`. -/
def vecOf (T : Finset V) : V → Finset V → ZMod 2 :=
  fun x W => ((degTo (cliqueEdges T) x W : ℕ) : ZMod 2)

/-- The unit vector supported on the coordinate `(u, W)`. -/
def uvec (u : V) (W : Finset V) : V → Finset V → ZMod 2 :=
  fun x W' => if x = u ∧ W' = W then 1 else 0

@[simp] theorem uvec_apply_self (u : V) (W : Finset V) : uvec u W u W = 1 := by simp [uvec]

theorem uvec_eq_zero_of_ne_left {u x : V} (h : x ≠ u) (W W' : Finset V) : uvec u W x W' = 0 := by
  simp [uvec, h]

theorem uvec_self_apply (u : V) (W W' : Finset V) :
    uvec u W u W' = if W' = W then 1 else 0 := by
  simp [uvec]

/-- `d_{K(T)}(x, W)` counts the vertices of `T` other than `x` lying in `W` (and is `0` when
`x ∉ T`). -/
theorem degTo_cliqueEdges_eq (T W : Finset V) (x : V) :
    degTo (cliqueEdges T) x W = if x ∈ T then (W ∩ T.erase x).card else 0 := by
  classical
  by_cases hx : x ∈ T
  · rw [if_pos hx]
    have : nbhdIn (cliqueEdges T) x W = W ∩ T.erase x := by
      ext y
      simp only [mem_nbhdIn, Finset.mem_inter, Finset.mem_erase, mem_cliqueEdgesV,
        Sym2.mem_iff, Sym2.isDiag_iff_proj_eq]
      constructor
      · rintro ⟨hyW, hall, hne⟩
        exact ⟨hyW, fun h => hne (h ▸ rfl), hall y (Or.inr rfl)⟩
      · rintro ⟨hyW, hyx, hyT⟩
        refine ⟨hyW, ?_, fun h => hyx h.symm⟩
        rintro z (rfl | rfl)
        · exact hx
        · exact hyT
    rw [degTo, this]
  · rw [if_neg hx]
    have : nbhdIn (cliqueEdges T) x W = ∅ := by
      ext y
      simp only [mem_nbhdIn, Finset.notMem_empty, iff_false, not_and]
      intro _ hmem
      rw [mem_cliqueEdgesV] at hmem
      exact hx (hmem.1 x (by simp))
    rw [degTo, this]
    rfl

theorem vecOf_eq_zero_of_notMem {T : Finset V} {x : V} (hx : x ∉ T) (W : Finset V) :
    vecOf T x W = 0 := by
  simp [vecOf, degTo_cliqueEdges_eq, hx]

/-- The value of the parity vector of `{a, b, c}` at the coordinate `(a, W)`. -/
theorem vecOf_val {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (W : Finset V) :
    vecOf ({a, b, c} : Finset V) a W
      = (if b ∈ W then 1 else 0) + (if c ∈ W then 1 else 0) := by
  classical
  have hmem : a ∈ ({a, b, c} : Finset V) := by simp
  have herase : ({a, b, c} : Finset V).erase a = {b, c} := by
    ext y
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hy, rfl | rfl | rfl⟩
      · exact absurd rfl hy
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨fun h => hab h.symm, by simp⟩
      · exact ⟨fun h => hac h.symm, by simp⟩
  have hcard : (W ∩ ({b, c} : Finset V)).card
      = (if b ∈ W then 1 else 0) + (if c ∈ W then 1 else 0) := by
    by_cases hb : b ∈ W <;> by_cases hc : c ∈ W
    · have : W ∩ ({b, c} : Finset V) = {b, c} := by
        ext y; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · tauto
        · rintro (rfl | rfl) <;> simp_all
      rw [this, Finset.card_pair hbc, if_pos hb, if_pos hc]
    · have : W ∩ ({b, c} : Finset V) = {b} := by
        ext y; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hyW, rfl | rfl⟩
          · rfl
          · exact absurd hyW hc
        · rintro rfl; exact ⟨hb, by simp⟩
      rw [this, Finset.card_singleton, if_pos hb, if_neg hc]
    · have : W ∩ ({b, c} : Finset V) = {c} := by
        ext y; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hyW, rfl | rfl⟩
          · exact absurd hyW hb
          · rfl
        · rintro rfl; exact ⟨hc, by simp⟩
      rw [this, Finset.card_singleton, if_neg hb, if_pos hc]
    · have : W ∩ ({b, c} : Finset V) = ∅ := by
        ext y; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
          Finset.notMem_empty, iff_false, not_and]
        rintro hyW (rfl | rfl)
        · exact hb hyW
        · exact hc hyW
      rw [this, Finset.card_empty, if_neg hb, if_neg hc]
  rw [vecOf, degTo_cliqueEdges_eq, if_pos hmem, herase, hcard]
  push_cast
  rfl

/-! ### Permuting the vertices of a triangle -/

theorem triple_swap₁ (a b c : V) : ({a, b, c} : Finset V) = {b, a, c} :=
  Finset.insert_comm a b {c}

theorem triple_swap₂ (a b c : V) : ({a, b, c} : Finset V) = {c, a, b} := by
  ext y; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

/-! ### Parts -/

section Parts

variable {P : Finset (Finset V)} {idx : Finset V → ℕ}

/-- In a partition, a vertex determines its part. -/
theorem part_unique (hdisj : ∀ W ∈ P, ∀ W' ∈ P, W ≠ W' → Disjoint W W')
    {A B : Finset V} (hA : A ∈ P) (hB : B ∈ P) {x : V} (hxA : x ∈ A) (hxB : x ∈ B) : A = B := by
  by_contra hne
  exact (Finset.disjoint_left.1 (hdisj A hA B hB hne) hxA) hxB

theorem mem_part_iff (hdisj : ∀ W ∈ P, ∀ W' ∈ P, W ≠ W' → Disjoint W W')
    {A W : Finset V} (hA : A ∈ P) (hW : W ∈ P) {x : V} (hxA : x ∈ A) :
    x ∈ W ↔ W = A :=
  ⟨fun hx => part_unique hdisj hW hA hx hxA, fun h => h ▸ hxA⟩

/-- An admissible coordinate `(x, W)` forces the part of `x` to precede `W`. -/
theorem idx_lt_of_mem_beforeParts (hdisj : ∀ W ∈ P, ∀ W' ∈ P, W ≠ W' → Disjoint W W')
    {A W : Finset V} (hA : A ∈ P) {x : V} (hxA : x ∈ A) (hx : x ∈ beforeParts P idx W) :
    idx A < idx W := by
  obtain ⟨A', hA', hlt, hxA'⟩ := mem_beforeParts.1 hx
  rwa [part_unique hdisj hA hA' hxA hxA']

end Parts

/-! ### The parity vector of a triangle in terms of the parts -/

section Vectors

variable {P : Finset (Finset V)} {idx : Finset V → ℕ}
  (hdisj : ∀ W ∈ P, ∀ W' ∈ P, W ≠ W' → Disjoint W W')

include hdisj

/-- The value of the parity vector of `{a, b, c}` at `(a, W)`, in terms of the parts of `b`
and `c`. -/
theorem vecOf_val_parts {B C W : Finset V} (hB : B ∈ P) (hC : C ∈ P) (hW : W ∈ P)
    {a b c : V} (hb : b ∈ B) (hc : c ∈ C) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    vecOf ({a, b, c} : Finset V) a W
      = (if W = B then 1 else 0) + (if W = C then 1 else 0) := by
  rw [vecOf_val hab hac hbc]
  have h1 : (b ∈ W) ↔ (W = B) := mem_part_iff hdisj hB hW hb
  have h2 : (c ∈ W) ↔ (W = C) := mem_part_iff hdisj hC hW hc
  have e1 : (if b ∈ W then (1 : ZMod 2) else 0) = if W = B then 1 else 0 := by
    by_cases h : W = B
    · rw [if_pos (h1.2 h), if_pos h]
    · rw [if_neg (fun hh => h (h1.1 hh)), if_neg h]
  have e2 : (if c ∈ W then (1 : ZMod 2) else 0) = if W = C then 1 else 0 := by
    by_cases h : W = C
    · rw [if_pos (h2.2 h), if_pos h]
    · rw [if_neg (fun hh => h (h2.1 hh)), if_neg h]
  rw [e1, e2]

/-- **A triangle with two vertices in one part.**  If `b, c` lie in the part `B` and `a` lies in
the part `A`, then, on admissible coordinates, the parity vector of `{a, b, c}` is the sum of the
two units `(b, A)` and `(c, A)`. -/
theorem vecOf_two_in_part {A B : Finset V} (hA : A ∈ P) (hB : B ∈ P)
    {a b c : V} (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ B)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {W : Finset V} (hW : W ∈ P) {x : V} (hx : x ∈ beforeParts P idx W) :
    vecOf ({a, b, c} : Finset V) x W = uvec b A x W + uvec c A x W := by
  classical
  have hz : ∀ z : ZMod 2, z + z = 0 := by decide +kernel
  by_cases hxa : x = a
  · subst hxa
    rw [vecOf_val_parts hdisj hB hB hW hb hc hab hac hbc,
      uvec_eq_zero_of_ne_left hab A W, uvec_eq_zero_of_ne_left hac A W]
    simp only [add_zero]
    exact hz _
  · by_cases hxb : x = b
    · subst hxb
      have hWne : W ≠ B := by
        intro h
        exact absurd (idx_lt_of_mem_beforeParts hdisj hB hb (h ▸ hx)) (by simp)
      rw [triple_swap₁ a x c,
        vecOf_val_parts hdisj hA hB hW ha hc (Ne.symm hab) hbc hac,
        uvec_eq_zero_of_ne_left hbc A W, uvec_self_apply, if_neg hWne]
    · by_cases hxc : x = c
      · subst hxc
        have hWne : W ≠ B := by
          intro h
          exact absurd (idx_lt_of_mem_beforeParts hdisj hB hc (h ▸ hx)) (by simp)
        rw [triple_swap₂ a b x,
          vecOf_val_parts hdisj hA hB hW ha hb (Ne.symm hac) (Ne.symm hbc) hab,
          uvec_eq_zero_of_ne_left (Ne.symm hbc) A W, uvec_self_apply, if_neg hWne]
        ring
      · rw [vecOf_eq_zero_of_notMem (by simp [hxa, hxb, hxc]),
          uvec_eq_zero_of_ne_left hxb A W, uvec_eq_zero_of_ne_left hxc A W]
        ring

/-- **Moving one vertex of a transversal triangle.**  If `a, a'` lie in the part `A`, `b` in the
part `B` and `c` in the part `C`, with `A, B, C` distinct parts, then the parity vectors of
`{a, b, c}` and `{a', b, c}` differ by the two "column" pairs in the columns `B` and `C`. -/
theorem vecOf_move {A B C : Finset V} (hA : A ∈ P) (hB : B ∈ P) (hC : C ∈ P)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    {a a' b c : V} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hc : c ∈ C)
    {W : Finset V} (hW : W ∈ P) (x : V) :
    vecOf ({a, b, c} : Finset V) x W + vecOf ({a', b, c} : Finset V) x W
      = (uvec a B x W + uvec a' B x W) + (uvec a C x W + uvec a' C x W) := by
  classical
  have hab : a ≠ b := fun h => hAB (part_unique hdisj hA hB ha (h ▸ hb))
  have hac : a ≠ c := fun h => hAC (part_unique hdisj hA hC ha (h ▸ hc))
  have ha'b : a' ≠ b := fun h => hAB (part_unique hdisj hA hB ha' (h ▸ hb))
  have ha'c : a' ≠ c := fun h => hAC (part_unique hdisj hA hC ha' (h ▸ hc))
  have hbc : b ≠ c := fun h => hBC (part_unique hdisj hB hC hb (h ▸ hc))
  have h2 : ∀ z : ZMod 2, z + z = 0 := by decide +kernel
  rcases eq_or_ne a a' with rfl | haa'
  · simp only [h2]
  by_cases hxa : x = a
  · subst hxa
    rw [vecOf_val_parts hdisj hB hC hW hb hc hab hac hbc,
      vecOf_eq_zero_of_notMem (by simp [haa', hab, hac]),
      uvec_eq_zero_of_ne_left haa' B W, uvec_eq_zero_of_ne_left haa' C W,
      uvec_self_apply, uvec_self_apply]
    ring
  · by_cases hxa' : x = a'
    · subst hxa'
      rw [vecOf_eq_zero_of_notMem (by simp [hxa, ha'b, ha'c]),
        vecOf_val_parts hdisj hB hC hW hb hc ha'b ha'c hbc,
        uvec_eq_zero_of_ne_left hxa B W, uvec_eq_zero_of_ne_left hxa C W,
        uvec_self_apply, uvec_self_apply]
      ring
    · by_cases hxb : x = b
      · subst hxb
        rw [triple_swap₁ a x c, triple_swap₁ a' x c,
          vecOf_val_parts hdisj hA hC hW ha hc (Ne.symm hab) hbc hac,
          vecOf_val_parts hdisj hA hC hW ha' hc (Ne.symm ha'b) hbc ha'c,
          uvec_eq_zero_of_ne_left hxa B W, uvec_eq_zero_of_ne_left hxa' B W,
          uvec_eq_zero_of_ne_left hxa C W, uvec_eq_zero_of_ne_left hxa' C W]
        simp only [add_zero]
        exact h2 _
      · by_cases hxc : x = c
        · subst hxc
          rw [triple_swap₂ a b x, triple_swap₂ a' b x,
            vecOf_val_parts hdisj hA hB hW ha hb (Ne.symm hac) (Ne.symm hbc) hab,
            vecOf_val_parts hdisj hA hB hW ha' hb (Ne.symm ha'c) (Ne.symm hbc) ha'b,
            uvec_eq_zero_of_ne_left hxa B W, uvec_eq_zero_of_ne_left hxa' B W,
            uvec_eq_zero_of_ne_left hxa C W, uvec_eq_zero_of_ne_left hxa' C W]
          simp only [add_zero]
          exact h2 _
        · rw [vecOf_eq_zero_of_notMem (by simp [hxa, hxb, hxc]),
            vecOf_eq_zero_of_notMem (by simp [hxa', hxb, hxc]),
            uvec_eq_zero_of_ne_left hxa B W, uvec_eq_zero_of_ne_left hxa' B W,
            uvec_eq_zero_of_ne_left hxa C W, uvec_eq_zero_of_ne_left hxa' C W]
          ring

end Vectors

/-! ### Vectors reachable by subfamilies -/

/-- `f` is *reachable* from the triangle family `𝒯`: some subfamily of `𝒯` has parity vector `f`
(on the admissible coordinates). -/
def Reach (P : Finset (Finset V)) (idx : Finset V → ℕ) (𝒯 : Finset (Finset V))
    (f : V → Finset V → ZMod 2) : Prop :=
  ∃ 𝒮 : Finset (Finset V), 𝒮 ⊆ 𝒯 ∧ ∀ W ∈ P, ∀ x ∈ beforeParts P idx W, flipv 𝒮 x W = f x W

theorem Reach.zero (P : Finset (Finset V)) (idx : Finset V → ℕ) (𝒯 : Finset (Finset V)) :
    Reach P idx 𝒯 (fun _ _ => 0) := by
  refine ⟨∅, Finset.empty_subset _, fun W _ x _ => ?_⟩
  simp [flipv, famEdges, degTo, nbhdIn]

theorem Reach.mono {P : Finset (Finset V)} {idx : Finset V → ℕ} {𝒯 𝒯' : Finset (Finset V)}
    (h : 𝒯 ⊆ 𝒯') {f : V → Finset V → ZMod 2} (hf : Reach P idx 𝒯 f) : Reach P idx 𝒯' f := by
  obtain ⟨𝒮, hs, hv⟩ := hf
  exact ⟨𝒮, hs.trans h, hv⟩

theorem Reach.congr {P : Finset (Finset V)} {idx : Finset V → ℕ} {𝒯 : Finset (Finset V)}
    {f g : V → Finset V → ZMod 2} (hf : Reach P idx 𝒯 f)
    (h : ∀ W ∈ P, ∀ x ∈ beforeParts P idx W, f x W = g x W) : Reach P idx 𝒯 g := by
  obtain ⟨𝒮, hs, hv⟩ := hf
  exact ⟨𝒮, hs, fun W hW x hx => (hv W hW x hx).trans (h W hW x hx)⟩

theorem Reach.add {P : Finset (Finset V)} {idx : Finset V → ℕ} {𝒯 : Finset (Finset V)}
    (hfam : IsTriFamily 𝒯) {f g : V → Finset V → ZMod 2}
    (hf : Reach P idx 𝒯 f) (hg : Reach P idx 𝒯 g) :
    Reach P idx 𝒯 (fun x W => f x W + g x W) := by
  obtain ⟨𝒮₁, hs₁, hv₁⟩ := hf
  obtain ⟨𝒮₂, hs₂, hv₂⟩ := hg
  refine ⟨symmDiff 𝒮₁ 𝒮₂, ?_, fun W hW x hx => ?_⟩
  · intro T hT
    rcases Finset.mem_symmDiff.1 hT with ⟨h, -⟩ | ⟨h, -⟩
    · exact hs₁ h
    · exact hs₂ h
  · rw [flipv_symmDiff hfam hs₁ hs₂, hv₁ W hW x hx, hv₂ W hW x hx]

theorem Reach.of_mem {P : Finset (Finset V)} {idx : Finset V → ℕ} {𝒯 : Finset (Finset V)}
    {T : Finset V} (hT : T ∈ 𝒯) : Reach P idx 𝒯 (vecOf T) := by
  refine ⟨{T}, Finset.singleton_subset_iff.2 hT, fun W _ x _ => ?_⟩
  have h : famEdges ({T} : Finset (Finset V)) = cliqueEdges T := by
    simp [famEdges]
  rw [flipv, h, vecOf]

end BKLO
