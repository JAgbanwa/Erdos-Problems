/-
# Nibble — the coupled dyadic gate at **arbitrary granularity**, and the general "coupling is free"

`Nibble.CoupledDyadicGate` settles the 3-way coherence gate of the laminar (dyadic) route with one
explicit instance, at one fixed block scale (`τ = 1 slot`, blocks of relative size `1/4` and `1/8`
of a cluster).  The residual `Nibble.AX1.BlockCoverResidualCoupled` however needs blocks of
*vanishing* relative size, so the instance is only convincing if the exact tiling survives
refinement.  This file proves that it does, at every granularity — and it proves the underlying
fact in general, for an arbitrary cluster set and an arbitrary family of members.

## The sum-zero blow-up

Blow every cluster up by a factor `r+1`: an atom of the scaled instance is a pair `(α, a)` with
`α : ZMod (r+1)` a *copy index* and `a` an atom of the base instance.  Each base member `m`, which
meets exactly three clusters, is replicated `(r+1)²` times, one copy per pair `(a, b)` of
`ZMod (r+1)`; the copy places its `c`-block inside the copy `cShift m c a b` of the cluster `c`,
where the three clusters that `m` meets — in the order of a fixed indexing of the clusters —
receive the copy indices `a`, `b` and `-(a+b)`: a **sum-zero (Latin) rule**.

For any two of the three clusters, the two copy indices they receive form a *bijection*
`(a,b) ↦ (·,·)` of `ZMod (r+1) × ZMod (r+1)` (`Nibble.AX1.cShift_existsUnique`).  Hence at every
cluster pair the `(r+1)²` copies of one member spread over the `(r+1)²` copy-cells of that pair
exactly once each, and the cover count of the scaled family at a cell `((α,a),(β,b))` equals the
cover count of the base family at `(a,b)`: **the three-way coupling is free**
(`Nibble.AX1.cCover_eq`), for every base family and every blow-up factor.

## Consequence for the gate instance

Applied to `Nibble.AX1.gateFamily` this gives `Nibble.AX1.scaled_exact_tiling`: for every `r`, the
scaled family covers every cell of every one of the six cluster-pair squares **exactly once**,
while the blocks have relative size `≤ 1/(4(r+1)) → 0`
(`Nibble.AX1.scaled_block_relative_size`) and are still laminar/dyadic inside their copy
(`Nibble.AX1.scaled_block_dyadic`).  So the positive answer to the coherence gate is not an
artefact of the coarse scale of the instance.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoupledDyadicGate
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.IntervalCases

open Finset

namespace Nibble.AX1

/-! ## 0. Generic counting helpers -/

private theorem countP_univ_toList {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (Finset.univ : Finset α).toList.countP (fun a => decide (p a)) = #(Finset.univ.filter p) := by
  rw [← Multiset.coe_countP, Finset.coe_toList, Multiset.countP_eq_card_filter]
  rfl

private theorem card_filter_eq_one {α : Type*} [Fintype α] [DecidableEq α] (p : α → Prop)
    [DecidablePred p] (h : ∃! a, p a) : #(Finset.univ.filter p) = 1 := by
  obtain ⟨a, ha, hu⟩ := h
  rw [Finset.card_eq_one]
  refine ⟨a, Finset.eq_singleton_iff_unique_mem.2 ⟨by simp [ha], ?_⟩⟩
  intro x hx
  exact hu x (Finset.mem_filter.1 hx).2

private theorem sum_map_eq_countP {α : Type*} (l : List α) (g : α → ℕ) (q : α → Bool)
    (h : ∀ m ∈ l, g m = if q m then 1 else 0) : (l.map g).sum = l.countP q := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.sum_cons, List.countP_cons,
        h a (List.mem_cons_self ..), ih (fun m hm => h m (List.mem_cons_of_mem _ hm))]
      by_cases hq : q a
      · simp [hq]; omega
      · simp [hq]

/-! ## 1. The sum-zero rule and its bijectivity -/

private theorem exU12 {A : Type*} (u v : A) : ∃! p : A × A, u = p.1 ∧ v = p.2 := by
  refine ⟨(u, v), ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨x, y⟩ ⟨h1, h2⟩
  simp_all

private theorem exU21 {A : Type*} (u v : A) : ∃! p : A × A, u = p.2 ∧ v = p.1 := by
  refine ⟨(v, u), ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨x, y⟩ ⟨h1, h2⟩
  simp_all

section Forms

variable {A : Type*} [AddCommGroup A]

private theorem exU13 (u v : A) : ∃! p : A × A, u = p.1 ∧ v = -(p.1 + p.2) := by
  refine ⟨(u, -v - u), ⟨rfl, by simp [sub_eq_add_neg]⟩, ?_⟩
  rintro ⟨x, y⟩ ⟨h1, h2⟩
  simp only at h1 h2
  subst h1; subst h2
  refine Prod.ext_iff.2 ⟨rfl, ?_⟩
  simp [sub_eq_add_neg]

private theorem exU31 (u v : A) : ∃! p : A × A, u = -(p.1 + p.2) ∧ v = p.1 := by
  refine ⟨(v, -u - v), ⟨by simp [sub_eq_add_neg], rfl⟩, ?_⟩
  rintro ⟨x, y⟩ ⟨h1, h2⟩
  simp only at h1 h2
  subst h2; subst h1
  refine Prod.ext_iff.2 ⟨rfl, ?_⟩
  simp [sub_eq_add_neg]

private theorem exU23 (u v : A) : ∃! p : A × A, u = p.2 ∧ v = -(p.1 + p.2) := by
  refine ⟨(-v - u, u), ⟨rfl, by simp [sub_eq_add_neg]⟩, ?_⟩
  rintro ⟨x, y⟩ ⟨h1, h2⟩
  simp only at h1 h2
  subst h1; subst h2
  refine Prod.ext_iff.2 ⟨?_, rfl⟩
  simp [sub_eq_add_neg]

private theorem exU32 (u v : A) : ∃! p : A × A, u = -(p.1 + p.2) ∧ v = p.2 := by
  refine ⟨(-u - v, v), ⟨by simp [sub_eq_add_neg], rfl⟩, ?_⟩
  rintro ⟨x, y⟩ ⟨h1, h2⟩
  simp only at h1 h2
  subst h2; subst h1
  refine Prod.ext_iff.2 ⟨?_, rfl⟩
  simp [sub_eq_add_neg]

/-- The sum-zero rule as a function of the *rank* `i ∈ {0,1,2}` of a cluster in the (ordered)
triple of clusters a member meets: the ranks `0`, `1`, `2` get the copy indices `a`, `b`,
`-(a+b)`. -/
def cPick (i : ℕ) (a b : A) : A := if i = 0 then a else if i = 1 then b else -(a + b)

/-- **Two of the three sum-zero indices determine the pair `(a,b)`**: the map
`(a,b) ↦ (cPick i a b, cPick j a b)` is a bijection of `A × A` for distinct ranks `i ≠ j` in
`{0,1,2}`.  This is the whole content of "the coupling is free". -/
theorem cPick_existsUnique {i j : ℕ} (hi : i < 3) (hj : j < 3) (hij : i ≠ j) (u v : A) :
    ∃! p : A × A, u = cPick i p.1 p.2 ∧ v = cPick j p.1 p.2 := by
  interval_cases i <;> interval_cases j <;> simp only [cPick, reduceIte] <;>
    first
      | exact absurd rfl hij
      | exact exU12 u v
      | exact exU13 u v
      | exact exU21 u v
      | exact exU23 u v
      | exact exU31 u v
      | exact exU32 u v

end Forms

/-! ## 2. The general sum-zero blow-up -/

section General

variable {C A : Type*} [Fintype C] [DecidableEq C] [DecidableEq A]

/-- The clusters a member meets. -/
def cSupport (m : C → Finset A) : Finset C := Finset.univ.filter (fun c => (m c).Nonempty)

/-- The rank of a cluster inside the triple a member meets, for a fixed indexing `idx` of the
clusters. -/
def cRank (idx : C → ℕ) (m : C → Finset A) (c : C) : ℕ :=
  #((cSupport m).filter (fun d => idx d < idx c))

omit [DecidableEq A] in
theorem cRank_lt_three {idx : C → ℕ} {m : C → Finset A} (h3 : #(cSupport m) = 3) {c : C}
    (hc : c ∈ cSupport m) : cRank idx m c < 3 := by
  have hsub : (cSupport m).filter (fun d => idx d < idx c) ⊆ (cSupport m).erase c := by
    intro d hd
    obtain ⟨hd1, hd2⟩ := Finset.mem_filter.1 hd
    refine Finset.mem_erase.2 ⟨?_, hd1⟩
    rintro rfl
    exact lt_irrefl _ hd2
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hc, h3] at hle
  rw [cRank]
  omega

omit [DecidableEq C] [DecidableEq A] in
theorem cRank_lt {idx : C → ℕ} {m : C → Finset A} {c c' : C} (hc : c ∈ cSupport m)
    (h : idx c < idx c') : cRank idx m c < cRank idx m c' := by
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro d hd
    obtain ⟨hd1, hd2⟩ := Finset.mem_filter.1 hd
    exact Finset.mem_filter.2 ⟨hd1, lt_trans hd2 h⟩
  · intro hsub
    have : c ∈ (cSupport m).filter (fun d => idx d < idx c) :=
      hsub (Finset.mem_filter.2 ⟨hc, h⟩)
    exact lt_irrefl _ (Finset.mem_filter.1 this).2

omit [DecidableEq C] [DecidableEq A] in
theorem cRank_ne {idx : C → ℕ} (hidx : Function.Injective idx) {m : C → Finset A} {c c' : C}
    (hc : c ∈ cSupport m) (hc' : c' ∈ cSupport m) (hne : c ≠ c') :
    cRank idx m c ≠ cRank idx m c' := by
  rcases lt_trichotomy (idx c) (idx c') with h | h | h
  · exact Nat.ne_of_lt (cRank_lt hc h)
  · exact absurd (hidx h) hne
  · exact Nat.ne_of_gt (cRank_lt hc' h)

/-- The copy index the sum-zero rule gives to the cluster `c` of the member `m`. -/
def cShift {G : Type*} [AddCommGroup G] (idx : C → ℕ) (m : C → Finset A) (c : C) (a b : G) : G :=
  cPick (cRank idx m c) a b

omit [DecidableEq A] in
/-- **The coupling is free.**  For any two distinct clusters met by a member, the two copy indices
the sum-zero rule assigns to them run over *all* pairs of copies, exactly once each. -/
theorem cShift_existsUnique {G : Type*} [AddCommGroup G] {idx : C → ℕ}
    (hidx : Function.Injective idx) {m : C → Finset A} (h3 : #(cSupport m) = 3) {c c' : C}
    (hc : c ∈ cSupport m) (hc' : c' ∈ cSupport m) (hne : c ≠ c') (u v : G) :
    ∃! p : G × G, u = cShift idx m c p.1 p.2 ∧ v = cShift idx m c' p.1 p.2 :=
  cPick_existsUnique (cRank_lt_three h3 hc) (cRank_lt_three h3 hc')
    (cRank_ne hidx hc hc' hne) u v

variable (idx : C → ℕ)

/-- The copy `(a, b)` of the base member `m`: at each cluster `c` it uses the block `m c` inside the
copy `cShift idx m c a b` of `c`. -/
def cCopy {r : ℕ} (m : C → Finset A) (a b : ZMod (r + 1)) : C → Finset (ZMod (r + 1) × A) :=
  fun c => (m c).image (fun x => (cShift idx m c a b, x))

/-- The blown-up family: every base member replicated once per pair of copy indices. -/
noncomputable def cScaled (fam : List (C → Finset A)) (r : ℕ) :
    List (C → Finset (ZMod (r + 1) × A)) :=
  fam.flatMap (fun m =>
    (Finset.univ : Finset (ZMod (r + 1) × ZMod (r + 1))).toList.map (fun p => cCopy idx m p.1 p.2))

/-- How many members of the blown-up family cover the cell `(x, y)` of the cluster pair `(c, c')`. -/
noncomputable def cCover (fam : List (C → Finset A)) (r : ℕ) (c c' : C)
    (x y : ZMod (r + 1) × A) : ℕ :=
  (cScaled idx fam r).countP (fun m => decide (x ∈ m c ∧ y ∈ m c'))

omit [DecidableEq C] in
theorem mem_cCopy {r : ℕ} {m : C → Finset A} {a b : ZMod (r + 1)} {c : C}
    {x : ZMod (r + 1) × A} :
    x ∈ cCopy idx m a b c ↔ x.1 = cShift idx m c a b ∧ x.2 ∈ m c := by
  obtain ⟨u, a0⟩ := x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.1 hx
    have h1 : cShift idx m c a b = u := congrArg Prod.fst hxy
    have h2 : y = a0 := congrArg Prod.snd hxy
    exact ⟨h1.symm, h2 ▸ hy⟩
  · rintro ⟨h1, h2⟩
    simp only at h1 h2
    exact Finset.mem_image.2 ⟨a0, h2, by rw [h1]⟩

/-- The count of the copies of one base member that cover a given cell of a cluster pair: `1` if the
base member covers the underlying base cell, `0` otherwise. -/
theorem cCopies_count {r : ℕ} (hidx : Function.Injective idx) {m : C → Finset A}
    (h3 : #(cSupport m) = 3) {c c' : C} (hcc : c ≠ c') (x y : ZMod (r + 1) × A) :
    ((Finset.univ : Finset (ZMod (r + 1) × ZMod (r + 1))).toList.map
        (fun p => cCopy idx m p.1 p.2)).countP (fun n => decide (x ∈ n c ∧ y ∈ n c'))
      = if decide (x.2 ∈ m c ∧ y.2 ∈ m c') then 1 else 0 := by
  classical
  rw [List.countP_map]
  have hrw : ∀ p : ZMod (r + 1) × ZMod (r + 1),
      ((fun n => decide (x ∈ n c ∧ y ∈ n c')) ∘ (fun p => cCopy idx m p.1 p.2)) p
        = decide ((x.1 = cShift idx m c p.1 p.2 ∧ y.1 = cShift idx m c' p.1 p.2)
            ∧ (x.2 ∈ m c ∧ y.2 ∈ m c')) := by
    intro p
    simp only [Function.comp_apply, mem_cCopy, decide_eq_decide]
    tauto
  rw [show ((fun n : C → Finset (ZMod (r + 1) × A) => decide (x ∈ n c ∧ y ∈ n c'))
        ∘ (fun p => cCopy idx m p.1 p.2))
      = (fun p : ZMod (r + 1) × ZMod (r + 1) =>
          decide ((x.1 = cShift idx m c p.1 p.2 ∧ y.1 = cShift idx m c' p.1 p.2)
            ∧ (x.2 ∈ m c ∧ y.2 ∈ m c'))) from funext hrw, countP_univ_toList]
  by_cases hin : x.2 ∈ m c ∧ y.2 ∈ m c'
  · have hc : c ∈ cSupport m := Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨x.2, hin.1⟩⟩
    have hc' : c' ∈ cSupport m := Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨y.2, hin.2⟩⟩
    simp only [hin, and_true, decide_true, if_true]
    exact card_filter_eq_one _ (cShift_existsUnique hidx h3 hc hc' hcc x.1 y.1)
  · have hempty : (Finset.univ.filter (fun p : ZMod (r + 1) × ZMod (r + 1) =>
        (x.1 = cShift idx m c p.1 p.2 ∧ y.1 = cShift idx m c' p.1 p.2)
          ∧ (x.2 ∈ m c ∧ y.2 ∈ m c'))) = ∅ :=
      Finset.filter_eq_empty_iff.2 (fun p _ h => hin h.2)
    rw [hempty]
    simp [hin]

/-- **The blown-up family has exactly the cover counts of the base family.**  The sum-zero rule
couples the three clusters of every member — the same cluster copy has to serve both of that
member's rectangles at that cluster — and this coupling costs nothing: at every cluster pair and
every cell, the count is the base count. -/
theorem cCover_eq {r : ℕ} (hidx : Function.Injective idx) (fam : List (C → Finset A))
    (h3 : ∀ m ∈ fam, #(cSupport m) = 3) {c c' : C} (hcc : c ≠ c') (x y : ZMod (r + 1) × A) :
    cCover idx fam r c c' x y = fam.countP (fun m => decide (x.2 ∈ m c ∧ y.2 ∈ m c')) := by
  rw [cCover, cScaled, List.countP_flatMap]
  exact sum_map_eq_countP _ _ _ (fun m hm => cCopies_count idx hidx (h3 m hm) hcc x y)

end General

/-! ## 3. The scaled gate instance -/

/-- The indexing of the four clusters used by the sum-zero rule. -/
def gidx : GCl → ℕ
  | GCl.S => 0 | GCl.T => 1 | GCl.U => 2 | GCl.Z => 3

theorem gidx_injective : Function.Injective gidx := by decide +kernel

theorem gsupport_eq_cSupport (m : GMem) : gsupport m = cSupport m := rfl

theorem gate_support_three : ∀ m ∈ gateFamily, #(cSupport m) = 3 := gate_support_card

/-- An atom of the scaled instance: a copy index together with an atom of the gate instance. -/
abbrev SAtom (r : ℕ) := ZMod (r + 1) × GAtom

/-- A member of the scaled instance. -/
abbrev SMem (r : ℕ) := GCl → Finset (SAtom r)

/-- The copy `(a, b)` of the gate member `m`. -/
def smem {r : ℕ} (m : GMem) (a b : ZMod (r + 1)) : SMem r := cCopy gidx m a b

/-- **The scaled coupled dyadic family**: `60 · (r+1)²` members. -/
noncomputable def sfam (r : ℕ) : List (SMem r) := cScaled gidx gateFamily r

/-- How many members of the scaled family cover the cell `(x, y)` of the cluster pair `(c, c')`. -/
noncomputable def scoverCount {r : ℕ} (c c' : GCl) (x y : SAtom r) : ℕ :=
  cCover gidx gateFamily r c c' x y

/-- The gate cover count as a `countP`. -/
theorem gcoverCount_eq_countP (c c' : GCl) (a b : GAtom) :
    gcoverCount c c' (a, b) = gateFamily.countP (fun m => decide (a ∈ m c ∧ b ∈ m c')) := by
  rw [gcoverCount, List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro m _
  simp [grect, Finset.mem_product]

/-- **The scaled family has the same cover count as the gate family.** -/
theorem scoverCount_eq {r : ℕ} {c c' : GCl} (hcc : c ≠ c') (x y : SAtom r) :
    scoverCount c c' x y = gcoverCount c c' (x.2, y.2) := by
  rw [scoverCount, cCover_eq gidx gidx_injective gateFamily gate_support_three hcc,
    gcoverCount_eq_countP]
  rfl

/-- **The exact tiling survives refinement to every granularity.**  For every blow-up factor
`r + 1`, the scaled coupled dyadic family covers every cell of every one of the six cluster-pair
squares exactly once: the three-way coupling of the shared laminar cluster trees is free at all
scales. -/
theorem scaled_exact_tiling {r : ℕ} (c c' : GCl) (hcc : c ≠ c') (x y : SAtom r) :
    scoverCount c c' x y = 1 := by
  rw [scoverCount_eq hcc]
  exact gate_exact_tiling c c' hcc (x.2, y.2)

/-! ## 4. The scaled blocks are dyadic, and small -/

/-- Every block of the gate family is a full slot or a half: at most `2` atoms. -/
theorem gate_block_card_le_two : ∀ m ∈ gateFamily, ∀ c : GCl, #(m c) ≤ 2 := by decide +kernel

theorem smem_card {r : ℕ} (m : GMem) (a b : ZMod (r + 1)) (c : GCl) :
    #(smem m a b c) = #(m c) :=
  Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.injEq .. ▸ h).2)

/-- Every scaled block is a dyadic block of the gate instance sitting inside a single copy: the
laminar structure of the cluster trees is preserved by the blow-up. -/
theorem scaled_block_dyadic {r : ℕ} : ∀ m ∈ gateFamily, ∀ (a b : ZMod (r + 1)) (c : GCl),
    ∃ s : Finset GAtom, (s = ∅ ∨ IsGDyadic s) ∧
      smem m a b c = ({cShift gidx m c a b} : Finset (ZMod (r + 1))) ×ˢ s := by
  intro m hm a b c
  refine ⟨m c, gate_blocks_dyadic m hm c, ?_⟩
  ext x
  rw [smem, mem_cCopy, Finset.mem_product, Finset.mem_singleton]

/-- **The blocks are of vanishing relative size.**  A scaled block occupies at most a fraction
`1/(4(r+1))` of its cluster, so the construction realises the exact tiling at every block scale. -/
theorem scaled_block_relative_size {r : ℕ} : ∀ m ∈ gateFamily, ∀ (a b : ZMod (r + 1)) (c : GCl),
    #(smem m a b c) * (4 * (r + 1)) ≤ Fintype.card (SAtom r) := by
  intro m hm a b c
  have hcard : #(smem m a b c) ≤ 2 := by
    rw [smem_card]
    exact gate_block_card_le_two m hm c
  have htot : Fintype.card (SAtom r) = 8 * (r + 1) := by
    simp [SAtom, Fintype.card_prod, ZMod.card, Nat.mul_comm]
  rw [htot]
  calc #(smem m a b c) * (4 * (r + 1)) ≤ 2 * (4 * (r + 1)) :=
        Nat.mul_le_mul_right _ hcard
    _ = 8 * (r + 1) := by ring

/-- The scaled family has `60·(r+1)²` members. -/
theorem sfam_length (r : ℕ) : (sfam r).length = 60 * (r + 1) ^ 2 := by
  rw [sfam, cScaled, List.length_flatMap]
  have hlen : ∀ m : GMem,
      ((Finset.univ : Finset (ZMod (r + 1) × ZMod (r + 1))).toList.map
        (fun p => cCopy gidx m p.1 p.2)).length = (r + 1) ^ 2 := by
    intro m
    rw [List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_prod, ZMod.card]
    ring
  simp only [hlen, List.map_const', List.sum_replicate, smul_eq_mul]
  have hg : gateFamily.length = 60 := by decide +kernel
  rw [hg]

#print axioms cPick_existsUnique
#print axioms cShift_existsUnique
#print axioms cCover_eq
#print axioms scoverCount_eq
#print axioms scaled_exact_tiling
#print axioms scaled_block_dyadic
#print axioms scaled_block_relative_size
#print axioms sfam_length

end Nibble.AX1
