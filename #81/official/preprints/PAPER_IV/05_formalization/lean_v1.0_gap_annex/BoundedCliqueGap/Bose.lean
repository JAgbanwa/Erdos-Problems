import BoundedCliqueGap.SteinerTools
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-
`BoundedCliqueGap.Bose` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Steiner ladder, rung S2 — the Bose construction

An explicit edge-disjoint triangle family on the complete graph
`K_{3m} = (⊤ : SimpleGraph (R × Fin 3))`, where `R` is any finite commutative
ring carrying an element `ih` with `2 * ih = 1` (a "half").  Taking
`R = ZMod n` for odd `n` gives `K_{3n}`.

The family (Bose 1939) is built from the idempotent commutative quasigroup
`x ∘ y = (x + y)/2` on `R`:

* type-A blocks `AT x = {(x,0),(x,1),(x,2)}`, one per `x : R`;
* type-B blocks `BT i x y = {(x,i),(y,i),(x∘y, i+1)}`, for `i : Fin 3` and
  `x ≠ y` in `R`.

The whole content is that **every edge of `K_{3m}` lies in exactly one block**
(so the family is not merely a packing but a Steiner triple system).  This is
proved by exhibiting, for each pair of distinct vertices `u ≠ v`, the block
`blk u v` containing them, and showing that any block containing both equals
`blk u v`.  Cardinality is then a counting consequence: the blocks are
edge-disjoint and cover, so `3·|family| = |E(K_{3m})| = C(3m,2)`, i.e.
`2·|family| = m(3m-1)`, the exact Steiner number — no loss at all, so the
constant `c` allowed by the rung is `c = 0`.
-/

namespace BoundedCliqueGap

namespace Bose

open Finset

/-! ## The quasigroup `x ∘ y = (x+y)/2` -/

section Algebra

variable {R : Type*} [CommRing R] {ih : R}

/-- The quasigroup operation `x ∘ y = (x+y)/2`, where `ih` is a half of `1`. -/
def op (ih : R) (x y : R) : R := (x + y) * ih

lemma op_comm (x y : R) : op ih x y = op ih y x := by unfold op; ring

lemma half_two_mul (hih : (2 : R) * ih = 1) (a : R) : (2 * a) * ih = a := by
  calc (2 * a) * ih = a * (2 * ih) := by ring
    _ = a := by rw [hih, mul_one]

lemma two_mul_op (hih : (2 : R) * ih = 1) (x y : R) : 2 * op ih x y = x + y := by
  unfold op
  calc 2 * ((x + y) * ih) = (x + y) * (2 * ih) := by ring
    _ = x + y := by rw [hih, mul_one]

lemma op_eq_iff (hih : (2 : R) * ih = 1) {x y b : R} : op ih x y = b ↔ y = 2 * b - x := by
  constructor
  · intro h
    have h2 := two_mul_op hih x y
    rw [h] at h2
    linear_combination -h2
  · rintro rfl
    unfold op
    have h3 : x + (2 * b - x) = 2 * b := by ring
    rw [h3, half_two_mul hih]

lemma op_ne_left (hih : (2 : R) * ih = 1) {x y : R} (hxy : x ≠ y) : op ih x y ≠ x := by
  intro h
  rw [op_eq_iff hih] at h
  exact hxy (by linear_combination -h)

lemma op_ne_right (hih : (2 : R) * ih = 1) {x y : R} (hxy : x ≠ y) : op ih x y ≠ y :=
  fun h => op_ne_left hih (Ne.symm hxy) (by rw [op_comm]; exact h)

lemma op_two_sub (hih : (2 : R) * ih = 1) (x c : R) : op ih x (2 * c - x) = c :=
  (op_eq_iff hih).2 rfl

lemma two_sub_ne (hih : (2 : R) * ih = 1) {x c : R} (hxc : x ≠ c) : x ≠ 2 * c - x := by
  intro h
  apply hxc
  have : (2 : R) * x = 2 * c := by linear_combination h
  calc x = (2 * x) * ih := (half_two_mul hih x).symm
    _ = (2 * c) * ih := by rw [this]
    _ = c := half_two_mul hih c

end Algebra

/-! ## Arithmetic of the three layers -/

lemma fin3_succ_ne : ∀ i : Fin 3, i + 1 ≠ i := by decide

lemma fin3_cases : ∀ i j : Fin 3, i ≠ j → j = i + 1 ∨ i = j + 1 := by decide

/-! ## The blocks -/

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

/-- A type-A block. -/
def AT (x : R) : Finset (R × Fin 3) := {(x, 0), (x, 1), (x, 2)}

/-- A type-B block. -/
def BT (ih : R) (i : Fin 3) (x y : R) : Finset (R × Fin 3) :=
  {(x, i), (y, i), (op ih x y, i + 1)}

variable {ih : R}

omit [CommRing R] [Fintype R] in
lemma mem_AT (x : R) (i : Fin 3) : (x, i) ∈ AT x := by
  fin_cases i <;> simp [AT]

omit [CommRing R] [Fintype R] in
lemma AT_eq_of_mem {x : R} {u : R × Fin 3} (hu : u ∈ AT x) : u.1 = x := by
  simp only [AT, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl <;> rfl

omit [CommRing R] [Fintype R] in
lemma card_AT (x : R) : (AT x).card = 3 := by
  rw [AT, Finset.card_insert_of_notMem (by simp [Prod.ext_iff]),
    Finset.card_insert_of_notMem (by simp [Prod.ext_iff]), Finset.card_singleton]

omit [Fintype R] in
lemma BT_comm (i : Fin 3) (x y : R) : BT ih i x y = BT ih i y x := by
  rw [BT, BT, op_comm, Finset.insert_comm]

omit [Fintype R] in
lemma card_BT {i : Fin 3} {x y : R} (hxy : x ≠ y) : (BT ih i x y).card = 3 := by
  have h1 : ((x, i) : R × Fin 3) ∉ ({(y, i), (op ih x y, i + 1)} : Finset (R × Fin 3)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, not_or]
    exact ⟨fun h => hxy h.1, fun h => (fin3_succ_ne i) h.2.symm⟩
  have h2 : ((y, i) : R × Fin 3) ∉ ({(op ih x y, i + 1)} : Finset (R × Fin 3)) := by
    simp only [Finset.mem_singleton, Prod.ext_iff]
    exact fun h => (fin3_succ_ne i) h.2.symm
  rw [BT, Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
    Finset.card_singleton]

/-- The Bose family of blocks on `R × Fin 3`. -/
noncomputable def family (ih : R) : Finset (Finset (R × Fin 3)) := by
  classical
  exact Finset.univ.filter fun T => (∃ x, T = AT x) ∨ ∃ i x y, x ≠ y ∧ T = BT ih i x y

lemma mem_family {T : Finset (R × Fin 3)} :
    T ∈ family ih ↔ (∃ x, T = AT x) ∨ ∃ i x y, x ≠ y ∧ T = BT ih i x y := by
  classical
  simp [family]

lemma AT_mem_family (x : R) : AT x ∈ family ih := mem_family.2 (Or.inl ⟨x, rfl⟩)

lemma BT_mem_family {i : Fin 3} {x y : R} (hxy : x ≠ y) : BT ih i x y ∈ family ih :=
  mem_family.2 (Or.inr ⟨i, x, y, hxy, rfl⟩)

/-- Every block is a triangle of the complete graph. -/
lemma isTriangle_of_mem_family {T : Finset (R × Fin 3)} (hT : T ∈ family ih) :
    IsTriangle (⊤ : SimpleGraph (R × Fin 3)) T := by
  refine ⟨?_, fun u _ v _ huv => by simpa using huv⟩
  rcases mem_family.1 hT with ⟨x, rfl⟩ | ⟨i, x, y, hxy, rfl⟩
  · exact card_AT x
  · exact card_BT hxy

/-! ## The block through a pair of vertices -/

/-- The canonical block containing the two distinct vertices `u` and `v`. -/
noncomputable def blk (ih : R) (u v : R × Fin 3) : Finset (R × Fin 3) := by
  classical
  exact
    if u.2 = v.2 then BT ih u.2 u.1 v.1
    else if u.1 = v.1 then AT u.1
    else if v.2 = u.2 + 1 then BT ih u.2 u.1 (2 * v.1 - u.1)
    else BT ih v.2 v.1 (2 * u.1 - v.1)

omit [Fintype R] in
lemma blk_same_layer (i : Fin 3) (x y : R) : blk ih (x, i) (y, i) = BT ih i x y := by
  classical
  simp [blk]

omit [Fintype R] in
lemma blk_vert {x : R} {i j : Fin 3} (hij : i ≠ j) : blk ih (x, i) (x, j) = AT x := by
  classical
  simp [blk, hij]

omit [Fintype R] in
lemma blk_up {x c : R} {i j : Fin 3} (hij : j = i + 1) (hxc : x ≠ c) :
    blk ih (x, i) (c, j) = BT ih i x (2 * c - x) := by
  classical
  subst hij
  have h1 : ¬ (i = i + 1) := fun h => fin3_succ_ne i h.symm
  simp [blk, h1, hxc]

omit [Fintype R] in
lemma blk_down {x c : R} {i j : Fin 3} (hij : i = j + 1) (hxc : x ≠ c) :
    blk ih (x, i) (c, j) = BT ih j c (2 * x - c) := by
  classical
  subst hij
  have h1 : ¬ ((j : Fin 3) + 1 = j) := fin3_succ_ne j
  have h2 : ¬ ((j : Fin 3) = j + 1 + 1) := by revert j; decide
  simp [blk, h1, hxc, h2]

omit [Fintype R] in
/-- Both endpoints lie in their canonical block. -/
lemma mem_blk (hih : (2 : R) * ih = 1) {u v : R × Fin 3} (huv : u ≠ v) :
    u ∈ blk ih u v ∧ v ∈ blk ih u v := by
  obtain ⟨x, i⟩ := u
  obtain ⟨c, j⟩ := v
  by_cases hij : i = j
  · subst hij
    have hxc : x ≠ c := fun h => huv (by rw [h])
    rw [blk_same_layer]
    exact ⟨by simp [BT], by simp [BT]⟩
  · by_cases hxc : x = c
    · subst hxc
      rw [blk_vert hij]
      exact ⟨mem_AT _ _, mem_AT _ _⟩
    · rcases fin3_cases i j hij with h | h
      · rw [blk_up h hxc]
        refine ⟨by simp [BT], ?_⟩
        subst h
        simp [BT, op_two_sub hih]
      · rw [blk_down h hxc]
        refine ⟨?_, by simp [BT]⟩
        subst h
        simp [BT, op_two_sub hih]

lemma blk_mem_family (hih : (2 : R) * ih = 1) {u v : R × Fin 3} (huv : u ≠ v) :
    blk ih u v ∈ family ih := by
  obtain ⟨x, i⟩ := u
  obtain ⟨c, j⟩ := v
  by_cases hij : i = j
  · subst hij
    have hxc : x ≠ c := fun h => huv (by rw [h])
    rw [blk_same_layer]
    exact BT_mem_family hxc
  · by_cases hxc : x = c
    · subst hxc
      rw [blk_vert hij]
      exact AT_mem_family x
    · rcases fin3_cases i j hij with h | h
      · rw [blk_up h hxc]
        exact BT_mem_family (two_sub_ne hih hxc)
      · rw [blk_down h hxc]
        exact BT_mem_family (two_sub_ne hih (Ne.symm hxc))

/-! ## Uniqueness: a block containing `u` and `v` is `blk u v` -/

omit [Fintype R] in
lemma AT_eq_blk {x : R} {u v : R × Fin 3} (hu : u ∈ AT x) (hv : v ∈ AT x) (huv : u ≠ v) :
    AT x = blk ih u v := by
  obtain ⟨a, i⟩ := u
  obtain ⟨b, j⟩ := v
  have ha : a = x := AT_eq_of_mem hu
  have hb : b = x := AT_eq_of_mem hv
  subst ha
  subst hb
  have hij : i ≠ j := fun h => huv (by rw [h])
  rw [blk_vert hij]

omit [Fintype R] in
lemma BT_eq_blk (hih : (2 : R) * ih = 1) {i : Fin 3} {x y : R} (hxy : x ≠ y)
    {u v : R × Fin 3} (hu : u ∈ BT ih i x y) (hv : v ∈ BT ih i x y) (huv : u ≠ v) :
    BT ih i x y = blk ih u v := by
  have hc : op ih x y = op ih x y := rfl
  set c := op ih x y with hcdef
  have hcx : c ≠ x := op_ne_left hih hxy
  have hcy : c ≠ y := op_ne_right hih hxy
  have h2c : 2 * c - x = y := by
    have := two_mul_op hih x y
    rw [← hcdef] at this
    linear_combination this
  have h2c' : 2 * c - y = x := by
    have := two_mul_op hih x y
    rw [← hcdef] at this
    linear_combination this
  have hmem : ∀ w ∈ BT ih i x y, w = (x, i) ∨ w = (y, i) ∨ w = (c, i + 1) := by
    intro w hw
    simpa [BT, ← hcdef] using hw
  rcases hmem u hu with rfl | rfl | rfl <;> rcases hmem v hv with rfl | rfl | rfl
  · exact absurd rfl huv
  · rw [blk_same_layer]
  · rw [blk_up rfl (Ne.symm hcx), h2c]
  · rw [blk_same_layer, BT_comm]
  · exact absurd rfl huv
  · rw [blk_up rfl (Ne.symm hcy), h2c', BT_comm]
  · rw [blk_down rfl hcx, h2c]
  · rw [blk_down rfl hcy, h2c', BT_comm]
  · exact absurd rfl huv

/-- **Uniqueness.**  A block containing two distinct vertices is *the* block
`blk u v` through them. -/
lemma eq_blk_of_mem_family (hih : (2 : R) * ih = 1) {T : Finset (R × Fin 3)}
    (hT : T ∈ family ih) {u v : R × Fin 3} (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v) :
    T = blk ih u v := by
  rcases mem_family.1 hT with ⟨x, rfl⟩ | ⟨i, x, y, hxy, rfl⟩
  · exact AT_eq_blk hu hv huv
  · exact BT_eq_blk hih hxy hu hv huv

/-! ## Rung S2 -/

/-- **Rung S2.**  The Bose family is an edge-disjoint family of triangles of
the complete graph on `R × Fin 3`. -/
theorem family_isPacking (hih : (2 : R) * ih = 1) :
    IsPacking (⊤ : SimpleGraph (R × Fin 3)) (family ih) := by
  refine ⟨fun T hT => isTriangle_of_mem_family hT, ?_⟩
  intro T hT T' hT' hne
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨u, hu, v, hv, huv, rfl⟩ := mem_triEdges_iff.1 he
  obtain ⟨u', hu', v', hv', huv', hee⟩ := mem_triEdges_iff.1 he'
  have huv2 : u ∈ T' ∧ v ∈ T' := by
    rw [Sym2.eq_iff] at hee
    rcases hee with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hu', hv'⟩
    · exact ⟨hv', hu'⟩
  exact hne ((eq_blk_of_mem_family hih hT hu hv huv).trans
    (eq_blk_of_mem_family hih hT' huv2.1 huv2.2 huv).symm)

/-- Every edge of the complete graph is covered by a block: the family is in
fact a Steiner triple system. -/
theorem family_covers (hih : (2 : R) * ih = 1) (e : Sym2 (R × Fin 3)) (hnd : ¬ e.IsDiag) :
    ∃ T ∈ family ih, e ∈ triEdges T := by
  induction e with
  | _ u v =>
    have huv : u ≠ v := by simpa using hnd
    obtain ⟨h1, h2⟩ := mem_blk hih huv
    exact ⟨blk ih u v, blk_mem_family hih huv, mk_mem_triEdges h1 h2 huv⟩

/-- **Rung S2, count.**  The Bose family has exactly `m(3m-1)/2` blocks, where
`m = |R|` — the exact Steiner number of `K_{3m}`. -/
theorem card_family (hih : (2 : R) * ih = 1) :
    2 * (family ih).card = Fintype.card R * (3 * Fintype.card R - 1) := by
  classical
  set N := Fintype.card (R × Fin 3) with hN
  have hbi : (family ih).biUnion triEdges = (⊤ : SimpleGraph (R × Fin 3)).edgeFinset := by
    ext e
    simp only [Finset.mem_biUnion, SimpleGraph.mem_edgeFinset]
    constructor
    · rintro ⟨T, hT, he⟩
      exact mem_edgeSet_of_mem_triEdges (isTriangle_of_mem_family hT) he
    · intro he
      have hnd : ¬ e.IsDiag := SimpleGraph.not_isDiag_of_mem_edgeSet _ he
      obtain ⟨T, hT, hTe⟩ := family_covers hih e hnd
      exact ⟨T, hT, hTe⟩
  have hdisj : ((family ih : Finset (Finset (R × Fin 3))) : Set (Finset (R × Fin 3))).PairwiseDisjoint
      triEdges := by
    intro T hT T' hT' hne
    exact (family_isPacking hih).2 T hT T' hT' hne
  have hcard := Finset.card_biUnion hdisj
  rw [hbi, SimpleGraph.card_edgeFinset_top_eq_card_choose_two] at hcard
  have hsum : ∑ T ∈ family ih, (triEdges T).card = 3 * (family ih).card := by
    rw [Finset.sum_congr rfl (fun T hT => card_triEdges (isTriangle_of_mem_family hT))]
    simp [mul_comm]
  rw [hsum] at hcard
  -- `hcard : 3 * card = N.choose 2` with `N = 3 * card R`
  have hNval : N = 3 * Fintype.card R := by
    rw [hN, Fintype.card_prod, Fintype.card_fin]
    ring
  have hchoose : 2 * N.choose 2 = N * (N - 1) := by
    rw [Nat.choose_two_right]
    rcases N with _ | n
    · simp
    · have : Even ((n + 1) * n) := by
        simpa [Nat.mul_comm] using Nat.even_mul_succ_self n
      obtain ⟨t, ht⟩ := this
      simp only [Nat.add_sub_cancel]
      omega
  have h3 : 3 * (2 * (family ih).card) = 3 * (Fintype.card R * (3 * Fintype.card R - 1)) := by
    have : 2 * (3 * (family ih).card) = 2 * N.choose 2 := by rw [hcard]
    rw [hchoose, hNval] at this
    have hexp : 3 * Fintype.card R * (3 * Fintype.card R - 1)
        = 3 * (Fintype.card R * (3 * Fintype.card R - 1)) := by ring
    rw [hexp] at this
    omega
  omega

end Bose

/-- A half of `1` exists in `ZMod n` for odd `n`. -/
lemma zmod_two_mul_half {n : ℕ} [NeZero n] (hodd : Odd n) :
    ∃ ih : ZMod n, (2 : ZMod n) * ih = 1 := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨((k + 1 : ℕ) : ZMod n), ?_⟩
  have h : ((2 * (k + 1) : ℕ) : ZMod n) = ((n + 1 : ℕ) : ZMod n) := by
    congr 1; omega
  push_cast at h
  rw [ZMod.natCast_self] at h
  simpa using h

end BoundedCliqueGap
