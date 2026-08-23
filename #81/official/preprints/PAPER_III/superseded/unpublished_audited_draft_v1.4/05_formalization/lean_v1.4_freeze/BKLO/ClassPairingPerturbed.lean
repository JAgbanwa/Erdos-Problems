/-
# One **perturbed** block of a link, paired class for class.

At an unperturbed link the two classes a class matching pairs up have exactly the same trace `c`,
and `BKLO.exists_class_pair_involution_avoiding` matches them bijectively.  At a perturbed link
`X u` the two traces differ — the adversary added and deleted vertices — and the pairing has to
absorb the difference.  This file does that for **one** pair of classes:

* `BKLO.card_bad_partners_in_class_le` — the partners of a vertex `a` inside a subset `T` of one
  class that are *unusable* (equal to `a`, a non-neighbour in `F`, or a forbidden pair) number at
  most `q/4 + m + 1`.  This is the counting step of `BKLO.exists_class_involution_avoiding` and of
  `BKLO.exists_class_matching_avoiding`, isolated so that it can be used at **arbitrary** subsets
  of a class — which is what a perturbed trace is.
* `BKLO.exists_class_pair_perturbed_involution` — **one perturbed block**: two distinct classes of
  the region, with traces of *different* sizes, carry a fixed-point-free involution by edges of `F`
  outside `U` of their union minus at most one vertex (a parity correction), which pairs the two
  traces with each other except for a leftover set inside the *larger* trace, of size exactly the
  difference of the two traces.

The leftovers of a perturbed block therefore stay inside a single class: a vertex whose partner
does not obey the cross-side rule is paired inside its own class.  That is what keeps the used
degree of a vertex inside every *other* class as small as at an unperturbed link.

Everything here is `sorry`-free.
-/
import BKLO.ClassPairing
import BKLO.PerturbedBlock

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ}

/-! ### The unusable partners inside one class -/

/-- **A vertex has few unusable partners inside a subset of a class.**  Of the vertices `b` of
`T ⊆ C k`, at most a quarter of a class are non-neighbours of `a`, at most `m` are forbidden, and
one is `a` itself. -/
theorem card_bad_partners_in_class_le
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (hW'W : W' ⊆ W)
    {k : ℕ} (hk : k < gridSize ε K * gridSize ε K)
    {T : Finset V} (hTC : T ⊆ C k) (hTW' : T ⊆ W')
    {a : V} (haW' : a ∈ W') {U : Finset (Sym2 V)} {m q : ℕ}
    (hq : ∀ l < gridSize ε K * gridSize ε K, (C l).card = q)
    (hU : (T.filter (fun b => s(a, b) ∈ U)).card ≤ m) :
    4 * (T.filter (fun b => ¬ (b ≠ a ∧ (s(a, b) ∈ F ∧ s(a, b) ∉ U)))).card ≤ q + 4 * m + 4 := by
  classical
  have hbal := hgrid.classBalancedSharp a (hW'W haW') k hk
  rw [hq k hk] at hbal
  have hbad : T.filter (fun b => ¬ (b ≠ a ∧ (s(a, b) ∈ F ∧ s(a, b) ∉ U)))
      ⊆ insert a ((nonNbrs F W' a ∩ C k) ∪ T.filter (fun b => s(a, b) ∈ U)) := by
    intro b hb
    obtain ⟨hbT, hbr⟩ := Finset.mem_filter.1 hb
    by_cases hba : b = a
    · exact hba ▸ Finset.mem_insert_self b _
    refine Finset.mem_insert_of_mem ?_
    by_cases hU' : s(a, b) ∈ U
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hbT, hU'⟩)
    · refine Finset.mem_union_left _ (Finset.mem_inter.2 ⟨?_, hTC hbT⟩)
      refine Finset.mem_sdiff.2 ⟨hTW' hbT, ?_⟩
      intro hmem
      exact hbr ⟨hba, (mem_resLink.1 hmem).2, hU'⟩
  have h1 : (T.filter (fun b => ¬ (b ≠ a ∧ (s(a, b) ∈ F ∧ s(a, b) ∉ U)))).card
      ≤ 1 + ((nonNbrs F W' a ∩ C k).card + (T.filter (fun b => s(a, b) ∈ U)).card) := by
    refine le_trans (Finset.card_le_card hbad) ?_
    refine le_trans (Finset.card_insert_le _ _) ?_
    have := Finset.card_union_le (nonNbrs F W' a ∩ C k) (T.filter (fun b => s(a, b) ∈ U))
    omega
  omega

/-! ### One perturbed block -/

/-- **One perturbed block, the larger trace ordered first.**  Auxiliary, ordered form of
`BKLO.exists_class_pair_perturbed_involution`. -/
theorem exists_class_pair_perturbed_involution_aux
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (hW'W : W' ⊆ W)
    {i j : ℕ} (hi : i < gridSize ε K * gridSize ε K) (hj : j < gridSize ε K * gridSize ε K)
    (hij : i ≠ j) {Xu : Finset V} (hXW' : Xu ⊆ W') {U : Finset (Sym2 V)} {m q : ℕ}
    (hq : ∀ l < gridSize ε K * gridSize ε K, (C l).card = q)
    (hU : ∀ a ∈ Xu, ∀ l < gridSize ε K * gridSize ε K,
      ((C l ∩ Xu).filter (fun b => s(a, b) ∈ U)).card ≤ m)
    (hle : (C i ∩ Xu).card ≤ (C j ∩ Xu).card)
    (hsize : q + 4 * m + 6 ≤ 2 * (C i ∩ Xu).card) :
    ∃ (zb lb : Finset V) (p : V → V),
      zb ⊆ C j ∩ Xu ∧ zb.card ≤ 1 ∧
      zb.card ≤ (C j ∩ Xu).card - (C i ∩ Xu).card ∧
      Even (((C i ∩ Xu) ∪ (C j ∩ Xu)) \ zb).card ∧
      lb ⊆ (C j ∩ Xu) \ zb ∧
      lb.card ≤ (C j ∩ Xu).card - (C i ∩ Xu).card ∧
      (∀ z ∈ ((C i ∩ Xu) ∪ (C j ∩ Xu)) \ zb, p z ∈ ((C i ∩ Xu) ∪ (C j ∩ Xu)) \ zb) ∧
      (∀ z ∈ ((C i ∩ Xu) ∪ (C j ∩ Xu)) \ zb, p (p z) = z) ∧
      (∀ z ∈ ((C i ∩ Xu) ∪ (C j ∩ Xu)) \ zb, p z ≠ z) ∧
      (∀ z ∈ ((C i ∩ Xu) ∪ (C j ∩ Xu)) \ zb, s(z, p z) ∈ F ∧ s(z, p z) ∉ U) ∧
      (∀ z ∈ C i ∩ Xu, p z ∈ C j ∩ Xu) ∧
      (∀ z ∈ (C j ∩ Xu) \ zb, z ∉ lb → p z ∈ C i ∩ Xu) := by
  classical
  set A : Finset V := C i ∩ Xu with hAdef
  set B₀ : Finset V := C j ∩ Xu with hB₀def
  have hdisj₀ : Disjoint A B₀ := by
    refine Finset.disjoint_left.2 fun z hzA hzB => ?_
    exact (Finset.disjoint_left.1 (hgrid.classDisjoint i hi j hj hij))
      (Finset.mem_inter.1 hzA).1 (Finset.mem_inter.1 hzB).1
  have hAC : A ⊆ C i := fun z hz => (Finset.mem_inter.1 hz).1
  have hBC : B₀ ⊆ C j := fun z hz => (Finset.mem_inter.1 hz).1
  have hAW' : A ⊆ W' := fun z hz => hXW' (Finset.mem_inter.1 hz).2
  have hBW' : B₀ ⊆ W' := fun z hz => hXW' (Finset.mem_inter.1 hz).2
  -- the parity correction
  obtain ⟨zb, hzbsub, hzbcard, hzbdev, hzbpar, hzble⟩ :
      ∃ zb : Finset V, zb ⊆ B₀ ∧ zb.card ≤ 1 ∧ zb.card ≤ B₀.card - A.card ∧
        Even (A.card + (B₀ \ zb).card) ∧ A.card ≤ (B₀ \ zb).card := by
    by_cases hpar : Even (A.card + B₀.card)
    · exact ⟨∅, Finset.empty_subset _, by simp, by simp, by simpa using hpar, by simpa using hle⟩
    · have hlt : A.card < B₀.card := by
        rcases lt_or_eq_of_le hle with h | h
        · exact h
        · exact absurd (by rw [← h]; exact ⟨A.card, by omega⟩) hpar
      have hne : B₀.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨b₀, hb₀⟩ := hne
      have hcard : (B₀ \ ({b₀} : Finset V)).card = B₀.card - 1 := by
        rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 hb₀),
          Finset.card_singleton]
      refine ⟨{b₀}, Finset.singleton_subset_iff.2 hb₀, by simp,
        by simp only [Finset.card_singleton]; omega, ?_, by omega⟩
      rw [hcard]
      rw [Nat.even_add] at hpar ⊢
      rw [Nat.even_sub (by omega)]
      simp only [Nat.even_iff] at *
      omega
  set B : Finset V := B₀ \ zb with hBdef
  have hBsub : B ⊆ B₀ := Finset.sdiff_subset
  have hdisj : Disjoint A B := Finset.disjoint_of_subset_right hBsub hdisj₀
  have hunion : (A ∪ B₀) \ zb = A ∪ B := by
    rw [hBdef]
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2⟩
    · rintro (h1 | ⟨h1, h2⟩)
      · exact ⟨Or.inl h1, fun hcon => (Finset.disjoint_left.1 hdisj₀) h1 (hzbsub hcon)⟩
      · exact ⟨Or.inr h1, h2⟩
  have hcardU : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hdisj
  -- the counting bounds
  set r : V → V → Prop := fun a b => s(a, b) ∈ F ∧ s(a, b) ∉ U with hrdef
  have hsymm : ∀ a b : V, r a b → r b a := by
    intro a b hab
    rw [hrdef]
    simp only []
    rw [Sym2.eq_swap]
    exact hab
  have hbadB : ∀ a ∈ Xu, 4 * (B.filter (fun b => ¬ (b ≠ a ∧ r a b))).card ≤ q + 4 * m + 4 := by
    intro a ha
    refine card_bad_partners_in_class_le hgrid hW'W hj (fun z hz => hBC (hBsub hz))
      (fun z hz => hBW' (hBsub hz)) (hXW' ha) hq ?_
    refine le_trans (Finset.card_le_card ?_) (hU a ha j hj)
    intro z hz
    obtain ⟨hzB, hzU⟩ := Finset.mem_filter.1 hz
    exact Finset.mem_filter.2 ⟨hBsub hzB, hzU⟩
  have hbadA : ∀ a ∈ Xu, 4 * (A.filter (fun b => ¬ (b ≠ a ∧ r a b))).card ≤ q + 4 * m + 4 := by
    intro a ha
    refine card_bad_partners_in_class_le hgrid hW'W hi hAC hAW' (hXW' ha) hq ?_
    exact hU a ha i hi
  have hBXu : ∀ z ∈ B, z ∈ Xu := fun z hz => (Finset.mem_inter.1 (hBsub hz)).2
  have hAXu : ∀ z ∈ A, z ∈ Xu := fun z hz => (Finset.mem_inter.1 hz).2
  -- the three degree conditions of the unbalanced block
  have hsplitB : ∀ b : V, (B.filter (fun z => z ≠ b ∧ r b z)).card
      + (B.filter (fun z => ¬ (z ≠ b ∧ r b z))).card = B.card :=
    fun b => Finset.card_filter_add_card_filter_not _
  have hsplitA : ∀ b : V, (A.filter (fun z => z ≠ b ∧ r b z)).card
      + (A.filter (fun z => ¬ (z ≠ b ∧ r b z))).card = A.card :=
    fun b => Finset.card_filter_add_card_filter_not _
  have hBdeg : ∀ b ∈ B, B.card - A.card ≤ (B.filter (fun z => z ≠ b ∧ r b z)).card := by
    intro b hb
    have h1 := hbadB b (hBXu b hb)
    have h2 := hsplitB b
    omega
  have hABdeg : ∀ a ∈ A, A.card + 2 * (B.card - A.card)
      < 2 * (B.filter (fun z => r a z)).card := by
    intro a ha
    have h1 := hbadB a (hAXu a ha)
    have h2 := hsplitB a
    have h3 : (B.filter (fun z => z ≠ a ∧ r a z)).card ≤ (B.filter (fun z => r a z)).card := by
      refine Finset.card_le_card ?_
      intro z hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
      exact Finset.mem_filter.2 ⟨hz1, hz2.2⟩
    omega
  have hBAdeg : ∀ b ∈ B, A.card < 2 * (A.filter (fun z => r z b)).card := by
    intro b hb
    have h1 := hbadA b (hBXu b hb)
    have h2 := hsplitA b
    have h3 : (A.filter (fun z => z ≠ b ∧ r b z)).card ≤ (A.filter (fun z => r z b)).card := by
      refine Finset.card_le_card ?_
      intro z hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
      exact Finset.mem_filter.2 ⟨hz1, hsymm _ _ hz2.2⟩
    omega
  have hparB : Even (B.card - A.card) := by
    rcases hzbpar with ⟨s, hs⟩
    exact ⟨s - A.card, by omega⟩
  obtain ⟨L, p, hLB, hLcard, hpA, hpL, hpBA, hpU, hpinv, hpne, hpr⟩ :=
    exists_unbalanced_block_involution hdisj r hsymm hzble hparB hBdeg hABdeg hBAdeg
  have hBleB₀ : B.card ≤ B₀.card := Finset.card_le_card hBsub
  refine ⟨zb, L, p, hzbsub, hzbcard, hzbdev, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hunion, hcardU]
    exact hzbpar
  · rw [← hBdef]
    exact hLB
  · omega
  · rw [hunion]; exact hpU
  · rw [hunion]; exact hpinv
  · rw [hunion]; exact hpne
  · rw [hunion]; exact hpr
  · intro z hz
    exact hBsub (hpA z hz)
  · intro z hz hzL
    rw [← hBdef] at hz
    exact hpBA z hz hzL

/-- **One perturbed block of a link.**  Two distinct classes `i ≠ j` of the region, whose traces on
the (perturbed) link `Xu` may have *different* sizes, carry a fixed-point-free involution by edges
of `F` outside `U` of their union minus a parity correction `zb` of at most one vertex.  Outside a
leftover set `lb` — of size at most the difference of the two traces, and contained in the larger
trace — the involution pairs the two traces with each other, so it obeys the cross-side rule.

The hypothesis is the one of the unperturbed case, `q + 4 m + 6 ≤ 2 c`, asked of both traces: the
perturbation is paid for in the leftovers, not in the hypothesis. -/
theorem exists_class_pair_perturbed_involution
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (hW'W : W' ⊆ W)
    {i j : ℕ} (hi : i < gridSize ε K * gridSize ε K) (hj : j < gridSize ε K * gridSize ε K)
    (hij : i ≠ j) {Xu : Finset V} (hXW' : Xu ⊆ W') {U : Finset (Sym2 V)} {m q : ℕ}
    (hq : ∀ l < gridSize ε K * gridSize ε K, (C l).card = q)
    (hU : ∀ a ∈ Xu, ∀ l < gridSize ε K * gridSize ε K,
      ((C l ∩ Xu).filter (fun b => s(a, b) ∈ U)).card ≤ m)
    (hsizei : q + 4 * m + 6 ≤ 2 * (C i ∩ Xu).card)
    (hsizej : q + 4 * m + 6 ≤ 2 * (C j ∩ Xu).card) :
    ∃ (zb lb : Finset V) (p : V → V),
      zb ⊆ (C i ∩ Xu) ∪ (C j ∩ Xu) ∧ zb.card ≤ 1 ∧
      zb.card ≤ ((C i ∩ Xu).card - (C j ∩ Xu).card) + ((C j ∩ Xu).card - (C i ∩ Xu).card) ∧
      Even (((C i ∩ Xu) ∪ (C j ∩ Xu)) \ zb).card ∧
      lb ⊆ ((C i ∩ Xu) ∪ (C j ∩ Xu)) \ zb ∧
      lb.card ≤ ((C i ∩ Xu).card - (C j ∩ Xu).card) + ((C j ∩ Xu).card - (C i ∩ Xu).card) ∧
      (∀ z ∈ ((C i ∩ Xu) ∪ (C j ∩ Xu)) \ zb, p z ∈ ((C i ∩ Xu) ∪ (C j ∩ Xu)) \ zb) ∧
      (∀ z ∈ ((C i ∩ Xu) ∪ (C j ∩ Xu)) \ zb, p (p z) = z) ∧
      (∀ z ∈ ((C i ∩ Xu) ∪ (C j ∩ Xu)) \ zb, p z ≠ z) ∧
      (∀ z ∈ ((C i ∩ Xu) ∪ (C j ∩ Xu)) \ zb, s(z, p z) ∈ F ∧ s(z, p z) ∉ U) ∧
      (∀ z ∈ ((C i ∩ Xu) ∪ (C j ∩ Xu)) \ zb, z ∉ lb →
        (z ∈ C i → p z ∈ C j ∩ Xu) ∧ (z ∈ C j → p z ∈ C i ∩ Xu)) := by
  classical
  by_cases hle : (C i ∩ Xu).card ≤ (C j ∩ Xu).card
  · obtain ⟨zb, lb, p, hzb, hzbc, hzbd, hpar, hlb, hlbc, hmaps, hinv, hne, hr, hacross, hback⟩ :=
      exists_class_pair_perturbed_involution_aux hgrid hW'W hi hj hij hXW' hq hU hle hsizei
    refine ⟨zb, lb, p, fun z hz => Finset.mem_union_right _ (hzb hz), hzbc, by omega, hpar, ?_,
      by omega, hmaps, hinv, hne, hr, ?_⟩
    · intro z hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_sdiff.1 (hlb hz)
      exact Finset.mem_sdiff.2 ⟨Finset.mem_union_right _ hz1, hz2⟩
    · intro z hz hzlb
      obtain ⟨hzU, hzzb⟩ := Finset.mem_sdiff.1 hz
      have hzXu : z ∈ Xu := by
        rcases Finset.mem_union.1 hzU with h | h <;> exact (Finset.mem_inter.1 h).2
      refine ⟨fun hzi => hacross z (Finset.mem_inter.2 ⟨hzi, hzXu⟩), fun hzj => ?_⟩
      exact hback z (Finset.mem_sdiff.2 ⟨Finset.mem_inter.2 ⟨hzj, hzXu⟩, hzzb⟩) hzlb
  · have hle' : (C j ∩ Xu).card ≤ (C i ∩ Xu).card := by omega
    obtain ⟨zb, lb, p, hzb, hzbc, hzbd, hpar, hlb, hlbc, hmaps, hinv, hne, hr, hacross, hback⟩ :=
      exists_class_pair_perturbed_involution_aux hgrid hW'W hj hi (Ne.symm hij) hXW' hq hU hle'
        hsizej
    have hcomm : (C j ∩ Xu) ∪ (C i ∩ Xu) = (C i ∩ Xu) ∪ (C j ∩ Xu) := Finset.union_comm _ _
    rw [hcomm] at hpar hmaps hinv hne hr
    refine ⟨zb, lb, p, fun z hz => Finset.mem_union_left _ (hzb hz), hzbc, by omega, hpar, ?_,
      by omega, hmaps, hinv, hne, hr, ?_⟩
    · intro z hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_sdiff.1 (hlb hz)
      exact Finset.mem_sdiff.2 ⟨Finset.mem_union_left _ hz1, hz2⟩
    · intro z hz hzlb
      obtain ⟨hzU, hzzb⟩ := Finset.mem_sdiff.1 hz
      have hzXu : z ∈ Xu := by
        rcases Finset.mem_union.1 hzU with h | h <;> exact (Finset.mem_inter.1 h).2
      refine ⟨fun hzi => ?_, fun hzj => hacross z (Finset.mem_inter.2 ⟨hzj, hzXu⟩)⟩
      exact hback z (Finset.mem_sdiff.2 ⟨Finset.mem_inter.2 ⟨hzi, hzXu⟩, hzzb⟩) hzlb

/-! ### One class, with a few foreign vertices thrown in -/

/-- **A class absorbs a few foreign vertices.**  The trace of one class on the link, together with
a small set `Z` of vertices from elsewhere, carries a fixed-point-free involution by edges of `F`
outside `U`, as soon as the trace is large enough to pay for `Z` twice over.  This is how the
parity corrections of the other blocks of a perturbed link are absorbed by the orphan class. -/
theorem exists_class_involution_with_extras
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (hW'W : W' ⊆ W)
    {k : ℕ} (hk : k < gridSize ε K * gridSize ε K)
    {Xu Z : Finset V} (hXW' : Xu ⊆ W') (hZXu : Z ⊆ Xu)
    {U : Finset (Sym2 V)} {m q : ℕ}
    (hq : ∀ l < gridSize ε K * gridSize ε K, (C l).card = q)
    (hU : ∀ a ∈ Xu, ((C k ∩ Xu).filter (fun b => s(a, b) ∈ U)).card ≤ m)
    (heven : Even ((C k ∩ Xu) ∪ Z).card)
    (hsize : 2 * q + 8 * m + 4 * Z.card + 8 ≤ 4 * (C k ∩ Xu).card) :
    ∃ p : V → V, (∀ z ∈ (C k ∩ Xu) ∪ Z, p z ∈ (C k ∩ Xu) ∪ Z) ∧
      (∀ z ∈ (C k ∩ Xu) ∪ Z, p (p z) = z) ∧ (∀ z ∈ (C k ∩ Xu) ∪ Z, p z ≠ z) ∧
      (∀ z ∈ (C k ∩ Xu) ∪ Z, s(z, p z) ∈ F ∧ s(z, p z) ∉ U) := by
  classical
  set A : Finset V := C k ∩ Xu with hAdef
  set T : Finset V := A ∪ Z with hTdef
  have hAXu : A ⊆ Xu := fun z hz => (Finset.mem_inter.1 hz).2
  have hTXu : T ⊆ Xu := by
    intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · exact hAXu h
    · exact hZXu h
  refine exists_involution_of_half_degree T (fun a b => s(a, b) ∈ F ∧ s(a, b) ∉ U) ?_ heven ?_
  · intro a b hab
    rw [Sym2.eq_swap]
    exact hab
  · intro a ha
    show T.card ≤ 2 * (T.filter (fun b => b ≠ a ∧ (s(a, b) ∈ F ∧ s(a, b) ∉ U))).card
    have haXu : a ∈ Xu := hTXu ha
    have hbad := card_bad_partners_in_class_le hgrid hW'W hk
      (T := A) (fun z hz => (Finset.mem_inter.1 hz).1) (fun z hz => hXW' (hAXu hz))
      (hXW' haXu) hq (hU a haXu)
    have hsplit : (A.filter (fun b => b ≠ a ∧ (s(a, b) ∈ F ∧ s(a, b) ∉ U))).card
        + (A.filter (fun b => ¬ (b ≠ a ∧ (s(a, b) ∈ F ∧ s(a, b) ∉ U)))).card = A.card :=
      Finset.card_filter_add_card_filter_not _
    have hsub : A.filter (fun b => b ≠ a ∧ (s(a, b) ∈ F ∧ s(a, b) ∉ U))
        ⊆ T.filter (fun b => b ≠ a ∧ (s(a, b) ∈ F ∧ s(a, b) ∉ U)) := by
      intro z hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
      exact Finset.mem_filter.2 ⟨Finset.mem_union_left _ hz1, hz2⟩
    have hcard := Finset.card_le_card hsub
    have hTcard : T.card ≤ A.card + Z.card := Finset.card_union_le _ _
    omega


/-! ### One whole perturbed link, paired class for class -/

/-- **A perturbed link is paired class for class, with the leftovers confined to the orphan class
and a small correction.**

Let `ρ` be a permutation of the `h` row indices with inverse `σ`, not fixing the corner class:
`ρ (y u) ≠ x u`.  The classes of the region of `u` are paired up as in
`BKLO.exists_classMatched_pairing_orphan` — the corner class with the row class of `B = σ (x u)`,
the row class `β` with the column class `ρ β`, the column class `A = ρ (y u)` left over — but now
the traces of the two classes of a block on the link `Xu` need not have the same size, because the
link is **perturbed**.

Each block absorbs its own imbalance (`BKLO.exists_class_pair_perturbed_involution`): the vertices
that cannot be sent across are paired *inside their own class*, and there are at most as many of
them per block as the difference of the two traces of the block.  The parity corrections of the
blocks — at most one vertex each, and only at a block whose two traces differ — are absorbed by the
orphan class (`BKLO.exists_class_involution_with_extras`).

So the whole link is paired by edges of `F` outside `U`, and every vertex outside the leftover set
`e` obeys the cross-side rule, where `e` is the orphan class together with at most `2 D + f`
further vertices, `D` being the **sum** over the classes of the region of the deviation of the
trace of the class from the unperturbed value `c`.  This is the sharp form: a block whose two
traces are equal contributes nothing at all — neither a leftover nor a parity vertex — so the
bound is by the total deviation of the perturbation and not by `h` times its maximum. -/
theorem exists_classMatched_pairing_perturbed
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (hW'W : W' ⊆ W)
    {u : V} (hu : u ∈ W \ W') {q m c D f : ℕ}
    (hq : ∀ k < gridSize ε K * gridSize ε K, (C k).card = q)
    {Xu : Finset V} (hXW' : Xu ⊆ W')
    (hXeven : Even Xu.card)
    {ρ σ : ℕ → ℕ} (hρlt : ∀ β < gridSize ε K, ρ β < gridSize ε K)
    (hσlt : ∀ α < gridSize ε K, σ α < gridSize ε K)
    (hσρ : ∀ β < gridSize ε K, σ (ρ β) = β) (hρσ : ∀ α < gridSize ε K, ρ (σ α) = α)
    (hAne : ρ (y u) ≠ x u)
    {U : Finset (Sym2 V)}
    (hU : ∀ a ∈ Xu, ∀ k < gridSize ε K * gridSize ε K,
      ((C k ∩ Xu).filter (fun b => s(a, b) ∈ U)).card ≤ m)
    (hdev : ∑ i ∈ gridIdx (gridSize ε K) (x u) (y u),
      (((C i ∩ Xu).card - c) + (c - (C i ∩ Xu).card)) ≤ D)
    (hfor : (Xu \ gridRegion (gridSize ε K) C (x u) (y u)).card ≤ f)
    (hsize : ∀ i ∈ gridIdx (gridSize ε K) (x u) (y u),
      2 * q + 8 * m + 4 * gridSize ε K + 4 * f + 16 ≤ 4 * (C i ∩ Xu).card) :
    ∃ (p : V → V) (e : Finset V),
      (∀ a ∈ Xu, p a ∈ Xu) ∧ (∀ a ∈ Xu, p (p a) = a) ∧ (∀ a ∈ Xu, p a ≠ a) ∧
      (∀ a ∈ Xu, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
      e ⊆ Xu ∧ (C (ρ (y u) * gridSize ε K + y u) ∩ Xu ⊆ e) ∧
      (e \ C (ρ (y u) * gridSize ε K + y u)).card ≤ 2 * D + f ∧
      ∀ (a : V) (α β : ℕ), α < gridSize ε K → β < gridSize ε K →
        a ∈ C (α * gridSize ε K + β) → a ∈ Xu → a ∉ e →
        IsCrossSideAt (gridSize ε K) C x y α β u (p a) (ρ β) (σ α) := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hxu : x u < h := hgrid.rowLt u hu
  have hyu : y u < h := hgrid.colLt u hu
  set rowI : ℕ → ℕ := fun β => x u * h + β with hrowIdef
  set colI : ℕ → ℕ := fun α => α * h + y u with hcolIdef
  set A : ℕ := ρ (y u) with hAdef
  set B : ℕ := σ (x u) with hBdef
  -- the vertices of the link outside the region of `u`
  set Fo : Finset V := Xu \ gridRegion h C (x u) (y u) with hFodef
  have hAlt : A < h := hρlt (y u) hyu
  have hBlt : B < h := hσlt (x u) hxu
  have hρB : ρ B = x u := hρσ (x u) hxu
  have hBne : B ≠ y u := by
    intro hcon
    exact hAne (by rw [hAdef, ← hcon, hρB])
  have hmemreg : ∀ k ∈ gridIdx h (x u) (y u), ∀ z ∈ C k, z ∈ gridRegion h C (x u) (y u) := by
    intro k hk z hz
    rw [gridRegion_eq_biUnion]
    exact Finset.mem_biUnion.2 ⟨k, hk, hz⟩
  have hrowmem : ∀ β < h, rowI β ∈ gridIdx h (x u) (y u) := fun β hβ =>
    mem_gridIdx.2 (Or.inl ⟨β, hβ, rfl⟩)
  have hcolmem : ∀ α < h, colI α ∈ gridIdx h (x u) (y u) := fun α hα =>
    mem_gridIdx.2 (Or.inr ⟨α, hα, rfl⟩)
  have hrowlt : ∀ β < h, rowI β < h * h := fun β hβ => gridIdx_lt hxu hyu (hrowmem β hβ)
  have hcollt : ∀ α < h, colI α < h * h := fun α hα => gridIdx_lt hxu hyu (hcolmem α hα)
  have hρinj : ∀ β < h, ∀ β' < h, ρ β = ρ β' → β = β' := by
    intro β hβ β' hβ' heq
    rw [← hσρ β hβ, ← hσρ β' hβ', heq]
  have hrowinj : ∀ γ δ : ℕ, rowI γ = rowI δ → γ = δ := by
    intro γ δ hcon
    simpa [hrowIdef] using hcon
  have hcolinj : ∀ γ < h, ∀ δ < h, colI γ = colI δ → γ = δ := by
    intro γ hγ δ hδ hcon
    exact (gridDigits_inj hyu hyu (by simpa [hcolIdef] using hcon)).1
  have hrowcol : ∀ γ < h, ∀ δ < h, rowI γ = colI δ → γ = y u ∧ δ = x u := by
    intro γ hγ δ hδ hcon
    have h1 := gridDigits_inj hγ hyu (by simpa [hrowIdef, hcolIdef] using hcon)
    exact ⟨h1.2, h1.1.symm⟩
  have hcornercol : colI (x u) = rowI (y u) := by rw [hcolIdef, hrowIdef]
  -- the partner class of a block
  set Jj : ℕ → ℕ := fun β => if β = y u then rowI B else colI (ρ β) with hJjdef
  -- the blocks
  set T : ℕ → Finset V := fun β =>
    if β = y u then (C (rowI (y u)) ∩ Xu) ∪ (C (rowI B) ∩ Xu)
    else if β = B then C (colI A) ∩ Xu
    else (C (rowI β) ∩ Xu) ∪ (C (colI (ρ β)) ∩ Xu) with hTdef
  set I : Finset ℕ := Finset.range h with hIdef
  have hIlt : ∀ β ∈ I, β < h := fun β hβ => Finset.mem_range.1 hβ
  have hyuI : y u ∈ I := Finset.mem_range.2 hyu
  have hBI : B ∈ I := Finset.mem_range.2 hBlt
  have hTy : T (y u) = (C (rowI (y u)) ∩ Xu) ∪ (C (rowI B) ∩ Xu) := by
    simp only [hTdef, reduceIte]
  have hTB : T B = C (colI A) ∩ Xu := by
    simp only [hTdef, if_neg hBne, reduceIte]
  have hTo : ∀ β, β ≠ y u → β ≠ B →
      T β = (C (rowI β) ∩ Xu) ∪ (C (colI (ρ β)) ∩ Xu) := by
    intro β h1 h2
    simp only [hTdef, if_neg h1, if_neg h2]
  have hJjy : Jj (y u) = rowI B := by simp only [hJjdef, reduceIte]
  have hJjo : ∀ β, β ≠ y u → Jj β = colI (ρ β) := by
    intro β h1
    simp only [hJjdef, if_neg h1]
  have hTpair : ∀ β, β ≠ B → T β = (C (rowI β) ∩ Xu) ∪ (C (Jj β) ∩ Xu) := by
    intro β hβB
    by_cases hβy : β = y u
    · subst hβy
      rw [hTy, hJjy]
    · rw [hTo β hβy hβB, hJjo β hβy]
  -- which classes a block lives in
  have hTclass : ∀ β ∈ I, ∀ z ∈ T β, ∃ l : ℕ, l < h * h ∧ z ∈ C l ∧
      ((β = y u ∧ (l = rowI (y u) ∨ l = rowI B)) ∨ (β = B ∧ l = colI A) ∨
        (β ≠ y u ∧ β ≠ B ∧ (l = rowI β ∨ l = colI (ρ β)))) := by
    intro β hβ z hz
    by_cases hcase : β = y u
    · subst hcase
      rw [hTy] at hz
      rcases Finset.mem_union.1 hz with h1 | h1
      · exact ⟨rowI (y u), hrowlt _ hyu, (Finset.mem_inter.1 h1).1, Or.inl ⟨rfl, Or.inl rfl⟩⟩
      · exact ⟨rowI B, hrowlt _ hBlt, (Finset.mem_inter.1 h1).1, Or.inl ⟨rfl, Or.inr rfl⟩⟩
    · by_cases hcase' : β = B
      · subst hcase'
        rw [hTB] at hz
        exact ⟨colI A, hcollt _ hAlt, (Finset.mem_inter.1 hz).1, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      · rw [hTo β hcase hcase'] at hz
        rcases Finset.mem_union.1 hz with h1 | h1
        · exact ⟨rowI β, hrowlt _ (hIlt β hβ), (Finset.mem_inter.1 h1).1,
            Or.inr (Or.inr ⟨hcase, hcase', Or.inl rfl⟩)⟩
        · exact ⟨colI (ρ β), hcollt _ (hρlt β (hIlt β hβ)), (Finset.mem_inter.1 h1).1,
            Or.inr (Or.inr ⟨hcase, hcase', Or.inr rfl⟩)⟩
  have hTsub : ∀ β ∈ I, T β ⊆ Xu := by
    intro β hβ z hz
    by_cases hcase : β = y u
    · subst hcase
      rw [hTy] at hz
      rcases Finset.mem_union.1 hz with h1 | h1 <;> exact (Finset.mem_inter.1 h1).2
    · by_cases hcase' : β = B
      · subst hcase'
        rw [hTB] at hz
        exact (Finset.mem_inter.1 hz).2
      · rw [hTo β hcase hcase'] at hz
        rcases Finset.mem_union.1 hz with h1 | h1 <;> exact (Finset.mem_inter.1 h1).2
  -- the blocks lie in the region
  have hTgrid : ∀ β ∈ I, ∀ z ∈ T β, z ∈ gridRegion h C (x u) (y u) := by
    intro β hβ z hz
    obtain ⟨l, hllt, hzl, hlcase⟩ := hTclass β hβ z hz
    have hlmem : l ∈ gridIdx h (x u) (y u) := by
      rcases hlcase with ⟨-, hc⟩ | ⟨-, hc⟩ | ⟨-, -, hc⟩
      · rcases hc with rfl | rfl
        · exact hrowmem _ hyu
        · exact hrowmem _ hBlt
      · exact hc ▸ hcolmem _ hAlt
      · rcases hc with rfl | rfl
        · exact hrowmem _ (hIlt β hβ)
        · exact hcolmem _ (hρlt β (hIlt β hβ))
    exact hmemreg l hlmem z hzl
  -- every vertex of the link inside the region lies in a block
  have hclassU : ∀ z ∈ Xu, z ∉ Fo → ∃ k ∈ gridIdx h (x u) (y u), z ∈ C k := by
    intro z hz hzF
    have hmem : z ∈ gridRegion h C (x u) (y u) := by
      by_contra hcon
      exact hzF (Finset.mem_sdiff.2 ⟨hz, hcon⟩)
    rw [gridRegion_eq_biUnion] at hmem
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.1 hmem
    exact ⟨k, hk, hzk⟩
  have hunion : I.biUnion T = Xu \ Fo := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro z hz
      obtain ⟨β, hβ, hzβ⟩ := Finset.mem_biUnion.1 hz
      refine Finset.mem_sdiff.2 ⟨hTsub β hβ hzβ, ?_⟩
      intro hcon
      exact (Finset.mem_sdiff.1 hcon).2 (hTgrid β hβ z hzβ)
    · intro z hzs
      obtain ⟨hz, hzF⟩ := Finset.mem_sdiff.1 hzs
      obtain ⟨k, hk, hzk⟩ := hclassU z hz hzF
      rcases mem_gridIdx.1 hk with ⟨j, hj, rfl⟩ | ⟨l, hl, rfl⟩
      · by_cases hjy : j = y u
        · refine Finset.mem_biUnion.2 ⟨y u, hyuI, ?_⟩
          rw [hTy]
          exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hjy ▸ hzk, hz⟩)
        · by_cases hjB : j = B
          · refine Finset.mem_biUnion.2 ⟨y u, hyuI, ?_⟩
            rw [hTy]
            exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hjB ▸ hzk, hz⟩)
          · refine Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, ?_⟩
            rw [hTo j hjy hjB]
            exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hzk, hz⟩)
      · by_cases hlx : l = x u
        · refine Finset.mem_biUnion.2 ⟨y u, hyuI, ?_⟩
          rw [hTy]
          refine Finset.mem_union_left _ (Finset.mem_inter.2 ⟨?_, hz⟩)
          rw [← hcornercol, ← hlx]
          exact hzk
        · by_cases hlA : l = A
          · refine Finset.mem_biUnion.2 ⟨B, hBI, ?_⟩
            rw [hTB]
            exact Finset.mem_inter.2 ⟨hlA ▸ hzk, hz⟩
          · have hσly : σ l ≠ y u := by
              intro hcon
              exact hlA (by rw [← hρσ l hl, hcon, ← hAdef])
            have hσlB : σ l ≠ B := by
              intro hcon
              exact hlx (by rw [← hρσ l hl, hcon, hρB])
            refine Finset.mem_biUnion.2 ⟨σ l, Finset.mem_range.2 (hσlt l hl), ?_⟩
            rw [hTo (σ l) hσly hσlB]
            refine Finset.mem_union_right _ (Finset.mem_inter.2 ⟨?_, hz⟩)
            rwa [hρσ l hl]
  -- the index of a class determines its block
  have hkey : ∀ β < h, ∀ β' < h, ∀ l : ℕ,
      ((β = y u ∧ (l = rowI (y u) ∨ l = rowI B)) ∨ (β = B ∧ l = colI A) ∨
        (β ≠ y u ∧ β ≠ B ∧ (l = rowI β ∨ l = colI (ρ β)))) →
      ((β' = y u ∧ (l = rowI (y u) ∨ l = rowI B)) ∨ (β' = B ∧ l = colI A) ∨
        (β' ≠ y u ∧ β' ≠ B ∧ (l = rowI β' ∨ l = colI (ρ β')))) → β = β' := by
    have hcorA : rowI (y u) ≠ colI A := by
      intro hcon
      exact hAne (hrowcol (y u) hyu A hAlt hcon).2
    have hrowBA : rowI B ≠ colI A := by
      intro hcon
      exact hBne (hrowcol B hBlt A hAlt hcon).1
    intro β hβ β' hβ' l hl hl'
    rcases hl with ⟨hβy, hcase⟩ | ⟨hβB, hcase⟩ | ⟨hβy, hβB, hcase⟩
    · rcases hl' with ⟨hβ'y, -⟩ | ⟨hβ'B, hcase'⟩ | ⟨hβ'y, hβ'B, hcase'⟩
      · rw [hβy, hβ'y]
      · rcases hcase with h1 | h1
        · exact absurd (h1.symm.trans hcase') hcorA
        · exact absurd (h1.symm.trans hcase') hrowBA
      · rcases hcase with h1 | h1 <;> rcases hcase' with h2 | h2
        · exact absurd (hrowinj _ _ (h1.symm.trans h2)).symm hβ'y
        · exact absurd (hρinj β' hβ' B hBlt
            (((hrowcol (y u) hyu (ρ β') (hρlt β' hβ') (h1.symm.trans h2)).2).trans hρB.symm))
            hβ'B
        · exact absurd (hrowinj _ _ (h1.symm.trans h2)).symm hβ'B
        · exact absurd (hrowcol B hBlt (ρ β') (hρlt β' hβ') (h1.symm.trans h2)).1 hBne
    · rcases hl' with ⟨hβ'y, hcase'⟩ | ⟨hβ'B, -⟩ | ⟨hβ'y, hβ'B, hcase'⟩
      · rcases hcase' with h1 | h1
        · exact absurd (h1.symm.trans hcase) hcorA
        · exact absurd (h1.symm.trans hcase) hrowBA
      · rw [hβB, hβ'B]
      · rcases hcase' with h2 | h2
        · exact absurd (hrowcol β' hβ' A hAlt (h2.symm.trans hcase)).1 hβ'y
        · exact absurd (hρinj β' hβ' (y u) hyu
            ((hcolinj (ρ β') (hρlt β' hβ') A hAlt (h2.symm.trans hcase)).trans hAdef)) hβ'y
    · rcases hl' with ⟨hβ'y, hcase'⟩ | ⟨hβ'B, hcase'⟩ | ⟨hβ'y, hβ'B, hcase'⟩
      · rcases hcase with h1 | h1 <;> rcases hcase' with h2 | h2
        · exact absurd (hrowinj _ _ (h1.symm.trans h2)) hβy
        · exact absurd (hrowinj _ _ (h1.symm.trans h2)) hβB
        · exact absurd (hρinj β hβ B hBlt
            (((hrowcol (y u) hyu (ρ β) (hρlt β hβ) (h2.symm.trans h1)).2).trans hρB.symm)) hβB
        · exact absurd (hrowcol B hBlt (ρ β) (hρlt β hβ) (h2.symm.trans h1)).1 hBne
      · rcases hcase with h1 | h1
        · exact absurd (hrowcol β hβ A hAlt (h1.symm.trans hcase')).1 hβy
        · exact absurd (hρinj β hβ (y u) hyu
            ((hcolinj (ρ β) (hρlt β hβ) A hAlt (h1.symm.trans hcase')).trans hAdef)) hβy
      · rcases hcase with h1 | h1 <;> rcases hcase' with h2 | h2
        · exact hrowinj _ _ (h1.symm.trans h2)
        · exact absurd (hrowcol β hβ (ρ β') (hρlt β' hβ') (h1.symm.trans h2)).1 hβy
        · exact absurd (hrowcol β' hβ' (ρ β) (hρlt β hβ) (h2.symm.trans h1)).1 hβ'y
        · exact hρinj β hβ β' hβ'
            (hcolinj (ρ β) (hρlt β hβ) (ρ β') (hρlt β' hβ') (h1.symm.trans h2))
  -- the blocks are pairwise disjoint
  have hdisjT : ∀ β ∈ I, ∀ β' ∈ I, β ≠ β' → Disjoint (T β) (T β') := by
    intro β hβ β' hβ' hne
    refine Finset.disjoint_left.2 fun z hz hz' => ?_
    obtain ⟨l, hllt, hzl, hlcase⟩ := hTclass β hβ z hz
    obtain ⟨l', hl'lt, hzl', hl'case⟩ := hTclass β' hβ' z hz'
    have hll' : l = l' := by
      by_contra hcon
      exact (Finset.disjoint_left.1 (hgrid.classDisjoint l hllt l' hl'lt hcon)) hzl hzl'
    subst hll'
    exact hne (hkey β (hIlt β hβ) β' (hIlt β' hβ') l hlcase hl'case)
  -- the partner class of a block, and its index
  have hJjlt : ∀ β ∈ I, Jj β < h * h := by
    intro β hβ
    have hβlt : β < h := hIlt β hβ
    by_cases hβy : β = y u
    · rw [hβy, hJjy]; exact hrowlt _ hBlt
    · rw [hJjo β hβy]; exact hcollt _ (hρlt β hβlt)
  have hJjmem : ∀ β ∈ I, Jj β ∈ gridIdx h (x u) (y u) := by
    intro β hβ
    have hβlt : β < h := hIlt β hβ
    by_cases hβy : β = y u
    · rw [hβy, hJjy]; exact hrowmem _ hBlt
    · rw [hJjo β hβy]; exact hcolmem _ (hρlt β hβlt)
  have hidxne : ∀ β ∈ I, rowI β ≠ Jj β := by
    intro β hβ
    have hβlt : β < h := hIlt β hβ
    by_cases hβy : β = y u
    · rw [hβy, hJjy]
      intro hcon
      exact hBne (hrowinj _ _ hcon).symm
    · rw [hJjo β hβy]
      intro hcon
      exact hβy (hrowcol β hβlt _ (hρlt β hβlt) hcon).1
  -- the deviation of the trace of a class of the region from the unperturbed value `c`
  set dev : ℕ → ℕ := fun l => ((C l ∩ Xu).card - c) + (c - (C l ∩ Xu).card) with hdevdef
  -- each block off the orphan carries a perturbed involution
  have hblock : ∀ β : ℕ, ∃ (zbβ lbβ : Finset V) (pbβ : V → V), β ∈ I → β ≠ B →
      (zbβ ⊆ T β ∧ zbβ.card ≤ 1 ∧ Even (T β \ zbβ).card ∧ lbβ ⊆ T β \ zbβ ∧
        lbβ.card + zbβ.card ≤ 2 * (dev (rowI β) + dev (Jj β)) ∧
        (∀ z ∈ T β \ zbβ, pbβ z ∈ T β \ zbβ) ∧ (∀ z ∈ T β \ zbβ, pbβ (pbβ z) = z) ∧
        (∀ z ∈ T β \ zbβ, pbβ z ≠ z) ∧
        (∀ z ∈ T β \ zbβ, s(z, pbβ z) ∈ F ∧ s(z, pbβ z) ∉ U) ∧
        (∀ z ∈ T β \ zbβ, z ∉ lbβ →
          (z ∈ C (rowI β) → pbβ z ∈ C (Jj β) ∩ Xu) ∧
          (z ∈ C (Jj β) → pbβ z ∈ C (rowI β) ∩ Xu))) := by
    intro β
    by_cases hβ : β ∈ I
    swap
    · exact ⟨∅, ∅, id, fun hcon => absurd hcon hβ⟩
    by_cases hβB : β = B
    · exact ⟨∅, ∅, id, fun _ hcon => absurd hβB hcon⟩
    have hβlt : β < h := hIlt β hβ
    have hsi : q + 4 * m + 6 ≤ 2 * (C (rowI β) ∩ Xu).card := by
      have h1 := hsize _ (hrowmem β hβlt)
      omega
    have hsj : q + 4 * m + 6 ≤ 2 * (C (Jj β) ∩ Xu).card := by
      have h1 := hsize _ (hJjmem β hβ)
      omega
    obtain ⟨zbβ, lbβ, pbβ, hz1, hz2, hz2d, hzpar, hlb1, hlb2, hm1, hm2, hm3, hm4, hcross⟩ :=
      exists_class_pair_perturbed_involution hgrid hW'W (hrowlt β hβlt) (hJjlt β hβ)
        (hidxne β hβ) hXW' hq hU hsi hsj
    have hTβ : (C (rowI β) ∩ Xu) ∪ (C (Jj β) ∩ Xu) = T β := (hTpair β hβB).symm
    rw [hTβ] at hz1 hzpar hlb1 hm1 hm2 hm3 hm4 hcross
    have hlbd : lbβ.card + zbβ.card ≤ 2 * (dev (rowI β) + dev (Jj β)) := by
      rw [hdevdef]
      simp only []
      omega
    exact ⟨zbβ, lbβ, pbβ, fun _ _ =>
      ⟨hz1, hz2, hzpar, hlb1, hlbd, hm1, hm2, hm3, hm4, hcross⟩⟩
  choose zb lb pb hpb using hblock
  have hzbT : ∀ β ∈ I, β ≠ B → zb β ⊆ T β := fun β h1 h2 => (hpb β h1 h2).1
  have hzbcard : ∀ β ∈ I, β ≠ B → (zb β).card ≤ 1 := fun β h1 h2 => (hpb β h1 h2).2.1
  have hbpar : ∀ β ∈ I, β ≠ B → Even (T β \ zb β).card := fun β h1 h2 => (hpb β h1 h2).2.2.1
  have hlbsub : ∀ β ∈ I, β ≠ B → lb β ⊆ T β \ zb β :=
    fun β h1 h2 => (hpb β h1 h2).2.2.2.1
  have hlbcard : ∀ β ∈ I, β ≠ B →
      (lb β).card + (zb β).card ≤ 2 * (dev (rowI β) + dev (Jj β)) :=
    fun β h1 h2 => (hpb β h1 h2).2.2.2.2.1
  have hbmaps : ∀ β ∈ I, β ≠ B → ∀ z ∈ T β \ zb β, pb β z ∈ T β \ zb β :=
    fun β h1 h2 => (hpb β h1 h2).2.2.2.2.2.1
  have hbinv : ∀ β ∈ I, β ≠ B → ∀ z ∈ T β \ zb β, pb β (pb β z) = z :=
    fun β h1 h2 => (hpb β h1 h2).2.2.2.2.2.2.1
  have hbne : ∀ β ∈ I, β ≠ B → ∀ z ∈ T β \ zb β, pb β z ≠ z :=
    fun β h1 h2 => (hpb β h1 h2).2.2.2.2.2.2.2.1
  have hbr : ∀ β ∈ I, β ≠ B → ∀ z ∈ T β \ zb β, s(z, pb β z) ∈ F ∧ s(z, pb β z) ∉ U :=
    fun β h1 h2 => (hpb β h1 h2).2.2.2.2.2.2.2.2.1
  have hbcross : ∀ β ∈ I, β ≠ B → ∀ z ∈ T β \ zb β, z ∉ lb β →
      (z ∈ C (rowI β) → pb β z ∈ C (Jj β) ∩ Xu) ∧
      (z ∈ C (Jj β) → pb β z ∈ C (rowI β) ∩ Xu) :=
    fun β h1 h2 => (hpb β h1 h2).2.2.2.2.2.2.2.2.2
  -- the parity corrections of the blocks, collected
  set Z : Finset V := (I.erase B).biUnion zb ∪ Fo with hZdef
  have hZmem : ∀ z ∈ Z, (∃ β ∈ I, β ≠ B ∧ z ∈ zb β) ∨ z ∈ Fo := by
    intro z hz
    rcases Finset.mem_union.1 hz with h1 | h1
    · obtain ⟨β, hβ, hzβ⟩ := Finset.mem_biUnion.1 h1
      exact Or.inl ⟨β, Finset.mem_of_mem_erase hβ, Finset.ne_of_mem_erase hβ, hzβ⟩
    · exact Or.inr h1
  have hzbZ : ∀ γ ∈ I, γ ≠ B → zb γ ⊆ Z := by
    intro γ hγ hγB z hz
    rw [hZdef]
    exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨γ, Finset.mem_erase.2 ⟨hγB, hγ⟩, hz⟩)
  have hFoZ : Fo ⊆ Z := by
    intro z hz
    rw [hZdef]
    exact Finset.mem_union_right _ hz
  have hZsub : Z ⊆ Xu := by
    intro z hz
    rcases hZmem z hz with ⟨β, hβ, hβB, hzβ⟩ | h1
    · exact hTsub β hβ (hzbT β hβ hβB hzβ)
    · exact (Finset.mem_sdiff.1 h1).1
  have hZcard : Z.card ≤ h + f := by
    have h1 : ((I.erase B).biUnion zb).card ≤ h := by
      refine le_trans Finset.card_biUnion_le ?_
      calc ∑ β ∈ I.erase B, (zb β).card ≤ ∑ _β ∈ I.erase B, 1 :=
            Finset.sum_le_sum fun β hβ =>
              hzbcard β (Finset.mem_of_mem_erase hβ) (Finset.ne_of_mem_erase hβ)
        _ = (I.erase B).card := by simp
        _ ≤ I.card := Finset.card_le_card (Finset.erase_subset _ _)
        _ = h := by simp [hIdef]
    have h2 := Finset.card_union_le ((I.erase B).biUnion zb) Fo
    have h3 : Z.card ≤ ((I.erase B).biUnion zb).card + Fo.card := by
      rw [hZdef]; exact h2
    omega
  have hZcardS : Z.card ≤ (∑ β ∈ I.erase B, (zb β).card) + f := by
    have h1 : ((I.erase B).biUnion zb).card ≤ ∑ β ∈ I.erase B, (zb β).card :=
      Finset.card_biUnion_le
    have h2 := Finset.card_union_le ((I.erase B).biUnion zb) Fo
    have h3 : Z.card ≤ ((I.erase B).biUnion zb).card + Fo.card := by
      rw [hZdef]; exact h2
    omega
  -- the blocks of the perturbed link: the orphan block absorbs the parity corrections
  set T' : ℕ → Finset V := fun β =>
    if β = B then (C (colI A) ∩ Xu) ∪ Z else T β \ zb β with hT'def
  have hT'B : T' B = (C (colI A) ∩ Xu) ∪ Z := by
    show (if B = B then (C (colI A) ∩ Xu) ∪ Z else T B \ zb B) = (C (colI A) ∩ Xu) ∪ Z
    rw [if_pos rfl]
  have hT'o : ∀ β, β ≠ B → T' β = T β \ zb β := by
    intro β hβ
    show (if β = B then (C (colI A) ∩ Xu) ∪ Z else T β \ zb β) = T β \ zb β
    rw [if_neg hβ]
  have hT'sub : ∀ β ∈ I, T' β ⊆ Xu := by
    intro β hβ
    by_cases hβB : β = B
    · subst hβB
      rw [hT'B]
      intro z hz
      rcases Finset.mem_union.1 hz with h1 | h1
      · exact (Finset.mem_inter.1 h1).2
      · exact hZsub h1
    · rw [hT'o β hβB]
      exact fun z hz => hTsub β hβ (Finset.mem_sdiff.1 hz).1
  have hT'oZ : ∀ β ∈ I, β ≠ B → Disjoint (T β \ zb β) Z := by
    intro β hβ hβB
    refine Finset.disjoint_left.2 fun z hz hzZ => ?_
    obtain ⟨hzT, hznot⟩ := Finset.mem_sdiff.1 hz
    rcases hZmem z hzZ with ⟨γ, hγ, hγB, hzγ⟩ | hzF
    · by_cases hβγ : β = γ
      · exact hznot (hβγ ▸ hzγ)
      · exact (Finset.disjoint_left.1 (hdisjT β hβ γ hγ hβγ)) hzT (hzbT γ hγ hγB hzγ)
    · exact (Finset.mem_sdiff.1 hzF).2 (hTgrid β hβ z hzT)
  have hT'BT : ∀ β ∈ I, β ≠ B → Disjoint (T β \ zb β) ((C (colI A) ∩ Xu) ∪ Z) := by
    intro β hβ hβB
    refine Finset.disjoint_union_right.2 ⟨?_, hT'oZ β hβ hβB⟩
    refine Finset.disjoint_of_subset_left Finset.sdiff_subset ?_
    rw [← hTB]
    exact hdisjT β hβ B hBI hβB
  have hdisjT' : ∀ β ∈ I, ∀ β' ∈ I, β ≠ β' → Disjoint (T' β) (T' β') := by
    intro β hβ β' hβ' hne
    by_cases hβB : β = B
    · subst hβB
      rw [hT'B, hT'o β' (Ne.symm hne)]
      exact (hT'BT β' hβ' (Ne.symm hne)).symm
    · by_cases hβ'B : β' = B
      · subst hβ'B
        rw [hT'B, hT'o β hβB]
        exact hT'BT β hβ hβB
      · rw [hT'o β hβB, hT'o β' hβ'B]
        exact Finset.disjoint_of_subset_left Finset.sdiff_subset
          (Finset.disjoint_of_subset_right Finset.sdiff_subset (hdisjT β hβ β' hβ' hne))
  have hunion' : I.biUnion T' = Xu := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro z hz
      obtain ⟨β, hβ, hzβ⟩ := Finset.mem_biUnion.1 hz
      exact hT'sub β hβ hzβ
    · intro z hz
      by_cases hzF : z ∈ Fo
      · refine Finset.mem_biUnion.2 ⟨B, hBI, ?_⟩
        rw [hT'B]
        exact Finset.mem_union_right _ (hFoZ hzF)
      have hzU : z ∈ I.biUnion T := by
        rw [hunion]
        exact Finset.mem_sdiff.2 ⟨hz, hzF⟩
      obtain ⟨β, hβ, hzβ⟩ := Finset.mem_biUnion.1 hzU
      by_cases hβB : β = B
      · subst hβB
        refine Finset.mem_biUnion.2 ⟨B, hβ, ?_⟩
        rw [hT'B]
        exact Finset.mem_union_left _ (hTB ▸ hzβ)
      · by_cases hzz : z ∈ zb β
        · refine Finset.mem_biUnion.2 ⟨B, hBI, ?_⟩
          rw [hT'B]
          exact Finset.mem_union_right _ (hzbZ β hβ hβB hzz)
        · refine Finset.mem_biUnion.2 ⟨β, hβ, ?_⟩
          rw [hT'o β hβB]
          exact Finset.mem_sdiff.2 ⟨hzβ, hzz⟩
  -- the orphan block has an even number of places
  have hevenB : Even (T' B).card := by
    have hsum : Xu.card = ∑ β ∈ I, (T' β).card := by
      have hpd : (↑I : Set ℕ).PairwiseDisjoint T' := by
        intro β hβ β' hβ' hne
        exact hdisjT' β (Finset.mem_coe.1 hβ) β' (Finset.mem_coe.1 hβ') hne
      rw [← hunion', Finset.card_biUnion hpd]
    have hsplit : (T' B).card + ∑ β ∈ I.erase B, (T' β).card = ∑ β ∈ I, (T' β).card :=
      Finset.add_sum_erase I (fun β => (T' β).card) hBI
    have hev : Even (∑ β ∈ I.erase B, (T' β).card) := by
      refine Finset.even_sum _ fun β hβ => ?_
      have hβI : β ∈ I := Finset.mem_of_mem_erase hβ
      have hβB : β ≠ B := Finset.ne_of_mem_erase hβ
      rw [hT'o β hβB]
      exact hbpar β hβI hβB
    have h1 : Xu.card % 2 = 0 := Nat.even_iff.1 hXeven
    have h2 : (∑ β ∈ I.erase B, (T' β).card) % 2 = 0 := Nat.even_iff.1 hev
    exact Nat.even_iff.2 (by omega)
  -- the orphan block, with the parity corrections thrown in
  have hsizeB : 2 * q + 8 * m + 4 * Z.card + 8 ≤ 4 * (C (colI A) ∩ Xu).card := by
    have h1 := hsize _ (hcolmem A hAlt)
    omega
  obtain ⟨pB, hB1, hB2, hB3, hB4⟩ :=
    exists_class_involution_with_extras hgrid hW'W (hcollt A hAlt) hXW' hZsub hq
      (fun a ha => hU a ha _ (hcollt A hAlt)) (by rw [← hT'B]; exact hevenB) hsizeB
  set pb' : ℕ → V → V := fun β => if β = B then pB else pb β with hpb'def
  have hpb'B : pb' B = pB := by
    show (if B = B then pB else pb B) = pB
    rw [if_pos rfl]
  have hpb'o : ∀ β, β ≠ B → pb' β = pb β := by
    intro β hβ
    show (if β = B then pB else pb β) = pb β
    rw [if_neg hβ]
  -- the blocks glue
  have hmapsT' : ∀ β ∈ I, ∀ z ∈ T' β, pb' β z ∈ T' β := by
    intro β hβ z hz
    by_cases hβB : β = B
    · subst hβB
      rw [hT'B] at hz ⊢
      rw [hpb'B]
      exact hB1 z hz
    · rw [hT'o β hβB] at hz ⊢
      rw [hpb'o β hβB]
      exact hbmaps β hβ hβB z hz
  have hinvT' : ∀ β ∈ I, ∀ z ∈ T' β, pb' β (pb' β z) = z := by
    intro β hβ z hz
    by_cases hβB : β = B
    · subst hβB
      rw [hT'B] at hz
      rw [hpb'B]
      exact hB2 z hz
    · rw [hT'o β hβB] at hz
      rw [hpb'o β hβB]
      exact hbinv β hβ hβB z hz
  have hneT' : ∀ β ∈ I, ∀ z ∈ T' β, pb' β z ≠ z := by
    intro β hβ z hz
    by_cases hβB : β = B
    · subst hβB
      rw [hT'B] at hz
      rw [hpb'B]
      exact hB3 z hz
    · rw [hT'o β hβB] at hz
      rw [hpb'o β hβB]
      exact hbne β hβ hβB z hz
  have hrT' : ∀ β ∈ I, ∀ z ∈ T' β, s(z, pb' β z) ∈ F ∧ s(z, pb' β z) ∉ U := by
    intro β hβ z hz
    by_cases hβB : β = B
    · subst hβB
      rw [hT'B] at hz
      rw [hpb'B]
      exact hB4 z hz
    · rw [hT'o β hβB] at hz
      rw [hpb'o β hβB]
      exact hbr β hβ hβB z hz
  obtain ⟨P, hPeq, hPmaps, hPinv, hPne, hPr⟩ :=
    exists_involution_biUnion I T' pb' (fun a b => s(a, b) ∈ F ∧ s(a, b) ∉ U)
      hdisjT' hmapsT' hinvT' hneT' hrT'
  rw [hunion'] at hPmaps hPinv hPne hPr
  -- the leftovers
  set e : Finset V := ((C (colI A) ∩ Xu) ∪ Z) ∪ (I.erase B).biUnion lb with hedef
  have hcolAeq : colI A = ρ (y u) * h + y u := rfl
  refine ⟨P, e, hPmaps, hPinv, hPne, hPr, ?_, ?_, ?_, ?_⟩
  · -- the leftovers lie in the link
    intro z hz
    rcases Finset.mem_union.1 hz with h1 | h1
    · rcases Finset.mem_union.1 h1 with h2 | h2
      · exact (Finset.mem_inter.1 h2).2
      · exact hZsub h2
    · obtain ⟨β, hβ, hzβ⟩ := Finset.mem_biUnion.1 h1
      have hβI : β ∈ I := Finset.mem_of_mem_erase hβ
      have hβB : β ≠ B := Finset.ne_of_mem_erase hβ
      exact hTsub β hβI (Finset.mem_sdiff.1 (hlbsub β hβI hβB hzβ)).1
  · -- the orphan class is left over
    rw [← hcolAeq]
    exact fun z hz => Finset.mem_union_left _ (Finset.mem_union_left _ hz)
  · -- the leftovers outside the orphan class are few
    rw [← hcolAeq]
    have hsub : e \ C (colI A) ⊆ Z ∪ (I.erase B).biUnion lb := by
      intro z hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_sdiff.1 hz
      rcases Finset.mem_union.1 hz1 with h1 | h1
      · rcases Finset.mem_union.1 h1 with h2 | h2
        · exact absurd (Finset.mem_inter.1 h2).1 hz2
        · exact Finset.mem_union_left _ h2
      · exact Finset.mem_union_right _ h1
    have hlbsum : ((I.erase B).biUnion lb).card ≤ ∑ β ∈ I.erase B, (lb β).card :=
      Finset.card_biUnion_le
    -- the classes of the blocks are distinct classes of the region
    have hcasePred : ∀ β ∈ I.erase B, ∀ l ∈ ({rowI β, Jj β} : Finset ℕ),
        ((β = y u ∧ (l = rowI (y u) ∨ l = rowI B)) ∨ (β = B ∧ l = colI A) ∨
          (β ≠ y u ∧ β ≠ B ∧ (l = rowI β ∨ l = colI (ρ β)))) := by
      intro β hβ l hl
      have hβB : β ≠ B := Finset.ne_of_mem_erase hβ
      rcases Finset.mem_insert.1 hl with rfl | hl'
      · by_cases hβy : β = y u
        · exact Or.inl ⟨hβy, Or.inl (by rw [hβy])⟩
        · exact Or.inr (Or.inr ⟨hβy, hβB, Or.inl rfl⟩)
      · have hlJ : l = Jj β := Finset.mem_singleton.1 hl'
        by_cases hβy : β = y u
        · refine Or.inl ⟨hβy, Or.inr ?_⟩
          rw [hlJ, hβy, hJjy]
        · refine Or.inr (Or.inr ⟨hβy, hβB, Or.inr ?_⟩)
          rw [hlJ, hJjo β hβy]
    have hNdisj : ((I.erase B : Finset ℕ) : Set ℕ).PairwiseDisjoint
        (fun β => ({rowI β, Jj β} : Finset ℕ)) := by
      intro β hβ β' hβ' hne
      have hmemB : β ∈ I.erase B := Finset.mem_coe.1 hβ
      have hmemB' : β' ∈ I.erase B := Finset.mem_coe.1 hβ'
      refine Finset.disjoint_left.2 fun l hl hl' => ?_
      exact hne (hkey β (hIlt β (Finset.mem_of_mem_erase hmemB))
        β' (hIlt β' (Finset.mem_of_mem_erase hmemB')) l
        (hcasePred β hmemB l hl) (hcasePred β' hmemB' l hl'))
    have hNsub : (I.erase B).biUnion (fun β => ({rowI β, Jj β} : Finset ℕ))
        ⊆ gridIdx h (x u) (y u) := by
      intro l hl
      obtain ⟨β, hβ, hlβ⟩ := Finset.mem_biUnion.1 hl
      have hβI : β ∈ I := Finset.mem_of_mem_erase hβ
      rcases Finset.mem_insert.1 hlβ with rfl | hl'
      · exact hrowmem β (hIlt β hβI)
      · rw [Finset.mem_singleton.1 hl']
        exact hJjmem β hβI
    have hsumN : ∑ l ∈ (I.erase B).biUnion (fun β => ({rowI β, Jj β} : Finset ℕ)), dev l
        = ∑ β ∈ I.erase B, (dev (rowI β) + dev (Jj β)) := by
      rw [Finset.sum_biUnion hNdisj]
      exact Finset.sum_congr rfl fun β hβ =>
        Finset.sum_pair (hidxne β (Finset.mem_of_mem_erase hβ))
    have hsumle : ∑ β ∈ I.erase B, (dev (rowI β) + dev (Jj β))
        ≤ ∑ l ∈ gridIdx h (x u) (y u), dev l := by
      rw [← hsumN]
      exact Finset.sum_le_sum_of_subset hNsub
    have hsumblocks : ∑ β ∈ I.erase B, ((lb β).card + (zb β).card) ≤ 2 * D := by
      have hstep : ∑ β ∈ I.erase B, ((lb β).card + (zb β).card)
          ≤ ∑ β ∈ I.erase B, 2 * (dev (rowI β) + dev (Jj β)) :=
        Finset.sum_le_sum fun β hβ =>
          hlbcard β (Finset.mem_of_mem_erase hβ) (Finset.ne_of_mem_erase hβ)
      have hpull : ∑ β ∈ I.erase B, 2 * (dev (rowI β) + dev (Jj β))
          = 2 * ∑ β ∈ I.erase B, (dev (rowI β) + dev (Jj β)) := by
        rw [Finset.mul_sum]
      have hfin : 2 * ∑ l ∈ gridIdx h (x u) (y u), dev l ≤ 2 * D :=
        Nat.mul_le_mul_left 2 hdev
      omega
    have hsplitsum : ∑ β ∈ I.erase B, ((lb β).card + (zb β).card)
        = (∑ β ∈ I.erase B, (lb β).card) + ∑ β ∈ I.erase B, (zb β).card :=
      Finset.sum_add_distrib
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le Z ((I.erase B).biUnion lb)
    omega
  · -- the cross-side rule outside the leftovers
    intro a α β hα hβ hacls haXu hnote
    have hnotA : a ∉ C (colI A) := by
      intro hcon
      exact hnote (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hcon, haXu⟩)))
    have hnotZ : a ∉ Z := fun hcon =>
      hnote (Finset.mem_union_left _ (Finset.mem_union_right _ hcon))
    have hnotlb : ∀ γ ∈ I, γ ≠ B → a ∉ lb γ := by
      intro γ hγ hγB hcon
      exact hnote (Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨γ, Finset.mem_erase.2 ⟨hγB, hγ⟩, hcon⟩))
    have hnotFo : a ∉ Fo := fun hcon => hnotZ (hFoZ hcon)
    have hnotzb : ∀ γ ∈ I, γ ≠ B → a ∉ zb γ := by
      intro γ hγ hγB hcon
      exact hnotZ (hzbZ γ hγ hγB hcon)
    have hstep : ∀ γ ∈ I, γ ≠ B → a ∈ T γ →
        P a = pb γ a ∧
        ((a ∈ C (rowI γ) → pb γ a ∈ C (Jj γ) ∩ Xu) ∧
          (a ∈ C (Jj γ) → pb γ a ∈ C (rowI γ) ∩ Xu)) := by
      intro γ hγ hγB haT
      have haT' : a ∈ T γ \ zb γ := Finset.mem_sdiff.2 ⟨haT, hnotzb γ hγ hγB⟩
      have haT'' : a ∈ T' γ := by rw [hT'o γ hγB]; exact haT'
      refine ⟨?_, hbcross γ hγ hγB a haT' (hnotlb γ hγ hγB)⟩
      rw [hPeq γ hγ a haT'', hpb'o γ hγB]
    have hαβlt : α * h + β < h * h := by
      calc α * h + β < α * h + h := by omega
        _ = (α + 1) * h := by ring
        _ ≤ h * h := Nat.mul_le_mul_right h (by omega)
    obtain ⟨k, hk, hak⟩ := hclassU a haXu hnotFo
    have hklt : k < h * h := gridIdx_lt hxu hyu hk
    have hkeq : k = α * h + β := by
      by_contra hcon
      exact (Finset.disjoint_left.1 (hgrid.classDisjoint k hklt _ hαβlt hcon)) hak hacls
    subst hkeq
    have hyuB : y u ≠ B := Ne.symm hBne
    rcases mem_gridIdx.1 hk with ⟨j, hj, heq⟩ | ⟨l, hl, heq⟩
    · -- `a` lies in the row part of the region
      obtain ⟨hx, hb⟩ := gridDigits_inj hβ hj heq
      have hmem : a ∈ C (rowI j) ∩ Xu := by
        refine Finset.mem_inter.2 ⟨?_, haXu⟩
        show a ∈ C (x u * h + j)
        rw [← hx, ← hb]
        exact hacls
      by_cases hjy : j = y u
      · -- the corner class: it goes to the row class of `B`
        have hmemc : a ∈ C (rowI (y u)) ∩ Xu := by rw [← hjy]; exact hmem
        have hinT : a ∈ T (y u) := by rw [hTy]; exact Finset.mem_union_left _ hmemc
        obtain ⟨hPa, hru, -⟩ := hstep (y u) hyuI hyuB hinT
        have hrule := hru (Finset.mem_inter.1 hmemc).1
        rw [hJjy] at hrule
        refine Or.inr ⟨(hb.trans hjy).symm, ?_⟩
        rw [hPa, hx]
        simpa [hrowIdef, hBdef] using (Finset.mem_inter.1 hrule).1
      · by_cases hjB : j = B
        · -- the row class of `B`: it goes back to the corner class
          have hmemB : a ∈ C (rowI B) ∩ Xu := by rw [← hjB]; exact hmem
          have hinT : a ∈ T (y u) := by rw [hTy]; exact Finset.mem_union_right _ hmemB
          obtain ⟨hPa, -, hru⟩ := hstep (y u) hyuI hyuB hinT
          have hrule := hru (by rw [hJjy]; exact (Finset.mem_inter.1 hmemB).1)
          have hρβ : ρ β = x u := by rw [hb, hjB]; exact hρB
          refine Or.inl ⟨hx.symm, ?_⟩
          rw [hPa, hρβ]
          simpa [hrowIdef] using (Finset.mem_inter.1 hrule).1
        · -- an ordinary row class
          have hjI : j ∈ I := Finset.mem_range.2 hj
          have hinT : a ∈ T j := by
            rw [hTo j hjy hjB]; exact Finset.mem_union_left _ hmem
          obtain ⟨hPa, hru, -⟩ := hstep j hjI hjB hinT
          have hrule := hru (Finset.mem_inter.1 hmem).1
          rw [hJjo j hjy] at hrule
          refine Or.inl ⟨hx.symm, ?_⟩
          rw [hPa, hb]
          simpa [hcolIdef] using (Finset.mem_inter.1 hrule).1
    · -- `a` lies in the column part of the region
      obtain ⟨hx, hb⟩ := gridDigits_inj hβ hyu heq
      have hmem : a ∈ C (colI l) ∩ Xu := by
        refine Finset.mem_inter.2 ⟨?_, haXu⟩
        show a ∈ C (l * h + y u)
        rw [← hx, ← hb]
        exact hacls
      by_cases hlx : l = x u
      · -- the corner class again
        have hmemc : a ∈ C (rowI (y u)) ∩ Xu := by
          rw [← hcornercol, ← hlx]; exact hmem
        have hinT : a ∈ T (y u) := by rw [hTy]; exact Finset.mem_union_left _ hmemc
        obtain ⟨hPa, hru, -⟩ := hstep (y u) hyuI hyuB hinT
        have hrule := hru (Finset.mem_inter.1 hmemc).1
        rw [hJjy] at hrule
        refine Or.inr ⟨hb.symm, ?_⟩
        rw [hPa, hx, hlx]
        simpa [hrowIdef, hBdef] using (Finset.mem_inter.1 hrule).1
      · by_cases hlA : l = A
        · -- the orphan class is left over
          refine absurd ?_ hnotA
          rw [← hlA]
          exact (Finset.mem_inter.1 hmem).1
        · -- an ordinary column class
          have hσly : σ l ≠ y u := by
            intro hcon
            exact hlA (by rw [← hρσ l hl, hcon, ← hAdef])
          have hσlB : σ l ≠ B := by
            intro hcon
            exact hlx (by rw [← hρσ l hl, hcon, hρB])
          have hσlI : σ l ∈ I := Finset.mem_range.2 (hσlt l hl)
          have hmem' : a ∈ C (colI (ρ (σ l))) ∩ Xu := by rw [hρσ l hl]; exact hmem
          have hinT : a ∈ T (σ l) := by
            rw [hTo (σ l) hσly hσlB]; exact Finset.mem_union_right _ hmem'
          obtain ⟨hPa, -, hru⟩ := hstep (σ l) hσlI hσlB hinT
          have hrule := hru (by rw [hJjo (σ l) hσly]; exact (Finset.mem_inter.1 hmem').1)
          refine Or.inr ⟨hb.symm, ?_⟩
          rw [hPa, hx]
          simpa [hrowIdef] using (Finset.mem_inter.1 hrule).1

end BKLO
