import E34.CoBipartite

/-!
# E34 — finite rooted trees and subtree representations

Combinatorial replacement of the topological trees of arXiv:1902.06135, §4.

* `RTree K` — a rooted tree on `Fin K`, given by a parent map `par` (with `par root = root`)
  and a height function `h` strictly decreasing along `par` (so every vertex reaches the root).
* `Anc y x` — `y` is an ancestor of `x` (or `y = x`).  It depends only on `par`.
* `IsSubAt S t` — `S` is a subtree with top `t` (connected set: every `x ∈ S` descends from
  `t`, and the whole path from `x` up to `t` lies in `S`); `IsSub S := ∃ t, IsSubAt S t`.
* `OnPath a b x` — `x` lies in every subtree containing `a` and `b` (the path from `a` to `b`).

Main facts: the union of two intersecting subtrees is a subtree (`isSub_union`); the "top
lemma" `top_mem_of_inter` (Helly for two subtrees); intersection graphs of subtrees are chordal
(`isChordal_of_subtrees`); the *gate lemma* `gate_exists` (Lemma 10 of the paper: for disjoint
subtrees `A`, `B` there is a point of `A` lying in every subtree that meets both).
-/

namespace E34

open Finset

/-- A rooted tree on `Fin K`. -/
structure RTree (K : ℕ) where
  par : Fin K → Fin K
  root : Fin K
  h : Fin K → ℕ
  par_root : par root = root
  h_par : ∀ x, x ≠ root → h (par x) < h x

namespace RTree

variable {K : ℕ} (T : RTree K)

/-- `y` is an ancestor of `x` (possibly `y = x`). -/
def Anc (y x : Fin K) : Prop := ∃ j : ℕ, T.par^[j] x = y

theorem anc_refl (x : Fin K) : T.Anc x x := ⟨0, rfl⟩

theorem anc_par (x : Fin K) : T.Anc (T.par x) x := ⟨1, rfl⟩

theorem anc_trans {x y z : Fin K} (h1 : T.Anc z y) (h2 : T.Anc y x) : T.Anc z x := by
  obtain ⟨i, rfl⟩ := h1
  obtain ⟨j, rfl⟩ := h2
  exact ⟨i + j, Function.iterate_add_apply _ _ _ _⟩

theorem iterate_root (j : ℕ) : T.par^[j] T.root = T.root := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, T.par_root, ih]

theorem h_le_of_anc {x y : Fin K} (hy : T.Anc y x) : T.h y ≤ T.h x := by
  obtain ⟨j, rfl⟩ := hy
  induction j generalizing x with
  | zero => exact le_refl _
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    by_cases hx : x = T.root
    · subst hx; rw [T.par_root, T.iterate_root]
    · exact (ih).trans (T.h_par x hx).le

theorem h_lt_of_anc {x y : Fin K} (hy : T.Anc y x) (hne : y ≠ x) : T.h y < T.h x := by
  obtain ⟨j, rfl⟩ := hy
  cases j with
  | zero => exact absurd rfl hne
  | succ j =>
    rw [Function.iterate_succ_apply] at hne ⊢
    by_cases hx : x = T.root
    · subst hx; rw [T.par_root, T.iterate_root] at hne; exact absurd rfl hne
    · exact lt_of_le_of_lt (T.h_le_of_anc ⟨j, rfl⟩) (T.h_par x hx)

theorem anc_antisymm {x y : Fin K} (h1 : T.Anc y x) (h2 : T.Anc x y) : x = y := by
  by_contra hne
  exact absurd (T.h_lt_of_anc h1 (Ne.symm hne)) (not_lt.2 (T.h_le_of_anc h2))

theorem anc_step {x y : Fin K} (hy : T.Anc y x) : y = x ∨ T.Anc y (T.par x) := by
  obtain ⟨j, rfl⟩ := hy
  cases j with
  | zero => exact Or.inl rfl
  | succ j => exact Or.inr ⟨j, (Function.iterate_succ_apply _ _ _).symm⟩

theorem anc_chain {x y z : Fin K} (hy : T.Anc y x) (hz : T.Anc z x) : T.Anc y z ∨ T.Anc z y := by
  obtain ⟨i, rfl⟩ := hy
  obtain ⟨j, rfl⟩ := hz
  rcases le_total i j with hij | hij
  · refine Or.inr ⟨j - i, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij]
  · refine Or.inl ⟨i - j, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij]

theorem anc_root (x : Fin K) : T.Anc T.root x := by
  induction hx : T.h x using Nat.strong_induction_on generalizing x with
  | _ m ih =>
    by_cases hr : x = T.root
    · subst hr; exact T.anc_refl _
    · exact T.anc_trans (ih _ (hx ▸ T.h_par x hr) _ rfl) (T.anc_par x)

theorem anc_of_anc_par {x y : Fin K} (hy : T.Anc y (T.par x)) : T.Anc y x :=
  T.anc_trans hy (T.anc_par x)

/-! ## Subtrees -/

/-- `S` is a subtree with top `t`. -/
def IsSubAt (S : Finset (Fin K)) (t : Fin K) : Prop :=
  t ∈ S ∧ ∀ x ∈ S, T.Anc t x ∧ ∀ y, T.Anc y x → T.Anc t y → y ∈ S

/-- `S` is a subtree. -/
def IsSub (S : Finset (Fin K)) : Prop := ∃ t, T.IsSubAt S t

/-- `x` lies on the path between `a` and `b`. -/
def OnPath (a b x : Fin K) : Prop := ∀ S, T.IsSub S → a ∈ S → b ∈ S → x ∈ S

variable {T} in
theorem IsSubAt.nonempty {S : Finset (Fin K)} {t : Fin K} (h : T.IsSubAt S t) : S.Nonempty :=
  ⟨t, h.1⟩

variable {T} in
theorem IsSubAt.top_unique {S : Finset (Fin K)} {t t' : Fin K} (h : T.IsSubAt S t)
    (h' : T.IsSubAt S t') : t = t' :=
  T.anc_antisymm ((h'.2 t h.1).1) ((h.2 t' h'.1).1)

/-- A set closed under `par` below its top is a subtree. -/
theorem isSubAt_of_closed (S : Finset (Fin K)) (t : Fin K) (ht : t ∈ S)
    (hcl : ∀ x ∈ S, x ≠ t → T.par x ∈ S ∧ T.h t < T.h x) : T.IsSubAt S t := by
  refine ⟨ht, fun x hx => ?_⟩
  induction hxm : T.h x using Nat.strong_induction_on generalizing x with
  | _ m ih =>
    by_cases hxt : x = t
    · subst hxt
      exact ⟨T.anc_refl _, fun y h1 h2 => (T.anc_antisymm h1 h2) ▸ hx⟩
    · obtain ⟨hpx, hlt⟩ := hcl x hx hxt
      have hxr : x ≠ T.root := by
        rintro rfl
        exact absurd (T.h_le_of_anc (T.anc_root t)) (not_le.2 hlt)
      have hpl : T.h (T.par x) < m := hxm ▸ T.h_par x hxr
      obtain ⟨ih1, ih2⟩ := ih _ hpl (T.par x) hpx rfl
      refine ⟨T.anc_of_anc_par ih1, fun y hy hty => ?_⟩
      rcases T.anc_step hy with rfl | hy'
      · exact hx
      · exact ih2 y hy' hty

theorem isSubAt_univ : T.IsSubAt univ T.root :=
  ⟨mem_univ _, fun x _ => ⟨T.anc_root x, fun _ _ _ => mem_univ _⟩⟩

theorem isSub_univ : T.IsSub univ := ⟨_, T.isSubAt_univ⟩

theorem isSubAt_singleton (x : Fin K) : T.IsSubAt {x} x := by
  refine ⟨mem_singleton_self _, fun y hy => ?_⟩
  rw [mem_singleton] at hy; subst hy
  exact ⟨T.anc_refl _, fun z h1 h2 => by rw [T.anc_antisymm h1 h2]; exact mem_singleton_self _⟩

variable {T} in
/-- Path property: an element between `x ∈ S` and the top lies in `S`. -/
theorem IsSubAt.mem_of_between {S : Finset (Fin K)} {t : Fin K} (h : T.IsSubAt S t)
    {x y : Fin K} (hx : x ∈ S) (hyx : T.Anc y x) (hty : T.Anc t y) : y ∈ S :=
  (h.2 x hx).2 y hyx hty

variable {T} in
/-- More generally: an ancestor `y` of `x ∈ S` that is a descendant of some `z ∈ S` lies in `S`. -/
theorem IsSubAt.mem_of_between' {S : Finset (Fin K)} {t : Fin K} (h : T.IsSubAt S t)
    {x y z : Fin K} (hx : x ∈ S) (hz : z ∈ S) (hyx : T.Anc y x) (hzy : T.Anc z y) : y ∈ S :=
  h.mem_of_between hx hyx (T.anc_trans (h.2 z hz).1 hzy)

/-- **Top lemma** (Helly for two subtrees): if `A ∩ B ≠ ∅` and the top of `B` is not higher than
the top of `A`, then the top of `B` lies in `A`. -/
theorem top_mem_of_inter {A B : Finset (Fin K)} {tA tB : Fin K} (hA : T.IsSubAt A tA)
    (hB : T.IsSubAt B tB) (hh : T.h tA ≤ T.h tB) (hAB : (A ∩ B).Nonempty) : tB ∈ A := by
  obtain ⟨z, hz⟩ := hAB
  rw [mem_inter] at hz
  have h1 := (hA.2 z hz.1).1
  have h2 := (hB.2 z hz.2).1
  rcases T.anc_chain h1 h2 with h | h
  · exact hA.mem_of_between hz.1 h2 h
  · by_cases he : tB = tA
    · rw [he]; exact hA.1
    · exact absurd (T.h_lt_of_anc h he) (not_lt.2 hh)

theorem isSub_union_aux {A B : Finset (Fin K)} {tA tB : Fin K} (hA : T.IsSubAt A tA)
    (hB : T.IsSubAt B tB) (hAB : (A ∩ B).Nonempty) (hh : T.h tA ≤ T.h tB) :
    T.IsSub (A ∪ B) := by
  have htB := T.top_mem_of_inter hA hB hh hAB
  have hAtB := (hA.2 tB htB).1
  refine ⟨tA, mem_union_left _ hA.1, fun x hx => ?_⟩
  rcases mem_union.1 hx with hx | hx
  · exact ⟨(hA.2 x hx).1, fun y h1 h2 => mem_union_left _ (hA.mem_of_between hx h1 h2)⟩
  · have hBx := (hB.2 x hx).1
    refine ⟨T.anc_trans hAtB hBx, fun y h1 h2 => ?_⟩
    rcases T.anc_chain hBx h1 with h | h
    · exact mem_union_right _ (hB.mem_of_between hx h1 h)
    · exact mem_union_left _ (hA.mem_of_between htB h h2)

/-- The union of two intersecting subtrees is a subtree. -/
theorem isSub_union {A B : Finset (Fin K)} (hA : T.IsSub A) (hB : T.IsSub B)
    (hAB : (A ∩ B).Nonempty) : T.IsSub (A ∪ B) := by
  obtain ⟨tA, hA⟩ := hA
  obtain ⟨tB, hB⟩ := hB
  rcases le_total (T.h tA) (T.h tB) with hh | hh
  · exact T.isSub_union_aux hA hB hAB hh
  · rw [union_comm]; exact T.isSub_union_aux hB hA (by rwa [inter_comm]) hh

variable {T} in
/-- Two subtrees whose union is not connected... we only need: points on a path lie in any
union of two intersecting subtrees containing the endpoints. -/
theorem OnPath.mem_union {a b x : Fin K} (hp : T.OnPath a b x) {A B : Finset (Fin K)}
    (hA : T.IsSub A) (hB : T.IsSub B) (hAB : (A ∩ B).Nonempty) (ha : a ∈ A) (hb : b ∈ B) :
    x ∈ A ∪ B :=
  hp _ (T.isSub_union hA hB hAB) (mem_union_left _ ha) (mem_union_right _ hb)

/-! ## Intersection graphs of subtrees are chordal -/

theorem isChordal_of_subtrees {n : ℕ} (G : SimpleGraph (Fin n)) (Tu : Fin n → Finset (Fin K))
    (hsub : ∀ u, T.IsSub (Tu u))
    (hadj : ∀ u v, u ≠ v → (G.Adj u v ↔ (Tu u ∩ Tu v).Nonempty)) :
    AlonShapira.IsChordal G := by
  choose top htop using hsub
  set B := ∑ x, T.h x
  have hB : ∀ x, T.h x ≤ B := fun x =>
    single_le_sum (f := fun x => T.h x) (fun _ _ => Nat.zero_le _) (mem_univ x)
  refine isChordal_of_rank G (fun u => (B - T.h (top u)) * n + u) ?_ ?_
  · intro u v huv
    simp only at huv
    have hu := u.isLt
    have hv := v.isLt
    have h1 : (B - T.h (top u)) * n + u = (B - T.h (top v)) * n + v := huv
    have h2 := congrArg (· % n) h1
    simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] at h2
    exact Fin.ext h2
  · intro v x y hvx hvy hx hy hxy
    simp only at hx hy
    have key : ∀ w, (B - T.h (top v)) * n + v < (B - T.h (top w)) * n + w →
        T.h (top w) ≤ T.h (top v) := by
      intro w hw
      by_contra hc
      push_neg at hc
      have hvB := hB (top v)
      have hwB := hB (top w)
      have : B - T.h (top w) + 1 ≤ B - T.h (top v) := by omega
      have h3 : (B - T.h (top w) + 1) * n ≤ (B - T.h (top v)) * n := Nat.mul_le_mul_right _ this
      have := v.isLt; have := w.isLt
      nlinarith
    have hxv : x ≠ v := fun h => by subst h; exact lt_irrefl _ hx
    have hyv : y ≠ v := fun h => by subst h; exact lt_irrefl _ hy
    have h1 := T.top_mem_of_inter (htop x) (htop v) (key x hx)
      (by rw [inter_comm]; exact (hadj v x (Ne.symm hxv)).1 hvx)
    have h2 := T.top_mem_of_inter (htop y) (htop v) (key y hy)
      (by rw [inter_comm]; exact (hadj v y (Ne.symm hyv)).1 hvy)
    exact (hadj x y hxy).2 ⟨top v, mem_inter.2 ⟨h1, h2⟩⟩

/-! ## The gate lemma (Lemma 10 of the paper) -/

/-- For disjoint subtrees `A` and `B` there is a point `y ∈ A` contained in every subtree
meeting both `A` and `B`. -/
theorem gate_exists {A B : Finset (Fin K)} (hA : T.IsSub A) (hB : T.IsSub B)
    (hAB : Disjoint A B) :
    ∃ y ∈ A, ∀ C, T.IsSub C → (C ∩ A).Nonempty → (C ∩ B).Nonempty → y ∈ C := by
  classical
  obtain ⟨tA, hA⟩ := hA
  obtain ⟨tB, hB⟩ := hB
  by_cases hcase : T.Anc tA tB
  · -- the lowest ancestor of `tB` in `A`
    have hne : (A.filter (fun y => T.Anc y tB)).Nonempty := ⟨tA, mem_filter.2 ⟨hA.1, hcase⟩⟩
    obtain ⟨y, hy, hymax⟩ := exists_max_image _ T.h hne
    rw [mem_filter] at hy
    refine ⟨y, hy.1, fun C ⟨tC, hC⟩ ⟨a, ha⟩ ⟨b, hb⟩ => ?_⟩
    rw [mem_inter] at ha hb
    have hCb := (hC.2 b hb.1).1
    have hBb := (hB.2 b hb.2).1
    have hyb : T.Anc y b := T.anc_trans hy.2 hBb
    rcases T.anc_chain hCb hyb with h | h
    · exact hC.mem_of_between hb.1 hyb h
    · by_cases hyC : tC = y
      · rw [← hyC]; exact hC.1
      exfalso
      have hya : T.Anc tA y := (hA.2 y hy.1).1
      have hCa := (hC.2 a ha.1).1
      have htCA : tC ∈ A := hA.mem_of_between ha.2 hCa (T.anc_trans hya h)
      rcases T.anc_chain hCb hBb with h' | h'
      · have := T.h_lt_of_anc h (Ne.symm hyC)
        have := hymax tC (mem_filter.2 ⟨htCA, h'⟩)
        omega
      · have htCB : tC ∈ B := hB.mem_of_between hb.2 hCb h'
        exact disjoint_left.1 hAB htCA htCB
  · refine ⟨tA, hA.1, fun C ⟨tC, hC⟩ ⟨a, ha⟩ ⟨b, hb⟩ => ?_⟩
    rw [mem_inter] at ha hb
    have hCa := (hC.2 a ha.1).1
    have hAa := (hA.2 a ha.2).1
    rcases T.anc_chain hCa hAa with h | h
    · exact hC.mem_of_between ha.1 hAa h
    · exfalso
      have hAb : T.Anc tA b := T.anc_trans h (hC.2 b hb.1).1
      have hBb := (hB.2 b hb.2).1
      rcases T.anc_chain hAb hBb with h' | h'
      · exact hcase h'
      · exact disjoint_left.1 hAB hA.1 (hB.mem_of_between hb.2 hAb h')

end RTree

end E34
