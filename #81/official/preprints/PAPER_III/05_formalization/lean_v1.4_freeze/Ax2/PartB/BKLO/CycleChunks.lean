/-
  Part B (Phase 2) — cycle decomposition of an admissible leftover.

  The absorbing kernel (`AbsorbingCoreExists`) has to handle an arbitrary *admissible* leftover
  `L`: a sparse subgraph of `G` with all degrees even and `3 ∣ |L|`.  The first structural step of
  every construction is to present `L` in *cycle form*: an even-degree edge set is an
  edge-disjoint union of cycles, which is what the coning gadgets
  (`triDecomposable_doubleCone`, `HexValid.localAbsorbable`) consume.

  This file proves that step from scratch:

  * `edgeDeg` — the degree of a vertex in a `Finset (Sym2 V)`, with its basic calculus
    (`edgeDeg_insert`, `edgeDeg_sdiff`, `edgeDeg_mono`);
  * `walkEdges`, `pathEdges`, `cycleEdges`, `IsCycleEdgeSet` — cycles presented by a nodup vertex
    list, together with the exact degree formulas `edgeDeg_pathEdges` and `edgeDeg_cycleEdges`
    (every vertex of a cycle has degree exactly `2`);
  * `exists_cycle_subset` — a nonempty even-degree edge set contains a cycle (maximal-path
    argument);
  * `exists_cycle_decomposition` — an even-degree edge set is an edge-disjoint union of cycles.
-/
import Ax2.PartB.BKLO.ReservedSplitParts

namespace Ax2.BKLO

open SimpleGraph Finset

variable {V : Type*} [DecidableEq V]

/-! ### Degrees of an edge set -/

/-- The number of edges of the edge set `L` incident to `v`. -/
def edgeDeg (L : Finset (Sym2 V)) (v : V) : ℕ := (L.filter (fun e => v ∈ e)).card

theorem edgeDeg_insert {L : Finset (Sym2 V)} {e : Sym2 V} (he : e ∉ L) (v : V) :
    edgeDeg (insert e L) v = edgeDeg L v + (if v ∈ e then 1 else 0) := by
  classical
  unfold edgeDeg
  rw [Finset.filter_insert]
  by_cases hv : v ∈ e
  · rw [if_pos hv, Finset.card_insert_of_notMem (by simp [he]), if_pos hv]
  · rw [if_neg hv, if_neg hv, Nat.add_zero]

theorem edgeDeg_mono {L₁ L₂ : Finset (Sym2 V)} (h : L₁ ⊆ L₂) (v : V) :
    edgeDeg L₁ v ≤ edgeDeg L₂ v :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem edgeDeg_sdiff {L C : Finset (Sym2 V)} (h : C ⊆ L) (v : V) :
    edgeDeg (L \ C) v = edgeDeg L v - edgeDeg C v := by
  classical
  unfold edgeDeg
  have hf : (L \ C).filter (fun e => v ∈ e) = L.filter (fun e => v ∈ e) \ C.filter (fun e => v ∈ e) := by
    ext e; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  rw [hf, Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ h)]

theorem edgeDeg_empty (v : V) : edgeDeg (∅ : Finset (Sym2 V)) v = 0 := by simp [edgeDeg]

/-! ### Paths and cycles given by vertex lists -/

/-- The edges of the walk starting at `a` and visiting the vertices of `l` in order. -/
def walkEdges : V → List V → Finset (Sym2 V)
  | _, [] => ∅
  | a, b :: t => insert s(a, b) (walkEdges b t)

/-- The edges of the path along the list `l`. -/
def pathEdges : List V → Finset (Sym2 V)
  | [] => ∅
  | a :: t => walkEdges a t

/-- The edges of the cycle along the list `l` (meaningful for nodup `l` of length `≥ 3`). -/
def cycleEdges : List V → Finset (Sym2 V)
  | [] => ∅
  | a :: t => insert s((a :: t).getLast (List.cons_ne_nil a t), a) (walkEdges a t)

/-- An edge set which is the edge set of a cycle. -/
def IsCycleEdgeSet (C : Finset (Sym2 V)) : Prop :=
  ∃ l : List V, l.Nodup ∧ 3 ≤ l.length ∧ C = cycleEdges l

@[simp] theorem walkEdges_nil (a : V) : walkEdges a ([] : List V) = ∅ := rfl

@[simp] theorem walkEdges_cons (a b : V) (t : List V) :
    walkEdges a (b :: t) = insert s(a, b) (walkEdges b t) := rfl

@[simp] theorem pathEdges_nil : pathEdges ([] : List V) = ∅ := rfl

@[simp] theorem pathEdges_cons (a : V) (t : List V) : pathEdges (a :: t) = walkEdges a t := rfl

/-- Every endpoint of an edge of a walk is a vertex of the walk. -/
theorem mem_of_mem_walkEdges : ∀ (t : List V) (a : V) (e : Sym2 V), e ∈ walkEdges a t →
    ∀ {v : V}, v ∈ e → v ∈ a :: t := by
  intro t
  induction t with
  | nil => intro a e he; simp at he
  | cons b t ih =>
      intro a e he v hv
      rw [walkEdges_cons, Finset.mem_insert] at he
      rcases he with rfl | he
      · rw [Sym2.mem_iff] at hv
        rcases hv with rfl | rfl <;> simp
      · have := ih b e he hv
        rcases List.mem_cons.mp this with rfl | h
        · simp
        · simp [h]

theorem mem_of_mem_pathEdges {l : List V} {e : Sym2 V} (he : e ∈ pathEdges l)
    {v : V} (hv : v ∈ e) : v ∈ l := by
  cases l with
  | nil => simp [pathEdges] at he
  | cons a t => exact mem_of_mem_walkEdges t a e he hv

/-- Passing to a suffix only shrinks the path edge set. -/
theorem pathEdges_subset_of_suffix {l' l : List V} (h : l' <:+ l) :
    pathEdges l' ⊆ pathEdges l := by
  obtain ⟨p, rfl⟩ := h
  induction p with
  | nil => simp
  | cons a p ih =>
      refine ih.trans ?_
      cases hp : p ++ l' with
      | nil => simp [pathEdges]
      | cons b t =>
          rw [List.cons_append, hp]
          simp only [pathEdges_cons, walkEdges_cons]
          exact Finset.subset_insert _ _

theorem pathEdges_append_singleton {l : List V} (hl : l ≠ []) (u : V) :
    pathEdges (l ++ [u]) = insert s(l.getLast hl, u) (pathEdges l) := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a t ih =>
      cases t with
      | nil => simp [pathEdges, walkEdges]
      | cons b t' =>
          have hne : (b :: t') ≠ [] := List.cons_ne_nil b t'
          have := ih hne
          simp only [List.cons_append, pathEdges_cons, walkEdges_cons] at this ⊢
          rw [this, List.getLast_cons hne]
          rw [Finset.insert_comm]

/-! ### Degrees along a path and along a cycle -/

/-- **The degree formula for a path.**  On a nodup list the interior vertices of the path have
degree `2`, the two endpoints degree `1`, and every other vertex degree `0`. -/
theorem edgeDeg_walkEdges : ∀ (t : List V) (a : V), (a :: t).Nodup → ∀ v : V,
    edgeDeg (walkEdges a t) v =
      if t = [] then 0
      else if v = a ∨ t.getLast? = some v then 1
      else if v ∈ t then 2 else 0 := by
  intro t
  induction t with
  | nil => intro a _ v; simp [edgeDeg]
  | cons b t' ih =>
      intro a hnd v
      have hmain : a ∉ b :: t' := (List.nodup_cons.mp hnd).1
      have hnd' : (b :: t').Nodup := (List.nodup_cons.mp hnd).2
      have hab : a ≠ b := fun h => hmain (by simp [h])
      have hant : a ∉ t' := fun h => hmain (List.mem_cons_of_mem b h)
      have hbt : b ∉ t' := (List.nodup_cons.mp hnd').1
      have hnotmem : s(a, b) ∉ walkEdges b t' := fun hmem =>
        hmain (mem_of_mem_walkEdges t' b _ hmem (by simp))
      rw [walkEdges_cons, edgeDeg_insert hnotmem, ih b hnd' v]
      rcases eq_or_ne t' [] with rfl | ht'
      · by_cases hva : v = a
        · subst hva; simp [hab]
        · by_cases hvb : v = b
          · subst hvb; simp [Ne.symm hab]
          · simp [hva, hvb, Ne.symm hvb]
      · have hlast : (b :: t').getLast? = t'.getLast? := by
          cases t' with
          | nil => exact absurd rfl ht'
          | cons c t'' => simp
        by_cases hva : v = a
        · subst hva
          have h1 : t'.getLast? ≠ some v := fun h => hant (List.mem_of_mem_getLast? h)
          simp [ht', h1, hant, hab, hlast]
        · by_cases hvb : v = b
          · subst hvb
            have h1 : t'.getLast? ≠ some v := fun h => hbt (List.mem_of_mem_getLast? h)
            simp [ht', h1, hbt, hva, hlast]
          · simp only [ht', if_false, hva, hvb, false_or, hlast, List.mem_cons]
            by_cases hg : t'.getLast? = some v
            · simp [hg, hva, hvb]
            · simp [hg, hva, hvb]

/-- A vertex outside the list has no path edges. -/
theorem edgeDeg_pathEdges_of_notMem {l : List V} {v : V} (hv : v ∉ l) :
    edgeDeg (pathEdges l) v = 0 := by
  classical
  unfold edgeDeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hve
  exact hv (mem_of_mem_pathEdges he hve)

/-- The last vertex of a nontrivial nodup path has exactly one path edge. -/
theorem edgeDeg_pathEdges_getLast {a : V} {t : List V} (hnd : (a :: t).Nodup) (ht : t ≠ []) :
    edgeDeg (pathEdges (a :: t)) ((a :: t).getLast (List.cons_ne_nil a t)) = 1 := by
  set x := (a :: t).getLast (List.cons_ne_nil a t) with hx
  have hxlast : t.getLast? = some x := by
    rw [hx, List.getLast_cons ht, List.getLast?_eq_some_getLast ht]
  rw [pathEdges_cons, edgeDeg_walkEdges t a hnd x]
  simp [ht, hxlast]

/-- The head of a nontrivial nodup path has exactly one path edge. -/
theorem edgeDeg_pathEdges_head {a : V} {t : List V} (hnd : (a :: t).Nodup) (ht : t ≠ []) :
    edgeDeg (pathEdges (a :: t)) a = 1 := by
  rw [pathEdges_cons, edgeDeg_walkEdges t a hnd a]
  simp [ht]

/-- The closing edge of a cycle of length `≥ 3` is not one of its path edges. -/
theorem closing_notMem_pathEdges {a : V} {t : List V} (hnd : (a :: t).Nodup)
    (h3 : 3 ≤ (a :: t).length) :
    s((a :: t).getLast (List.cons_ne_nil a t), a) ∉ walkEdges a t := by
  cases t with
  | nil => simp at h3
  | cons b t' =>
      have ht' : t' ≠ [] := by
        rintro rfl; simp at h3
      have hmain : a ∉ b :: t' := (List.nodup_cons.mp hnd).1
      have hbt : b ∉ t' := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
      have hxeq : (a :: b :: t').getLast (List.cons_ne_nil a _) = t'.getLast ht' := by
        rw [List.getLast_cons (List.cons_ne_nil b t'), List.getLast_cons ht']
      rw [hxeq]
      have hxt : t'.getLast ht' ∈ t' := List.getLast_mem ht'
      have hax : a ≠ t'.getLast ht' := fun h => hmain (List.mem_cons_of_mem b (h ▸ hxt))
      have hbx : b ≠ t'.getLast ht' := fun h => hbt (h ▸ hxt)
      intro hmem
      rw [walkEdges_cons, Finset.mem_insert] at hmem
      rcases hmem with heq | hmem
      · rw [Sym2.eq_iff] at heq
        rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hax h1.symm
        · exact hbx h1.symm
      · exact hmain (mem_of_mem_walkEdges _ _ _ hmem (by simp))

/-- **The degree formula for a cycle.**  Every vertex of a nodup cycle of length `≥ 3` has
exactly two cycle edges at it; every other vertex none. -/
theorem edgeDeg_cycleEdges {l : List V} (hnd : l.Nodup) (h3 : 3 ≤ l.length) (v : V) :
    edgeDeg (cycleEdges l) v = if v ∈ l then 2 else 0 := by
  cases l with
  | nil => simp at h3
  | cons a t =>
      have ht : t ≠ [] := by
        rintro rfl; simp at h3
      set x := (a :: t).getLast (List.cons_ne_nil a t) with hx
      have hxlast : t.getLast? = some x := by
        rw [hx, List.getLast_cons ht, List.getLast?_eq_some_getLast ht]
      have hnotmem : s(x, a) ∉ walkEdges a t := closing_notMem_pathEdges hnd h3
      have : cycleEdges (a :: t) = insert s(x, a) (walkEdges a t) := rfl
      rw [this, edgeDeg_insert hnotmem, edgeDeg_walkEdges t a hnd v]
      have hxt : x ∈ t := List.mem_of_mem_getLast? hxlast
      have hxmem : x ∈ a :: t := List.mem_cons_of_mem a hxt
      have hxa : x ≠ a := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hxt)
      by_cases hva : v = a
      · subst hva
        simp [ht, Ne.symm hxa]
      · by_cases hvx : v = x
        · subst hvx
          simp [ht, hxlast, hva, hxmem]
        · by_cases hvt : v ∈ t
          · have hg : t.getLast? ≠ some v := by
              rw [hxlast]; simp [Ne.symm hvx]
            simp [ht, hg, hva, hvt, hvx]
          · have hg : t.getLast? ≠ some v := by
              rw [hxlast]; simp [Ne.symm hvx]
            simp [ht, hg, hva, hvt, hvx]

/-- A cycle edge set is nonempty. -/
theorem nonempty_of_isCycleEdgeSet {C : Finset (Sym2 V)} (hC : IsCycleEdgeSet C) : C.Nonempty := by
  obtain ⟨l, hnd, h3, rfl⟩ := hC
  cases l with
  | nil => simp at h3
  | cons a t => exact ⟨_, Finset.mem_insert_self _ _⟩

/-- Every vertex of a cycle edge set has even degree in it. -/
theorem edgeDeg_even_of_isCycleEdgeSet {C : Finset (Sym2 V)} (hC : IsCycleEdgeSet C) (v : V) :
    Even (edgeDeg C v) := by
  obtain ⟨l, hnd, h3, rfl⟩ := hC
  rw [edgeDeg_cycleEdges hnd h3 v]
  by_cases h : v ∈ l <;> simp [h]

/-- A nodup path has exactly one edge per step. -/
theorem card_walkEdges : ∀ (t : List V) (a : V), (a :: t).Nodup →
    (walkEdges a t).card = t.length := by
  intro t
  induction t with
  | nil => intro a _; simp
  | cons b t' ih =>
      intro a hnd
      have hmain : a ∉ b :: t' := (List.nodup_cons.mp hnd).1
      have hnd' : (b :: t').Nodup := (List.nodup_cons.mp hnd).2
      have hnotmem : s(a, b) ∉ walkEdges b t' := fun hmem =>
        hmain (mem_of_mem_walkEdges t' b _ hmem (by simp))
      rw [walkEdges_cons, Finset.card_insert_of_notMem hnotmem, ih b hnd']
      simp

/-- **A cycle has as many edges as vertices.** -/
theorem card_cycleEdges {l : List V} (hnd : l.Nodup) (h3 : 3 ≤ l.length) :
    (cycleEdges l).card = l.length := by
  cases l with
  | nil => simp at h3
  | cons a t =>
      have hnotmem := closing_notMem_pathEdges hnd h3
      have : cycleEdges (a :: t) =
          insert s((a :: t).getLast (List.cons_ne_nil a t), a) (walkEdges a t) := rfl
      rw [this, Finset.card_insert_of_notMem hnotmem, card_walkEdges t a hnd]
      simp

/-- Membership in the union of a list of edge sets. -/
theorem mem_foldr_union {Cs : List (Finset (Sym2 V))} {f : Sym2 V} :
    f ∈ Cs.foldr (· ∪ ·) ∅ ↔ ∃ C ∈ Cs, f ∈ C := by
  induction Cs with
  | nil => simp
  | cons E Es ih => simp [ih]

theorem subset_foldr_union {Cs : List (Finset (Sym2 V))} {C : Finset (Sym2 V)} (hC : C ∈ Cs) :
    C ⊆ Cs.foldr (· ∪ ·) ∅ := fun _ hf => mem_foldr_union.mpr ⟨C, hC, hf⟩

/-- The union of a list of edge sets only depends on the list up to reordering. -/
theorem foldr_union_of_perm {Cs Ds : List (Finset (Sym2 V))} (h : Cs.Perm Ds) :
    Cs.foldr (· ∪ ·) ∅ = Ds.foldr (· ∪ ·) ∅ := by
  ext f
  simp only [mem_foldr_union]
  constructor
  · rintro ⟨C, hC, hf⟩; exact ⟨C, h.mem_iff.mp hC, hf⟩
  · rintro ⟨C, hC, hf⟩; exact ⟨C, h.mem_iff.mpr hC, hf⟩

/-- The union of pairwise disjoint edge sets has the sum of their cardinalities. -/
theorem card_foldr_union : ∀ {Cs : List (Finset (Sym2 V))}, Cs.Pairwise Disjoint →
    (Cs.foldr (· ∪ ·) ∅).card = (Cs.map Finset.card).sum := by
  intro Cs
  induction Cs with
  | nil => simp
  | cons C Cs ih =>
      intro hpair
      have hd : Disjoint C (Cs.foldr (· ∪ ·) ∅) := by
        rw [Finset.disjoint_left]
        intro f hf hf'
        obtain ⟨D, hD, hfD⟩ := mem_foldr_union.mp hf'
        exact (Finset.disjoint_left.mp ((List.pairwise_cons.mp hpair).1 D hD)) hf hfD
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      rw [Finset.card_union_of_disjoint hd, ih (List.Pairwise.of_cons hpair)]

/-! ### Finding a cycle inside an even-degree edge set -/

section Fintype

variable [Fintype V]

/-- **A nonempty edge set all of whose degrees are even contains a cycle.**  Maximal-path
argument: an endpoint `x` of a maximal path has another `L`-edge `s(x,u)` besides its path edge;
by maximality `u` lies on the path, and the portion of the path from `u` to `x` closes up into a
cycle. -/
theorem exists_cycle_subset (L : Finset (Sym2 V)) (hdiag : ∀ e ∈ L, ¬ e.IsDiag)
    (heven : ∀ v, Even (edgeDeg L v)) (hne : L.Nonempty) :
    ∃ C : Finset (Sym2 V), IsCycleEdgeSet C ∧ C ⊆ L := by
  classical
  obtain ⟨e₀, he₀⟩ := hne
  obtain ⟨p, q, rfl⟩ : ∃ p q, e₀ = s(p, q) := by
    clear he₀
    induction e₀ using Sym2.ind with
    | _ p q => exact ⟨p, q, rfl⟩
  have hpq : p ≠ q := by
    have := hdiag _ he₀
    simpa [Sym2.isDiag_iff_proj_eq] using this
  set P : ℕ → Prop := fun k => ∃ l : List V, l.Nodup ∧ l.length = k ∧ pathEdges l ⊆ L with hP
  have hP2 : P 2 := by
    refine ⟨[p, q], by simp [hpq], by simp, ?_⟩
    intro e he
    simp only [pathEdges_cons, walkEdges_cons, walkEdges_nil, Finset.mem_insert,
      Finset.notMem_empty, or_false] at he
    rw [he]; exact he₀
  have h2n : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff_nontrivial.mpr ⟨p, q, hpq⟩
  set m := Nat.findGreatest P (Fintype.card V) with hm
  have hPm : P m := Nat.findGreatest_spec h2n hP2
  have hm2 : 2 ≤ m := Nat.le_findGreatest h2n hP2
  have hmax : ∀ l : List V, l.Nodup → pathEdges l ⊆ L → l.length ≤ m := by
    intro l hnd hsub
    exact Nat.le_findGreatest hnd.length_le_card ⟨l, hnd, rfl, hsub⟩
  obtain ⟨l, hnd, hlen, hsub⟩ := hPm
  -- the maximal path is nontrivial
  cases l with
  | nil => simp at hlen; omega
  | cons a t =>
  have ht : t ≠ [] := by
    rintro rfl
    simp at hlen
    omega
  set x := (a :: t).getLast (List.cons_ne_nil a t) with hxdef
  have hdegpath : edgeDeg (pathEdges (a :: t)) x = 1 := edgeDeg_pathEdges_getLast hnd ht
  -- `x` has another `L`-edge
  have hlt : (pathEdges (a :: t)).filter (fun e => x ∈ e) ⊆ L.filter (fun e => x ∈ e) :=
    Finset.filter_subset_filter _ hsub
  have hdeg2 : 2 ≤ edgeDeg L x := by
    have h1 : 1 ≤ edgeDeg L x := hdegpath ▸ edgeDeg_mono hsub x
    rcases heven x with ⟨k, hk⟩
    omega
  have hex : ∃ e ∈ L, x ∈ e ∧ e ∉ pathEdges (a :: t) := by
    by_contra hcon
    push_neg at hcon
    have hsub' : L.filter (fun e => x ∈ e) ⊆ (pathEdges (a :: t)).filter (fun e => x ∈ e) := by
      intro e he
      rw [Finset.mem_filter] at he ⊢
      exact ⟨hcon e he.1 he.2, he.2⟩
    have := Finset.card_le_card hsub'
    rw [← edgeDeg, ← edgeDeg, hdegpath] at this
    omega
  obtain ⟨e, heL, hxe, henp⟩ := hex
  obtain ⟨u, rfl⟩ : ∃ u, e = s(x, u) := by
    induction e using Sym2.inductionOn with
    | _ c d =>
        rcases Sym2.mem_iff.mp hxe with rfl | rfl
        · exact ⟨d, rfl⟩
        · exact ⟨c, Sym2.eq_swap⟩
  have hxu : x ≠ u := by
    have := hdiag _ heL
    simpa [Sym2.isDiag_iff_proj_eq] using this
  -- by maximality, `u` lies on the path
  have hu : u ∈ a :: t := by
    by_contra hu
    have hnd' : ((a :: t) ++ [u]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hnd, List.nodup_singleton u, ?_⟩
      intro w hw z hz
      have hzu : z = u := by simpa using hz
      subst hzu
      rintro rfl
      exact hu hw
    have hsub' : pathEdges ((a :: t) ++ [u]) ⊆ L := by
      rw [pathEdges_append_singleton (List.cons_ne_nil a t) u]
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact heL
      · exact hsub hf
    have := hmax _ hnd' hsub'
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    simp only [List.length_cons] at hlen
    omega
  obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hu
  have hsuffix : (u :: l₂) <:+ (a :: t) := ⟨l₁, hl.symm⟩
  have hcnd : (u :: l₂).Nodup := by
    rw [hl] at hnd
    exact hnd.of_append_right
  have hcsub : pathEdges (u :: l₂) ⊆ pathEdges (a :: t) := pathEdges_subset_of_suffix hsuffix
  have hlast : (u :: l₂).getLast (List.cons_ne_nil u l₂) = x := by
    have h1 : (a :: t).getLast? = some x :=
      List.getLast?_eq_some_getLast (List.cons_ne_nil a t)
    have h3 : (u :: l₂).getLast? = some ((u :: l₂).getLast (List.cons_ne_nil u l₂)) :=
      List.getLast?_eq_some_getLast _
    have h2 : (a :: t).getLast? = some ((u :: l₂).getLast (List.cons_ne_nil u l₂)) := by
      rw [hl, List.getLast?_append, h3]
      simp
    rw [h2] at h1
    exact Option.some.inj h1
  have hl₂ : l₂ ≠ [] := by
    rintro rfl
    simp only [List.getLast_singleton] at hlast
    exact hxu hlast.symm
  have h3 : 3 ≤ (u :: l₂).length := by
    rcases l₂ with _ | ⟨w, l₃⟩
    · exact absurd rfl hl₂
    · rcases l₃ with _ | ⟨w', l₄⟩
      · -- then `l₂ = [x]` and `s(x,u)` would be a path edge
        exfalso
        have hw : w = x := by simpa using hlast
        refine henp (hcsub ?_)
        simp only [pathEdges_cons, walkEdges_cons, walkEdges_nil, Finset.mem_insert,
          Finset.notMem_empty, or_false]
        rw [hw, Sym2.eq_swap]
      · simp
  refine ⟨cycleEdges (u :: l₂), ⟨u :: l₂, hcnd, h3, rfl⟩, ?_⟩
  have : cycleEdges (u :: l₂) = insert s(x, u) (walkEdges u l₂) := by
    rw [show cycleEdges (u :: l₂) =
      insert s((u :: l₂).getLast (List.cons_ne_nil u l₂), u) (walkEdges u l₂) from rfl, hlast]
  rw [this]
  intro f hf
  rcases Finset.mem_insert.mp hf with rfl | hf
  · exact heL
  · exact hsub (hcsub hf)

/-- **Cycle decomposition.**  An edge set all of whose degrees are even is the union of a list of
pairwise edge-disjoint cycles. -/
theorem exists_cycle_decomposition (L : Finset (Sym2 V)) (hdiag : ∀ e ∈ L, ¬ e.IsDiag)
    (heven : ∀ v, Even (edgeDeg L v)) :
    ∃ Cs : List (Finset (Sym2 V)), (∀ C ∈ Cs, IsCycleEdgeSet C) ∧ Cs.Pairwise Disjoint ∧
      Cs.foldr (· ∪ ·) ∅ = L := by
  classical
  induction hcard : L.card using Nat.strong_induction_on generalizing L with
  | _ N ih =>
  rcases L.eq_empty_or_nonempty with rfl | hne
  · exact ⟨[], by simp, by simp, by simp⟩
  obtain ⟨C, hC, hCL⟩ := exists_cycle_subset L hdiag heven hne
  have hCne : C.Nonempty := nonempty_of_isCycleEdgeSet hC
  have hcardlt : (L \ C).card < L.card := by
    obtain ⟨f, hf⟩ := hCne
    have : (L \ C) ⊆ L := Finset.sdiff_subset
    refine Finset.card_lt_card ⟨this, ?_⟩
    intro hsub
    have := hsub (hCL hf)
    simp only [Finset.mem_sdiff] at this
    exact this.2 hf
  have hdiag' : ∀ e ∈ L \ C, ¬ e.IsDiag := fun e he => hdiag e (Finset.mem_sdiff.mp he).1
  have heven' : ∀ v, Even (edgeDeg (L \ C) v) := by
    intro v
    rw [edgeDeg_sdiff hCL v]
    have h1 := heven v
    have h2 := edgeDeg_even_of_isCycleEdgeSet hC v
    have h3 := edgeDeg_mono hCL v
    rcases h1 with ⟨k, hk⟩
    rcases h2 with ⟨j, hj⟩
    exact ⟨k - j, by omega⟩
  obtain ⟨Cs, hCs, hpair, hunion⟩ :=
    ih (L \ C).card (by omega) (L \ C) hdiag' heven' rfl
  refine ⟨C :: Cs, ?_, ?_, ?_⟩
  · intro D hD
    rcases List.mem_cons.mp hD with rfl | hD
    · exact hC
    · exact hCs D hD
  · refine List.pairwise_cons.mpr ⟨?_, hpair⟩
    intro D hD
    have hDsub : D ⊆ L \ C := hunion ▸ subset_foldr_union hD
    exact Finset.disjoint_left.mpr fun f hf hfD => (Finset.mem_sdiff.mp (hDsub hfD)).2 hf
  · simp only [List.foldr_cons, hunion]
    rw [Finset.union_sdiff_of_subset hCL]

/-! ### Bridging cycle edge sets to the gadgets of `ReservedSplitParts` -/

omit [Fintype V] in
/-- A cycle of length three is a triangle. -/
theorem cycleEdges_triple {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    cycleEdges [a, b, c] = triEdges ({a, b, c} : Finset V) := by
  rw [triEdges_triple hab hac hbc]
  have : cycleEdges [a, b, c] = insert s(c, a) (insert s(a, b) (insert s(b, c) ∅)) := rfl
  rw [this]
  ext e
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false,
    Sym2.eq_swap]
  tauto

omit [Fintype V] in
/-- A cycle of length six, in list form, is the corresponding `sixCycleEdges`. -/
theorem cycleEdges_six (a x b z c y : V) :
    cycleEdges [a, x, b, z, c, y] = sixCycleEdges a x b z c y := by
  have : cycleEdges [a, x, b, z, c, y] =
      insert s(y, a) (insert s(a, x) (insert s(x, b) (insert s(b, z)
        (insert s(z, c) (insert s(c, y) ∅))))) := rfl
  rw [this]
  ext e
  simp only [sixCycleEdges, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
    or_false, Sym2.eq_swap]
  tauto

omit [Fintype V] in
/-- **A six-cycle whose alternating triple spans a triangle is absorbed by that triangle.**  The
list form of `HexValid.localAbsorbable`, so that a chunk produced by
`exists_cycle_decomposition` can be fed directly to the subdivided-triangle gadget. -/
theorem localAbsorbable_cycleEdges_six (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b c x y z : V} (h : HexValid G a b c x y z) :
    LocalAbsorbable G ({{a, b, c}} : Finset (Finset V)) (cycleEdges [a, x, b, z, c, y]) := by
  rw [cycleEdges_six, sixCycleEdges_eq_hexCfg]
  exact h.localAbsorbable

omit [Fintype V] in
/-- **A three-cycle chunk is absorbed outright** (no reserved edges are needed for it): it is a
triangle of `G`, so it is triangle-decomposable on its own. -/
theorem localAbsorbable_cycleEdges_triple (G : SimpleGraph V) [DecidableRel G.Adj]
    {B : Finset (Finset V)} (hB : ∀ t ∈ B, G.IsNClique 3 t) (hBd : EdgeDisjoint B)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (htri : G.IsNClique 3 ({a, b, c} : Finset V))
    (hdisj : Disjoint (cycleEdges [a, b, c]) (coveredEdges B)) :
    LocalAbsorbable G B (cycleEdges [a, b, c]) := by
  refine localAbsorbable_of_decomposable G hB hBd (P := {({a, b, c} : Finset V)}) ?_ ?_ ?_ hdisj
  · intro t ht
    rw [Finset.mem_singleton] at ht
    subst ht
    exact htri
  · intro t₁ h₁ t₂ h₂ hne
    rw [Finset.mem_singleton] at h₁ h₂
    exact absurd (h₁.trans h₂.symm) hne
  · rw [coveredEdges, Finset.singleton_biUnion, cycleEdges_triple hab hac hbc]

/-- A cycle with three edges inside `G` is (the edge set of) a triangle of `G`. -/
theorem exists_triangle_of_isCycleEdgeSet_card_three (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Finset (Sym2 V)} (hC : IsCycleEdgeSet C) (hCG : C ⊆ G.edgeFinset) (hcard : C.card = 3) :
    ∃ t : Finset V, G.IsNClique 3 t ∧ triEdges t = C := by
  obtain ⟨l, hnd, h3, rfl⟩ := hC
  have hlen : l.length = 3 := by
    rw [card_cycleEdges hnd h3] at hcard
    exact hcard
  match l, hlen with
  | [a, b, c], _ =>
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
        not_or, or_false, and_true] at hnd
      obtain ⟨⟨hab, hac⟩, hbc, -⟩ := hnd
      have hCe : cycleEdges [a, b, c] = insert s(c, a) (insert s(a, b) (insert s(b, c) ∅)) := rfl
      have hadj : ∀ x y : V, s(x, y) ∈ cycleEdges [a, b, c] → G.Adj x y := by
        intro x y hxy
        have := hCG hxy
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
      refine ⟨{a, b, c}, ?_, (cycleEdges_triple hab hac hbc).symm⟩
      refine SimpleGraph.is3Clique_triple_iff.2 ⟨?_, ?_, ?_⟩
      · exact hadj a b (by rw [hCe]; simp)
      · exact (hadj c a (by rw [hCe]; simp)).symm
      · exact hadj b c (by rw [hCe]; simp)

omit [Fintype V] in
/-- The edge set of a single triangle of `G` is triangle-decomposable. -/
theorem triDecomposable_triEdges (G : SimpleGraph V) [DecidableRel G.Adj] {t : Finset V}
    (ht : G.IsNClique 3 t) : TriDecomposable G (triEdges t) := by
  refine ⟨{t}, ?_, ?_, ?_⟩
  · intro u hu
    rw [Finset.mem_singleton] at hu
    exact hu ▸ ht
  · intro t₁ h₁ t₂ h₂ hne
    rw [Finset.mem_singleton] at h₁ h₂
    exact absurd (h₁.trans h₂.symm) hne
  · rw [coveredEdges, Finset.singleton_biUnion]

omit [Fintype V] in
/-- The union of a list of edge sets splits along the concatenation. -/
theorem foldr_union_append (Cs Ds : List (Finset (Sym2 V))) :
    (Cs ++ Ds).foldr (· ∪ ·) ∅ = Cs.foldr (· ∪ ·) ∅ ∪ Ds.foldr (· ∪ ·) ∅ := by
  induction Cs with
  | nil => simp
  | cons C Cs ih => simp [ih, Finset.union_assoc]

omit [Fintype V] in
/-- **The triangles of a cycle decomposition need no absorber**: a union of pairwise disjoint
three-edge cycles of `G` is triangle-decomposable on its own. -/
theorem triDecomposable_foldr_of_triangleCycles (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ Ts : List (Finset (Sym2 V)), Ts.Pairwise Disjoint →
      (∀ C ∈ Ts, ∃ t : Finset V, G.IsNClique 3 t ∧ triEdges t = C) →
      TriDecomposable G (Ts.foldr (· ∪ ·) ∅) := by
  intro Ts
  induction Ts with
  | nil => exact fun _ _ => ⟨∅, by simp, by simp [EdgeDisjoint], by simp [coveredEdges]⟩
  | cons C Ts ih =>
      intro hpair htri
      obtain ⟨t, ht, htC⟩ := htri C (by simp)
      have hdisj : Disjoint C (Ts.foldr (· ∪ ·) ∅) := by
        rw [Finset.disjoint_left]
        intro f hf hf'
        obtain ⟨D, hD, hfD⟩ := mem_foldr_union.mp hf'
        exact Finset.disjoint_left.mp ((List.pairwise_cons.mp hpair).1 D hD) hf hfD
      exact (htC ▸ triDecomposable_triEdges G ht).union
        (ih (List.Pairwise.of_cons hpair) (fun D hD => htri D (by simp [hD]))) hdisj

/-! ### Regrouping a list into blocks of weight divisible by three -/

section Grouping

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem sum_map_mod_three {l : List α} {w : α → ℕ} {r : ℕ} (h : ∀ a ∈ l, w a % 3 = r) :
    (l.map w).sum % 3 = (l.length * r) % 3 := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha := h a (by simp)
      have hrec := ih (fun b hb => h b (by simp [hb]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, one_mul]
      omega

/-- **A nonempty list whose total weight is a multiple of three has a block of at most three
elements whose weight is a multiple of three.** -/
theorem exists_small_threeDivisible_block (l : List α) (w : α → ℕ) (hne : l ≠ [])
    (h : 3 ∣ (l.map w).sum) :
    ∃ g rest : List α, (g ++ rest).Perm l ∧ g ≠ [] ∧ g.length ≤ 3 ∧ 3 ∣ (g.map w).sum := by
  classical
  by_cases h0 : ∃ a ∈ l, w a % 3 = 0
  · obtain ⟨a, ha, ha0⟩ := h0
    refine ⟨[a], l.erase a, ?_, by simp, by simp, ?_⟩
    · simpa using (List.perm_cons_erase ha).symm
    · simpa using Nat.dvd_of_mod_eq_zero ha0
  by_cases h12 : (∃ a ∈ l, w a % 3 = 1) ∧ (∃ b ∈ l, w b % 3 = 2)
  · obtain ⟨⟨a, ha, ha1⟩, ⟨b, hb, hb2⟩⟩ := h12
    have hab : a ≠ b := by rintro rfl; omega
    have hb' : b ∈ l.erase a := (List.mem_erase_of_ne (Ne.symm hab)).mpr hb
    refine ⟨[a, b], (l.erase a).erase b, ?_, by simp, by simp, ?_⟩
    · refine List.Perm.trans ?_ (List.perm_cons_erase ha).symm
      exact List.Perm.cons a (List.perm_cons_erase hb').symm
    · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, Nat.add_zero]
      omega
  -- all weights have the same nonzero residue
  push_neg at h0
  obtain ⟨a₀, l₀, rfl⟩ : ∃ a l', l = a :: l' := by
    cases l with
    | nil => exact absurd rfl hne
    | cons a l' => exact ⟨a, l', rfl⟩
  set r := w a₀ % 3 with hr
  have hr0 : r ≠ 0 := h0 a₀ (by simp)
  have hall : ∀ a ∈ a₀ :: l₀, w a % 3 = r := by
    intro a ha
    have hne0 : w a % 3 ≠ 0 := h0 a ha
    have hlt : w a % 3 < 3 := Nat.mod_lt _ (by norm_num)
    rcases (by omega : w a % 3 = 0 ∨ w a % 3 = 1 ∨ w a % 3 = 2) with h1 | h1 | h1
    · exact absurd h1 hne0
    · -- `a` has residue 1, so no element has residue 2, in particular `a₀` has residue 1
      have hno2 : ¬ ∃ b ∈ a₀ :: l₀, w b % 3 = 2 := fun hex => h12 ⟨⟨a, ha, h1⟩, hex⟩
      have hr2 : r ≠ 2 := fun hcon => hno2 ⟨a₀, by simp, hcon ▸ hr ▸ rfl⟩
      have hrlt : r < 3 := Nat.mod_lt _ (by norm_num)
      omega
    · have hno1 : ¬ ∃ b ∈ a₀ :: l₀, w b % 3 = 1 := fun hex => h12 ⟨hex, ⟨a, ha, h1⟩⟩
      have hr1 : r ≠ 1 := fun hcon => hno1 ⟨a₀, by simp, hcon ▸ hr ▸ rfl⟩
      have hrlt : r < 3 := Nat.mod_lt _ (by norm_num)
      omega
  have hsum := sum_map_mod_three hall
  have hrlt : r < 3 := Nat.mod_lt _ (by norm_num)
  obtain ⟨k, hk⟩ := h
  have hlen3 : (a₀ :: l₀).length % 3 = 0 := by
    have hr12 : r = 1 ∨ r = 2 := by omega
    rcases hr12 with h1 | h1 <;> rw [h1] at hsum <;> omega
  -- hence the list has at least three elements
  rcases l₀ with _ | ⟨b, l₁⟩
  · simp at hlen3
  rcases l₁ with _ | ⟨c, l₂⟩
  · simp at hlen3
  refine ⟨[a₀, b, c], l₂, by simp, by simp, by simp, ?_⟩
  have hwa := hall a₀ (by simp)
  have hwb := hall b (by simp)
  have hwc := hall c (by simp)
  simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, Nat.add_zero]
  omega

/-- **Regrouping into three-divisible blocks.**  A list whose total weight is a multiple of
three splits, up to reordering, into nonempty blocks of at most three elements, each of weight a
multiple of three.  Applied to a cycle decomposition of an admissible leftover (weights = numbers
of edges) this produces the chunks a reserved family has to absorb. -/
theorem exists_threeDivisible_grouping (l : List α) (w : α → ℕ) (h : 3 ∣ (l.map w).sum) :
    ∃ gs : List (List α), gs.flatten.Perm l ∧
      ∀ g ∈ gs, g ≠ [] ∧ g.length ≤ 3 ∧ 3 ∣ (g.map w).sum := by
  classical
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ N ih =>
  rcases eq_or_ne l [] with rfl | hne
  · exact ⟨[], by simp, by simp⟩
  obtain ⟨g, rest, hperm, hg, hglen, hgsum⟩ := exists_small_threeDivisible_block l w hne h
  have hsum : ((g ++ rest).map w).sum = (l.map w).sum := (hperm.map w).sum_eq
  rw [List.map_append, List.sum_append] at hsum
  have hrest : 3 ∣ (rest.map w).sum := by
    obtain ⟨k, hk⟩ := h
    obtain ⟨j, hj⟩ := hgsum
    exact ⟨k - j, by omega⟩
  have hgpos : 0 < g.length := by
    cases g with
    | nil => exact absurd rfl hg
    | cons _ _ => simp
  have hlenlt : rest.length < l.length := by
    have hle := hperm.length_eq
    simp only [List.length_append] at hle
    omega
  obtain ⟨gs, hgsperm, hgsprop⟩ := ih rest.length (by omega) rest hrest rfl
  refine ⟨g :: gs, ?_, ?_⟩
  · simp only [List.flatten_cons]
    exact List.Perm.trans (List.Perm.append_left g hgsperm) hperm
  · intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact ⟨hg, hglen, hgsum⟩
    · exact hgsprop g' hg'

end Grouping

/-! ### The absorbing kernel with the leftover presented in cycle form -/

/-- **The absorbing kernel, with the leftover handed over in chunked cycle form.**  Same as
`BoundedAbsorbingCoreExists` (hence, by `absorbingCoreExists_of_bounded`, sufficient for
`AbsorbingCoreExists`), except that the admissible leftover `L` comes together with:

* a decomposition of `L` into pairwise edge-disjoint cycles, *all of length at least four*, and
* a grouping of those cycles into *chunks* of at most three cycles, each chunk carrying a number
  of edges divisible by three (so that each chunk is a legitimate config: by
  `localAbsorbable_card_dvd_three` an absorbable config must have `3 ∣` its size).

By `boundedAbsorbingCoreExists_of_cycleForm` all this extra structure is free: the cycles are
supplied by `exists_cycle_decomposition`, the three-cycles among them are triangles of `G` and
are decomposed outright (`triDecomposable_foldr_of_triangleCycles`), and the remaining ones are
grouped by `exists_threeDivisible_grouping`.  The evenness hypothesis of
`BoundedAbsorbingCoreExists` has been consumed by the decomposition. -/
def CycleFormAbsorberExists (ε : ℝ) : Prop :=
  ∃ (n₀ : ℕ) (β₀ : ℝ), 0 < β₀ ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ),
      n₀ ≤ Fintype.card V → 0 < β → β ≤ β₀ →
      (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
      ∃ B : Finset (Finset V), (∀ t ∈ B, G.IsNClique 3 t) ∧ EdgeDisjoint B ∧
        (∀ v : V, (20 * (B.filter (fun t => v ∈ t)).card : ℝ)
          ≤ 10 * ε * (Fintype.card V : ℝ)) ∧
        ∀ (L : Finset (Sym2 V)) (Ch : List (List (Finset (Sym2 V)))),
          L ⊆ G.edgeFinset → Disjoint L (coveredEdges B) →
          (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 → 3 ∣ L.card →
          (∀ C ∈ Ch.flatten, IsCycleEdgeSet C ∧ 4 ≤ C.card) → Ch.flatten.Pairwise Disjoint →
          Ch.flatten.foldr (· ∪ ·) ∅ = L →
          (∀ g ∈ Ch, g ≠ [] ∧ g.length ≤ 3 ∧ 3 ∣ (g.map Finset.card).sum) →
          LocalAbsorbable G B L

/-- **Reduction (sorry-free): it suffices to absorb leftovers presented in chunked cycle form.**
Every admissible leftover has all degrees even, hence decomposes into edge-disjoint cycles
(`exists_cycle_decomposition`).  The three-edge cycles among them are triangles of `G`, so their
union is decomposed outright and needs no reserved edges; the remaining cycles have at least four
edges, their total size is still divisible by three, and they regroup into chunks of at most
three cycles with `3 ∣` chunk size (`exists_threeDivisible_grouping`). -/
theorem boundedAbsorbingCoreExists_of_cycleForm (ε : ℝ) (h : CycleFormAbsorberExists ε) :
    BoundedAbsorbingCoreExists ε := by
  classical
  obtain ⟨n₀, β₀, hβ₀, H⟩ := h
  refine ⟨n₀, β₀, hβ₀, ?_⟩
  intro V _ _ G _ β hn hβpos hβ hδ
  obtain ⟨B, hcl, hd, hload, habs⟩ := H G β hn hβpos hβ hδ
  refine ⟨B, hcl, hd, hload, ?_⟩
  intro L hLsub hLdisj hLcard hLdiv hLeven
  have hdiag : ∀ e ∈ L, ¬ e.IsDiag := by
    intro e he
    exact G.not_isDiag_of_mem_edgeSet (by simpa using hLsub he)
  obtain ⟨Cs, hCs, hpair, hunion⟩ := exists_cycle_decomposition L hdiag hLeven
  have hCsub : ∀ C ∈ Cs, C ⊆ L := fun C hC => hunion ▸ subset_foldr_union hC
  have hCcard : ∀ C ∈ Cs, 3 ≤ C.card := by
    intro C hC
    obtain ⟨l, hnd, h3, rfl⟩ := hCs C hC
    rw [card_cycleEdges hnd h3]
    exact h3
  -- split the cycles into triangles and longer cycles
  set Ts := Cs.filter (fun C => decide (C.card = 3)) with hTs
  set Rs := Cs.filter (fun C => !decide (C.card = 3)) with hRs
  have hperm : (Ts ++ Rs).Perm Cs := List.filter_append_perm _ Cs
  have hpair' : (Ts ++ Rs).Pairwise Disjoint :=
    (hperm.pairwise_iff (fun {x y} hxy => hxy.symm)).mpr hpair
  obtain ⟨hpairT, hpairR, hcross⟩ := List.pairwise_append.mp hpair'
  have hTmem : ∀ C ∈ Ts, C ∈ Cs ∧ C.card = 3 := by
    intro C hC
    rw [hTs, List.mem_filter] at hC
    exact ⟨hC.1, by simpa using hC.2⟩
  have hRmem : ∀ C ∈ Rs, C ∈ Cs ∧ 4 ≤ C.card := by
    intro C hC
    rw [hRs, List.mem_filter] at hC
    have h3 := hCcard C hC.1
    have : C.card ≠ 3 := by simpa using hC.2
    exact ⟨hC.1, by omega⟩
  have hsplit : Ts.foldr (· ∪ ·) ∅ ∪ Rs.foldr (· ∪ ·) ∅ = L := by
    rw [← foldr_union_append, foldr_union_of_perm hperm, hunion]
  have hdisjTR : Disjoint (Ts.foldr (· ∪ ·) ∅) (Rs.foldr (· ∪ ·) ∅) := by
    rw [Finset.disjoint_left]
    intro f hf hf'
    obtain ⟨C, hC, hfC⟩ := mem_foldr_union.mp hf
    obtain ⟨D, hD, hfD⟩ := mem_foldr_union.mp hf'
    exact Finset.disjoint_left.mp (hcross C hC D hD) hfC hfD
  -- the triangles are decomposed outright
  have hTdec : TriDecomposable G (Ts.foldr (· ∪ ·) ∅) := by
    refine triDecomposable_foldr_of_triangleCycles G Ts hpairT ?_
    intro C hC
    obtain ⟨hCs', hcard3⟩ := hTmem C hC
    exact exists_triangle_of_isCycleEdgeSet_card_three G (hCs C hCs')
      ((hCsub C hCs').trans hLsub) hcard3
  -- the longer cycles keep a size divisible by three
  have hcardT : 3 ∣ (Ts.foldr (· ∪ ·) ∅).card := by
    rw [card_foldr_union hpairT]
    refine List.dvd_sum ?_
    intro k hk
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hk
    rw [(hTmem C hC).2]
  have hcardL : (Ts.foldr (· ∪ ·) ∅).card + (Rs.foldr (· ∪ ·) ∅).card = L.card := by
    rw [← hsplit, Finset.card_union_of_disjoint hdisjTR]
  have hcardR : 3 ∣ (Rs.foldr (· ∪ ·) ∅).card := by
    obtain ⟨k, hk⟩ := hLdiv
    obtain ⟨j, hj⟩ := hcardT
    exact ⟨k - j, by omega⟩
  have hRsub : Rs.foldr (· ∪ ·) ∅ ⊆ L := by
    rw [← hsplit]
    exact Finset.subset_union_right
  -- group the longer cycles into three-divisible chunks and absorb them
  have hdvdR : 3 ∣ (Rs.map Finset.card).sum := by
    rw [← card_foldr_union hpairR]
    exact hcardR
  obtain ⟨Ch, hpermCh, hchunks⟩ := exists_threeDivisible_grouping Rs Finset.card hdvdR
  have habsR : LocalAbsorbable G B (Rs.foldr (· ∪ ·) ∅) := by
    refine habs (Rs.foldr (· ∪ ·) ∅) Ch (hRsub.trans hLsub)
      (Finset.disjoint_of_subset_left hRsub hLdisj) ?_ hcardR ?_ ?_ ?_ hchunks
    · refine le_trans ?_ hLcard
      exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hRsub)
    · intro C hC
      obtain ⟨hCs', hcard4⟩ := hRmem C (hpermCh.mem_iff.mp hC)
      exact ⟨hCs C hCs', hcard4⟩
    · exact (hpermCh.pairwise_iff (fun {x y} hxy => hxy.symm)).mpr hpairR
    · rw [foldr_union_of_perm hpermCh]
  -- assemble
  rw [localAbsorbable_iff_triDecomposable]
  have heq : coveredEdges B ∪ L =
      (coveredEdges B ∪ Rs.foldr (· ∪ ·) ∅) ∪ Ts.foldr (· ∪ ·) ∅ := by
    rw [← hsplit]
    ext e
    simp only [Finset.mem_union]
    tauto
  rw [heq]
  have hdisjBT : Disjoint (coveredEdges B) (Ts.foldr (· ∪ ·) ∅) := by
    refine Finset.disjoint_of_subset_right ?_ hLdisj.symm
    rw [← hsplit]
    exact Finset.subset_union_left
  exact ((localAbsorbable_iff_triDecomposable G B _).mp habsR).union hTdec
    (Finset.disjoint_union_left.mpr ⟨hdisjBT, hdisjTR.symm⟩)

/-- The absorbing-core kernel follows from its cycle form. -/
theorem absorbingCoreExists_of_cycleForm (ε : ℝ) (h : CycleFormAbsorberExists ε) :
    AbsorbingCoreExists ε :=
  absorbingCoreExists_of_bounded ε (boundedAbsorbingCoreExists_of_cycleForm ε h)

end Fintype

end Ax2.BKLO
