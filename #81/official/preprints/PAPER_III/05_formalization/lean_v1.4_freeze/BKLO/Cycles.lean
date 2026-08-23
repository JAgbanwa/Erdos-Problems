/-
# Cycles in the edge-set model, and the elementary "cover" moves.

A *cover* of an edge set `C` is an edge-disjoint `T` with `T ∪ C` triangle-decomposable
(`BKLO.Covers`).  Everything the absorber construction of §8.1 needs about cycles is derived from a
single induction, `subdiv_path`: *a path together with the path obtained by subdividing each of its
edges splits into triangles*.  From it:

* `subdiv_cyc`, `subdiv_cyc'` — a cycle, and the fresh copy of a cycle, both cover the edgewise
  subdivision (this is the *relocation* move);
* `covers_even`   — a cycle of even length `2k ≥ 6` is covered by the cycle on its even-indexed
  vertices, of length `k` (this is `subdiv_cyc` read backwards);
* `covers_odd`    — a cycle of odd length `2k+1 ≥ 5` is covered by the chord cycle through one
  fresh vertex, of length `k+2`.

Since a cover multiplies out to `3 ∣ |T| + |C|`, a family whose total size is divisible by `3` is
covered by a family whose total size is again divisible by `3`; iterating the moves shrinks every
cycle to length `3`, `4` or `5`, which is where the explicit gadgets of `BKLO.Gadgets` take over.
-/
import BKLO.Lists
import Nibble.Prelude

open Finset

namespace BKLO

/-! ### Basic covers -/

theorem covers_of_disjoint {T C : Finset (Sym2 ℕ)} (hd : Disjoint T C) (hT : TriDecomp T)
    (hC : TriDecomp C) : Covers T C := ⟨hd, TriDecomp.union hd hT hC⟩

theorem Covers.symm {T C : Finset (Sym2 ℕ)} (h : Covers T C) : Covers C T :=
  ⟨h.1.symm, by rw [Finset.union_comm]; exact h.2⟩

/-! ### Looplessness -/

/-- Every edge of a path has two distinct ends, provided the vertex list has no duplicates. -/
theorem pathEdges_not_isDiag {l : List ℕ} (hnd : l.Nodup) {e : Sym2 ℕ} (he : e ∈ pathEdges l) :
    ¬ e.IsDiag := by
  obtain ⟨i, hi, rfl⟩ := mem_pathEdges_iff.1 he
  simp only [Sym2.isDiag_iff_proj_eq]
  intro h
  rw [hnd.getElem_inj_iff] at h
  omega

/-- The first edge of a path is not an edge of the rest of the path. -/
theorem head_edge_notMem {a b : ℕ} {t : List ℕ} (hnd : (a :: b :: t).Nodup) :
    s(a, b) ∉ pathEdges (b :: t) := by
  intro hc
  have h1 : a ∈ supp (pathEdges (b :: t)) := mem_supp.2 ⟨_, hc, by simp⟩
  have h2 := supp_pathEdges _ h1
  rw [List.mem_toFinset] at h2
  exact (List.nodup_cons.1 hnd).1 h2

/-- The vertex list of a genuine cycle, split as head / second vertex / nonempty rest. -/
theorem cycle_shape {l : List ℕ} (h3 : 3 ≤ l.length) :
    ∃ a b t, l = a :: b :: t ∧ t ≠ [] := by
  match l with
  | [] => simp at h3
  | [_] => simp at h3
  | [_, _] => simp at h3
  | a :: b :: c :: t => exact ⟨a, b, c :: t, rfl, by simp⟩

theorem exists_getLast? {a : ℕ} {t : List ℕ} : ∃ z, (a :: t).getLast? = some z := by
  cases hh : (a :: t).getLast? with
  | none => simp [List.getLast?_eq_none_iff] at hh
  | some z => exact ⟨z, rfl⟩

/-- The edge set of a cycle: the path plus the chord joining its two ends. -/
theorem cycEdges_eq {l : List ℕ} (hnd : l.Nodup) (h3 : 3 ≤ l.length) :
    ∃ a z, l.head? = some a ∧ l.getLast? = some z ∧ a ≠ z ∧ z ∈ l ∧
      cycEdges l = insert s(z, a) (pathEdges l) ∧ s(z, a) ∉ pathEdges l := by
  obtain ⟨a, b, t, rfl, ht⟩ := cycle_shape h3
  obtain ⟨z, hz⟩ := exists_getLast? (a := b) (t := t)
  have hzt : z ∈ t := by
    rw [getLast?_cons_of_ne_nil ht] at hz
    exact List.mem_of_getLast? hz
  have hfull : (a :: b :: t).getLast? = some z := by rw [List.getLast?_cons_cons]; exact hz
  refine ⟨a, z, rfl, hfull, ?_, by simp [hzt], cycEdges_eq_insert hfull, ?_⟩
  · rintro rfl
    exact (List.nodup_cons.1 hnd).1 (by simp [hzt])
  · rw [Sym2.eq_swap]
    exact head_last_notMem_pathEdges hnd ht hz

theorem cycEdges_not_isDiag {l : List ℕ} (hnd : l.Nodup) (h3 : 3 ≤ l.length) {e : Sym2 ℕ}
    (he : e ∈ cycEdges l) : ¬ e.IsDiag := by
  obtain ⟨a, z, -, -, haz, -, heq, -⟩ := cycEdges_eq hnd h3
  rw [heq] at he
  rcases Finset.mem_insert.1 he with rfl | he
  · simpa [Sym2.isDiag_iff_proj_eq] using fun h => haz h.symm
  · exact pathEdges_not_isDiag hnd he

/-! ### Counting -/

/-- The number of edges of a genuine cycle is its length. -/
theorem card_cycEdges {l : List ℕ} (hnd : l.Nodup) (h3 : 3 ≤ l.length) :
    (cycEdges l).card = l.length := by
  obtain ⟨a, z, -, -, -, -, heq, hnot⟩ := cycEdges_eq hnd h3
  rw [heq, Finset.card_insert_of_notMem hnot, card_pathEdges hnd]
  omega

/-- The number of edges of `E` at `v`. -/
def deg (E : Finset (Sym2 ℕ)) (v : ℕ) : ℕ := (E.filter (fun e => v ∈ e)).card

theorem deg_insert {e : Sym2 ℕ} {E : Finset (Sym2 ℕ)} (he : e ∉ E) (v : ℕ) :
    deg (insert e E) v = (if v ∈ e then 1 else 0) + deg E v := by
  classical
  unfold deg
  rw [Finset.filter_insert]
  by_cases h : v ∈ e
  · rw [if_pos h, Finset.card_insert_of_notMem (fun hc => he (Finset.mem_filter.1 hc).1), if_pos h]
    omega
  · rw [if_neg h, if_neg h, Nat.zero_add]

theorem deg_pathEdges_parity : ∀ {l : List ℕ}, l.Nodup → ∀ {a z : ℕ}, l.head? = some a →
    l.getLast? = some z → ∀ v : ℕ,
    (deg (pathEdges l) v + (if v = a then 1 else 0) + (if v = z then 1 else 0)) % 2 = 0
  | [], _, a, z, ha, _, _ => by simp at ha
  | [x], _, a, z, ha, hz, v => by
    simp only [List.head?_cons, Option.some.injEq] at ha
    simp only [List.getLast?_singleton, Option.some.injEq] at hz
    subst ha; subst hz
    simp only [pathEdges_singleton, deg, Finset.filter_empty, Finset.card_empty]
    by_cases h : v = x <;> simp [h]
  | x :: y :: t, hnd, a, z, ha, hz, v => by
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    rw [List.getLast?_cons_cons] at hz
    have hxy : x ≠ y := fun h => (List.nodup_cons.1 hnd).1 (by simp [h])
    have IH := deg_pathEdges_parity hnd.of_cons (show (y :: t).head? = some y from rfl) hz v
    rw [pathEdges_cons₂, deg_insert (head_edge_notMem hnd)]
    have key : (if v ∈ s(x, y) then 1 else 0)
        = (if v = x then 1 else 0) + (if v = y then 1 else 0) := by
      by_cases h1 : v = x
      · subst h1
        simp [Sym2.mem_iff, hxy]
      · by_cases h2 : v = y
        · subst h2
          simp [Sym2.mem_iff, h1]
        · simp [Sym2.mem_iff, h1, h2]
    rw [key]
    revert IH
    generalize (if v = x then 1 else 0) = p
    generalize (if v = y then 1 else 0) = q
    generalize (if v = z then 1 else 0) = r
    generalize deg (pathEdges (y :: t)) v = D
    omega

/-- Every vertex lies on an even number of edges of a cycle. -/
theorem even_deg_cycEdges {l : List ℕ} (hnd : l.Nodup) (h3 : 3 ≤ l.length) (v : ℕ) :
    Even (deg (cycEdges l) v) := by
  obtain ⟨a, z, hha, hhz, haz, -, heq, hnot⟩ := cycEdges_eq hnd h3
  have hpar := deg_pathEdges_parity hnd hha hhz v
  rw [Nat.even_iff, heq, deg_insert hnot]
  have key : (if v ∈ s(z, a) then 1 else 0)
      = (if v = a then 1 else 0) + (if v = z then 1 else 0) := by
    by_cases h1 : v = a
    · subst h1
      simp [Sym2.mem_iff, haz]
    · by_cases h2 : v = z
      · subst h2
        simp [Sym2.mem_iff, h1]
      · simp [Sym2.mem_iff, h1, h2]
  rw [key]
  revert hpar
  generalize (if v = a then 1 else 0) = p
  generalize (if v = z then 1 else 0) = q
  generalize deg (pathEdges l) v = D
  omega

theorem cycEdges_rotate {l : List ℕ} (h : l ≠ []) : cycEdges (l.rotate 1) = cycEdges l := by
  match l with
  | [] => exact absurd rfl h
  | [a] => simp
  | a :: b :: t =>
    obtain ⟨z, hz⟩ := exists_getLast? (a := b) (t := t)
    have hrot : (a :: b :: t).rotate 1 = b :: (t ++ [a]) := by
      rw [List.rotate_cons_succ, List.rotate_zero]; rfl
    have hlast : (b :: (t ++ [a])).getLast? = some a := by
      rw [show b :: (t ++ [a]) = (b :: t) ++ [a] from rfl]
      exact List.getLast?_concat
    rw [hrot, cycEdges_eq_insert hlast,
      show b :: (t ++ [a]) = (b :: t) ++ [a] from rfl, pathEdges_snoc hz a,
      cycEdges_eq_insert (by rw [List.getLast?_cons_cons]; exact hz), pathEdges_cons₂,
      Finset.insert_comm]

/-! ### The subdivision induction -/

/-- The subdivided path and the path are edge-disjoint. -/
theorem subdiv_disjoint {a m : List ℕ} (hnd : (a ++ m).Nodup) :
    Disjoint (pathEdges (interleave a m)) (pathEdges a) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨v, hv, hvm⟩ := mem_snd_of_mem_pathEdges_interleave a m e he
  have hva : v ∈ a := by
    have := supp_pathEdges a (mem_supp.2 ⟨e, he', hv⟩)
    rwa [List.mem_toFinset] at this
  exact (List.disjoint_of_nodup_append hnd) hva hvm

/-- **The workhorse.**  A path `a₀ a₁ … a_k` together with its edgewise subdivision
`a₀ m₀ a₁ m₁ … a_k` splits into the triangles `{aᵢ, mᵢ, aᵢ₊₁}`. -/
theorem subdiv_path : ∀ {a m : List ℕ}, a.length = m.length + 1 → (a ++ m).Nodup →
    TriDecomp (pathEdges (interleave a m) ∪ pathEdges a)
  | [], m, h, _ => by simp at h
  | [_], [], _, _ => by simp [interleave, triDecomp_empty]
  | [_], _ :: _, h, _ => by simp at h
  | _ :: _ :: _, [], h, _ => by simp at h
  | a0 :: a1 :: l, m0 :: t, h, hnd => by
    simp only [List.length_cons] at h
    have hlt : l.length = t.length := by omega
    obtain ⟨R, hR⟩ := interleave_cons_left a1 l t
    have hnd0 : a0 ∉ (a1 :: l) ++ (m0 :: t) := (List.nodup_cons.1 hnd).1
    have hnd1 : ((a1 :: l) ++ (m0 :: t)).Nodup := (List.nodup_cons.1 hnd).2
    have ha0X : a0 ∉ a1 :: l := fun hc => hnd0 (List.mem_append_left _ hc)
    have ha0t : a0 ∉ t := fun hc => hnd0 (List.mem_append_right _ (by simp [hc]))
    have ha0m0 : a0 ≠ m0 := fun hc => hnd0 (List.mem_append_right _ (by simp [hc]))
    have hm0X : m0 ∉ a1 :: l := fun hc =>
      List.disjoint_of_nodup_append hnd1 hc (by simp)
    have hm0t : m0 ∉ t := (List.nodup_cons.1 (List.nodup_append.1 hnd1).2.1).1
    have hm0a1 : m0 ≠ a1 := fun hc => hm0X (by simp [hc])
    have ha0a1 : a0 ≠ a1 := fun hc => ha0X (by simp [hc])
    have hndS : ((a1 :: l) ++ t).Nodup := by
      refine List.Sublist.nodup ?_ hnd
      refine List.Sublist.cons _ ?_
      exact List.Sublist.append_left (List.sublist_cons_self m0 t) (a1 :: l)
    have hS := subdiv_path (a := a1 :: l) (m := t) (by simp [hlt]) hndS
    set S : Finset (Sym2 ℕ) := pathEdges (interleave (a1 :: l) t) ∪ pathEdges (a1 :: l) with hSdef
    have hsuppS : ∀ v ∈ supp S, v ∈ a1 :: l ∨ v ∈ t := by
      intro v hv
      rw [hSdef, supp_union, Finset.mem_union] at hv
      rcases hv with hv | hv
      · have := supp_pathEdges _ hv
        rw [List.mem_toFinset] at this
        exact mem_interleave this
      · have := supp_pathEdges _ hv
        rw [List.mem_toFinset] at this
        exact Or.inl this
    have hEq : pathEdges (interleave (a0 :: a1 :: l) (m0 :: t)) ∪ pathEdges (a0 :: a1 :: l)
        = ({s(a0, m0), s(m0, a1), s(a0, a1)} : Finset (Sym2 ℕ)) ∪ S := by
      show pathEdges (a0 :: m0 :: interleave (a1 :: l) t) ∪ _ = _
      rw [pathEdges_cons₂, hR, pathEdges_cons₂, ← hR, pathEdges_cons₂, hSdef]
      ext e; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; itauto
    rw [hEq]
    refine TriDecomp.union ?_ (triDecomp_tri ha0m0 hm0a1 ha0a1) hS
    rw [Finset.disjoint_left]
    intro e he heS
    have hbad : ∀ v : ℕ, v ∈ e → v ∈ a1 :: l ∨ v ∈ t := fun v hv =>
      hsuppS v (mem_supp.2 ⟨e, heS, hv⟩)
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · rcases hbad a0 (by simp) with hc | hc
      · exact ha0X hc
      · exact ha0t hc
    · rcases hbad m0 (by simp) with hc | hc
      · exact hm0X hc
      · exact hm0t hc
    · rcases hbad a0 (by simp) with hc | hc
      · exact ha0X hc
      · exact ha0t hc

/-! ### The relocation covers -/

/-- **Relocation, first half.**  A cycle covers its edgewise subdivision. -/
theorem subdiv_cyc {a m : List ℕ} (hlen : a.length = m.length) (h3 : 3 ≤ a.length)
    (hnd : (a ++ m).Nodup) : Covers (cycEdges a) (cycEdges (interleave a m)) := by
  obtain ⟨a0, a1, rest, rfl, hrest⟩ := cycle_shape h3
  obtain ⟨a2, rest', rfl⟩ : ∃ a2 rest', rest = a2 :: rest' := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons a2 rest' => exact ⟨a2, rest', rfl⟩
  obtain ⟨m0, t, rfl⟩ : ∃ m0 t, m = m0 :: t := by
    cases m with
    | nil => simp at hlen
    | cons m0 t => exact ⟨m0, t, rfl⟩
  simp only [List.length_cons] at hlen
  set X : List ℕ := a1 :: a2 :: rest' with hXdef
  set A : List ℕ := a1 :: a2 :: (rest' ++ [a0]) with hAdef
  have hAX : X ++ [a0] = A := rfl
  have hXt : X.length = t.length := by simp only [hXdef, List.length_cons]; omega
  -- basic nodup facts
  have hnd0 : a0 ∉ X ++ (m0 :: t) := (List.nodup_cons.1 hnd).1
  have hnd1 : (X ++ (m0 :: t)).Nodup := (List.nodup_cons.1 hnd).2
  have ha0X : a0 ∉ X := fun hc => hnd0 (List.mem_append_left _ hc)
  have ha0t : a0 ∉ t := fun hc => hnd0 (List.mem_append_right _ (by simp [hc]))
  have ha0m0 : a0 ≠ m0 := fun hc => hnd0 (List.mem_append_right _ (by simp [hc]))
  have hm0X : m0 ∉ X := fun hc => List.disjoint_of_nodup_append hnd1 hc (by simp)
  have hm0t : m0 ∉ t := (List.nodup_cons.1 (List.nodup_append.1 hnd1).2.1).1
  have hm0a1 : m0 ≠ a1 := fun hc => hm0X (by simp [hXdef, hc])
  have ha0a1 : a0 ≠ a1 := fun hc => ha0X (by simp [hXdef, hc])
  -- nodup of the reopened path
  have hndAt : (A ++ t).Nodup := by
    have e1 : A ++ t = X ++ (a0 :: t) := by rw [← hAX]; simp
    rw [e1, List.perm_middle.nodup_iff]
    refine List.Sublist.nodup ?_ hnd
    refine List.Sublist.cons₂ _ ?_
    exact List.Sublist.append_left (List.sublist_cons_self m0 t) X
  have hndA : A.Nodup := List.Sublist.nodup (List.sublist_append_left A t) hndAt
  have hlenA : A.length = t.length + 1 := by
    rw [← hAX]; simp only [List.length_append, List.length_singleton, hXt]
  -- the last vertex of `A`
  have hlastA : (a2 :: (rest' ++ [a0])).getLast? = some a0 := by
    rw [show a2 :: (rest' ++ [a0]) = (a2 :: rest') ++ [a0] from rfl]
    exact List.getLast?_concat
  -- the two cycle edge sets
  have hcyc1 : cycEdges (a0 :: X) = insert s(a0, a1) (pathEdges A) := by
    rw [cycEdges_cons]
    show pathEdges (a0 :: a1 :: (a2 :: rest' ++ [a0])) = _
    rw [pathEdges_cons₂]
    rfl
  obtain ⟨R, hR⟩ := interleave_cons_left a1 (a2 :: (rest' ++ [a0])) t
  have hcyc2 : cycEdges (interleave (a0 :: X) (m0 :: t))
      = insert s(a0, m0) (insert s(m0, a1) (pathEdges (interleave A t))) := by
    show cycEdges (a0 :: m0 :: interleave X t) = _
    rw [cycEdges_cons]
    show pathEdges (a0 :: m0 :: (interleave X t ++ [a0])) = _
    rw [interleave_append_last hXt a0, hAX, pathEdges_cons₂]
    congr 1
    rw [hR, pathEdges_cons₂, ← hR]
  -- the subdivision decomposes
  have hS := subdiv_path (a := A) (m := t) hlenA hndAt
  set S : Finset (Sym2 ℕ) := pathEdges (interleave A t) ∪ pathEdges A with hSdef
  have hmemA : ∀ v ∈ A, v ∈ X ∨ v = a0 := by
    intro v hv
    rw [← hAX, List.mem_append] at hv
    simpa using hv
  have hsuppS : ∀ v ∈ supp S, v ∈ X ∨ v = a0 ∨ v ∈ t := by
    intro v hv
    rw [hSdef, supp_union, Finset.mem_union] at hv
    have key : v ∈ A ∨ v ∈ t := by
      rcases hv with hv | hv
      · have := supp_pathEdges _ hv
        rw [List.mem_toFinset] at this
        exact mem_interleave this
      · have := supp_pathEdges _ hv
        rw [List.mem_toFinset] at this
        exact Or.inl this
    rcases key with hk | hk
    · rcases hmemA v hk with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr hk)
  have hm0S : m0 ∉ supp S := by
    intro hc
    rcases hsuppS m0 hc with h' | h' | h'
    · exact hm0X h'
    · exact ha0m0 h'.symm
    · exact hm0t h'
  -- the chord `a₀a₁` is not in the subdivision picture
  have hchord : s(a0, a1) ∉ S := by
    rw [hSdef]
    intro hc
    rcases Finset.mem_union.1 hc with hc | hc
    · obtain ⟨v, hv, hvt⟩ := mem_snd_of_mem_pathEdges_interleave A t _ hc
      have hvX : v ∈ a0 :: X := by
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · simp
        · rw [hXdef]; simp
      exact List.disjoint_of_nodup_append hnd hvX (by simp [hvt])
    · exact head_last_notMem_pathEdges hndA (by simp) hlastA (by rwa [Sym2.eq_swap] at hc)
  refine ⟨?_, ?_⟩
  · -- the two cycles are edge-disjoint
    rw [hcyc1, hcyc2, Finset.disjoint_left]
    intro e he he'
    have hbadm : ∃ v ∈ e, v ∈ m0 :: t := by
      rcases Finset.mem_insert.1 he' with rfl | he'
      · exact ⟨m0, by simp, by simp⟩
      rcases Finset.mem_insert.1 he' with rfl | he'
      · exact ⟨m0, by simp, by simp⟩
      · obtain ⟨v, hv, hvt⟩ := mem_snd_of_mem_pathEdges_interleave A t _ he'
        exact ⟨v, hv, by simp [hvt]⟩
    obtain ⟨v, hv, hvm⟩ := hbadm
    have hva : v ∈ a0 :: X := by
      rcases Finset.mem_insert.1 he with rfl | he
      · rcases Sym2.mem_iff.1 hv with rfl | rfl
        · simp
        · simp [hXdef]
      · have := supp_pathEdges A (mem_supp.2 ⟨e, he, hv⟩)
        rw [List.mem_toFinset] at this
        rcases hmemA v this with h' | rfl
        · exact List.mem_cons_of_mem _ h'
        · simp
    exact List.disjoint_of_nodup_append hnd hva hvm
  · -- the union decomposes
    have hEq : cycEdges (a0 :: X) ∪ cycEdges (interleave (a0 :: X) (m0 :: t))
        = ({s(a0, m0), s(m0, a1), s(a0, a1)} : Finset (Sym2 ℕ)) ∪ S := by
      rw [hcyc1, hcyc2, hSdef]
      ext e; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; itauto
    rw [hEq]
    refine TriDecomp.union ?_ (triDecomp_tri ha0m0 hm0a1 ha0a1) hS
    rw [Finset.disjoint_left]
    intro e he heS
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact hm0S (mem_supp.2 ⟨_, heS, by simp⟩)
    · exact hm0S (mem_supp.2 ⟨_, heS, by simp⟩)
    · exact hchord heS

/-- **Relocation, second half.**  The fresh copy also covers the subdivision. -/
theorem subdiv_cyc' {a m : List ℕ} (hlen : a.length = m.length) (h3 : 3 ≤ a.length)
    (hnd : (a ++ m).Nodup) : Covers (cycEdges m) (cycEdges (interleave a m)) := by
  have hane : a ≠ [] := by rintro rfl; simp at h3
  have hine : interleave a m ≠ [] := by
    cases a with
    | nil => exact absurd rfl hane
    | cons a0 a' =>
      cases m with
      | nil => simp at hlen
      | cons m0 m' => simp [interleave]
  have hrot : cycEdges (interleave a m) = cycEdges (interleave m (a.rotate 1)) := by
    rw [← interleave_rotate hlen hane, cycEdges_rotate hine]
  rw [hrot]
  refine subdiv_cyc (by rw [List.length_rotate]; omega) (by omega) ?_
  have hp : (m ++ a.rotate 1).Perm (a ++ m) :=
    (List.Perm.append_left m (a.rotate_perm 1)).trans List.perm_append_comm
  rw [hp.nodup_iff]
  exact hnd

/-! ### The elementary moves -/

/-- A triangle is triangle-decomposable. -/
theorem triDecomp_cyc3 {l : List ℕ} (hnd : l.Nodup) (h : l.length = 3) :
    TriDecomp (cycEdges l) := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, l = [a, b, c] := by
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩
    · simp at h
    · simp at h
    · simp at h
    · exact ⟨a, b, c, rfl⟩
    · simp at h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.nodup_nil, and_true, or_false, not_or] at hnd
  have hab : a ≠ b := hnd.1.1
  have hac : a ≠ c := hnd.1.2
  have hbc : b ≠ c := hnd.2.1
  have heq : cycEdges [a, b, c] = ({s(a, b), s(b, c), s(a, c)} : Finset (Sym2 ℕ)) := by
    show pathEdges [a, b, c, a] = _
    rw [pathEdges_cons₂, pathEdges_cons₂, pathEdges_cons₂]
    ext e
    simp only [pathEdges_singleton, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, or_false]
    rw [Sym2.eq_swap (a := c) (b := a)]
  rw [heq]
  exact triDecomp_tri hab hbc hac

/-- **Halving move.**  A cycle of even length `2k ≥ 6` is covered by the cycle on its even-indexed
vertices, which has length `k`. -/
theorem covers_even {l : List ℕ} {k : ℕ} (hnd : l.Nodup) (hlen : l.length = 2 * k) (hk : 3 ≤ k) :
    Covers (cycEdges (evensL l)) (cycEdges l) := by
  have hperm := evensL_oddsL_perm l
  have hnd' : (evensL l ++ oddsL l).Nodup := hperm.nodup_iff.2 hnd
  have h1 : (evensL l).length = k := by rw [evensL_length]; omega
  have h2 : (oddsL l).length = k := by rw [oddsL_length]; omega
  have hc := subdiv_cyc (a := evensL l) (m := oddsL l) (by omega) (by omega) hnd'
  rwa [interleave_evens_odds] at hc

/-- **Odd move.**  A cycle of odd length `2k+1 ≥ 5` is covered by the chord cycle through a fresh
vertex `w`, which has length `k+2`. -/
theorem covers_odd {l : List ℕ} {w k : ℕ} (hnd : l.Nodup) (hw : w ∉ l)
    (hlen : l.length = 2 * k + 1) (hk : 2 ≤ k) :
    Covers (cycEdges (evensL l ++ [w])) (cycEdges l) := by
  set A : List ℕ := evensL l with hAdef
  set M : List ℕ := oddsL l with hMdef
  have hperm := evensL_oddsL_perm l
  have hndAM : (A ++ M).Nodup := hperm.nodup_iff.2 hnd
  have hlA : A.length = k + 1 := by rw [hAdef, evensL_length]; omega
  have hlM : M.length = k := by rw [hMdef, oddsL_length]; omega
  have hint : interleave A M = l := interleave_evens_odds l
  have hndA : A.Nodup := List.Sublist.nodup (List.sublist_append_left A M) hndAM
  have hAsub : ∀ v ∈ A, v ∈ l := fun v hv => evensL_subset hv
  -- head and last vertex of `l`
  obtain ⟨a0, b0, t0, hl, ht0⟩ := cycle_shape (l := l) (by omega)
  obtain ⟨z, hz⟩ := exists_getLast? (a := b0) (t := t0)
  have hlz : l.getLast? = some z := by rw [hl, List.getLast?_cons_cons]; exact hz
  have hla : l.head? = some a0 := by rw [hl]; rfl
  have hzt0 : z ∈ t0 := by
    rw [getLast?_cons_of_ne_nil ht0] at hz
    exact List.mem_of_getLast? hz
  have hzl : z ∈ l := by rw [hl]; simp [hzt0]
  have ha0l : a0 ∈ l := by rw [hl]; simp
  have ha0z : a0 ≠ z := by
    rintro rfl
    rw [hl] at hnd
    exact (List.nodup_cons.1 hnd).1 (by simp [hzt0])
  have hAhead : A.head? = some a0 := by rw [hAdef, evensL_head?]; exact hla
  have hAlast : A.getLast? = some z := by rw [hAdef, evensL_getLast?_odd (by omega)]; exact hlz
  -- the shape of `A`
  obtain ⟨x, y, A3, hAshape, hA3⟩ := cycle_shape (l := A) (by omega)
  have hx : x = a0 := by rw [hAshape] at hAhead; simpa using hAhead
  rw [hx] at hAshape
  have hlastA : (y :: A3).getLast? = some z := by
    rw [hAshape, List.getLast?_cons_cons] at hAlast; exact hAlast
  -- the two cycle edge sets
  have hcycA : cycEdges (A ++ [w]) = insert s(w, a0) (insert s(z, w) (pathEdges A)) := by
    have e1 : A ++ [w] = a0 :: ((y :: A3) ++ [w]) := by rw [hAshape]; rfl
    have e2 : (A ++ [w]).getLast? = some w := List.getLast?_concat
    rw [e1] at e2 ⊢
    rw [cycEdges_eq_insert e2, ← e1, pathEdges_snoc hAlast]
  have hcycl : cycEdges l = insert s(z, a0) (pathEdges l) := by
    have e2 : l.getLast? = some z := hlz
    rw [hl] at e2 ⊢
    rw [cycEdges_eq_insert e2]
  have hnotl : s(z, a0) ∉ pathEdges l := by
    rw [Sym2.eq_swap, hl]
    exact head_last_notMem_pathEdges (hl ▸ hnd) ht0 hz
  have hnotA : s(z, a0) ∉ pathEdges A := by
    rw [Sym2.eq_swap, hAshape]
    exact head_last_notMem_pathEdges (hAshape ▸ hndA) hA3 hlastA
  -- the fresh triangle
  have hwa0 : a0 ≠ w := fun hc => hw (by rw [← hc]; exact ha0l)
  have hwz : w ≠ z := fun hc => hw (by rw [hc]; exact hzl)
  have hS := subdiv_path (a := A) (m := M) (by omega) hndAM
  rw [hint] at hS
  have hdisjlA : Disjoint (pathEdges l) (pathEdges A) := by
    have := subdiv_disjoint (a := A) (m := M) hndAM
    rwa [hint] at this
  set S : Finset (Sym2 ℕ) := pathEdges l ∪ pathEdges A with hSdef
  have hsuppS : ∀ v ∈ supp S, v ∈ l := by
    intro v hv
    rw [hSdef, supp_union, Finset.mem_union] at hv
    rcases hv with hv | hv
    · have := supp_pathEdges _ hv; rwa [List.mem_toFinset] at this
    · have := supp_pathEdges _ hv
      rw [List.mem_toFinset] at this
      exact hAsub v this
  have hchord : s(z, a0) ∉ S := by
    rw [hSdef]
    intro hc
    rcases Finset.mem_union.1 hc with hc | hc
    · exact hnotl hc
    · exact hnotA hc
  refine ⟨?_, ?_⟩
  · rw [hcycA, hcycl, Finset.disjoint_left]
    intro e he he'
    have hwnot : w ∉ e → False → False := fun _ h => h
    have hene : ∀ v : ℕ, v ∈ e → v ∈ l := by
      intro v hv
      rcases Finset.mem_insert.1 he' with rfl | he'
      · rcases Sym2.mem_iff.1 hv with rfl | rfl
        · exact hzl
        · exact ha0l
      · exact hsuppS v (mem_supp.2 ⟨e, Finset.mem_union_left _ he', hv⟩)
    rcases Finset.mem_insert.1 he with rfl | he
    · exact hw (hene w (by simp))
    rcases Finset.mem_insert.1 he with rfl | he
    · exact hw (hene w (by simp))
    · rcases Finset.mem_insert.1 he' with heq | he'
      · exact hnotA (by rw [← heq]; exact he)
      · exact Finset.disjoint_left.1 hdisjlA he' he
  · have hEq : cycEdges (A ++ [w]) ∪ cycEdges l
        = ({s(a0, w), s(w, z), s(a0, z)} : Finset (Sym2 ℕ)) ∪ S := by
      rw [hcycA, hcycl, hSdef]
      ext e
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      rw [Sym2.eq_swap (a := a0) (b := w), Sym2.eq_swap (a := w) (b := z),
        Sym2.eq_swap (a := a0) (b := z)]
      itauto
    rw [hEq]
    refine TriDecomp.union ?_ (triDecomp_tri hwa0 hwz ha0z) hS
    rw [Finset.disjoint_left]
    intro e he heS
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact hw (hsuppS w (mem_supp.2 ⟨_, heS, by simp⟩))
    · exact hw (hsuppS w (mem_supp.2 ⟨_, heS, by simp⟩))
    · exact hchord (by rw [Sym2.eq_swap] at heS; exact heS)

/-! ### Families of cycles -/

/-- The edge set of a family of cycles. -/
def cycFamEdges : List (List ℕ) → Finset (Sym2 ℕ)
  | [] => ∅
  | l :: L => cycEdges l ∪ cycFamEdges L

/-- Total number of edges of a family of cycles. -/
def totalLen (L : List (List ℕ)) : ℕ := (L.map List.length).sum

/-- A family of genuine cycles which are pairwise **edge**-disjoint. -/
structure EdgeDisjFam (L : List (List ℕ)) : Prop where
  nodup : ∀ l ∈ L, l.Nodup
  three : ∀ l ∈ L, 3 ≤ l.length
  pdisj : L.Pairwise fun l l' => Disjoint (cycEdges l) (cycEdges l')

/-- A family of genuine cycles which are pairwise **vertex**-disjoint. -/
structure VertDisjFam (L : List (List ℕ)) : Prop where
  nodup : ∀ l ∈ L, l.Nodup
  three : ∀ l ∈ L, 3 ≤ l.length
  pdisj : L.Pairwise fun l l' => ∀ v ∈ l, v ∉ l'

@[simp] theorem cycFamEdges_nil : cycFamEdges [] = ∅ := rfl

@[simp] theorem cycFamEdges_cons (l : List ℕ) (L : List (List ℕ)) :
    cycFamEdges (l :: L) = cycEdges l ∪ cycFamEdges L := rfl

@[simp] theorem totalLen_nil : totalLen [] = 0 := rfl

@[simp] theorem totalLen_cons (l : List ℕ) (L : List (List ℕ)) :
    totalLen (l :: L) = l.length + totalLen L := rfl

theorem supp_cycFamEdges : ∀ L : List (List ℕ), supp (cycFamEdges L) ⊆ L.flatten.toFinset
  | [] => by simp
  | l :: L => by
    rw [cycFamEdges_cons, supp_union]
    intro v hv
    rcases Finset.mem_union.1 hv with h | h
    · have := supp_cycEdges l h
      rw [List.mem_toFinset] at this ⊢
      simp [this]
    · have := supp_cycFamEdges L h
      rw [List.mem_toFinset] at this ⊢
      simp only [List.flatten_cons, List.mem_append]
      exact Or.inr this

theorem disjoint_cycFamEdges {l : List ℕ} {L : List (List ℕ)}
    (h : ∀ l' ∈ L, Disjoint (cycEdges l) (cycEdges l')) :
    Disjoint (cycEdges l) (cycFamEdges L) := by
  induction L with
  | nil => simp
  | cons l' L' IH =>
    rw [cycFamEdges_cons]
    exact Finset.disjoint_union_right.2
      ⟨h l' (by simp), IH (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem EdgeDisjFam.tail {l : List ℕ} {L : List (List ℕ)} (h : EdgeDisjFam (l :: L)) :
    EdgeDisjFam L :=
  ⟨fun x hx => h.nodup x (List.mem_cons_of_mem _ hx),
    fun x hx => h.three x (List.mem_cons_of_mem _ hx), (List.pairwise_cons.1 h.pdisj).2⟩

theorem EdgeDisjFam.head_disjoint {l : List ℕ} {L : List (List ℕ)} (h : EdgeDisjFam (l :: L)) :
    Disjoint (cycEdges l) (cycFamEdges L) :=
  disjoint_cycFamEdges (fun l' hl' => (List.pairwise_cons.1 h.pdisj).1 l' hl')

theorem VertDisjFam.toEdgeDisj {L : List (List ℕ)} (h : VertDisjFam L) : EdgeDisjFam L := by
  refine ⟨h.nodup, h.three, h.pdisj.imp ?_⟩
  intro l l' hll
  rw [Finset.disjoint_left]
  intro e
  induction e using Sym2.ind with
  | _ p q =>
    intro he he'
    have hp : p ∈ l := by
      have h1 : p ∈ supp (cycEdges l) := mem_supp.2 ⟨s(p, q), he, by simp⟩
      have h2 := supp_cycEdges l h1
      rwa [List.mem_toFinset] at h2
    have hp' : p ∈ l' := by
      have h1 : p ∈ supp (cycEdges l') := mem_supp.2 ⟨s(p, q), he', by simp⟩
      have h2 := supp_cycEdges l' h1
      rwa [List.mem_toFinset] at h2
    exact hll p hp hp'

theorem card_cycFamEdges : ∀ {L : List (List ℕ)}, EdgeDisjFam L →
    (cycFamEdges L).card = totalLen L
  | [], _ => by simp [totalLen]
  | l :: L, h => by
    rw [cycFamEdges_cons, Finset.card_union_of_disjoint h.head_disjoint,
      card_cycFamEdges h.tail,
      card_cycEdges (h.nodup l (by simp)) (h.three l (by simp)), totalLen_cons]

/-- Every triangle-decomposable edge set has a number of edges divisible by `3`. -/
theorem TriDecomp.three_dvd_card {E : Finset (Sym2 ℕ)} (h : TriDecomp E) : 3 ∣ E.card := by
  obtain ⟨P, hc, hd, rfl⟩ := h
  rw [famEdges, Finset.card_biUnion hd]
  refine Finset.dvd_sum ?_
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 (hc t ht)
  rw [cliqueEdges_triple hab hbc hac,
    Finset.card_insert_of_notMem (by simp; tauto),
    Finset.card_insert_of_notMem (by simp; tauto)]
  simp

end BKLO
