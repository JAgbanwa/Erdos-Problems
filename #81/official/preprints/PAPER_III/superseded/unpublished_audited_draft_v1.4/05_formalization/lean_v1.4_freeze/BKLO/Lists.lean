/-
# Paths and cycles as edge sets: the list-level foundations.

`pathEdges l` and `cycEdges l` are the edge sets of the path and of the closed cycle through the
vertex list `l`.  This file develops what the absorber construction needs about them: the index
description of membership, the support, the number of edges of a cycle, and the fact that every
vertex of a cycle lies on exactly two of its edges (which is what makes "remove a cycle" preserve
evenness in `BKLO.Veblen`).  It also sets up the `evensL` / `oddsL` / `interleave` triple used by
the subdivision induction.
-/
import BKLO.Core
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.Monotonicity

open Finset

namespace BKLO

/-! ### Definitions -/

/-- The list of edges along `l`. -/
def edgeList : List ℕ → List (Sym2 ℕ)
  | [] => []
  | [_] => []
  | a :: b :: t => s(a, b) :: edgeList (b :: t)

/-- Edges of the path along `l`. -/
def pathEdges (l : List ℕ) : Finset (Sym2 ℕ) := (edgeList l).toFinset

/-- Edges of the closed cycle along `l`. -/
def cycEdges : List ℕ → Finset (Sym2 ℕ)
  | [] => ∅
  | a :: t => pathEdges (a :: (t ++ [a]))

/-- The entries of `l` at even positions. -/
def evensL : List ℕ → List ℕ
  | [] => []
  | [a] => [a]
  | a :: _ :: t => a :: evensL t

/-- The entries of `l` at odd positions. -/
def oddsL : List ℕ → List ℕ
  | [] => []
  | [_] => []
  | _ :: b :: t => b :: oddsL t

/-- `[l₀, x₀, l₁, x₁, …]`; if `l` is one longer than `x` the result ends with the last entry of
`l`. -/
def interleave : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: _, [] => [a]
  | a :: l, x :: t => a :: x :: interleave l t

/-! ### Basic rewriting rules -/

@[simp] theorem edgeList_nil : edgeList [] = [] := rfl

@[simp] theorem edgeList_singleton (a : ℕ) : edgeList [a] = [] := rfl

@[simp] theorem edgeList_cons₂ (a b : ℕ) (t : List ℕ) :
    edgeList (a :: b :: t) = s(a, b) :: edgeList (b :: t) := rfl

@[simp] theorem pathEdges_nil : pathEdges [] = ∅ := rfl

@[simp] theorem pathEdges_singleton (a : ℕ) : pathEdges [a] = ∅ := rfl

theorem pathEdges_cons₂ (a b : ℕ) (t : List ℕ) :
    pathEdges (a :: b :: t) = insert s(a, b) (pathEdges (b :: t)) := by
  simp [pathEdges]

theorem cycEdges_cons (a : ℕ) (t : List ℕ) :
    cycEdges (a :: t) = pathEdges (a :: (t ++ [a])) := rfl

theorem edgeList_length (l : List ℕ) : (edgeList l).length = l.length - 1 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    match t with
    | [] => simp
    | b :: t' => simp only [edgeList_cons₂, List.length_cons] at *; omega

/-- The `i`-th edge of a path joins the `i`-th and `(i+1)`-st vertices. -/
theorem edgeList_getElem {l : List ℕ} {i : ℕ} (h : i < (edgeList l).length) :
    (edgeList l)[i] = s(l[i]'(by rw [edgeList_length] at h; omega),
      l[i + 1]'(by rw [edgeList_length] at h; omega)) := by
  induction l generalizing i with
  | nil => simp at h
  | cons a t ih =>
    match t with
    | [] => simp at h
    | b :: t' =>
      match i with
      | 0 => simp
      | (i + 1) =>
        simp only [edgeList_cons₂, List.getElem_cons_succ]
        exact ih (by simpa using h)

theorem mem_pathEdges_iff {l : List ℕ} {e : Sym2 ℕ} :
    e ∈ pathEdges l ↔ ∃ i, ∃ h : i + 1 < l.length,
      e = s(l[i]'(by omega), l[i + 1]'h) := by
  rw [pathEdges, List.mem_toFinset, List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [edgeList_getElem hi]
    rw [edgeList_length] at hi
    exact ⟨i, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, by rw [edgeList_length]; omega, ?_⟩
    rw [edgeList_getElem (by rw [edgeList_length]; omega)]

/-! ### Support -/

theorem supp_insert (e : Sym2 ℕ) (E : Finset (Sym2 ℕ)) :
    supp (insert e E) = e.toFinset ∪ supp E := by
  simp [supp, Finset.biUnion_insert]

theorem supp_pathEdges : ∀ l : List ℕ, supp (pathEdges l) ⊆ l.toFinset
  | [] => by simp
  | [_] => by simp
  | a :: b :: t => by
    rw [pathEdges_cons₂, supp_insert]
    intro v hv
    rcases Finset.mem_union.1 hv with h | h
    · have : v = a ∨ v = b := by simpa using h
      rcases this with rfl | rfl <;> simp
    · have := supp_pathEdges (b :: t) h
      simp only [List.toFinset_cons, Finset.mem_insert] at this ⊢
      tauto

theorem supp_cycEdges : ∀ l : List ℕ, supp (cycEdges l) ⊆ l.toFinset
  | [] => by simp [cycEdges]
  | a :: t => by
    rw [cycEdges_cons]
    intro v hv
    have := supp_pathEdges _ hv
    simp only [List.toFinset_cons, List.mem_toFinset, List.mem_cons, List.mem_append,
      Finset.mem_insert] at this ⊢
    tauto

/-! ### Lengths of `evensL`, `oddsL`, `interleave` -/

theorem evensL_length : ∀ l : List ℕ, (evensL l).length = (l.length + 1) / 2
  | [] => rfl
  | [_] => by simp [evensL]
  | _ :: _ :: t => by
    simp only [evensL, List.length_cons]
    rw [evensL_length t]
    omega

theorem oddsL_length : ∀ l : List ℕ, (oddsL l).length = l.length / 2
  | [] => rfl
  | [_] => by simp [oddsL]
  | _ :: _ :: t => by
    simp only [oddsL, List.length_cons]
    rw [oddsL_length t]
    omega

theorem evensL_subset : ∀ {l : List ℕ} {v : ℕ}, v ∈ evensL l → v ∈ l
  | [], _ => by simp [evensL]
  | [_], _ => by simp [evensL]
  | a :: b :: t, v => by
    intro h
    simp only [evensL, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (evensL_subset h))

theorem oddsL_subset : ∀ {l : List ℕ} {v : ℕ}, v ∈ oddsL l → v ∈ l
  | [], _ => by simp [oddsL]
  | [_], _ => by simp [oddsL]
  | a :: b :: t, v => by
    intro h
    simp only [oddsL, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (oddsL_subset h))

theorem evensL_nodup : ∀ {l : List ℕ}, l.Nodup → (evensL l).Nodup
  | [], _ => by simp [evensL]
  | [_], _ => by simp [evensL]
  | a :: b :: t, h => by
    simp only [evensL, List.nodup_cons]
    simp only [List.nodup_cons, List.mem_cons] at h
    exact ⟨fun hc => h.1 (Or.inr (evensL_subset hc)), evensL_nodup h.2.2⟩

theorem oddsL_nodup : ∀ {l : List ℕ}, l.Nodup → (oddsL l).Nodup
  | [], _ => by simp [oddsL]
  | [_], _ => by simp [oddsL]
  | a :: b :: t, h => by
    simp only [oddsL, List.nodup_cons]
    simp only [List.nodup_cons, List.mem_cons] at h
    exact ⟨fun hc => h.2.1 (oddsL_subset hc), oddsL_nodup h.2.2⟩

theorem interleave_evens_odds : ∀ l : List ℕ, interleave (evensL l) (oddsL l) = l
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    simp only [evensL, oddsL, interleave]
    rw [interleave_evens_odds t]

theorem interleave_length : ∀ {a m : List ℕ}, a.length = m.length →
    (interleave a m).length = 2 * a.length
  | [], m, h => by simp [interleave]
  | a :: l, [], h => by simp at h
  | a :: l, x :: t, h => by
    simp only [interleave, List.length_cons]
    simp only [List.length_cons] at h
    rw [interleave_length (Nat.succ_injective h)]
    omega

theorem interleave_length_succ : ∀ {a m : List ℕ}, a.length = m.length + 1 →
    (interleave a m).length = 2 * m.length + 1
  | [], m, h => by simp at h
  | a :: l, [], h => by simp [interleave]
  | a :: l, x :: t, h => by
    simp only [interleave, List.length_cons]
    simp only [List.length_cons] at h
    rw [interleave_length_succ (Nat.succ_injective h)]
    omega

theorem mem_interleave : ∀ {a m : List ℕ} {v : ℕ}, v ∈ interleave a m → v ∈ a ∨ v ∈ m
  | [], m, v => by simp [interleave]
  | a :: l, [], v => by
    intro h
    simp only [interleave, List.mem_singleton] at h
    exact Or.inl (by simp [h])
  | a :: l, x :: t, v => by
    intro h
    simp only [interleave, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
    · rcases mem_interleave h with h' | h'
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · exact Or.inr (List.mem_cons_of_mem _ h')

theorem interleave_nodup : ∀ {a m : List ℕ}, (a ++ m).Nodup → (interleave a m).Nodup
  | [], m, h => by simp [interleave]
  | a :: l, [], h => by simp [interleave]
  | a :: l, x :: t, h => by
    rw [List.cons_append, List.nodup_cons] at h
    obtain ⟨ha, h'⟩ := h
    rw [List.perm_middle.nodup_iff, List.nodup_cons] at h'
    obtain ⟨hx, h''⟩ := h'
    simp only [List.mem_append] at ha hx
    simp only [interleave, List.nodup_cons, List.mem_cons]
    refine ⟨?_, ?_, interleave_nodup h''⟩
    · rintro (rfl | hc)
      · exact ha (Or.inr (by simp))
      · rcases mem_interleave hc with h1 | h1
        · exact ha (Or.inl h1)
        · exact ha (Or.inr (by simp [h1]))
    · intro hc
      rcases mem_interleave hc with h1 | h1
      · exact hx (Or.inl h1)
      · exact hx (Or.inr h1)

/-! ### Prefixes and monotonicity -/

theorem edgeList_append_exists : ∀ (L M : List ℕ), ∃ N, edgeList (L ++ M) = edgeList L ++ N
  | [], M => ⟨edgeList M, by simp⟩
  | [a], M => ⟨edgeList ([a] ++ M), by simp⟩
  | a :: b :: t, M => by
    obtain ⟨N, hN⟩ := edgeList_append_exists (b :: t) M
    refine ⟨N, ?_⟩
    simp only [List.cons_append, edgeList_cons₂]
    rw [show b :: (t ++ M) = (b :: t) ++ M from rfl, hN]

theorem pathEdges_subset_append (L M : List ℕ) : pathEdges L ⊆ pathEdges (L ++ M) := by
  obtain ⟨N, hN⟩ := edgeList_append_exists L M
  intro e he
  rw [pathEdges, List.mem_toFinset] at he ⊢
  rw [hN]
  exact List.mem_append_left _ he

/-! ### Nodup and cardinality -/

theorem edgeList_nodup : ∀ {l : List ℕ}, l.Nodup → (edgeList l).Nodup
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: t, h => by
    rw [edgeList_cons₂, List.nodup_cons]
    refine ⟨?_, edgeList_nodup h.of_cons⟩
    intro hc
    have h1 : a ∈ supp (pathEdges (b :: t)) :=
      mem_supp.2 ⟨s(a, b), List.mem_toFinset.2 hc, by simp⟩
    have h2 := supp_pathEdges _ h1
    rw [List.mem_toFinset] at h2
    exact (List.nodup_cons.1 h).1 h2

theorem card_pathEdges {l : List ℕ} (h : l.Nodup) : (pathEdges l).card = l.length - 1 := by
  rw [pathEdges, List.toFinset_card_of_nodup (edgeList_nodup h), edgeList_length]

/-! ### The last vertex -/

theorem getLast?_cons_of_ne_nil {a : ℕ} {X : List ℕ} (h : X ≠ []) :
    (a :: X).getLast? = X.getLast? := by
  cases X with
  | nil => exact absurd rfl h
  | cons b Y => exact List.getLast?_cons_cons

theorem pathEdges_snoc : ∀ {L : List ℕ} {y : ℕ}, L.getLast? = some y → ∀ z : ℕ,
    pathEdges (L ++ [z]) = insert s(y, z) (pathEdges L)
  | [], y, h, z => by simp at h
  | [a], y, h, z => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h
    simp [pathEdges_cons₂]
  | a :: b :: t, y, h, z => by
    rw [List.getLast?_cons_cons] at h
    simp only [List.cons_append, pathEdges_cons₂]
    rw [show b :: (t ++ [z]) = (b :: t) ++ [z] from rfl, pathEdges_snoc h z, Finset.insert_comm]

theorem cycEdges_eq_insert {a : ℕ} {t : List ℕ} {z : ℕ} (h : (a :: t).getLast? = some z) :
    cycEdges (a :: t) = insert s(z, a) (pathEdges (a :: t)) := by
  rw [cycEdges_cons, show a :: (t ++ [a]) = (a :: t) ++ [a] from rfl]
  exact pathEdges_snoc h a

/-- The chord joining the two ends of a path of length `≥ 3` is not an edge of the path. -/
theorem head_last_notMem_pathEdges {a b : ℕ} {t : List ℕ} {z : ℕ}
    (hnd : (a :: b :: t).Nodup) (ht : t ≠ []) (hz : (b :: t).getLast? = some z) :
    s(a, z) ∉ pathEdges (a :: b :: t) := by
  rw [pathEdges_cons₂]
  intro hmem
  have hab : a ≠ b := by
    simp only [List.nodup_cons, List.mem_cons] at hnd; tauto
  have hzt : z ∈ t := by
    rw [getLast?_cons_of_ne_nil ht] at hz
    exact List.mem_of_getLast? hz
  have hbt : b ∉ t := by
    simp only [List.nodup_cons] at hnd; exact hnd.2.1
  rcases Finset.mem_insert.1 hmem with h | h
  · rw [Sym2.eq_iff] at h
    rcases h with ⟨-, rfl⟩ | ⟨rfl, -⟩
    · exact hbt hzt
    · exact hab rfl
  · have h1 : a ∈ supp (pathEdges (b :: t)) := mem_supp.2 ⟨_, h, by simp⟩
    have h2 := supp_pathEdges _ h1
    rw [List.mem_toFinset] at h2
    exact (List.nodup_cons.1 hnd).1 h2

/-! ### More on `evensL` / `oddsL` -/

theorem evensL_ne_nil : ∀ {l : List ℕ}, l ≠ [] → evensL l ≠ []
  | [], h => absurd rfl h
  | [_], _ => by simp [evensL]
  | _ :: _ :: _, _ => by simp [evensL]

theorem evensL_head? : ∀ l : List ℕ, (evensL l).head? = l.head?
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

theorem evensL_getLast?_odd : ∀ {l : List ℕ}, l.length % 2 = 1 → (evensL l).getLast? = l.getLast?
  | [], h => by simp at h
  | [a], _ => rfl
  | a :: b :: t, h => by
    simp only [List.length_cons] at h
    have ht : t ≠ [] := by
      rintro rfl; simp at h
    rw [evensL, getLast?_cons_of_ne_nil (evensL_ne_nil ht), List.getLast?_cons_cons,
      getLast?_cons_of_ne_nil ht]
    exact evensL_getLast?_odd (by omega)

theorem evensL_oddsL_perm : ∀ l : List ℕ, (evensL l ++ oddsL l).Perm l
  | [] => by simp [evensL, oddsL]
  | [a] => by simp [evensL, oddsL]
  | a :: b :: t => by
    simp only [evensL, oddsL, List.cons_append]
    refine List.Perm.cons a ?_
    refine List.Perm.trans List.perm_middle ?_
    exact List.Perm.cons b (evensL_oddsL_perm t)

/-! ### More on `interleave` -/

theorem interleave_append_last : ∀ {a m : List ℕ}, a.length = m.length → ∀ z : ℕ,
    interleave a m ++ [z] = interleave (a ++ [z]) m
  | [], [], _, z => rfl
  | [], _ :: _, h, z => by simp at h
  | _ :: _, [], h, z => by simp at h
  | a :: l, x :: t, h, z => by
    simp only [List.length_cons] at h
    simp only [interleave, List.cons_append]
    rw [interleave_append_last (Nat.succ_injective h) z]

theorem interleave_cons_snoc : ∀ {a m : List ℕ}, a.length = m.length → ∀ x z : ℕ,
    x :: interleave (a ++ [z]) m = interleave (x :: m) (a ++ [z])
  | [], [], _, x, z => rfl
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | a :: l, y :: t, h, x, z => by
    simp only [List.length_cons] at h
    simp only [List.cons_append, interleave]
    rw [interleave_cons_snoc (Nat.succ_injective h) y z]

theorem interleave_rotate {a m : List ℕ} (h : a.length = m.length) (ha : a ≠ []) :
    (interleave a m).rotate 1 = interleave m (a.rotate 1) := by
  cases a with
  | nil => exact absurd rfl ha
  | cons a0 a' =>
  cases m with
  | nil => simp at h
  | cons m0 m' =>
    simp only [List.length_cons] at h
    have h' := Nat.succ_injective h
    simp only [interleave]
    rw [List.rotate_cons_succ, List.rotate_zero, List.rotate_cons_succ, List.rotate_zero]
    rw [List.cons_append, interleave_append_last h' a0]
    exact interleave_cons_snoc h' m0 a0

theorem interleave_head? : ∀ a m : List ℕ, (interleave a m).head? = a.head?
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: _, _ :: _ => rfl

theorem interleave_cons_left (b : ℕ) (l t : List ℕ) : ∃ R, interleave (b :: l) t = b :: R := by
  cases t with
  | nil => exact ⟨[], rfl⟩
  | cons c t' => exact ⟨c :: interleave l t', rfl⟩

/-- Every edge of the subdivided path meets the set of subdivision vertices. -/
theorem mem_snd_of_mem_pathEdges_interleave : ∀ (A M : List ℕ) (e : Sym2 ℕ),
    e ∈ pathEdges (interleave A M) → ∃ v ∈ e, v ∈ M
  | [], M, e, he => by simp [interleave] at he
  | a :: l, [], e, he => by simp [interleave] at he
  | a :: l, x :: t, e, he => by
    simp only [interleave] at he
    rw [pathEdges_cons₂] at he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact ⟨x, by simp, by simp⟩
    · cases l with
      | nil =>
        simp only [interleave] at he
        simp [pathEdges] at he
      | cons b l' =>
        obtain ⟨R, hR⟩ := interleave_cons_left b l' t
        rw [hR, pathEdges_cons₂] at he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact ⟨x, by simp, by simp⟩
        · rw [← hR] at he
          obtain ⟨v, hv, hvt⟩ := mem_snd_of_mem_pathEdges_interleave (b :: l') t e he
          exact ⟨v, hv, by simp [hvt]⟩

/-- Every edge of the subdivided path meets the set of original vertices. -/
theorem mem_fst_of_mem_pathEdges_interleave : ∀ (A M : List ℕ) (e : Sym2 ℕ),
    e ∈ pathEdges (interleave A M) → ∃ v ∈ e, v ∈ A
  | [], M, e, he => by simp [interleave] at he
  | a :: l, [], e, he => by simp [interleave] at he
  | a :: l, x :: t, e, he => by
    simp only [interleave] at he
    rw [pathEdges_cons₂] at he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact ⟨a, by simp, by simp⟩
    · cases l with
      | nil =>
        simp only [interleave] at he
        simp [pathEdges] at he
      | cons b l' =>
        obtain ⟨R, hR⟩ := interleave_cons_left b l' t
        rw [hR, pathEdges_cons₂] at he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact ⟨b, by simp, by simp⟩
        · rw [← hR] at he
          obtain ⟨v, hv, hvt⟩ := mem_fst_of_mem_pathEdges_interleave (b :: l') t e he
          exact ⟨v, hv, List.mem_cons_of_mem _ hvt⟩

/-! ### Every vertex of a path or cycle is used by one of its edges -/

theorem mem_supp_pathEdges : ∀ {l : List ℕ}, 2 ≤ l.length → ∀ v ∈ l, v ∈ supp (pathEdges l)
  | [], h, _, _ => by simp at h
  | [_], h, _, _ => by simp at h
  | a :: b :: t, _, v, hv => by
    rw [pathEdges_cons₂, supp_insert]
    rcases List.mem_cons.1 hv with rfl | hv'
    · simp
    · cases t with
      | nil =>
        have : v = b := by simpa using hv'
        subst this; simp
      | cons c t' =>
        exact Finset.mem_union_right _ (mem_supp_pathEdges (by simp) v hv')

theorem mem_supp_cycEdges {l : List ℕ} (h : 2 ≤ l.length) {v : ℕ} (hv : v ∈ l) :
    v ∈ supp (cycEdges l) := by
  cases l with
  | nil => simp at hv
  | cons a t =>
    rw [cycEdges_cons]
    refine mem_supp_pathEdges ?_ v ?_
    · simp only [List.length_cons, List.length_append]
      simp only [List.length_cons] at h
      omega
    · rcases List.mem_cons.1 hv with rfl | hv'
      · simp
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hv')

end BKLO
