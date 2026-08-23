import Mathlib

/-!
# A duplicate-free (simple) chain from a reflexive-transitive-closure path

This file proves, with no extra typeclass assumptions, that from a
`Relation.ReflTransGen R s t` path between two distinct points one can extract a
`List.IsChain R` list from `s` to `t` that is duplicate-free (`Nodup`).

The proof is fully general (no `DecidableEq`/`Fintype`), classical only (uses
`Classical`/`propext`/`Quot.sound`), and `sorry`-free.
-/

namespace Ax2.NodupChain

open List

/-- If `x` occurs at least twice in `l`, split `l` around the two occurrences. -/
private theorem dup_decomp {α : Type*} {x : α} {l : List α}
    (h : List.Duplicate x l) : ∃ A B C, l = A ++ x :: (B ++ x :: C) := by
  induction h with
  | @cons_mem l hx =>
      obtain ⟨B, C, rfl⟩ := List.append_of_mem hx
      exact ⟨[], B, C, rfl⟩
  | @cons_duplicate y l hd ih =>
      obtain ⟨A, B, C, rfl⟩ := ih
      exact ⟨y :: A, B, C, rfl⟩

/-- Splicing out the loop between two occurrences of `x` preserves the chain property. -/
private theorem chain_splice {α : Type*} {R : α → α → Prop} {x : α} {A B C : List α}
    (h : List.IsChain R (A ++ x :: (B ++ x :: C))) : List.IsChain R (A ++ x :: C) := by
  rw [isChain_split] at h ⊢
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  rw [← cons_append, isChain_split] at h2
  exact h2.2

/-- Core strong-induction lemma: any nonempty chain list has a `Nodup` chain sublist with the
same first and last elements. -/
private theorem core {α : Type*} {R : α → α → Prop} :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → l ≠ [] → l.IsChain R →
      ∃ l', l' ≠ [] ∧ l'.IsChain R ∧ l'.head? = l.head? ∧ l'.getLast? = l.getLast? ∧ l'.Nodup := by
  intro n
  induction n with
  | zero =>
      intro l hlen hne _
      exact absurd (List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)) hne
  | succ n ih =>
      intro l hlen hne hchain
      by_cases hnd : l.Nodup
      · exact ⟨l, hne, hchain, rfl, rfl, hnd⟩
      · obtain ⟨x, hx⟩ := (exists_duplicate_iff_not_nodup).mpr hnd
        obtain ⟨A, B, C, rfl⟩ := dup_decomp hx
        -- The spliced list `A ++ x :: C`.
        have hchain' : List.IsChain R (A ++ x :: C) := chain_splice hchain
        have hne' : (A ++ x :: C) ≠ [] := by cases A <;> simp
        -- head? is preserved.
        have hhead : (A ++ x :: C).head? = (A ++ x :: (B ++ x :: C)).head? := by
          cases A <;> rfl
        -- getLast? is preserved: both equal `getLast? (x :: C)`.
        have hlast : (A ++ x :: C).getLast? = (A ++ x :: (B ++ x :: C)).getLast? := by
          have e1 : (A ++ x :: C).getLast? = (x :: C).getLast? := getLast?_append_cons A x C
          have e2 : (A ++ x :: (B ++ x :: C)).getLast? = (x :: C).getLast? := by
            rw [getLast?_append_cons]
            rw [show (x :: (B ++ x :: C)) = (x :: B) ++ x :: C from by rw [cons_append]]
            rw [getLast?_append_cons]
          rw [e1, e2]
        -- length strictly decreased, so ≤ n.
        have hlen' : (A ++ x :: C).length ≤ n := by
          simp only [List.length_append, List.length_cons] at hlen ⊢
          omega
        obtain ⟨l', hl'ne, hl'chain, hl'head, hl'last, hl'nodup⟩ := ih _ hlen' hne' hchain'
        exact ⟨l', hl'ne, hl'chain, hl'head.trans hhead, hl'last.trans hlast, hl'nodup⟩

/-- From a reflexive-transitive-closure path between two DISTINCT points, extract a simple
(duplicate-free) chain list from `s` to `t`. -/
theorem exists_nodup_chain {α : Type*} {R : α → α → Prop} {s t : α}
    (h : Relation.ReflTransGen R s t) (hst : s ≠ t) :
    ∃ l : List α, l.IsChain R ∧ l.head? = some s ∧ l.getLast? = some t ∧ l.Nodup := by
  obtain ⟨l, hlne, hlchain, hlhead, hllast⟩ :=
    List.exists_isChain_ne_nil_of_relationReflTransGen h
  obtain ⟨l', _, hl'chain, hl'head, hl'last, hl'nodup⟩ :=
    core l.length l le_rfl hlne hlchain
  refine ⟨l', hl'chain, ?_, ?_, hl'nodup⟩
  · rw [hl'head, List.head?_eq_some_head hlne, hlhead]
  · rw [hl'last, List.getLast?_eq_some_getLast hlne, hllast]

end Ax2.NodupChain
