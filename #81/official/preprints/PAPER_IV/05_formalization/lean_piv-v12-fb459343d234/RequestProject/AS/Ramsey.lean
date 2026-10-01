module

public import Mathlib
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

/-!
# A finite Ramsey theorem

Every graph on at least `4^l` vertices contains a clique or an independent set of size `l`.
This is used in the proof of Lemma 3.5 of Alon–Shapira.
-/

@[expose] public section

open Finset

namespace AlonShapira

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Erdős–Szekeres form of Ramsey's theorem: a set of `2^(a+b)` vertices contains a clique of size
`a` or an independent set of size `b`. -/
theorem ramsey_finset (n : ℕ) : ∀ a b, a + b = n → ∀ s : Finset V, 2 ^ (a + b) ≤ #s →
    (∃ t ⊆ s, #t = a ∧ (t : Set V).Pairwise G.Adj) ∨
      (∃ t ⊆ s, #t = b ∧ (t : Set V).Pairwise fun x y => ¬ G.Adj x y) := by
  induction n with
  | zero =>
    intro a b hab s _
    left
    exact ⟨∅, empty_subset _, by simp; omega, by simp⟩
  | succ n ih =>
    intro a b hab s hs
    rcases Nat.eq_zero_or_pos a with ha | ha
    · left; exact ⟨∅, empty_subset _, by simp [ha], by simp⟩
    rcases Nat.eq_zero_or_pos b with hb | hb
    · right; exact ⟨∅, empty_subset _, by simp [hb], by simp⟩
    obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have hsne : s.Nonempty := by
      rw [← Finset.card_pos]; exact lt_of_lt_of_le (Nat.two_pow_pos _) hs
    obtain ⟨v, hv⟩ := hsne
    set N := (s.erase v).filter (G.Adj v) with hN
    set M := (s.erase v).filter (fun w => ¬ G.Adj v w) with hM
    have hNM : #N + #M = #s - 1 := by
      rw [hN, hM, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]
    have hpow : 2 ^ (a + 1 + (b + 1)) = 2 * 2 ^ (a + b + 1) := by
      rw [show a + 1 + (b + 1) = (a + b + 1) + 1 by ring, pow_succ]; ring
    have hNs : N ⊆ s := fun x hx => Finset.mem_of_mem_erase (Finset.mem_filter.1 hx).1
    have hMs : M ⊆ s := fun x hx => Finset.mem_of_mem_erase (Finset.mem_filter.1 hx).1
    have hvN : v ∉ N := by simp [hN]
    have hvM : v ∉ M := by simp [hM]
    by_cases hbig : 2 ^ (a + b + 1) ≤ #N
    · rcases ih a (b + 1) (by omega) N (by rw [show a + (b + 1) = a + b + 1 by ring]; exact hbig)
        with ⟨t, ht, htc, htp⟩ | ⟨t, ht, htc, htp⟩
      · left
        refine ⟨insert v t, Finset.insert_subset hv (ht.trans hNs), ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem (fun h => hvN (ht h)), htc]
        · rw [Finset.coe_insert]
          refine Set.Pairwise.insert htp fun w hw _ => ?_
          have := (Finset.mem_filter.1 (ht hw)).2
          exact ⟨this, this.symm⟩
      · right; exact ⟨t, ht.trans hNs, htc, htp⟩
    · have hbig' : 2 ^ (a + b + 1) ≤ #M := by omega
      rcases ih (a + 1) b (by omega) M (by rw [show a + 1 + b = a + b + 1 by ring]; exact hbig')
        with ⟨t, ht, htc, htp⟩ | ⟨t, ht, htc, htp⟩
      · left; exact ⟨t, ht.trans hMs, htc, htp⟩
      · right
        refine ⟨insert v t, Finset.insert_subset hv (ht.trans hMs), ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem (fun h => hvM (ht h)), htc]
        · rw [Finset.coe_insert]
          refine Set.Pairwise.insert htp fun w hw _ => ?_
          have := (Finset.mem_filter.1 (ht hw)).2
          exact ⟨this, fun h => this h.symm⟩

/-- **Ramsey.** Every graph on `Fin k` with `k ≥ 4^l` contains `l` vertices that are pairwise
adjacent (`c = true`) or pairwise non-adjacent (`c = false`). -/
theorem ramsey_fin (l k : ℕ) (hk : 4 ^ l ≤ k) (H : SimpleGraph (Fin k)) [DecidableRel H.Adj] :
    ∃ (c : Bool) (g : Fin l ↪ Fin k), ∀ a b, a ≠ b → (H.Adj (g a) (g b) ↔ c = true) := by
  have h4 : 2 ^ (l + l) ≤ #(univ : Finset (Fin k)) := by
    rw [card_univ, Fintype.card_fin, ← two_mul, pow_mul]; norm_num; exact hk
  have key : ∃ (c : Bool) (t : Finset (Fin k)), #t = l ∧
      ∀ x ∈ t, ∀ y ∈ t, x ≠ y → (H.Adj x y ↔ c = true) := by
    rcases ramsey_finset H (l + l) l l rfl univ h4 with ⟨t, -, htc, htp⟩ | ⟨t, -, htc, htp⟩
    · exact ⟨true, t, htc, fun x hx y hy hxy => by simpa using htp hx hy hxy⟩
    · exact ⟨false, t, htc, fun x hx y hy hxy => by simpa using htp hx hy hxy⟩
  obtain ⟨c, t, htc, ht⟩ := key
  let e : Fin l ≃ t := (t.equivFinOfCardEq htc).symm
  refine ⟨c, ⟨fun i => (e i).1, fun i j hij => e.injective (Subtype.ext hij)⟩, fun a b hab => ?_⟩
  exact ht _ (e a).2 _ (e b).2 fun h => hab (e.injective (Subtype.ext h))

end AlonShapira
