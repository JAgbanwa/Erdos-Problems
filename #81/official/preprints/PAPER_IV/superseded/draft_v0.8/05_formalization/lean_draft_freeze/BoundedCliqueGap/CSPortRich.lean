import BoundedCliqueGap.CSPorts

/-
`BoundedCliqueGap.CSPortRich` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Rung C2 — the port-rich regime: integral saturation of `CS`

The clique-part edges of `CS K S` are partitioned into matchings by the
"sum" map on `ZMod k`: for `c : ZMod k`, the family of pairs `{a, b}` with
`a + b = c` is a matching, and every clique edge lies in exactly one of them.
Handing the matching `M c` to the independent vertex `c` therefore turns
*every* clique edge into a triangle, as soon as there are at least `k`
independent vertices:

  `nu3_CS_ge_choose : k ≤ s → C(k,2) ≤ ν₃(CS (Fin k) (Fin s))`.

Combined with the C1(a) ceiling `value ≤ C(k,2)` this shows that the packing
LP of `CS(k,s)` is **integral** for `s ≥ k`, and gives a gap of at most `k`
throughout the port-rich regime `s⌊k/2⌋ ≥ C(k,2)`.
-/

namespace BoundedCliqueGap

open Finset

/-! ## The sum matchings on `ZMod k` -/

namespace PortRich

variable (k : ℕ) [NeZero k]

open scoped Classical in
/-- `sumMatching k c` : the clique edges `{a, b}` of `ZMod k` with `a + b = c`. -/
noncomputable def sumMatching (c : ZMod k) : Finset (Finset (ZMod k)) :=
  univ.filter fun e => e.card = 2 ∧ ∑ x ∈ e, x = c

variable {k}

open scoped Classical in
lemma mem_sumMatching {c : ZMod k} {e : Finset (ZMod k)} :
    e ∈ sumMatching k c ↔ e.card = 2 ∧ ∑ x ∈ e, x = c := by
  simp [sumMatching]

omit [NeZero k] in
/-- A two-element set is determined by any one of its elements and its sum. -/
lemma eq_pair_of_sum {c x : ZMod k} {e : Finset (ZMod k)}
    (hcard : e.card = 2) (hsum : ∑ y ∈ e, y = c) (hx : x ∈ e) : e = {x, c - x} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hcard
  rw [Finset.sum_pair hab] at hsum
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · have : c - x = b := by rw [← hsum]; ring
    rw [this]
  · have : c - x = a := by rw [← hsum]; ring
    rw [this, Finset.pair_comm]

end PortRich

/-! ## Rung C2 -/

open PortRich in
open scoped Classical in
/-- The clique edges of `CS (ZMod k) (ZMod k)` are all saturated: every one of
them becomes a triangle with its own independent vertex. -/
theorem nu3_CS_zmod_ge (k : ℕ) [NeZero k] :
    k.choose 2 ≤ nu3 (CS (ZMod k) (ZMod k)) := by
  classical
  have key := nu3_CS_ge (K := ZMod k) (S := ZMod k) (sumMatching k) ∅
    (fun c e he => (mem_sumMatching.1 he).1)
    (by
      intro c e he e' he' hne
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact hne ((eq_pair_of_sum (mem_sumMatching.1 he).1 (mem_sumMatching.1 he).2 hx).trans
        (eq_pair_of_sum (mem_sumMatching.1 he').1 (mem_sumMatching.1 he').2 hx').symm))
    (by
      intro c c' e he he'
      rw [← (mem_sumMatching.1 he).2, ← (mem_sumMatching.1 he').2])
    ⟨by simp, by simp⟩
    (by simp)
  -- the matchings partition the two-element subsets
  have hpart : (univ.filter fun e : Finset (ZMod k) => e.card = 2).card
      = ∑ c : ZMod k, (sumMatching k c).card := by
    refine Finset.card_eq_sum_card_fiberwise (f := fun e : Finset (ZMod k) => ∑ x ∈ e, x)
      (t := univ) (fun e _ => Finset.mem_univ _) |>.trans ?_
    refine Finset.sum_congr rfl (fun c _ => congrArg Finset.card ?_)
    ext e
    simp [sumMatching]
  have hchoose : (univ.filter fun e : Finset (ZMod k) => e.card = 2).card = k.choose 2 := by
    have h1 : (univ.filter fun e : Finset (ZMod k) => e.card = 2)
        = Finset.powersetCard 2 (univ : Finset (ZMod k)) := by
      ext e
      simp [Finset.mem_powersetCard]
    rw [h1, Finset.card_powersetCard, Finset.card_univ, ZMod.card]
  rw [Finset.card_empty, Nat.add_zero] at key
  rw [← hpart, hchoose] at key
  exact key

/-- **Rung C2.**  If there are at least `k` independent vertices, every clique
edge of `CS (Fin k) (Fin s)` can be given its own port, so `ν₃ = C(k,2)`
saturates the C1(a) ceiling: the packing LP is integral. -/
theorem nu3_CS_ge_choose {k s : ℕ} (h : k ≤ s) :
    k.choose 2 ≤ nu3 (CS (Fin k) (Fin s)) := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  haveI : NeZero k := ⟨by omega⟩
  refine le_trans (nu3_CS_zmod_ge k) (nu3_CS_mono ?_ ?_)
  · exact (Fintype.equivFinOfCardEq (ZMod.card k)).toEmbedding
  · exact ((Fintype.equivFinOfCardEq (ZMod.card k)).toEmbedding).trans
      (Fin.castLEEmb h)

/-- `2·C(k,2) = k(k-1)` over `ℕ`. -/
lemma two_mul_choose_two (k : ℕ) : 2 * k.choose 2 = k * (k - 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.choose_two_right, Nat.add_sub_cancel]
    rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
    · subst ht
      have h : (t + t + 1) * (t + t) = 2 * ((t + t + 1) * t) := by ring
      rw [h, Nat.mul_div_cancel_left _ (by norm_num)]
    · subst ht
      have h : (2 * t + 1 + 1) * (2 * t + 1) = 2 * ((t + 1) * (2 * t + 1)) := by ring
      rw [h, Nat.mul_div_cancel_left _ (by norm_num)]

end BoundedCliqueGap
