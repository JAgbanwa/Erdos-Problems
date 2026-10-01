import Mathlib

/-!
# Exact fibre counting for injections of slots into candidates

The RD09-L2 averaging step averages over the injections of a fixed finite set of
*slots* into the finite set of exterior *candidates*.  Only two counting facts about
that family are needed, and both are proved here in cross-multiplied integral form,
so that no division and no probability library appears anywhere:

* `card_mul_card_filter_apply_mem`: for one slot `u` and a set `S` of candidates,
  `q * #{ι : α ↪ β | ι u ∈ S} = #S * #(α ↪ β)`, where `q = #β`.  This is the exact
  first moment `P(ι u ∈ S) = #S / q`;
* `card_mul_pred_mul_card_filter_pair_le`: for two distinct slots `u ≠ v`,
  `q * (q - 1) * #{ι | ι u ∈ S ∧ ι v ∈ S} ≤ #S ^ 2 * #(α ↪ β)`.  This is the exact
  second moment `P(ι u ∈ S ∧ ι v ∈ S) = #S (#S - 1) / (q (q-1))`, relaxed to `#S ^ 2`.

Both follow from the same mechanism: the fibres of `ι ↦ ι u` (respectively of
`ι ↦ (ι u, ι v)` over ordered pairs of *distinct* candidates) all have the same
cardinality, because composing an injection with a permutation of the candidates is a
bijection of the family onto itself.
-/

namespace PaperIV.RD09CandidateCounting

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

/-! ## Transporting an injection by a permutation of the candidates -/

/-- Composing with a permutation `g` of the candidates is a bijection from the fibre of
`ι ↦ ι u` over `c` onto the fibre over `g c`. -/
theorem card_filter_apply_eq_perm (g : Equiv.Perm β) (u : α) (c : β) :
    (univ.filter fun ι : α ↪ β => ι u = c).card
      = (univ.filter fun ι : α ↪ β => ι u = g c).card := by
  classical
  refine Finset.card_nbij' (fun ι => ι.trans g.toEmbedding)
    (fun ι => ι.trans g.symm.toEmbedding) ?_ ?_ ?_ ?_
  · intro ι hι
    have h : ι u = c := by simpa using hι
    simp [h]
  · intro ι hι
    have h : ι u = g c := by simpa using hι
    simp [h]
  · intro ι _; ext x; simp
  · intro ι _; ext x; simp

/-- All fibres of `ι ↦ ι u` have the same cardinality. -/
theorem card_filter_apply_eq (u : α) (c c' : β) :
    (univ.filter fun ι : α ↪ β => ι u = c).card
      = (univ.filter fun ι : α ↪ β => ι u = c').card := by
  classical
  rw [card_filter_apply_eq_perm (Equiv.swap c c') u c, Equiv.swap_apply_left]

/-- The fibres of `ι ↦ ι u` partition the family of injections. -/
theorem sum_card_filter_apply (u : α) :
    (∑ c : β, (univ.filter fun ι : α ↪ β => ι u = c).card) = Fintype.card (α ↪ β) := by
  classical
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun ι : α ↪ β => ι u) (fun x _ => mem_univ _)]
  simp

/-- **The exact first moment.**  For one slot `u` and a candidate set `S`,
`q * #{ι | ι u ∈ S} = #S * #(α ↪ β)`, with `q = #β`.  Cross-multiplied, so no division
and no nonemptiness hypothesis is needed. -/
theorem card_mul_card_filter_apply_mem (u : α) (S : Finset β) :
    Fintype.card β * (univ.filter fun ι : α ↪ β => ι u ∈ S).card
      = S.card * Fintype.card (α ↪ β) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨c₀, hc₀⟩
  · simp
  set N := (univ.filter fun ι : α ↪ β => ι u = c₀).card with hN
  have hfib : ∀ c ∈ S,
      ((univ.filter fun ι : α ↪ β => ι u ∈ S).filter fun ι => ι u = c).card = N := by
    intro c hc
    rw [hN, card_filter_apply_eq u c₀ c]
    congr 1
    ext ι
    simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    rintro rfl
    exact hc
  have key := Finset.card_eq_sum_card_fiberwise
      (s := univ.filter fun ι : α ↪ β => ι u ∈ S) (t := S) (f := fun ι : α ↪ β => ι u)
      (fun x hx => (mem_filter.mp hx).2)
  have h1 : (univ.filter fun ι : α ↪ β => ι u ∈ S).card = S.card * N := by
    rw [key, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  have h2 : Fintype.card β * N = Fintype.card (α ↪ β) := by
    rw [← sum_card_filter_apply (β := β) u,
      Finset.sum_congr rfl (fun c _ => card_filter_apply_eq u c c₀)]
    simp [hN, Finset.card_univ, mul_comm]
  rw [h1, ← h2]; ring

/-! ## Pairs of distinct slots -/

/-- Composing with a permutation `g` is a bijection between the fibre of
`ι ↦ (ι u, ι v)` over `(c, d)` and the fibre over `(g c, g d)`. -/
theorem card_filter_pair_eq_perm (g : Equiv.Perm β) (u v : α) (c d : β) :
    (univ.filter fun ι : α ↪ β => ι u = c ∧ ι v = d).card
      = (univ.filter fun ι : α ↪ β => ι u = g c ∧ ι v = g d).card := by
  classical
  refine Finset.card_nbij' (fun ι => ι.trans g.toEmbedding)
    (fun ι => ι.trans g.symm.toEmbedding) ?_ ?_ ?_ ?_
  · intro ι hι
    have h : ι u = c ∧ ι v = d := by simpa using hι
    simp [h.1, h.2]
  · intro ι hι
    have h : ι u = g c ∧ ι v = g d := by simpa using hι
    simp [h.1, h.2]
  · intro ι _; ext x; simp
  · intro ι _; ext x; simp

/-- A permutation of the candidates carrying an ordered pair of distinct candidates to
any other ordered pair of distinct candidates. -/
noncomputable def transfer (c d c' d' : β) : Equiv.Perm β :=
  (Equiv.swap c c').trans (Equiv.swap ((Equiv.swap c c') d) d')

omit [Fintype β] in
theorem transfer_apply_left {c d c' d' : β} (hcd : c ≠ d) (hcd' : c' ≠ d') :
    transfer c d c' d' c = c' := by
  classical
  show Equiv.swap ((Equiv.swap c c') d) d' ((Equiv.swap c c') c) = c'
  rw [Equiv.swap_apply_left]
  have h1 : (Equiv.swap c c') d ≠ c' := by
    intro h
    exact hcd ((Equiv.swap c c').injective (h.trans (Equiv.swap_apply_left c c').symm)).symm
  exact Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) hcd'

omit [Fintype β] in
theorem transfer_apply_right (c d c' d' : β) : transfer c d c' d' d = d' := by
  classical
  show Equiv.swap ((Equiv.swap c c') d) d' ((Equiv.swap c c') d) = d'
  exact Equiv.swap_apply_left _ _

/-- All fibres of `ι ↦ (ι u, ι v)` over ordered pairs of *distinct* candidates have the
same cardinality. -/
theorem card_filter_pair_eq (u v : α) {c d c' d' : β} (hcd : c ≠ d) (hcd' : c' ≠ d') :
    (univ.filter fun ι : α ↪ β => ι u = c ∧ ι v = d).card
      = (univ.filter fun ι : α ↪ β => ι u = c' ∧ ι v = d').card := by
  rw [card_filter_pair_eq_perm (transfer c d c' d') u v c d,
    transfer_apply_left hcd hcd', transfer_apply_right]

/-- For distinct slots the pair fibres over the off-diagonal partition the family. -/
theorem sum_card_filter_pair (u v : α) (huv : u ≠ v) :
    (∑ cd ∈ (univ : Finset β).offDiag,
        (univ.filter fun ι : α ↪ β => ι u = cd.1 ∧ ι v = cd.2).card)
      = Fintype.card (α ↪ β) := by
  classical
  have key := Finset.card_eq_sum_card_fiberwise
      (s := (univ : Finset (α ↪ β))) (t := (univ : Finset β).offDiag)
      (f := fun ι : α ↪ β => (ι u, ι v))
      (fun ι _ => Finset.mem_offDiag.mpr ⟨mem_univ _, mem_univ _, fun h => huv (ι.injective h)⟩)
  rw [Finset.card_univ] at key
  rw [key]
  refine Finset.sum_congr rfl fun cd _ => ?_
  congr 1
  ext ι
  simp [Prod.ext_iff]

/-- The injections putting both distinct slots `u`, `v` into `S`, decomposed over the
ordered pairs of distinct elements of `S`. -/
theorem card_filter_both_mem (u v : α) (huv : u ≠ v) (S : Finset β) :
    (univ.filter fun ι : α ↪ β => ι u ∈ S ∧ ι v ∈ S).card
      = ∑ cd ∈ S.offDiag, (univ.filter fun ι : α ↪ β => ι u = cd.1 ∧ ι v = cd.2).card := by
  classical
  have key := Finset.card_eq_sum_card_fiberwise
      (s := univ.filter fun ι : α ↪ β => ι u ∈ S ∧ ι v ∈ S) (t := S.offDiag)
      (f := fun ι : α ↪ β => (ι u, ι v)) (fun ι hι => by
        obtain ⟨h1, h2⟩ := (mem_filter.mp hι).2
        exact Finset.mem_offDiag.mpr ⟨h1, h2, fun h => huv (ι.injective h)⟩)
  rw [key]
  refine Finset.sum_congr rfl fun cd hcd => ?_
  obtain ⟨hc, hd, -⟩ := Finset.mem_offDiag.mp hcd
  congr 1
  ext ι
  simp only [mem_filter, mem_univ, true_and, Prod.ext_iff]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1 ▸ hc, h2 ▸ hd⟩, h1, h2⟩

/-- **The exact second moment, relaxed.**  For two distinct slots `u ≠ v` and a candidate
set `S`, `q * (q - 1) * #{ι | ι u ∈ S ∧ ι v ∈ S} ≤ #S ^ 2 * #(α ↪ β)`, with `q = #β`.
The exact count has `#S * (#S - 1)` in place of `#S ^ 2`. -/
theorem card_mul_pred_mul_card_filter_pair_le (u v : α) (huv : u ≠ v) (S : Finset β) :
    Fintype.card β * (Fintype.card β - 1)
        * (univ.filter fun ι : α ↪ β => ι u ∈ S ∧ ι v ∈ S).card
      ≤ S.card ^ 2 * Fintype.card (α ↪ β) := by
  classical
  rcases S.offDiag.eq_empty_or_nonempty with hemp | ⟨cd₀, hcd₀⟩
  · rw [card_filter_both_mem u v huv S, hemp]
    simp
  obtain ⟨-, -, hne₀⟩ := Finset.mem_offDiag.mp hcd₀
  set N := (univ.filter fun ι : α ↪ β => ι u = cd₀.1 ∧ ι v = cd₀.2).card with hN
  have hS : (univ.filter fun ι : α ↪ β => ι u ∈ S ∧ ι v ∈ S).card = S.offDiag.card * N := by
    rw [card_filter_both_mem u v huv S]
    rw [Finset.sum_congr rfl (fun cd hcd => ?_), Finset.sum_const, smul_eq_mul]
    obtain ⟨-, -, hne⟩ := Finset.mem_offDiag.mp hcd
    rw [hN]
    exact card_filter_pair_eq u v hne hne₀
  have huniv : (Fintype.card β * Fintype.card β - Fintype.card β) * N
      = Fintype.card (α ↪ β) := by
    rw [← sum_card_filter_pair (β := β) u v huv]
    rw [Finset.sum_congr rfl (fun cd hcd => ?_), Finset.sum_const, smul_eq_mul,
      Finset.offDiag_card, Finset.card_univ]
    · obtain ⟨-, -, hne⟩ := Finset.mem_offDiag.mp hcd
      rw [hN]
      exact card_filter_pair_eq u v hne hne₀
  have hq : Fintype.card β * (Fintype.card β - 1)
      = Fintype.card β * Fintype.card β - Fintype.card β := by
    cases Fintype.card β with
    | zero => simp
    | succ m => simp [Nat.succ_sub_one, Nat.mul_succ]
  have hoff : S.offDiag.card ≤ S.card ^ 2 := by
    rw [Finset.offDiag_card, sq]
    exact Nat.sub_le _ _
  calc Fintype.card β * (Fintype.card β - 1)
        * (univ.filter fun ι : α ↪ β => ι u ∈ S ∧ ι v ∈ S).card
      = S.offDiag.card * ((Fintype.card β * Fintype.card β - Fintype.card β) * N) := by
        rw [hS, hq]; ring
    _ = S.offDiag.card * Fintype.card (α ↪ β) := by rw [huniv]
    _ ≤ S.card ^ 2 * Fintype.card (α ↪ β) := Nat.mul_le_mul_right _ hoff

/-! ## Nonemptiness of the family of injections -/

omit [DecidableEq β] in
/-- If there are at least as many candidates as slots, the family of injections is
nonempty, so averaging over it is legitimate. -/
theorem card_embedding_pos (h : Fintype.card α ≤ Fintype.card β) :
    0 < Fintype.card (α ↪ β) := by
  classical
  rw [Fintype.card_pos_iff]
  exact Function.Embedding.nonempty_of_card_le h

end PaperIV.RD09CandidateCounting


