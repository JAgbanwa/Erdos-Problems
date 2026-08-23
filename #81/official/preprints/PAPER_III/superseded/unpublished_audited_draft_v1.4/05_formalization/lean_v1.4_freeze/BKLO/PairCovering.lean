/-
# Averaging over subsets: how many marked pairs a random `k`-subset captures

This file develops the deterministic *subset averaging* step that underlies the sparse
pair-covering reservoirs discussed in `BOUNDED_LEFTOVER_STATUS.md`.

The situation is the following.  A vertex set `N` (in the application: the neighbourhood of a
prospective "hub" vertex) carries a set `U` of distinguished pairs — the pairs that still need to be
covered.  One wants to select a *small* subset `D ⊆ N` (the star that will actually be reserved at
the hub) capturing many of the distinguished pairs.  Averaging over all `k`-subsets of `N` gives the
optimal bound: some `k`-subset captures at least the expected number `|U| · k(k−1)/ν(ν−1)` of pairs,
where `ν = |N|`.  This is `BKLO.exists_subset_pairs_ge`, stated in a division-free form.

The two ingredients are elementary but useful in their own right:

* `BKLO.card_powersetCard_filter_pair`: exactly `(ν−2).choose (k−2)` of the `k`-subsets of `N`
  contain two prescribed distinct elements of `N`;
* `BKLO.choose_pair_identity`: `ν(ν−1)·(ν−2).choose (k−2) = k(k−1)·ν.choose k`.

Everything in this file is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic.Bound

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- Exactly `(|N| − 2).choose (k − 2)` of the `k`-element subsets of `N` contain both of two
prescribed distinct elements `x, y ∈ N`. -/
theorem card_powersetCard_filter_pair (N : Finset V) {x y : V} (hx : x ∈ N) (hy : y ∈ N)
    (hxy : x ≠ y) {k : ℕ} (hk : 2 ≤ k) :
    ((N.powersetCard k).filter (fun D => x ∈ D ∧ y ∈ D)).card = (N.card - 2).choose (k - 2) := by
  classical
  have hcard : ((N.erase x).erase y).card = N.card - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hxy, hy⟩),
      Finset.card_erase_of_mem hx]
    omega
  rw [← hcard, ← Finset.card_powersetCard]
  refine Finset.card_bij' (fun D _ => (D.erase x).erase y) (fun D' _ => insert x (insert y D'))
    ?_ ?_ ?_ ?_
  · intro D hD
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hD
    obtain ⟨⟨hDN, hDk⟩, hxD, hyD⟩ := hD
    simp only [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro a ha
      simp only [Finset.mem_erase] at ha ⊢
      exact ⟨ha.1, ha.2.1, hDN ha.2.2⟩
    · rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hxy, hyD⟩),
        Finset.card_erase_of_mem hxD, hDk]
      omega
  · intro D' hD'
    simp only [Finset.mem_powersetCard] at hD'
    obtain ⟨hsub, hc⟩ := hD'
    have hxD' : x ∉ D' := fun h => (Finset.mem_erase.1 (Finset.mem_erase.1 (hsub h)).2).1 rfl
    have hyD' : y ∉ D' := fun h => (Finset.mem_erase.1 (hsub h)).1 rfl
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self _ _,
      Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
    · intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact hx
      · rcases Finset.mem_insert.1 ha with rfl | ha
        · exact hy
        · exact (Finset.mem_erase.1 (Finset.mem_erase.1 (hsub ha)).2).2
    · rw [Finset.card_insert_of_notMem (by simp [hxy, hxD']),
        Finset.card_insert_of_notMem hyD', hc]
      omega
  · intro D hD
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hD
    obtain ⟨⟨hDN, hDk⟩, hxD, hyD⟩ := hD
    show insert x (insert y ((D.erase x).erase y)) = D
    rw [Finset.insert_erase (Finset.mem_erase.2 ⟨Ne.symm hxy, hyD⟩), Finset.insert_erase hxD]
  · intro D' hD'
    simp only [Finset.mem_powersetCard] at hD'
    have hxD' : x ∉ D' := fun h => (Finset.mem_erase.1 (Finset.mem_erase.1 (hD'.1 h)).2).1 rfl
    have hyD' : y ∉ D' := fun h => (Finset.mem_erase.1 (hD'.1 h)).1 rfl
    show ((insert x (insert y D')).erase x).erase y = D'
    rw [Finset.erase_insert (by simp [hxy, hxD']), Finset.erase_insert hyD']

/-- The pair-counting identity behind the averaging bound:
`ν(ν−1)·(ν−2).choose (k−2) = k(k−1)·ν.choose k` for `2 ≤ k ≤ ν`. -/
theorem choose_pair_identity {k v : ℕ} (hk : 2 ≤ k) (hkv : k ≤ v) :
    v * (v - 1) * ((v - 2).choose (k - 2)) = k * (k - 1) * (v.choose k) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v', v = v' + 2 := ⟨v - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 : (v + 2) * (v + 1) * (v.choose k) = (k + 2) * (k + 1) * ((v + 2).choose (k + 2)) := by
    have e1 := Nat.add_one_mul_choose_eq (v + 1) (k + 1)
    have e2 := Nat.add_one_mul_choose_eq v k
    simp at e1 e2 ⊢
    nlinarith only [e1, e2]
  simpa using h1

/-- **Double counting the marked pairs inside `k`-subsets.**  If every pair in `U` is a
non-degenerate pair of elements of `N`, then summing, over all `k`-subsets `D` of `N`, the number of
pairs of `U` inside `D` gives `|U| · (|N| − 2).choose (k − 2)`. -/
theorem sum_card_pairs_in_powersetCard (N : Finset V) (U : Finset (Sym2 V)) {k : ℕ} (hk : 2 ≤ k)
    (hU : ∀ e ∈ U, ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ N) :
    ∑ D ∈ N.powersetCard k, (U.filter (fun e : Sym2 V => e.toFinset ⊆ D)).card
      = U.card * ((N.card - 2).choose (k - 2)) := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm, Finset.card_eq_sum_ones U, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro e he
  obtain ⟨hnd, hmem⟩ := hU e he
  induction e using Sym2.ind with
  | _ x y =>
    have hxy : x ≠ y := by simpa [Sym2.isDiag_iff_proj_eq] using hnd
    have hx : x ∈ N := hmem x (by simp)
    have hy : y ∈ N := hmem y (by simp)
    have hiff : ∀ D : Finset V, (s(x, y) : Sym2 V).toFinset ⊆ D ↔ (x ∈ D ∧ y ∈ D) := by
      intro D
      constructor
      · intro h
        exact ⟨h (by simp [Sym2.mem_toFinset]), h (by simp [Sym2.mem_toFinset])⟩
      · intro h a ha
        rw [Sym2.mem_toFinset] at ha
        rcases Sym2.mem_iff.1 ha with rfl | rfl
        · exact h.1
        · exact h.2
    calc ∑ D ∈ N.powersetCard k, (if (s(x, y) : Sym2 V).toFinset ⊆ D then 1 else 0)
        = ((N.powersetCard k).filter (fun D => x ∈ D ∧ y ∈ D)).card := by
          rw [Finset.card_filter]
          exact Finset.sum_congr rfl (fun D _ => by simp [hiff D])
      _ = (N.card - 2).choose (k - 2) := card_powersetCard_filter_pair N hx hy hxy hk
      _ = 1 * ((N.card - 2).choose (k - 2)) := by ring

/-- **Subset averaging.**  Let `U` be a set of non-degenerate pairs inside a vertex set `N`, and let
`2 ≤ k ≤ |N|`.  Then some `k`-element subset `D ⊆ N` contains at least the average number of pairs
of `U`, i.e. `|U| · k(k−1) ≤ |{e ∈ U : e ⊆ D}| · |N|(|N|−1)`.

This is the deterministic replacement for "pick a random `k`-subset": it produces, in one step, a
star of prescribed size at a hub which captures a positive proportion `k(k−1)/|N|(|N|−1)` of the
pairs still to be covered. -/
theorem exists_subset_pairs_ge (N : Finset V) (U : Finset (Sym2 V)) {k : ℕ} (hk : 2 ≤ k)
    (hkN : k ≤ N.card) (hU : ∀ e ∈ U, ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ N) :
    ∃ D ∈ N.powersetCard k,
      U.card * (k * (k - 1))
        ≤ (U.filter (fun e : Sym2 V => e.toFinset ⊆ D)).card * (N.card * (N.card - 1)) := by
  classical
  have key := sum_card_pairs_in_powersetCard N U hk hU
  have hne : (N.powersetCard k).Nonempty := by
    rw [Finset.powersetCard_nonempty]; exact hkN
  obtain ⟨D, hD, hmax⟩ := Finset.exists_max_image (N.powersetCard k)
    (fun D : Finset V => (U.filter (fun e : Sym2 V => e.toFinset ⊆ D)).card) hne
  refine ⟨D, hD, ?_⟩
  have hsum : U.card * ((N.card - 2).choose (k - 2))
      ≤ (N.card.choose k) * (U.filter (fun e : Sym2 V => e.toFinset ⊆ D)).card := by
    rw [← key, ← Finset.card_powersetCard k N]
    exact Finset.sum_le_card_nsmul _ _ _ (fun D' hD' => hmax D' hD')
  have hpos : 0 < N.card.choose k := Nat.choose_pos hkN
  have h2 : (N.card.choose k) * (U.card * (k * (k - 1)))
      ≤ (N.card.choose k) *
          ((U.filter (fun e : Sym2 V => e.toFinset ⊆ D)).card * (N.card * (N.card - 1))) := by
    calc (N.card.choose k) * (U.card * (k * (k - 1)))
        = U.card * (k * (k - 1) * (N.card.choose k)) := by ring
      _ = U.card * (N.card * (N.card - 1) * ((N.card - 2).choose (k - 2))) := by
            rw [choose_pair_identity hk hkN]
      _ = (N.card * (N.card - 1)) * (U.card * ((N.card - 2).choose (k - 2))) := by ring
      _ ≤ (N.card * (N.card - 1)) *
            ((N.card.choose k) * (U.filter (fun e : Sym2 V => e.toFinset ⊆ D)).card) :=
            Nat.mul_le_mul_left _ hsum
      _ = (N.card.choose k) *
            ((U.filter (fun e : Sym2 V => e.toFinset ⊆ D)).card * (N.card * (N.card - 1))) := by
            ring
  exact Nat.le_of_mul_le_mul_left h2 hpos

/-! ### Choosing a hub -/

/-- **Hub averaging.**  If every pair `e` of `U` can be covered by at least `a` of the candidate
hubs in `Z`, then some single hub `z ∈ Z` covers at least the average fraction `a/|Z|` of the pairs
of `U`. -/
theorem exists_hub_covering_many (Z : Finset V) (U : Finset (Sym2 V)) (C : Sym2 V → Finset V)
    (a : ℕ) (hZ : Z.Nonempty) (hC : ∀ e ∈ U, C e ⊆ Z) (hsize : ∀ e ∈ U, a ≤ (C e).card) :
    ∃ z ∈ Z, U.card * a ≤ (U.filter (fun e => z ∈ C e)).card * Z.card := by
  classical
  have key : ∑ z ∈ Z, (U.filter (fun e => z ∈ C e)).card = ∑ e ∈ U, (C e).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e he => ?_
    have h1 : ∑ z ∈ Z, (if z ∈ C e then 1 else 0) = (Z.filter (fun z => z ∈ C e)).card :=
      (Finset.card_filter _ _).symm
    rw [h1, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (hC e he)]
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image Z
    (fun z : V => (U.filter (fun e : Sym2 V => z ∈ C e)).card) hZ
  refine ⟨z, hz, ?_⟩
  calc U.card * a ≤ ∑ e ∈ U, (C e).card := by
        rw [Finset.card_eq_sum_ones U, Finset.sum_mul]
        exact Finset.sum_le_sum fun e he => by simpa using hsize e he
    _ = ∑ z' ∈ Z, (U.filter (fun e => z' ∈ C e)).card := key.symm
    _ ≤ Z.card * (U.filter (fun e => z ∈ C e)).card := by
        simpa using Finset.sum_le_card_nsmul Z _ _ (fun z' hz' => hmax z' hz')
    _ = (U.filter (fun e => z ∈ C e)).card * Z.card := by ring

/-- **One greedy step of a sparse pair-covering reservoir.**  Suppose every pair `e` still to be
covered has at least `a` admissible hubs `C e ⊆ Z`, and that a hub `z ∈ C e` sees both endpoints of
`e` (they lie in `nbhd z`).  Then there is a hub `z` and a star `D ⊆ nbhd z` of the prescribed size
`k` which captures at least the expected fraction
`(a/|Z|) · (k(k−1)/|nbhd z|(|nbhd z|−1))` of the pairs of `U`.

The conclusion is stated multiplicatively so that no division or real arithmetic is involved.  This
is the deterministic substitute for choosing a random hub and a random star at it: reserving the
star `{z} × D` costs degree `k` at `z` and degree `1` at each vertex of `D`, and it covers every
pair inside `D`. -/
theorem exists_hub_star_capturing (Z : Finset V) (U : Finset (Sym2 V)) (C : Sym2 V → Finset V)
    (nbhd : V → Finset V) (a : ℕ) {k : ℕ} (hk : 2 ≤ k) (hZ : Z.Nonempty)
    (hC : ∀ e ∈ U, C e ⊆ Z) (hsize : ∀ e ∈ U, a ≤ (C e).card) (hnd : ∀ e ∈ U, ¬ e.IsDiag)
    (hmem : ∀ e ∈ U, ∀ z ∈ C e, ∀ v ∈ e, v ∈ nbhd z)
    (hkN : ∀ z ∈ Z, k ≤ (nbhd z).card) :
    ∃ z ∈ Z, ∃ D ∈ (nbhd z).powersetCard k,
      U.card * (a * (k * (k - 1))) ≤ (U.filter (fun e : Sym2 V => e.toFinset ⊆ D)).card *
        (Z.card * ((nbhd z).card * ((nbhd z).card - 1))) := by
  classical
  obtain ⟨z, hz, hzbound⟩ := exists_hub_covering_many Z U C a hZ hC hsize
  set Uz := U.filter (fun e => z ∈ C e) with hUz
  have hUzprop : ∀ e ∈ Uz, ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ nbhd z := by
    intro e he
    rw [hUz, Finset.mem_filter] at he
    exact ⟨hnd e he.1, fun v hv => hmem e he.1 z he.2 v hv⟩
  obtain ⟨D, hD, hDbound⟩ := exists_subset_pairs_ge (nbhd z) Uz hk (hkN z hz) hUzprop
  refine ⟨z, hz, D, hD, ?_⟩
  have hmono : (Uz.filter (fun e : Sym2 V => e.toFinset ⊆ D)).card
      ≤ (U.filter (fun e : Sym2 V => e.toFinset ⊆ D)).card := by
    apply Finset.card_le_card
    intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨(Finset.mem_filter.1 (hUz ▸ he.1)).1, he.2⟩
  calc U.card * (a * (k * (k - 1))) = (U.card * a) * (k * (k - 1)) := by ring
    _ ≤ (Uz.card * Z.card) * (k * (k - 1)) := Nat.mul_le_mul_right _ hzbound
    _ = (Uz.card * (k * (k - 1))) * Z.card := by ring
    _ ≤ ((Uz.filter (fun e : Sym2 V => e.toFinset ⊆ D)).card *
          ((nbhd z).card * ((nbhd z).card - 1))) * Z.card := Nat.mul_le_mul_right _ hDbound
    _ ≤ ((U.filter (fun e : Sym2 V => e.toFinset ⊆ D)).card *
          ((nbhd z).card * ((nbhd z).card - 1))) * Z.card :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hmono)
    _ = (U.filter (fun e : Sym2 V => e.toFinset ⊆ D)).card *
          (Z.card * ((nbhd z).card * ((nbhd z).card - 1))) := by ring

end BKLO
