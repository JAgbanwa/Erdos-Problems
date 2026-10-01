import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Galvin's theorem for complete bipartite graphs, proved from scratch

This module is self-contained over Mathlib.  It proves the list edge-colouring theorem
of Galvin for a complete bipartite graph `K_{R,C}` (the rectangular Dinitz problem): if
every edge has a list of at least `q` colours, where `|R|, |C| ≤ q`, the edges can be
coloured from their lists so that edges sharing an endpoint get distinct colours.

No external theorem is used.  The three steps are the classical ones.

* `kernel_list_colouring` (Bondy–Boppana–Siegel): in a digraph all of whose finite vertex
  sets have a kernel, lists longer than the out-degrees suffice.
* `exists_gridKernel` (stable matchings): the cells of a grid, oriented towards higher
  rank inside a row and towards lower rank inside a column, have a kernel in every subset.
  The proof is an induction on the number of cells: either the row-favourites lie in
  distinct columns (and are a kernel), or two of them share a column and the worse one
  may be deleted.
* `latin rank`: the rank `(i + j) mod q` is injective in rows and columns, and gives
  out-degree at most `q - 1`.
-/

namespace PaperIV.GalvinRect

open Finset

/-! ## 1. The kernel lemma -/

section Kernel

variable {X : Type*} [DecidableEq X] (arc : X → X → Prop) [DecidableRel arc]

/-- `K` is a kernel of `S`: an independent subset absorbing every other vertex of `S`. -/
def IsKernel (S K : Finset X) : Prop :=
  K ⊆ S ∧ (∀ k ∈ K, ∀ k' ∈ K, ¬ arc k k') ∧ ∀ s ∈ S, s ∉ K → ∃ k ∈ K, arc s k

/-- **Kernel lemma.**  If every finite set has a kernel and every list is longer than the
out-degree inside `S`, then `S` is list-colourable with arcs joining distinct colours. -/
theorem kernel_list_colouring {Col : Type*} [DecidableEq Col] [Nonempty Col]
    (hker : ∀ S : Finset X, ∃ K, IsKernel arc S K) :
    ∀ (S : Finset X) (L : X → Finset Col), (∀ s ∈ S, (S.filter (arc s)).card < (L s).card) →
      ∃ f : X → Col, (∀ s ∈ S, f s ∈ L s) ∧ ∀ s ∈ S, ∀ k ∈ S, arc s k → f s ≠ f k := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  intro L hL
  rcases S.eq_empty_or_nonempty with rfl | ⟨s0, hs0⟩
  · exact ⟨fun _ => Classical.arbitrary Col, by simp, by simp⟩
  have hL0 : (L s0).Nonempty := card_pos.1 (lt_of_le_of_lt (Nat.zero_le _) (hL s0 hs0))
  obtain ⟨γ, hγ⟩ := hL0
  obtain ⟨K, hKsub, hKind, hKdom⟩ := hker (S.filter (fun s => γ ∈ L s))
  have hKS : K ⊆ S := hKsub.trans (filter_subset _ _)
  have hKne : K.Nonempty := by
    by_cases h : s0 ∈ K
    · exact ⟨s0, h⟩
    · obtain ⟨k, hk, -⟩ := hKdom s0 (mem_filter.2 ⟨hs0, hγ⟩) h
      exact ⟨k, hk⟩
  have hS'lt : S \ K ⊂ S := sdiff_ssubset hKS hKne
  have hL' : ∀ s ∈ S \ K, ((S \ K).filter (arc s)).card < ((L s).erase γ).card := by
    intro s hs
    obtain ⟨hsS, hsK⟩ := mem_sdiff.1 hs
    by_cases hγs : γ ∈ L s
    · obtain ⟨k, hkK, hsk⟩ := hKdom s (mem_filter.2 ⟨hsS, hγs⟩) hsK
      have hsub : (S \ K).filter (arc s) ⊂ S.filter (arc s) := by
        refine ⟨filter_subset_filter _ sdiff_subset, fun h => ?_⟩
        have : k ∈ (S \ K).filter (arc s) := h (mem_filter.2 ⟨hKS hkK, hsk⟩)
        exact (mem_sdiff.1 (mem_filter.1 this).1).2 hkK
      have h1 := card_lt_card hsub
      have h2 := hL s hsS
      rw [card_erase_of_mem hγs]
      omega
    · rw [erase_eq_of_notMem hγs]
      exact lt_of_le_of_lt (card_le_card (filter_subset_filter _ sdiff_subset)) (hL s hsS)
  obtain ⟨f', hf'L, hf'p⟩ := ih (S \ K) hS'lt (fun s => (L s).erase γ) hL'
  refine ⟨fun s => if s ∈ K then γ else f' s, ?_, ?_⟩
  · intro s hs
    by_cases hsK : s ∈ K
    · simp only [hsK, if_true]
      exact (mem_filter.1 (hKsub hsK)).2
    · simp only [hsK, if_false]
      exact mem_of_mem_erase (hf'L s (mem_sdiff.2 ⟨hs, hsK⟩))
  · intro s hs k hk hsk
    by_cases hsK : s ∈ K <;> by_cases hkK : k ∈ K <;> simp only [hsK, hkK, if_true, if_false]
    · exact absurd hsk (hKind s hsK k hkK)
    · intro h
      exact (ne_of_mem_erase (hf'L k (mem_sdiff.2 ⟨hk, hkK⟩))) h.symm
    · intro h
      exact (ne_of_mem_erase (hf'L s (mem_sdiff.2 ⟨hs, hsK⟩))) h
    · exact hf'p s (mem_sdiff.2 ⟨hs, hsK⟩) k (mem_sdiff.2 ⟨hk, hkK⟩) hsk

end Kernel

/-! ## 2. Kernels of the grid orientation (stable matchings) -/

section Grid

variable {R C : Type*} [DecidableEq R] [DecidableEq C]

/-- The grid orientation for a rank `r`: inside a row towards higher rank, inside a
column towards lower rank. -/
def gridArc (r : R × C → ℕ) (s k : R × C) : Prop :=
  (k.1 = s.1 ∧ r s < r k) ∨ (k.2 = s.2 ∧ r k < r s)

instance (r : R × C → ℕ) : DecidableRel (gridArc r) := fun s k => by
  unfold gridArc; infer_instance

/-- **Every set of cells has a kernel** (for any rank function). -/
theorem exists_gridKernel (r : R × C → ℕ) :
    ∀ S : Finset (R × C), ∃ K, IsKernel (gridArc r) S K := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  -- row favourites
  let fav : R × C → Prop := fun s => ∀ t ∈ S, t.1 = s.1 → r t ≤ r s
  by_cases hclash : ∃ t ∈ S, ∃ t' ∈ S, fav t ∧ fav t' ∧ t ≠ t' ∧ t.2 = t'.2 ∧ r t' < r t
  · obtain ⟨t, htS, t', ht'S, -, hfav', htt', hcol', hlt⟩ := hclash
    obtain ⟨K, hKsub, hKind, hKdom⟩ := ih (S.erase t) (erase_ssubset htS)
    refine ⟨K, hKsub.trans (erase_subset _ _), hKind, ?_⟩
    intro s hs hsK
    by_cases hst : s = t
    · subst hst
      have ht'E : t' ∈ S.erase s := mem_erase.2 ⟨Ne.symm htt', ht'S⟩
      by_cases ht'K : t' ∈ K
      · exact ⟨t', ht'K, Or.inr ⟨hcol'.symm, hlt⟩⟩
      · obtain ⟨k, hkK, hk⟩ := hKdom t' ht'E ht'K
        rcases hk with ⟨hrow, hr⟩ | ⟨hc, hr⟩
        · have := hfav' k (mem_of_mem_erase (hKsub hkK)) hrow
          omega
        · exact ⟨k, hkK, Or.inr ⟨hc.trans hcol'.symm, lt_trans hr hlt⟩⟩
    · exact hKdom s (mem_erase.2 ⟨hst, hs⟩) hsK
  · push_neg at hclash
    refine ⟨S.filter fav, filter_subset _ _, ?_, ?_⟩
    · intro k hk k' hk' harc
      obtain ⟨hkS, hkf⟩ := mem_filter.1 hk
      obtain ⟨hk'S, hk'f⟩ := mem_filter.1 hk'
      rcases harc with ⟨hrow, hr⟩ | ⟨hc, hr⟩
      · have := hkf k' hk'S hrow
        omega
      · by_cases hkk : k = k'
        · subst hkk; omega
        · have := hclash k hkS k' hk'S hkf hk'f hkk hc.symm
          omega
    · intro s hs hsF
      obtain ⟨t, ht, htmax⟩ := exists_max_image (S.filter (fun t => t.1 = s.1)) r
        ⟨s, mem_filter.2 ⟨hs, rfl⟩⟩
      obtain ⟨htS, htrow⟩ := mem_filter.1 ht
      have htfav : fav t := fun u hu hurow =>
        htmax u (mem_filter.2 ⟨hu, hurow.trans htrow⟩)
      refine ⟨t, mem_filter.2 ⟨htS, htfav⟩, Or.inl ⟨htrow, ?_⟩⟩
      have hsfav : ¬ fav s := fun h => hsF (mem_filter.2 ⟨hs, h⟩)
      simp only [fav, not_forall, not_le] at hsfav
      obtain ⟨u, hu, hurow, hlt⟩ := hsfav
      have := htmax u (mem_filter.2 ⟨hu, hurow⟩)
      omega

end Grid

/-! ## 3. The latin rank and Galvin's theorem for `K_{R,C}` -/

section Latin

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

/-- The latin rank `(i(u) + j(v)) mod q`. -/
def latinRank (q : ℕ) (i : R → ℕ) (j : C → ℕ) (s : R × C) : ℕ := (i s.1 + j s.2) % q

omit [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C] in
theorem latinRank_lt {q : ℕ} (hq : 0 < q) (i : R → ℕ) (j : C → ℕ) (s : R × C) :
    latinRank q i j s < q := Nat.mod_lt _ hq

theorem mod_add_left_inj {q a b b' : ℕ} (hb : b < q) (hb' : b' < q)
    (h : (a + b) % q = (a + b') % q) : b = b' := by
  have h1 : (a + b) ≡ (a + b') [MOD q] := h
  have h2 : b ≡ b' [MOD q] := Nat.ModEq.add_left_cancel' a h1
  unfold Nat.ModEq at h2
  rwa [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at h2

omit [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C] in
theorem latinRank_row_inj {q : ℕ} {i : R → ℕ} {j : C → ℕ} (hj : Function.Injective j)
    (hjq : ∀ v, j v < q) {s t : R × C} (hrow : s.1 = t.1)
    (h : latinRank q i j s = latinRank q i j t) : s = t := by
  unfold latinRank at h
  rw [hrow] at h
  exact Prod.ext hrow (hj (mod_add_left_inj (hjq _) (hjq _) h))

omit [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C] in
theorem latinRank_col_inj {q : ℕ} {i : R → ℕ} {j : C → ℕ} (hi : Function.Injective i)
    (hiq : ∀ u, i u < q) {s t : R × C} (hcol : s.2 = t.2)
    (h : latinRank q i j s = latinRank q i j t) : s = t := by
  unfold latinRank at h
  rw [hcol, add_comm (i s.1), add_comm (i t.1)] at h
  exact Prod.ext (hi (mod_add_left_inj (hiq _) (hiq _) h)) hcol

/-- The out-degree of every cell under the latin rank is at most `q - 1`. -/
theorem card_filter_gridArc_le {q : ℕ} (hq : 0 < q) {i : R → ℕ} {j : C → ℕ}
    (hi : Function.Injective i) (hiq : ∀ u, i u < q)
    (hj : Function.Injective j) (hjq : ∀ v, j v < q) (s : R × C) :
    ((univ : Finset (R × C)).filter (gridArc (latinRank q i j) s)).card ≤ q - 1 := by
  set r := latinRank q i j
  have hsplit : (univ : Finset (R × C)).filter (gridArc r s) ⊆
      (univ.filter fun k : R × C => k.1 = s.1 ∧ r s < r k) ∪
        (univ.filter fun k : R × C => k.2 = s.2 ∧ r k < r s) := by
    intro k hk
    rcases (mem_filter.1 hk).2 with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, h⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, h⟩)
  have hrowc : (univ.filter fun k : R × C => k.1 = s.1 ∧ r s < r k).card ≤ q - 1 - r s := by
    have := card_le_card_of_injOn r (s := univ.filter fun k : R × C => k.1 = s.1 ∧ r s < r k)
      (t := Finset.Ioo (r s) q) (fun k hk => by
        have hk' := (mem_filter.1 hk).2
        exact mem_coe.2 (mem_Ioo.2 ⟨hk'.2, latinRank_lt hq i j k⟩))
      (fun k hk k' hk' hkk => by
        have h1 := (mem_filter.1 (mem_coe.1 hk)).2.1
        have h2 := (mem_filter.1 (mem_coe.1 hk')).2.1
        exact latinRank_row_inj hj hjq (h1.trans h2.symm) hkk)
    rw [Nat.card_Ioo] at this
    omega
  have hcolc : (univ.filter fun k : R × C => k.2 = s.2 ∧ r k < r s).card ≤ r s := by
    have := card_le_card_of_injOn r (s := univ.filter fun k : R × C => k.2 = s.2 ∧ r k < r s)
      (t := Finset.range (r s)) (fun k hk => by
        have hk' := (mem_filter.1 hk).2
        exact mem_coe.2 (mem_range.2 hk'.2))
      (fun k hk k' hk' hkk => by
        have h1 := (mem_filter.1 (mem_coe.1 hk)).2.1
        have h2 := (mem_filter.1 (mem_coe.1 hk')).2.1
        exact latinRank_col_inj hi hiq (h1.trans h2.symm) hkk)
    rwa [card_range] at this
  have hrs : r s < q := latinRank_lt hq i j s
  calc _ ≤ _ := card_le_card hsplit
    _ ≤ _ := card_union_le _ _
    _ ≤ q - 1 - r s + r s := add_le_add hrowc hcolc
    _ = q - 1 := by omega

/-- **Galvin's theorem for `K_{R,C}`.**  If `|R| ≤ q`, `|C| ≤ q` and every cell has a list
of at least `q` colours, there is a list colouring in which the cells of a row, and the
cells of a column, receive pairwise distinct colours. -/
theorem galvin_grid {Col : Type*} [DecidableEq Col] [Nonempty Col] (q : ℕ)
    (hR : Fintype.card R ≤ q) (hC : Fintype.card C ≤ q) (L : R × C → Finset Col)
    (hL : ∀ s, q ≤ (L s).card) :
    ∃ f : R × C → Col, (∀ s, f s ∈ L s) ∧
      (∀ s t : R × C, s ≠ t → s.1 = t.1 → f s ≠ f t) ∧
      (∀ s t : R × C, s ≠ t → s.2 = t.2 → f s ≠ f t) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · haveI : IsEmpty R := Fintype.card_eq_zero_iff.1 (by omega)
    exact ⟨fun _ => Classical.arbitrary Col, fun s => isEmptyElim s.1,
      fun s => isEmptyElim s.1, fun s => isEmptyElim s.1⟩
  let i : R → ℕ := fun u => (Fintype.equivFin R u : ℕ)
  let j : C → ℕ := fun v => (Fintype.equivFin C v : ℕ)
  have hi : Function.Injective i := fun u u' h =>
    (Fintype.equivFin R).injective (Fin.ext h)
  have hj : Function.Injective j := fun v v' h =>
    (Fintype.equivFin C).injective (Fin.ext h)
  have hiq : ∀ u, i u < q := fun u => lt_of_lt_of_le (Fintype.equivFin R u).isLt hR
  have hjq : ∀ v, j v < q := fun v => lt_of_lt_of_le (Fintype.equivFin C v).isLt hC
  set r := latinRank q i j with hr
  have hker := exists_gridKernel r
  obtain ⟨f, hfL, hfp⟩ := kernel_list_colouring (gridArc r) hker univ L (fun s _ =>
    lt_of_le_of_lt (card_filter_gridArc_le hq hi hiq hj hjq s) (by have := hL s; omega))
  have hsep : ∀ s t : R × C, r s ≠ r t → (s.1 = t.1 ∨ s.2 = t.2) → f s ≠ f t := by
    intro s t hne hst
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · rcases hst with h | h
      · exact hfp s (mem_univ _) t (mem_univ _) (Or.inl ⟨h.symm, hlt⟩)
      · exact fun he => hfp t (mem_univ _) s (mem_univ _) (Or.inr ⟨h, hlt⟩) he.symm
    · rcases hst with h | h
      · exact fun he => hfp t (mem_univ _) s (mem_univ _) (Or.inl ⟨h, hlt⟩) he.symm
      · exact hfp s (mem_univ _) t (mem_univ _) (Or.inr ⟨h.symm, hlt⟩)
  refine ⟨f, fun s => hfL s (mem_univ _), ?_, ?_⟩
  · intro s t hst hrow
    exact hsep s t (fun h => hst (latinRank_row_inj hj hjq hrow h)) (Or.inl hrow)
  · intro s t hst hcol
    exact hsep s t (fun h => hst (latinRank_col_inj hi hiq hcol h)) (Or.inr hcol)

end Latin

end PaperIV.GalvinRect
