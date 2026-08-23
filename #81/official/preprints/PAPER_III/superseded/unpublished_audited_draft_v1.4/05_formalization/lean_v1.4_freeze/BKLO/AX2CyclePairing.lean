/-
# One unperturbed link, paired class for class **by the three-class cycle**

`BKLO.exists_classMatched_pairing_unperturbed` pairs an unperturbed link with *no* leftovers at
all, but only for a class matching that fixes the corner class of the link: `ρ (y u) = x u`.  That
condition is exactly what a *feasible* class matching cannot satisfy — a matching fixing every
corner is constant on a cell (`BKLO.canonShift_const_on_cell`), and then a vertex would have to be
paired into one and the same class at all `20 K² t` links of a cell, while a class holds only `t`
places.

This file pairs an unperturbed link for a class matching that does **not** fix the corner, at the
price of the leftovers of the three-class cycle, which the ledger of
`BKLO.excLedgerSpread_of_cycleRouted` shows to be almost free:

* the corner class `C (x u · h + y u)` splits in half (`BKLO.corner_splits_in_half`), one half
  paired into the column class `C (ρ (y u) · h + y u)` and one half into the row class
  `C (x u · h + σ (x u))`;
* the remaining halves `LA` of the column class and `LB` of the row class are paired **with each
  other** — the cycle leftovers, whose partner class is on the *other* side of the region and whose
  index varies with the link;
* every other class of the region is paired with the class the matching prescribes, exactly as in
  the unperturbed case.

`BKLO.exists_classMatched_pairing_cycle` is that statement, and
`BKLO.exists_classMatched_pairing_cycle_shift` specialises it to the class matching of a shift
`φ`, in the shape `BKLO.IsCycleRoutedLeftover` asks for.

Everything here is `sorry`-free.
-/
import BKLO.AX2ThreeClassBlock
import BKLO.AX2CycleRouted

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ}

/-- **An unperturbed link is paired class for class by the three-class cycle.**

Let `ρ` be a permutation of the `h` class indices with inverse `σ` which does *not* fix the corner
class of the link of `u`: `ρ (y u) ≠ x u`.  Then the reserved link of `u` carries a fixed-point-free
involution by edges of `F` outside `U` which obeys the cross-side rule `BKLO.IsCrossSideAt` at every
vertex outside two sets `LA`, `LB` of exactly `c / 2` places each:

* `LA` lies in the column class `C (ρ (y u) · h + y u)` and is paired into the row class
  `C (x u · h + σ (x u))`;
* `LB` lies in that row class and is paired into the column class.

These are the leftovers of the three-class cycle; both indices of the partner's class are
coordinates of the link `u`, one of them shifted, which is what
`BKLO.excLedgerSpread_of_cycleRouted` needs. -/
theorem exists_classMatched_pairing_cycle
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (hW'W : W' ⊆ W)
    {u : V} (hu : u ∈ W \ W') {q c : ℕ}
    (hq : ∀ k < gridSize ε K * gridSize ε K, (C k).card = q)
    (hc : ∀ i ∈ gridIdx (gridSize ε K) (x u) (y u), (C i ∩ resLink R W' u).card = c)
    {ρ σ : ℕ → ℕ} (hρlt : ∀ β < gridSize ε K, ρ β < gridSize ε K)
    (hσlt : ∀ α < gridSize ε K, σ α < gridSize ε K)
    (hσρ : ∀ β < gridSize ε K, σ (ρ β) = β) (hρσ : ∀ α < gridSize ε K, ρ (σ α) = α)
    (hAne : ρ (y u) ≠ x u)
    {U : Finset (Sym2 V)} {m : ℕ}
    (hU : ∀ a ∈ resLink R W' u, ∀ k < gridSize ε K * gridSize ε K,
      ((C k ∩ resLink R W' u).filter (fun b => s(a, b) ∈ U)).card ≤ m)
    (heven : Even c) (hsize : q + 4 * m + 8 ≤ 2 * c) :
    ∃ (p : V → V) (LA LB : Finset V),
      LA ⊆ C (ρ (y u) * gridSize ε K + y u) ∩ resLink R W' u ∧
      LB ⊆ C (x u * gridSize ε K + σ (x u)) ∩ resLink R W' u ∧
      2 * LA.card = c ∧ 2 * LB.card = c ∧
      (∀ a ∈ resLink R W' u, p a ∈ resLink R W' u) ∧
      (∀ a ∈ resLink R W' u, p (p a) = a) ∧ (∀ a ∈ resLink R W' u, p a ≠ a) ∧
      (∀ a ∈ resLink R W' u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
      (∀ a ∈ LA, p a ∈ C (x u * gridSize ε K + σ (x u))) ∧
      (∀ a ∈ LB, p a ∈ C (ρ (y u) * gridSize ε K + y u)) ∧
      ∀ (a : V) (α β : ℕ), α < gridSize ε K → β < gridSize ε K →
        a ∈ C (α * gridSize ε K + β) → a ∈ resLink R W' u → a ∉ LA → a ∉ LB →
        IsCrossSideAt (gridSize ε K) C x y α β u (p a) (ρ β) (σ α) := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set Xu : Finset V := resLink R W' u with hXudef
  have hhpos : 0 < h := gridSize_pos ε K
  have hxu : x u < h := hgrid.rowLt u hu
  have hyu : y u < h := hgrid.colLt u hu
  have hXW' : Xu ⊆ W' := fun z hz => (mem_resLink.1 hz).1
  -- the classes of the region
  set rowI : ℕ → ℕ := fun β => x u * h + β with hrowIdef
  set colI : ℕ → ℕ := fun α => α * h + y u with hcolIdef
  set A : ℕ := ρ (y u) with hAdef
  set B : ℕ := σ (x u) with hBdef
  have hAlt : A < h := hρlt (y u) hyu
  have hBlt : B < h := hσlt (x u) hxu
  have hρB : ρ B = x u := hρσ (x u) hxu
  have hσA : σ A = y u := hσρ (y u) hyu
  have hBne : B ≠ y u := by
    intro hcon
    exact hAne (by rw [hAdef, ← hcon, hρB])
  have hrowmem : ∀ β < h, rowI β ∈ gridIdx h (x u) (y u) := fun β hβ =>
    mem_gridIdx.2 (Or.inl ⟨β, hβ, rfl⟩)
  have hcolmem : ∀ α < h, colI α ∈ gridIdx h (x u) (y u) := fun α hα =>
    mem_gridIdx.2 (Or.inr ⟨α, hα, rfl⟩)
  have hrowlt : ∀ β < h, rowI β < h * h := fun β hβ => gridIdx_lt hxu hyu (hrowmem β hβ)
  have hcollt : ∀ α < h, colI α < h * h := fun α hα => gridIdx_lt hxu hyu (hcolmem α hα)
  have hρinj : ∀ β < h, ∀ β' < h, ρ β = ρ β' → β = β' := by
    intro β hβ β' hβ' heq
    rw [← hσρ β hβ, ← hσρ β' hβ', heq]
  have hrowinj : ∀ γ δ : ℕ, rowI γ = rowI δ → γ = δ := by
    intro γ δ hcon
    simpa [hrowIdef] using hcon
  have hcolinj : ∀ γ < h, ∀ δ < h, colI γ = colI δ → γ = δ := by
    intro γ hγ δ hδ hcon
    exact (gridDigits_inj hyu hyu (by simpa [hcolIdef] using hcon)).1
  have hrowcol : ∀ γ < h, ∀ δ < h, rowI γ = colI δ → γ = y u ∧ δ = x u := by
    intro γ hγ δ hδ hcon
    have h1 := gridDigits_inj hγ hyu (by simpa [hrowIdef, hcolIdef] using hcon)
    exact ⟨h1.2, h1.1.symm⟩
  have hcorner : colI (x u) = rowI (y u) := by rw [hcolIdef, hrowIdef]
  -- the three classes of the cycle are distinct
  have hcyc1 : rowI (y u) ≠ colI A := by
    intro hcon
    exact hAne (hrowcol (y u) hyu A hAlt hcon).2
  have hcyc2 : rowI (y u) ≠ rowI B := fun hcon => hBne (hrowinj _ _ hcon).symm
  have hcyc3 : colI A ≠ rowI B := by
    intro hcon
    exact hBne (hrowcol B hBlt A hAlt hcon.symm).1
  -- the used degree, in the shape the constructions want
  have hUswap : ∀ (k l : ℕ), ∀ b ∈ C k ∩ Xu, l < h * h →
      ((C l ∩ Xu).filter (fun a => s(a, b) ∈ U)).card ≤ m := by
    intro k l b hb hl
    have hbXu : b ∈ Xu := (Finset.mem_inter.1 hb).2
    have hcong : ((C l ∩ Xu).filter (fun a => s(a, b) ∈ U))
        = ((C l ∩ Xu).filter (fun a => s(b, a) ∈ U)) := by
      refine Finset.filter_congr fun a _ => ?_
      rw [Sym2.eq_swap]
    rw [hcong]
    exact hU b hbXu l hl
  -- the cycle block on the corner, the column class `A` and the row class `B`
  obtain ⟨pc, LA, LB, hLA, hLB, hLAcard, hLBcard, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9⟩ :=
    exists_three_class_cycle_block (i := rowI (y u)) (j := colI A) (l := rowI B)
      hgrid hW'W (hrowlt _ hyu) (hcollt _ hAlt) (hrowlt _ hBlt) hcyc1 hcyc2 hcyc3 hXW' hq
      (fun a ha k hk => hU a ha k hk)
      (hc _ (hrowmem _ hyu)) (hc _ (hcolmem _ hAlt)) (hc _ (hrowmem _ hBlt)) heven hsize
  -- the blocks
  set T : ℕ → Finset V := fun β =>
    if β = y u then ((C (rowI (y u)) ∩ Xu) ∪ (C (colI A) ∩ Xu)) ∪ (C (rowI B) ∩ Xu)
    else if β = B then (∅ : Finset V)
    else (C (rowI β) ∩ Xu) ∪ (C (colI (ρ β)) ∩ Xu) with hTdef
  have hTy : T (y u) = ((C (rowI (y u)) ∩ Xu) ∪ (C (colI A) ∩ Xu)) ∪ (C (rowI B) ∩ Xu) := by
    simp only [hTdef, reduceIte]
  have hTB : T B = (∅ : Finset V) := by
    simp only [hTdef, if_neg hBne, reduceIte]
  have hTo : ∀ β, β ≠ y u → β ≠ B →
      T β = (C (rowI β) ∩ Xu) ∪ (C (colI (ρ β)) ∩ Xu) := by
    intro β h1 h2
    simp only [hTdef, if_neg h1, if_neg h2]
  have hTsub : ∀ β, T β ⊆ Xu := by
    intro β z hz
    by_cases hβy : β = y u
    · subst hβy
      rw [hTy] at hz
      rcases Finset.mem_union.1 hz with hz' | hz'
      · rcases Finset.mem_union.1 hz' with hz'' | hz'' <;> exact (Finset.mem_inter.1 hz'').2
      · exact (Finset.mem_inter.1 hz').2
    · by_cases hβB : β = B
      · subst hβB; rw [hTB] at hz; exact absurd hz (Finset.notMem_empty z)
      · rw [hTo β hβy hβB] at hz
        rcases Finset.mem_union.1 hz with hz' | hz' <;> exact (Finset.mem_inter.1 hz').2
  -- every vertex of the link lies in a class of the region
  have hclassU : ∀ z ∈ Xu, ∃ k ∈ gridIdx h (x u) (y u), z ∈ C k := by
    intro z hz
    have : z ∈ gridRegion h C (x u) (y u) :=
      (Finset.mem_inter.1 (hgrid.linkSubset u hu hz)).2
    rw [gridRegion_eq_biUnion] at this
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.1 this
    exact ⟨k, hk, hzk⟩
  have hunion : (Finset.range h).biUnion T = Xu := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro z hz
      obtain ⟨β, _, hzβ⟩ := Finset.mem_biUnion.1 hz
      exact hTsub β hzβ
    · intro z hz
      obtain ⟨k, hk, hzk⟩ := hclassU z hz
      rcases mem_gridIdx.1 hk with ⟨j, hj, rfl⟩ | ⟨l, hl, rfl⟩
      · -- a row class
        by_cases hjy : j = y u
        · subst hjy
          refine Finset.mem_biUnion.2 ⟨y u, Finset.mem_range.2 hyu, ?_⟩
          rw [hTy]
          exact Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hzk, hz⟩))
        · by_cases hjB : j = B
          · subst hjB
            refine Finset.mem_biUnion.2 ⟨y u, Finset.mem_range.2 hyu, ?_⟩
            rw [hTy]
            exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hzk, hz⟩)
          · refine Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, ?_⟩
            rw [hTo j hjy hjB]
            exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hzk, hz⟩)
      · -- a column class
        by_cases hlx : l = x u
        · subst hlx
          refine Finset.mem_biUnion.2 ⟨y u, Finset.mem_range.2 hyu, ?_⟩
          rw [hTy]
          refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨?_, hz⟩))
          rw [← hcorner]
          exact hzk
        · by_cases hlA : l = A
          · subst hlA
            refine Finset.mem_biUnion.2 ⟨y u, Finset.mem_range.2 hyu, ?_⟩
            rw [hTy]
            exact Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hzk, hz⟩))
          · refine Finset.mem_biUnion.2 ⟨σ l, Finset.mem_range.2 (hσlt l hl), ?_⟩
            have hσly : σ l ≠ y u := by
              intro hcon
              exact hlA (by rw [hAdef, ← hcon, hρσ l hl])
            have hσlB : σ l ≠ B := by
              intro hcon
              exact hlx (by rw [← hρσ l hl, hcon, hBdef, hρσ (x u) hxu])
            rw [hTo (σ l) hσly hσlB]
            refine Finset.mem_union_right _ (Finset.mem_inter.2 ⟨?_, hz⟩)
            rwa [hcolIdef, hρσ l hl]
  -- the blocks are pairwise disjoint
  have haux : ∀ β' < h, β' ≠ y u → β' ≠ B → ∀ k', (k' = rowI β' ∨ k' = colI (ρ β')) →
      k' ≠ rowI (y u) ∧ k' ≠ colI A ∧ k' ≠ rowI B := by
    intro β' hβ' hβ'y hβ'B k' hk'
    rcases hk' with rfl | rfl
    · refine ⟨fun hcon => hβ'y (hrowinj _ _ hcon), fun hcon => ?_, fun hcon => hβ'B (hrowinj _ _ hcon)⟩
      exact hβ'y (hrowcol β' hβ' A hAlt hcon).1
    · refine ⟨fun hcon => ?_, fun hcon => ?_, fun hcon => ?_⟩
      · have h1 := hrowcol (y u) hyu (ρ β') (hρlt β' hβ') hcon.symm
        exact hβ'B (by rw [hBdef, ← h1.2, hσρ β' hβ'])
      · exact hβ'y (hρinj β' hβ' (y u) hyu (hcolinj _ (hρlt β' hβ') _ hAlt hcon))
      · exact hBne (hrowcol B hBlt (ρ β') (hρlt β' hβ') hcon.symm).1
  have hdisjidx : ∀ β < h, ∀ β' < h, β ≠ β' →
      ∀ k, ((β = y u ∧ (k = rowI (y u) ∨ k = colI A ∨ k = rowI B)) ∨
        (β ≠ y u ∧ β ≠ B ∧ (k = rowI β ∨ k = colI (ρ β)))) →
      ∀ k', ((β' = y u ∧ (k' = rowI (y u) ∨ k' = colI A ∨ k' = rowI B)) ∨
        (β' ≠ y u ∧ β' ≠ B ∧ (k' = rowI β' ∨ k' = colI (ρ β')))) → k ≠ k' := by
    intro β hβ β' hβ' hne k hk k' hk' hcon
    rcases hk with ⟨hβy, hk⟩ | ⟨hβy, hβB, hk⟩
    · rcases hk' with ⟨hβ'y, hk'⟩ | ⟨hβ'y, hβ'B, hk'⟩
      · exact hne (by rw [hβy, hβ'y])
      · obtain ⟨e1, e2, e3⟩ := haux β' hβ' hβ'y hβ'B k' hk'
        rcases hk with rfl | rfl | rfl
        · exact e1 hcon.symm
        · exact e2 hcon.symm
        · exact e3 hcon.symm
    · rcases hk' with ⟨hβ'y, hk'⟩ | ⟨hβ'y, hβ'B, hk'⟩
      · obtain ⟨e1, e2, e3⟩ := haux β hβ hβy hβB k hk
        rcases hk' with rfl | rfl | rfl
        · exact e1 hcon
        · exact e2 hcon
        · exact e3 hcon
      · rcases hk with rfl | rfl <;> rcases hk' with rfl | rfl
        · exact hne (hrowinj _ _ hcon)
        · exact hβy (hrowcol β hβ (ρ β') (hρlt β' hβ') hcon).1
        · exact hβ'y (hrowcol β' hβ' (ρ β) (hρlt β hβ) hcon.symm).1
        · exact hne (hρinj β hβ β' hβ' (hcolinj _ (hρlt β hβ) _ (hρlt β' hβ') hcon))
  have hTclass : ∀ β < h, ∀ z ∈ T β, ∃ k, k < h * h ∧ z ∈ C k ∧
      ((β = y u ∧ (k = rowI (y u) ∨ k = colI A ∨ k = rowI B)) ∨
        (β ≠ y u ∧ β ≠ B ∧ (k = rowI β ∨ k = colI (ρ β)))) := by
    intro β hβ z hz
    by_cases hβy : β = y u
    · subst hβy
      rw [hTy] at hz
      rcases Finset.mem_union.1 hz with hz' | hz'
      · rcases Finset.mem_union.1 hz' with hz'' | hz''
        · exact ⟨rowI (y u), hrowlt _ hyu, (Finset.mem_inter.1 hz'').1, Or.inl ⟨rfl, Or.inl rfl⟩⟩
        · exact ⟨colI A, hcollt _ hAlt, (Finset.mem_inter.1 hz'').1,
            Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩⟩
      · exact ⟨rowI B, hrowlt _ hBlt, (Finset.mem_inter.1 hz').1,
          Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩⟩
    · by_cases hβB : β = B
      · subst hβB; rw [hTB] at hz; exact absurd hz (Finset.notMem_empty z)
      · rw [hTo β hβy hβB] at hz
        rcases Finset.mem_union.1 hz with hz' | hz'
        · exact ⟨rowI β, hrowlt _ hβ, (Finset.mem_inter.1 hz').1,
            Or.inr ⟨hβy, hβB, Or.inl rfl⟩⟩
        · exact ⟨colI (ρ β), hcollt _ (hρlt β hβ), (Finset.mem_inter.1 hz').1,
            Or.inr ⟨hβy, hβB, Or.inr rfl⟩⟩
  have hdisj : ∀ β ∈ Finset.range h, ∀ β' ∈ Finset.range h, β ≠ β' → Disjoint (T β) (T β') := by
    intro β hβ β' hβ' hne
    rw [Finset.mem_range] at hβ hβ'
    refine Finset.disjoint_left.2 fun z hz hz' => ?_
    obtain ⟨k, hklt, hzk, hkd⟩ := hTclass β hβ z hz
    obtain ⟨k', hk'lt, hzk', hk'd⟩ := hTclass β' hβ' z hz'
    exact (Finset.disjoint_left.1 (hgrid.classDisjoint k hklt k' hk'lt
      (hdisjidx β hβ β' hβ' hne k hkd k' hk'd))) hzk hzk'
  -- the ordinary blocks
  have hblock : ∀ β : ℕ, ∃ pb : V → V, β < h → β ≠ y u → β ≠ B →
      ((∀ z ∈ T β, pb z ∈ T β) ∧ (∀ z ∈ T β, pb (pb z) = z) ∧ (∀ z ∈ T β, pb z ≠ z) ∧
        (∀ z ∈ T β, s(z, pb z) ∈ F ∧ s(z, pb z) ∉ U) ∧
        (∀ z ∈ C (rowI β) ∩ Xu, pb z ∈ C (colI (ρ β)) ∩ Xu) ∧
        (∀ z ∈ C (colI (ρ β)) ∩ Xu, pb z ∈ C (rowI β) ∩ Xu)) := by
    intro β
    by_cases hβ : β < h
    swap
    · exact ⟨id, fun hcon => absurd hcon hβ⟩
    by_cases hβy : β = y u
    · exact ⟨id, fun _ hcon => absurd hβy hcon⟩
    by_cases hβB : β = B
    · exact ⟨id, fun _ _ hcon => absurd hβB hcon⟩
    have hcardrow : (C (rowI β) ∩ Xu).card = c := hc _ (hrowmem β hβ)
    have hcardcol : (C (colI (ρ β)) ∩ Xu).card = c := hc _ (hcolmem _ (hρlt β hβ))
    have hidxne : rowI β ≠ colI (ρ β) := by
      intro hcon
      exact hβy (hrowcol β hβ (ρ β) (hρlt β hβ) hcon).1
    obtain ⟨pb, hp1, hp2, hp3, hp4, hp5⟩ :=
      exists_class_pair_involution_avoiding hgrid hW'W (hrowlt β hβ)
        (hcollt _ (hρlt β hβ)) hidxne hXW' hq (by rw [hcardrow, hcardcol])
        (fun a ha => hU a (Finset.mem_inter.1 ha).2 _ (hcollt _ (hρlt β hβ)))
        (fun b hb => hUswap _ _ b hb (hrowlt β hβ))
        (by rw [hcardrow]; omega)
    refine ⟨pb, fun _ _ _ => ⟨?_, ?_, ?_, ?_, hp1, hp2⟩⟩
    · intro z hz
      rw [hTo β hβy hβB] at hz ⊢
      rcases Finset.mem_union.1 hz with hh | hh
      · exact Finset.mem_union_right _ (hp1 z hh)
      · exact Finset.mem_union_left _ (hp2 z hh)
    · rw [hTo β hβy hβB]; exact hp3
    · rw [hTo β hβy hβB]; exact hp4
    · rw [hTo β hβy hβB]; exact hp5
  choose pbo hpbo using hblock
  set pb : ℕ → V → V := fun β => if β = y u then pc else pbo β with hpbdef
  have hpby : pb (y u) = pc := by simp only [hpbdef, reduceIte]
  have hpbo' : ∀ β, β ≠ y u → pb β = pbo β := by
    intro β hβ; simp only [hpbdef, if_neg hβ]
  -- the cycle block, in the shape of a block
  have hcycT : ∀ z ∈ T (y u), pc z ∈ T (y u) ∧ pc (pc z) = z ∧ pc z ≠ z ∧
      (s(z, pc z) ∈ F ∧ s(z, pc z) ∉ U) := by
    intro z hz
    rw [hTy] at hz
    exact ⟨by rw [hTy]; exact hc1 z hz, hc2 z hz, hc3 z hz, hc4 z hz⟩
  -- the block hypotheses of the gluing
  have hbmaps : ∀ β ∈ Finset.range h, ∀ z ∈ T β, pb β z ∈ T β := by
    intro β hβ z hz
    rw [Finset.mem_range] at hβ
    by_cases hβy : β = y u
    · subst hβy; rw [hpby]; exact (hcycT z hz).1
    · by_cases hβB : β = B
      · subst hβB; rw [hTB] at hz; exact absurd hz (Finset.notMem_empty z)
      · rw [hpbo' β hβy]; exact (hpbo β hβ hβy hβB).1 z hz
  have hbinv : ∀ β ∈ Finset.range h, ∀ z ∈ T β, pb β (pb β z) = z := by
    intro β hβ z hz
    rw [Finset.mem_range] at hβ
    by_cases hβy : β = y u
    · subst hβy; rw [hpby]; exact (hcycT z hz).2.1
    · by_cases hβB : β = B
      · subst hβB; rw [hTB] at hz; exact absurd hz (Finset.notMem_empty z)
      · rw [hpbo' β hβy]; exact (hpbo β hβ hβy hβB).2.1 z hz
  have hbne : ∀ β ∈ Finset.range h, ∀ z ∈ T β, pb β z ≠ z := by
    intro β hβ z hz
    rw [Finset.mem_range] at hβ
    by_cases hβy : β = y u
    · subst hβy; rw [hpby]; exact (hcycT z hz).2.2.1
    · by_cases hβB : β = B
      · subst hβB; rw [hTB] at hz; exact absurd hz (Finset.notMem_empty z)
      · rw [hpbo' β hβy]; exact (hpbo β hβ hβy hβB).2.2.1 z hz
  have hbr : ∀ β ∈ Finset.range h, ∀ z ∈ T β, s(z, pb β z) ∈ F ∧ s(z, pb β z) ∉ U := by
    intro β hβ z hz
    rw [Finset.mem_range] at hβ
    by_cases hβy : β = y u
    · subst hβy; rw [hpby]; exact (hcycT z hz).2.2.2
    · by_cases hβB : β = B
      · subst hβB; rw [hTB] at hz; exact absurd hz (Finset.notMem_empty z)
      · rw [hpbo' β hβy]; exact (hpbo β hβ hβy hβB).2.2.2.1 z hz
  -- glue the blocks
  obtain ⟨P, hPeq, hPmaps, hPinv, hPne, hPr⟩ :=
    exists_involution_biUnion (Finset.range h) T pb (fun a b => s(a, b) ∈ F ∧ s(a, b) ∉ U)
      hdisj hbmaps hbinv hbne hbr
  rw [hunion] at hPmaps hPinv hPne hPr
  refine ⟨P, LA, LB, hLA, hLB, hLAcard, hLBcard, hPmaps, hPinv, hPne, hPr, ?_, ?_, ?_⟩
  · -- the leftovers of the column class go into the row class
    intro a ha
    have hmem : a ∈ T (y u) := by
      rw [hTy]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (hLA ha))
    have hPa : P a = pc a := by
      rw [hPeq (y u) (Finset.mem_range.2 hyu) a hmem, hpby]
    rw [hPa]
    exact (Finset.mem_inter.1 (hLB (hc8 a ha))).1
  · -- the leftovers of the row class go into the column class
    intro a ha
    have hmem : a ∈ T (y u) := by
      rw [hTy]
      exact Finset.mem_union_right _ (hLB ha)
    have hPa : P a = pc a := by
      rw [hPeq (y u) (Finset.mem_range.2 hyu) a hmem, hpby]
    rw [hPa]
    exact (Finset.mem_inter.1 (hLA (hc9 a ha))).1
  · -- the cross-side rule outside the leftovers
    intro a α β hα hβ hacls haXu haLA haLB
    obtain ⟨k, hk, hak⟩ := hclassU a haXu
    have hklt : k < h * h := gridIdx_lt hxu hyu hk
    have hαβlt : α * h + β < h * h := grid_idx_lt hα hβ
    have hkeq : k = α * h + β := by
      by_contra hcon
      exact (Finset.disjoint_left.1 (hgrid.classDisjoint k hklt _ hαβlt hcon)) hak hacls
    subst hkeq
    rcases mem_gridIdx.1 hk with ⟨j, hj, heq⟩ | ⟨l, hl, heq⟩
    · -- `a` lies in the row part: `α = x u`
      obtain ⟨hx, hb⟩ := gridDigits_inj hβ hj heq
      subst hx
      have hmemrow : a ∈ C (rowI β) ∩ Xu := Finset.mem_inter.2 ⟨hacls, haXu⟩
      by_cases hβy : β = y u
      · -- the corner class
        subst hβy
        have hmem : a ∈ T (y u) := by
          rw [hTy]; exact Finset.mem_union_left _ (Finset.mem_union_left _ hmemrow)
        have hPa : P a = pc a := by
          rw [hPeq (y u) (Finset.mem_range.2 hyu) a hmem, hpby]
        rcases Finset.mem_union.1 (hc5 a hmemrow) with hh | hh
        · refine Or.inl ⟨rfl, ?_⟩
          rw [hPa]
          exact (Finset.mem_inter.1 hh).1
        · refine Or.inr ⟨rfl, ?_⟩
          rw [hPa]
          exact (Finset.mem_inter.1 hh).1
      · by_cases hβB : β = B
        · -- the row class of the cycle, outside its leftovers
          subst hβB
          have hmem : a ∈ T (y u) := by
            rw [hTy]; exact Finset.mem_union_right _ hmemrow
          have hPa : P a = pc a := by
            rw [hPeq (y u) (Finset.mem_range.2 hyu) a hmem, hpby]
          refine Or.inl ⟨rfl, ?_⟩
          rw [hPa, hρB]
          exact (Finset.mem_inter.1 (hc7 a hmemrow haLB)).1
        · -- an ordinary block
          have hmem : a ∈ T β := by
            rw [hTo β hβy hβB]; exact Finset.mem_union_left _ hmemrow
          have hPa : P a = pbo β a := by
            rw [hPeq β (Finset.mem_range.2 hβ) a hmem, hpbo' β hβy]
          refine Or.inl ⟨rfl, ?_⟩
          rw [hPa]
          exact (Finset.mem_inter.1 ((hpbo β hβ hβy hβB).2.2.2.2.1 a hmemrow)).1
    · -- `a` lies in the column part: `β = y u`
      obtain ⟨hx, hb⟩ := gridDigits_inj hβ hyu heq
      subst hb
      have hmemcol : a ∈ C (colI α) ∩ Xu := Finset.mem_inter.2 ⟨hacls, haXu⟩
      by_cases hαx : α = x u
      · -- the corner class again
        subst hαx
        have hmemrow : a ∈ C (rowI (y u)) ∩ Xu := by rwa [← hcorner]
        have hmem : a ∈ T (y u) := by
          rw [hTy]; exact Finset.mem_union_left _ (Finset.mem_union_left _ hmemrow)
        have hPa : P a = pc a := by
          rw [hPeq (y u) (Finset.mem_range.2 hyu) a hmem, hpby]
        rcases Finset.mem_union.1 (hc5 a hmemrow) with hh | hh
        · refine Or.inl ⟨rfl, ?_⟩
          rw [hPa]
          exact (Finset.mem_inter.1 hh).1
        · refine Or.inr ⟨rfl, ?_⟩
          rw [hPa]
          exact (Finset.mem_inter.1 hh).1
      · by_cases hαA : α = A
        · -- the column class of the cycle, outside its leftovers
          subst hαA
          have hmem : a ∈ T (y u) := by
            rw [hTy]
            exact Finset.mem_union_left _ (Finset.mem_union_right _ hmemcol)
          have hPa : P a = pc a := by
            rw [hPeq (y u) (Finset.mem_range.2 hyu) a hmem, hpby]
          refine Or.inr ⟨rfl, ?_⟩
          rw [hPa, hσA]
          exact (Finset.mem_inter.1 (hc6 a hmemcol haLA)).1
        · -- an ordinary block
          have hσαy : σ α ≠ y u := by
            intro hcon
            exact hαA (by rw [hAdef, ← hcon, hρσ α hα])
          have hσαB : σ α ≠ B := by
            intro hcon
            exact hαx (by rw [← hρσ α hα, hcon, hBdef, hρσ (x u) hxu])
          have hmemcol' : a ∈ C (colI (ρ (σ α))) ∩ Xu := by rwa [hρσ α hα]
          have hmem : a ∈ T (σ α) := by
            rw [hTo (σ α) hσαy hσαB]; exact Finset.mem_union_right _ hmemcol'
          have hPa : P a = pbo (σ α) a := by
            rw [hPeq (σ α) (Finset.mem_range.2 (hσlt α hα)) a hmem, hpbo' _ hσαy]
          refine Or.inr ⟨rfl, ?_⟩
          rw [hPa]
          exact (Finset.mem_inter.1 ((hpbo (σ α) (hσlt α hα) hσαy hσαB).2.2.2.2.2 a hmemcol')).1

omit [DecidableEq V] in
/-- The shift is inverse to the inverse shift, in the other order. -/
theorem crossShift_crossShiftInv {h : ℕ} {φ : V → ℕ} {r : ℕ} {w : V} (hr : r < h)
    (hφ : φ w < h) : crossShift h φ (crossShiftInv h φ r w) w = r := by
  have h1 : (r + (h - φ w)) % h ≡ r + (h - φ w) [MOD h] := Nat.mod_modEq _ _
  have h2 : (r + (h - φ w)) % h + φ w ≡ (r + (h - φ w)) + φ w [MOD h] :=
    Nat.ModEq.add_right _ h1
  have h3 : (r + (h - φ w)) + φ w = r + h := by omega
  rw [h3] at h2
  have h4 : ((r + (h - φ w)) % h + φ w) % h = (r + h) % h := h2
  rw [crossShift, crossShiftInv, h4, Nat.add_mod_right, Nat.mod_eq_of_lt hr]

/-- **The three-class cycle at the class matching of a shift.**  The same pairing as
`BKLO.exists_classMatched_pairing_cycle`, for `ρ w β = crossShift h φ β w` and
`σ w α = crossShiftInv h φ α w`, with the two leftover sets in the shape
`BKLO.IsCycleRoutedLeftover` asks for: `Erow` lies in the column class
`C (crossShift h φ (y u) u · h + y u)` and is paired into the row class
`C (x u · h + crossShiftInv h φ (x u) u)`, and `Ecol` the other way round. -/
theorem exists_classMatched_pairing_cycle_shift
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (hW'W : W' ⊆ W)
    {u : V} (hu : u ∈ W \ W') {q c : ℕ}
    (hq : ∀ k < gridSize ε K * gridSize ε K, (C k).card = q)
    (hc : ∀ i ∈ gridIdx (gridSize ε K) (x u) (y u), (C i ∩ resLink R W' u).card = c)
    {φ : V → ℕ} (hφlt : φ u < gridSize ε K)
    (hAne : crossShift (gridSize ε K) φ (y u) u ≠ x u)
    {U : Finset (Sym2 V)} {m : ℕ}
    (hU : ∀ a ∈ resLink R W' u, ∀ k < gridSize ε K * gridSize ε K,
      ((C k ∩ resLink R W' u).filter (fun b => s(a, b) ∈ U)).card ≤ m)
    (heven : Even c) (hsize : q + 4 * m + 8 ≤ 2 * c) :
    ∃ (p : V → V) (Ecol Erow : Finset V),
      Erow ⊆ C (crossShift (gridSize ε K) φ (y u) u * gridSize ε K + y u) ∩ resLink R W' u ∧
      Ecol ⊆ C (x u * gridSize ε K + crossShiftInv (gridSize ε K) φ (x u) u)
        ∩ resLink R W' u ∧
      2 * Erow.card = c ∧ 2 * Ecol.card = c ∧
      (∀ a ∈ resLink R W' u, p a ∈ resLink R W' u) ∧
      (∀ a ∈ resLink R W' u, p (p a) = a) ∧ (∀ a ∈ resLink R W' u, p a ≠ a) ∧
      (∀ a ∈ resLink R W' u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
      (∀ a ∈ Ecol, a ∈ C (x u * gridSize ε K + crossShiftInv (gridSize ε K) φ (x u) u) ∧
        p a ∈ C (crossShift (gridSize ε K) φ (y u) u * gridSize ε K + y u)) ∧
      (∀ a ∈ Erow, a ∈ C (crossShift (gridSize ε K) φ (y u) u * gridSize ε K + y u) ∧
        p a ∈ C (x u * gridSize ε K + crossShiftInv (gridSize ε K) φ (x u) u)) ∧
      ∀ (a : V) (α β : ℕ), α < gridSize ε K → β < gridSize ε K →
        a ∈ C (α * gridSize ε K + β) → a ∈ resLink R W' u → a ∉ Ecol → a ∉ Erow →
        IsCrossSideAt (gridSize ε K) C x y α β u (p a)
          (crossShift (gridSize ε K) φ β u) (crossShiftInv (gridSize ε K) φ α u) := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hhpos : 0 < h := gridSize_pos ε K
  obtain ⟨p, LA, LB, hLA, hLB, hLAcard, hLBcard, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_classMatched_pairing_cycle (ρ := fun β => crossShift h φ β u)
      (σ := fun α => crossShiftInv h φ α u) hgrid hW'W hu hq hc
      (fun β _ => crossShift_lt hhpos φ β u) (fun α _ => crossShiftInv_lt hhpos φ α u)
      (fun β hβ => crossShiftInv_crossShift hβ hφlt)
      (fun α hα => crossShift_crossShiftInv hα hφlt) hAne hU heven hsize
  refine ⟨p, LB, LA, hLA, hLB, hLAcard, hLBcard, h1, h2, h3, h4, ?_, ?_, ?_⟩
  · exact fun a ha => ⟨(Finset.mem_inter.1 (hLB ha)).1, h6 a ha⟩
  · exact fun a ha => ⟨(Finset.mem_inter.1 (hLA ha)).1, h5 a ha⟩
  · exact fun a α β hα hβ hacls haXu ha1 ha2 => h7 a α β hα hβ hacls haXu ha2 ha1

end BKLO
