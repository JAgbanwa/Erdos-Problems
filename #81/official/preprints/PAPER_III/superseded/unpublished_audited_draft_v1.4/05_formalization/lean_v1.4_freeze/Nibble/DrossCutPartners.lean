/-
# Nibble — counting the opposite partners of an edge

The refined cut condition needs a *concave* upper bound on the number of edges that are **not**
opposite partners of a given edge `e` in a `K₄`.  The opposite partners of `e` are exactly the
edges inside the common neighbourhood of `e` (`Nibble.isOppPair_iff_subset_commonNbrs`), so the
non-partners are exactly the edges meeting the complement of that common neighbourhood, a set of
size `σ(e) + 2`.  Feeding the two double-counting estimates of `Nibble/DrossCutCount.lean` into
that description gives `Nibble.card_nonPartners_le`:

  `#{non-partners of e} ≤ cutPhi |V| σ(e)`.

Combined with the trivial cut estimate `Nibble.crossSum_ge_sub` and Cauchy–Schwarz this produces
the two `X`-inputs of `Nibble.cut_master`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DrossCutCount

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Opposite partners -/

/-- The opposite partners of `e` are exactly the edges inside its common neighbourhood. -/
theorem isOppPair_iff_subset_commonNbrs (G : SimpleGraph V) [DecidableRel G.Adj]
    (e₁ e₂ : EdgeV G) : IsOppPair G e₁ e₂ ↔ e₂.val ⊆ commonNbrs G e₁ := by
  classical
  constructor
  · intro h y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x hx => h x hx y hy⟩
  · intro h x hx y hy
    exact (Finset.mem_filter.mp (h hy)).2 x hx

/-- The edges that are *not* opposite partners of `e`. -/
noncomputable def nonPartners (G : SimpleGraph V) [DecidableRel G.Adj] (e : EdgeV G) :
    Finset (EdgeV G) :=
  Finset.univ.filter (fun e₂ => ¬ IsOppPair G e e₂)

theorem nonPartners_eq (G : SimpleGraph V) [DecidableRel G.Adj] (e : EdgeV G) :
    nonPartners G e = edgesMeeting G (Finset.univ \ commonNbrs G e) := by
  classical
  ext e₂
  simp only [nonPartners, edgesMeeting, Finset.mem_filter, Finset.mem_univ, true_and,
    isOppPair_iff_subset_commonNbrs]
  constructor
  · intro h
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine h (fun x hx => ?_)
    by_contra hxc
    have : x ∈ e₂.val ∩ (Finset.univ \ commonNbrs G e) :=
      Finset.mem_inter.mpr ⟨hx, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxc⟩⟩
    rw [hne] at this
    exact absurd this (Finset.notMem_empty x)
  · rintro ⟨x, hx⟩ hsub
    rw [Finset.mem_inter, Finset.mem_sdiff] at hx
    exact hx.2.2 (hsub hx.1)

/-- The complement of the common neighbourhood of `e` has `σ(e) + 2` elements. -/
theorem card_compl_commonNbrs (G : SimpleGraph V) [DecidableRel G.Adj] (e : EdgeV G) :
    (((Finset.univ \ commonNbrs G e).card : ℝ)) = ((outsideOf G e).card : ℝ) + 2 := by
  classical
  have hsub : commonNbrs G e ⊆ (Finset.univ : Finset V) := Finset.subset_univ _
  have hkey := Finset.card_sdiff_add_card_eq_card hsub
  rw [Finset.card_univ] at hkey
  have hout := card_outsideOf G e
  have : (Finset.univ \ commonNbrs G e).card = (outsideOf G e).card + 2 := by omega
  rw [this]
  push_cast
  ring

/-- **The concave bound on the non-partners.** -/
theorem card_nonPartners_le (G : SimpleGraph V) [DecidableRel G.Adj] (e : EdgeV G) :
    ((nonPartners G e).card : ℝ)
      ≤ cutPhi (Fintype.card V : ℝ) ((outsideOf G e).card : ℝ) := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hnd
  set W : Finset V := Finset.univ \ commonNbrs G e with hW
  set sg : ℝ := ((outsideOf G e).card : ℝ) with hsg
  have hWcard : (W.card : ℝ) = sg + 2 := card_compl_commonNbrs G e
  have hmeet := card_edgesMeeting_le G W
  have hdeg : ∑ u ∈ W, ((G.degree u : ℝ) + n - (W.card : ℝ))
      ≤ (W.card : ℝ) * ((n - 1) + n - (W.card : ℝ)) := by
    calc ∑ u ∈ W, ((G.degree u : ℝ) + n - (W.card : ℝ))
        ≤ ∑ _u ∈ W, ((n - 1) + n - (W.card : ℝ)) := by
          refine Finset.sum_le_sum (fun u _ => ?_)
          have : (G.degree u : ℝ) ≤ n - 1 := by
            have h := G.degree_lt_card_verts u
            have : (G.degree u : ℝ) < n := by rw [hnd]; exact_mod_cast h
            have hd : (G.degree u + 1 : ℕ) ≤ Fintype.card V := h
            have : ((G.degree u : ℝ) + 1) ≤ n := by rw [hnd]; exact_mod_cast hd
            linarith
          linarith
      _ = (W.card : ℝ) * ((n - 1) + n - (W.card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hsg0 : (0 : ℝ) ≤ sg := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  rw [nonPartners_eq G e, ← hW]
  simp only [cutPhi]
  rw [hWcard] at hmeet hdeg
  nlinarith only [hmeet, hdeg, hsg0, hn0]

/-! ### The cut estimate -/

/-- **The crossing pairs of a cut**, bounded below by the non-partner counts. -/
theorem crossSum_ge_sub (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (EdgeV G)) :
    (S.card : ℝ) * (Sᶜ.card : ℝ) - ∑ y ∈ S, ((nonPartners G y).card : ℝ) ≤ crossSum G S := by
  classical
  have hswap : crossSum G S = ∑ y ∈ S, ∑ x ∈ Sᶜ, (if IsOppPair G x y then (1 : ℝ) else 0) := by
    rw [crossSum, Finset.sum_comm]
  have hpt : ∀ y ∈ S, (Sᶜ.card : ℝ) - ((nonPartners G y).card : ℝ)
      ≤ ∑ x ∈ Sᶜ, (if IsOppPair G x y then (1 : ℝ) else 0) := by
    intro y _
    have hval : ∑ x ∈ Sᶜ, (if IsOppPair G x y then (1 : ℝ) else 0)
        = ((Sᶜ.filter (fun x => IsOppPair G x y)).card : ℝ) := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]
    have hcov : Sᶜ ⊆ (Sᶜ.filter (fun x => IsOppPair G x y)) ∪ nonPartners G y := by
      intro x hx
      by_cases hopp : IsOppPair G x y
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hopp⟩)
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
        intro hc
        exact hopp hc.symm
    have hcard : Sᶜ.card ≤ (Sᶜ.filter (fun x => IsOppPair G x y)).card + (nonPartners G y).card :=
      le_trans (Finset.card_le_card hcov) (Finset.card_union_le _ _)
    have hcardR : (Sᶜ.card : ℝ)
        ≤ ((Sᶜ.filter (fun x => IsOppPair G x y)).card : ℝ) + ((nonPartners G y).card : ℝ) := by
      exact_mod_cast hcard
    rw [hval]
    linarith
  have hsum : ∑ y ∈ S, ((Sᶜ.card : ℝ) - ((nonPartners G y).card : ℝ))
      ≤ ∑ y ∈ S, ∑ x ∈ Sᶜ, (if IsOppPair G x y then (1 : ℝ) else 0) :=
    Finset.sum_le_sum hpt
  rw [hswap]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  linarith

/-! ### The two flow inputs -/

/-- **The flow input on a side of the cut.**  This is the hypothesis `hXK` of
`Nibble.cut_master`. -/
theorem cut_input_side (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (EdgeV G)) :
    2 * (S.card : ℝ)
        * ((S.card : ℝ) * (Sᶜ.card : ℝ)
          - ((∑ e ∈ S, ((outsideOf G e).card : ℝ)) + 2 * (S.card : ℝ))
              * (21 * (Fintype.card V : ℝ) / 20)
          + ∑ e ∈ S, ((outsideOf G e).card : ℝ))
        + (∑ e ∈ S, ((outsideOf G e).card : ℝ)) ^ 2
      ≤ 2 * (S.card : ℝ) * crossSum G S := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hnd
  set A : ℝ := ∑ e ∈ S, ((outsideOf G e).card : ℝ) with hA
  set K : ℝ := (S.card : ℝ) with hK
  set L : ℝ := (Sᶜ.card : ℝ) with hL
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  -- the sum of the concave bounds
  have hphisum : ∑ y ∈ S, ((nonPartners G y).card : ℝ)
      ≤ (A + 2 * K) * (21 * n / 20) - A
        - (1 / 2) * ∑ y ∈ S, ((outsideOf G y).card : ℝ) ^ 2 := by
    have h1 : ∑ y ∈ S, ((nonPartners G y).card : ℝ)
        ≤ ∑ y ∈ S, cutPhi n ((outsideOf G y).card : ℝ) :=
      Finset.sum_le_sum (fun y _ => card_nonPartners_le G y)
    have h2 : ∑ y ∈ S, cutPhi n ((outsideOf G y).card : ℝ)
        = (A + 2 * K) * (21 * n / 20) - A
          - (1 / 2) * ∑ y ∈ S, ((outsideOf G y).card : ℝ) ^ 2 := by
      simp only [cutPhi]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div]
      rw [hA, hK]
      ring
    linarith
  have hcross := crossSum_ge_sub G S
  have hCS : A ^ 2 ≤ K * ∑ y ∈ S, ((outsideOf G y).card : ℝ) ^ 2 := by
    rw [hA, hK]
    exact_mod_cast sq_sum_le_card_mul_sum_sq
  have hstep : K * L - ((A + 2 * K) * (21 * n / 20) - A
      - (1 / 2) * ∑ y ∈ S, ((outsideOf G y).card : ℝ) ^ 2) ≤ crossSum G S := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hstep (by linarith : (0 : ℝ) ≤ 2 * K)
  nlinarith only [hmul, hCS]

end Nibble
