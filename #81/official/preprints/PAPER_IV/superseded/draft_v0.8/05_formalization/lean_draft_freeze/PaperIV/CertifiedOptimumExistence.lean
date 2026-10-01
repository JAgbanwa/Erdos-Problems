import PaperIV.FarRounding
import PaperI.FiniteLPDuality

/-!
# Rational optimum certificates for the Paper IV mixed model

This module instantiates the generic rational finite-LP duality kernel with the
literal `K₃/K₄` items and edge resources of `PaperIV.FarRounding`.  It removes
the last bookkeeping parameter from the final Erdős export: every finite graph
has a rational primal/dual certificate of its mixed optimum.
-/

open scoped BigOperators

namespace PaperIV.CertifiedOptimumExistence

open PaperIV.FarRounding

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev LPItem := ↥(items G)
abbrev LPResource := ↥G.edgeFinset

def lpIncidence (i : LPItem G) (e : LPResource G) : ℚ :=
  if e.1 ∈ pairs i.1 then 1 else 0

def lpGain (i : LPItem G) : ℚ := gainF ℚ i.1

theorem lpIncidence_nonneg (i : LPItem G) (e : LPResource G) :
    0 ≤ lpIncidence G i e := by
  unfold lpIncidence
  split <;> norm_num

theorem exists_lpIncidence_pos (i : LPItem G) :
    ∃ e : LPResource G, 0 < lpIncidence G i e := by
  have hitem : IsItem G i.1 := mem_items.mp i.2
  have hcard : 0 < (pairs i.1).card := by
    rw [card_pairs_of_isItem hitem]
    omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp hcard
  have heG : e ∈ G.edgeFinset := pairs_subset_edgeFinset hitem he
  exact ⟨⟨e, heG⟩, by simp [lpIncidence, he]⟩

noncomputable def fracOfLP
    (p : PaperI.FiniteLP.PrimalFeasible (lpIncidence G)) : FracPacking G ℚ where
  weight := fun K => if h : K ∈ items G then p.weight ⟨K, h⟩ else 0
  weight_nonneg := by
    intro K
    split_ifs with h
    · exact p.weight_nonnegative ⟨K, h⟩
    · exact le_rfl
  capacity := by
    intro e he
    have hp := p.capacity ⟨e, he⟩
    rw [← Finset.sum_attach]
    simpa [lpIncidence] using hp

noncomputable def dualOfLP
    (d : PaperI.FiniteLP.DualFeasible (lpIncidence G) (lpGain G)) : DualCover G ℚ where
  price := fun e => if h : e ∈ G.edgeFinset then d.price ⟨e, h⟩ else 0
  price_nonneg := by
    intro e
    split_ifs with h
    · exact d.price_nonnegative ⟨e, h⟩
    · exact le_rfl
  covers := by
    intro K hK
    let price : Sym2 V → ℚ := fun e =>
      if h : e ∈ G.edgeFinset then d.price ⟨e, h⟩ else 0
    have hpoint : ∀ e : LPResource G, d.price e = price e.1 := fun e => by
      show d.price e = if h : e.1 ∈ G.edgeFinset then d.price ⟨e.1, h⟩ else 0
      rw [dif_pos e.2]
    have hfilter : G.edgeFinset.filter (fun e => e ∈ pairs K) = pairs K := by
      rw [Finset.filter_mem_eq_inter]
      exact Finset.inter_eq_right.2 (pairs_subset_edgeFinset (mem_items.mp hK))
    calc
      gainF ℚ K = lpGain G ⟨K, hK⟩ := rfl
      _ ≤ ∑ e : LPResource G, lpIncidence G ⟨K, hK⟩ e * d.price e :=
            d.demand ⟨K, hK⟩
      _ = ∑ e : LPResource G,
          (if e.1 ∈ pairs K then price e.1 else 0) := by
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [hpoint]
            simp [lpIncidence]
      _ = ∑ e ∈ G.edgeFinset, (if e ∈ pairs K then price e else 0) := by
            rw [Finset.univ_eq_attach]
            exact Finset.sum_attach G.edgeFinset
              (fun e => if e ∈ pairs K then price e else 0)
      _ = ∑ e ∈ pairs K, price e := by
            rw [← Finset.sum_filter, hfilter]

theorem fracOfLP_value
    (p : PaperI.FiniteLP.PrimalFeasible (lpIncidence G)) :
    (fracOfLP G p).value = PaperI.FiniteLP.primalValue (lpGain G) p := by
  rw [FracPacking.value, PaperI.FiniteLP.primalValue, ← Finset.sum_attach]
  simp [fracOfLP, lpGain]

theorem dualOfLP_value
    (d : PaperI.FiniteLP.DualFeasible (lpIncidence G) (lpGain G)) :
    (dualOfLP G d).value = PaperI.FiniteLP.dualValue d := by
  rw [DualCover.value, PaperI.FiniteLP.dualValue, Finset.univ_eq_attach]
  calc
    ∑ e ∈ G.edgeFinset, (dualOfLP G d).price e =
        ∑ e ∈ G.edgeFinset.attach, (dualOfLP G d).price e.1 :=
      (Finset.sum_attach G.edgeFinset (fun e => (dualOfLP G d).price e)).symm
    _ = ∑ e ∈ G.edgeFinset.attach, d.price e := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [dualOfLP]
      rw [dif_pos e.2]

/-- Every finite graph has an attained rational primal/dual optimum certificate
for the literal mixed `K₃/K₄` program used throughout Paper IV. -/
theorem exists_certifiedFractionalOptimum :
    ∃ w : ℚ, CertifiedFractionalOptimum G w := by
  obtain ⟨p, d, heq, -, -⟩ :=
    PaperI.FiniteLP.exists_optimal_pair (Item := LPItem G) (Resource := LPResource G)
      (lpIncidence G) (lpGain G)
      (lpIncidence_nonneg G) (exists_lpIncidence_pos G)
  refine ⟨PaperI.FiniteLP.primalValue (lpGain G) p, fracOfLP G p, dualOfLP G d, ?_, ?_⟩
  · exact fracOfLP_value G p
  · rw [dualOfLP_value, ← heq]

end PaperIV.CertifiedOptimumExistence
