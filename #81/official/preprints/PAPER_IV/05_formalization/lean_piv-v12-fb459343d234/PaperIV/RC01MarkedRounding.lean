import PaperIV.JointTwoQuotaPhysical
import PaperIV.LowTriangleReduction

/-!
# RC01: from the marked physical selector to the rounding inequality

This module discharges the numerical tail after the mixed selector.  It does
not assume a rounding theorem.  Its only instance hypotheses are precisely
the near-perfect load, exceptional-set, codegree and triangle-mass estimates
which the RC01 regularity construction must supply.
-/

namespace PaperIV.RC01MarkedRounding

open Finset
open MixedRounding
open PaperIV.JointTwoQuotaPhysical

/-- The marker universe used by the additive nibble has at most `n²` elements
as soon as `n ≥ 1`.  We intentionally keep the diagonal pairs here: this is
the larger universe used by the proved marked-quota theorem. -/
theorem card_sym2_fin_le_sq {n : ℕ} (hn : 1 ≤ n) :
    (Fintype.card (Sym2 (Fin n)) : ℝ) ≤ (n : ℝ) ^ 2 := by
  rw [Sym2.card, Fintype.card_fin, Nat.cast_choose_two]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  norm_num
  nlinarith

/-- The two real masses used by the marked selector are exactly the rational
mixed LP objective after coercion. -/
theorem value_cast_eq_masses {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (x : FracPacking G) :
    ((x.value : ℚ) : ℝ) = 2 * triangleMass x + 5 * fourCliqueMass x := by
  have h := congrArg (fun q : ℚ => (q : ℝ))
    (PaperIV.LowTriangleReduction.value_eq_masses x)
  have htri : (((PaperIV.LowTriangleReduction.triMass x : ℚ) : ℝ))
      = triangleMass x := by
    rw [PaperIV.LowTriangleReduction.triMass, triangleMass]
    push_cast
    rfl
  have hquad : (((PaperIV.LowTriangleReduction.quadMass x : ℚ) : ℝ))
      = fourCliqueMass x := by
    rw [PaperIV.LowTriangleReduction.quadMass, fourCliqueMass]
    push_cast
    rfl
  norm_num [htri, hquad] at h
  exact h

/-- **The complete numerical tail of the marked RC01 selector.**

The displayed budget is deliberately exact.  It separates the only four
losses left after the physical construction: the multiplicative loss `β`,
the constant `6` caused by pairing triangles, the additive marked-quota loss,
and the requested target `ζ n²`.  No rounding or transfer hypothesis occurs
in the statement. -/
theorem exists_packing_loss_le_of_markedQuotaBudget
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (x : FracPacking G) (β ε ζ : ℝ)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hε : 0 < ε)
    (hbudget :
      β * ((5 / 12 : ℝ) * (n : ℝ) ^ 2) + 6 * (1 - β)
          + 5 * (ε * (Fintype.card (Sym2 (Fin n)) : ℝ))
        ≤ ζ * (n : ℝ) ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (Exc : Finset (Sym2 (Fin n))),
        (∀ e : Sym2 (Fin n), e ∉ Exc → 1 - γ ≤
          ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter (fun S => e ∈ S),
            MixedRounding.inducedWeight x S) →
        (Exc.card : ℝ) ≤ η * (Fintype.card (Sym2 (Fin n)) : ℝ) →
        (∀ e f : Sym2 (Fin n), e ≠ f →
          ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter
              (fun S => e ∈ S ∧ f ∈ S),
            MixedRounding.inducedWeight x S ≤ γ) →
        C ≤ triangleMass x →
        ∃ P : Packing G,
          (((x.value : ℚ) : ℝ) - (P.gain : ℝ)) ≤ ζ * (n : ℝ) ^ 2 := by
  obtain ⟨γ, hγ, η, hη, C, hC, hselect⟩ :=
    mixed_physical_packing_of_markedQuota β ε hβ hβ1 hε
  refine ⟨γ, hγ, η, hη, C, hC, ?_⟩
  intro Exc hload hExc hcodeg hmass
  obtain ⟨P, hP⟩ := hselect (Fin n) G x Exc hload hExc hcodeg hmass
  refine ⟨P, ?_⟩
  have hvalueQ := PaperIV.UniformDual.value_le_of_card
    (PaperIV.MixedRoundingAdapter.toFarFrac x)
  rw [PaperIV.MixedRoundingAdapter.value_toFarFrac] at hvalueQ
  have hvalue : ((x.value : ℚ) : ℝ) ≤ (5 / 12 : ℝ) * (n : ℝ) ^ 2 := by
    have h := (Rat.cast_le (K := ℝ)).2 hvalueQ
    norm_num at h ⊢
    exact h
  have hβvalue : β * ((x.value : ℚ) : ℝ)
      ≤ β * ((5 / 12 : ℝ) * (n : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hvalue hβ.le
  have hsplit := value_cast_eq_masses x
  nlinarith

/-- **RC01 marked rounding with an explicit parameter schedule.**

Take `β = ζ/4` and additive error `ε = ζ/20`.  For `12 ≤ ζ n²`, the
constant pairing loss and the marker universe both fit inside the target
`ζ n²`.  Consequently only the three genuine instance estimates remain:
near-perfect load outside a small exceptional set, small codegree, and a
constant lower bound on triangle mass. -/
theorem exists_packing_loss_le_of_markedQuota
    (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (x : FracPacking G) (Exc : Finset (Sym2 (Fin n))),
        12 ≤ ζ * (n : ℝ) ^ 2 →
        (∀ e : Sym2 (Fin n), e ∉ Exc → 1 - γ ≤
          ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter (fun S => e ∈ S),
            MixedRounding.inducedWeight x S) →
        (Exc.card : ℝ) ≤ η * (Fintype.card (Sym2 (Fin n)) : ℝ) →
        (∀ e f : Sym2 (Fin n), e ≠ f →
          ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter
              (fun S => e ∈ S ∧ f ∈ S),
            MixedRounding.inducedWeight x S ≤ γ) →
        C ≤ triangleMass x →
        ∃ P : Packing G,
          (((x.value : ℚ) : ℝ) - (P.gain : ℝ)) ≤ ζ * (n : ℝ) ^ 2 := by
  have hβ : (0 : ℝ) < ζ / 4 := by positivity
  have hβ1 : ζ / 4 ≤ (1 : ℝ) := by linarith
  have hε : (0 : ℝ) < ζ / 20 := by positivity
  obtain ⟨γ, hγ, η, hη, C, hC, hselect⟩ :=
    mixed_physical_packing_of_markedQuota (ζ / 4) (ζ / 20) hβ hβ1 hε
  refine ⟨γ, hγ, η, hη, C, hC, ?_⟩
  intro n hn G _ x Exc hsize hload hExc hcodeg hmass
  have hcard := card_sym2_fin_le_sq hn
  have hcard' : (ζ / 4) * (Fintype.card (Sym2 (Fin n)) : ℝ)
      ≤ (ζ / 4) * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hcard (by positivity)
  have hbudget :
      (ζ / 4) * ((5 / 12 : ℝ) * (n : ℝ) ^ 2) + 6 * (1 - ζ / 4)
          + 5 * ((ζ / 20) * (Fintype.card (Sym2 (Fin n)) : ℝ))
        ≤ ζ * (n : ℝ) ^ 2 := by
    nlinarith
  obtain ⟨P, hP⟩ := hselect (Fin n) G x Exc hload hExc hcodeg hmass
  refine ⟨P, ?_⟩
  have hvalueQ := PaperIV.UniformDual.value_le_of_card
    (PaperIV.MixedRoundingAdapter.toFarFrac x)
  rw [PaperIV.MixedRoundingAdapter.value_toFarFrac] at hvalueQ
  have hvalue : ((x.value : ℚ) : ℝ) ≤ (5 / 12 : ℝ) * (n : ℝ) ^ 2 := by
    have h := (Rat.cast_le (K := ℝ)).2 hvalueQ
    norm_num at h ⊢
    exact h
  have hβvalue : (ζ / 4) * ((x.value : ℚ) : ℝ)
      ≤ (ζ / 4) * ((5 / 12 : ℝ) * (n : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hvalue hβ.le
  have hsplit := value_cast_eq_masses x
  nlinarith

/-- **The complete numerical tail of the slack marked RC01 selector.**

Same budget as `exists_packing_loss_le_of_markedQuotaBudget`, plus the additive
slack constant `5 * D`, and with **no lower-load and no exceptional-set
hypothesis**: the upper load is automatic, and only the weighted codegree bound
and the constant triangle-mass bound remain. -/
theorem exists_packing_loss_le_of_slackMarkedQuotaBudget
    (β ε ζ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (x : FracPacking G),
        β * ((5 / 12 : ℝ) * (n : ℝ) ^ 2) + 6 * (1 - β)
            + 5 * (ε * (Fintype.card (Sym2 (Fin n)) : ℝ)) + 5 * D
          ≤ ζ * (n : ℝ) ^ 2 →
        (∀ e f : Sym2 (Fin n), e ≠ f →
          ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter
              (fun S => e ∈ S ∧ f ∈ S),
            MixedRounding.inducedWeight x S ≤ γ) →
        C ≤ triangleMass x →
        ∃ P : Packing G,
          (((x.value : ℚ) : ℝ) - (P.gain : ℝ)) ≤ ζ * (n : ℝ) ^ 2 := by
  obtain ⟨γ, hγ, C, hC, D, hD, hselect⟩ :=
    mixed_physical_packing_of_slackMarkedQuota β ε hβ hβ1 hε
  refine ⟨γ, hγ, C, hC, D, hD, ?_⟩
  intro n G _ x hbudget hcodeg hmass
  obtain ⟨P, hP⟩ := hselect (Fin n) G x hcodeg hmass
  refine ⟨P, ?_⟩
  have hvalueQ := PaperIV.UniformDual.value_le_of_card
    (PaperIV.MixedRoundingAdapter.toFarFrac x)
  rw [PaperIV.MixedRoundingAdapter.value_toFarFrac] at hvalueQ
  have hvalue : ((x.value : ℚ) : ℝ) ≤ (5 / 12 : ℝ) * (n : ℝ) ^ 2 := by
    have h := (Rat.cast_le (K := ℝ)).2 hvalueQ
    norm_num at h ⊢
    exact h
  have hβvalue : β * ((x.value : ℚ) : ℝ)
      ≤ β * ((5 / 12 : ℝ) * (n : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hvalue hβ.le
  have hsplit := value_cast_eq_masses x
  nlinarith

/-- **RC01 slack marked rounding with an explicit parameter schedule.**

As `exists_packing_loss_le_of_markedQuota`, with `β = ζ/4` and additive error
`ε = ζ/20`, but over the bounded-rank slack nibble.  The size condition absorbs
the slack constant as well (`12 + 10 D ≤ ζ n²`), and the only remaining
instance estimates are the weighted codegree bound and the constant lower bound
on the triangle mass: **no lower load, no exceptional set**. -/
theorem exists_packing_loss_le_of_slackMarkedQuota
    (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (x : FracPacking G),
        12 + 10 * D ≤ ζ * (n : ℝ) ^ 2 →
        (∀ e f : Sym2 (Fin n), e ≠ f →
          ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter
              (fun S => e ∈ S ∧ f ∈ S),
            MixedRounding.inducedWeight x S ≤ γ) →
        C ≤ triangleMass x →
        ∃ P : Packing G,
          (((x.value : ℚ) : ℝ) - (P.gain : ℝ)) ≤ ζ * (n : ℝ) ^ 2 := by
  have hβ : (0 : ℝ) < ζ / 4 := by positivity
  have hβ1 : ζ / 4 ≤ (1 : ℝ) := by linarith
  have hε : (0 : ℝ) < ζ / 20 := by positivity
  obtain ⟨γ, hγ, C, hC, D, hD, hselect⟩ :=
    mixed_physical_packing_of_slackMarkedQuota (ζ / 4) (ζ / 20) hβ hβ1 hε
  refine ⟨γ, hγ, C, hC, D, hD, ?_⟩
  intro n hn G _ x hsize hcodeg hmass
  have hcard := card_sym2_fin_le_sq hn
  obtain ⟨P, hP⟩ := hselect (Fin n) G x hcodeg hmass
  refine ⟨P, ?_⟩
  have hvalueQ := PaperIV.UniformDual.value_le_of_card
    (PaperIV.MixedRoundingAdapter.toFarFrac x)
  rw [PaperIV.MixedRoundingAdapter.value_toFarFrac] at hvalueQ
  have hvalue : ((x.value : ℚ) : ℝ) ≤ (5 / 12 : ℝ) * (n : ℝ) ^ 2 := by
    have h := (Rat.cast_le (K := ℝ)).2 hvalueQ
    norm_num at h ⊢
    exact h
  have hβvalue : (ζ / 4) * ((x.value : ℚ) : ℝ)
      ≤ (ζ / 4) * ((5 / 12 : ℝ) * (n : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hvalue hβ.le
  have hcard' : (ζ / 4) * (Fintype.card (Sym2 (Fin n)) : ℝ)
      ≤ (ζ / 4) * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hcard (by positivity)
  have hsplit := value_cast_eq_masses x
  nlinarith

end PaperIV.RC01MarkedRounding
