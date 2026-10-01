import PaperIV.MarkedQuotaGate
import PaperIV.MarkedQuotaSlackGate
import PaperIV.JointTypedQuota

/-!
# RC01: from the proved marked-quota gate to the additive typed gain

`PaperIV.MarkedQuotaGate.additiveMarkedQuotaNibbleAt_proved` produces, for a
`6`-uniform near-perfect system `H` with a marked subfamily `A ⊆ H`, one matching
which keeps the total mass and the marked mass up to an additive `ε |W|`.  After
the triangle pairing, the unmarked members of `H` are *pairs* of triangles and
the marked ones are `K₄`'s, so
`PaperIV.JointTypedQuota.typed_gain_of_paired_total_and_four_quota_additive`
turns those two inequalities into the mixed typed objective
`2·triangleMass + 5·fourMass`, at a total additive cost of `5 ε |W|` (the total
error is charged four times, the marked error once).

This is the promised connection: the probabilistic residue of RC01 is now a
theorem, and the typed gain follows from it by the algebraic ledger alone.
-/

namespace PaperIV.MarkedQuotaTypedGain

open Finset

/-- **The additive typed gain of RC01, unconditionally.**  For a `6`-uniform
near-perfect fractional matching whose marked subfamily `A` consists of the `K₄`
items and whose complement consists of the paired triangles, there is one
matching realising the mixed objective `2·triangleMass + 5·fourMass` up to the
pairing loss `6` and an additive `5 ε |W|`.

The hypotheses are exactly those of Paper III's nibble plus the pairing
inequality `(triangleMass - 3)/2 ≤ pairMass` supplied by the triangle-pairing
construction. -/
theorem typed_gain_additive (β ε : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W]
        (H A : Finset (Finset W)) (w : Finset W → ℝ) (Exc : Finset W) (triangleMass : ℝ),
        A ⊆ H →
        NibblePort.Hypergraph.IsUniform H 6 →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ v : W, v ∉ Exc → 1 - γ ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
        (Exc.card : ℝ) ≤ η * (Fintype.card W : ℝ) →
        (∀ x z : W, x ≠ z →
          ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        (triangleMass - 3) / 2 ≤ ∑ T ∈ H \ A, w T →
        ∃ M : Finset (Finset W), NibblePort.Hypergraph.IsMatching H M ∧
          (1 - β) * (2 * triangleMass + 5 * (∑ T ∈ A, w T) - 6)
              - 5 * (ε * (Fintype.card W : ℝ))
            ≤ 4 * ((M.filter (fun T => T ∉ A)).card : ℝ)
              + 5 * ((M.filter (fun T => T ∈ A)).card : ℝ) := by
  classical
  obtain ⟨γ, hγ, η, hη, hgate⟩ :=
    MarkedQuotaGate.additiveMarkedQuotaNibbleAt_proved 6 (by norm_num) β ε hβ hε
  refine ⟨γ, hγ, η, hη, ?_⟩
  intro W _ _ H A w Exc triangleMass hAH huni hw hload hlow hExc hcod hpair
  obtain ⟨M, hM, htotal, hmarked⟩ :=
    hgate H A w Exc hAH huni hw hload hlow hExc hcod
  refine ⟨M, hM, ?_⟩
  have hsplit : (M.filter (fun T => T ∈ A)).card + (M.filter (fun T => T ∉ A)).card
      = M.card := Finset.card_filter_add_card_filter_not _
  have hsplitR : ((M.filter (fun T => T ∈ A)).card : ℝ)
      + ((M.filter (fun T => T ∉ A)).card : ℝ) = (M.card : ℝ) := by exact_mod_cast hsplit
  have hmass : ∑ T ∈ H, w T = (∑ T ∈ H \ A, w T) + ∑ T ∈ A, w T :=
    (Finset.sum_sdiff hAH).symm
  rw [hmass] at htotal
  have htotal' : (1 - β) * ((∑ T ∈ H \ A, w T) + ∑ T ∈ A, w T) - ε * (Fintype.card W : ℝ)
      ≤ ((M.filter (fun T => T ∉ A)).card : ℝ) + ((M.filter (fun T => T ∈ A)).card : ℝ) := by
    linarith
  have key := PaperIV.JointTypedQuota.typed_gain_of_paired_total_and_four_quota_additive
    (β := β) (triangleMass := triangleMass) (pairMass := ∑ T ∈ H \ A, w T)
    (fourMass := ∑ T ∈ A, w T)
    (outPairs := ((M.filter (fun T => T ∉ A)).card : ℝ))
    (outFour := ((M.filter (fun T => T ∈ A)).card : ℝ))
    (errTotal := ε * (Fintype.card W : ℝ)) (errFour := ε * (Fintype.card W : ℝ))
    hβ1 hpair htotal' hmarked
  linarith

/-- **The additive typed gain of RC01 over the slack nibble.**

Same conclusion as `typed_gain_additive`, but obtained from
`PaperIV.MarkedQuotaSlackGate.slackMarkedQuotaNibbleAt_proved`.  Consequently
**no lower-load hypothesis and no exceptional set** occur: the only instance
hypotheses are the upper loads, the nonnegativity of the weights, the weighted
codegree bound and the pairing inequality.  The price is the additional
additive constant `5 * C`. -/
theorem typed_gain_slack (β ε : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W]
        (H A : Finset (Finset W)) (w : Finset W → ℝ) (triangleMass : ℝ),
        A ⊆ H →
        NibblePort.Hypergraph.IsUniform H 6 →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ x z : W, x ≠ z →
          ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        (triangleMass - 3) / 2 ≤ ∑ T ∈ H \ A, w T →
        ∃ M : Finset (Finset W), NibblePort.Hypergraph.IsMatching H M ∧
          (1 - β) * (2 * triangleMass + 5 * (∑ T ∈ A, w T) - 6)
              - 5 * (ε * (Fintype.card W : ℝ)) - 5 * C
            ≤ 4 * ((M.filter (fun T => T ∉ A)).card : ℝ)
              + 5 * ((M.filter (fun T => T ∈ A)).card : ℝ) := by
  classical
  obtain ⟨γ, hγ, C, hC, hgate⟩ :=
    MarkedQuotaSlackGate.slackMarkedQuotaNibbleAt_proved 6 (by norm_num) β ε hβ hε
  refine ⟨γ, hγ, C, hC, ?_⟩
  intro W _ _ H A w triangleMass hAH huni hw hload hcod hpair
  obtain ⟨M, hM, htotal, hmarked⟩ := hgate H A w hAH huni hw hload hcod
  refine ⟨M, hM, ?_⟩
  have hsplit : (M.filter (fun T => T ∈ A)).card + (M.filter (fun T => T ∉ A)).card
      = M.card := Finset.card_filter_add_card_filter_not _
  have hsplitR : ((M.filter (fun T => T ∈ A)).card : ℝ)
      + ((M.filter (fun T => T ∉ A)).card : ℝ) = (M.card : ℝ) := by exact_mod_cast hsplit
  have hmass : ∑ T ∈ H, w T = (∑ T ∈ H \ A, w T) + ∑ T ∈ A, w T :=
    (Finset.sum_sdiff hAH).symm
  rw [hmass] at htotal
  have htotal' : (1 - β) * ((∑ T ∈ H \ A, w T) + ∑ T ∈ A, w T)
        - (ε * (Fintype.card W : ℝ) + C)
      ≤ ((M.filter (fun T => T ∉ A)).card : ℝ) + ((M.filter (fun T => T ∈ A)).card : ℝ) := by
    linarith
  have hmarked' : (1 - β) * (∑ T ∈ A, w T) - (ε * (Fintype.card W : ℝ) + C)
      ≤ ((M.filter (fun T => T ∈ A)).card : ℝ) := by linarith
  have key := PaperIV.JointTypedQuota.typed_gain_of_paired_total_and_four_quota_additive
    (β := β) (triangleMass := triangleMass) (pairMass := ∑ T ∈ H \ A, w T)
    (fourMass := ∑ T ∈ A, w T)
    (outPairs := ((M.filter (fun T => T ∉ A)).card : ℝ))
    (outFour := ((M.filter (fun T => T ∈ A)).card : ℝ))
    (errTotal := ε * (Fintype.card W : ℝ) + C)
    (errFour := ε * (Fintype.card W : ℝ) + C)
    hβ1 hpair htotal' hmarked'
  linarith

end PaperIV.MarkedQuotaTypedGain

