import PaperIV.PaperIIINibbleAdapter

/-!
# RC01: the minimal marked-quota nibble residue

After pairing two triangles into one six-resource item, the typed objective
only needs two lower bounds on the same matching: its total cardinality and the
number of selected members of one marked subfamily.  It does **not** need a
separate lower bound for the complement of that subfamily.

This file states that smaller residue and proves its two boundary cases from
the frozen Paper III nibble.  The general marked case remains the probabilistic
gate.
-/

namespace PaperIV.MarkedQuotaNibble

open Finset

/-- The total quota of Paper III plus one marked-subfamily quota. -/
def MarkedQuotaConclusion {W : Type*} [DecidableEq W]
    (H A M : Finset (Finset W)) (w : Finset W → ℝ) (β : ℝ) : Prop :=
  NibblePort.Hypergraph.IsMatching H M ∧
    (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ) ∧
    (1 - β) * (∑ T ∈ A, w T) ≤ ((M.filter (fun T => T ∈ A)).card : ℝ)

/-- The minimal single-rank probabilistic obligation left by the triangle
pairing reduction: preserve total mass and one marked mass simultaneously. -/
def MarkedQuotaNibbleAt (r : ℕ) (β : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {W : Type} [Fintype W] [DecidableEq W]
      (H A : Finset (Finset W)) (w : Finset W → ℝ) (Exc : Finset W),
      A ⊆ H →
      NibblePort.Hypergraph.IsUniform H r →
      (∀ T, 0 ≤ w T) →
      (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
      (∀ v : W, v ∉ Exc → 1 - γ ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
      (Exc.card : ℝ) ≤ η * (Fintype.card W : ℝ) →
      (∀ x z : W, x ≠ z →
        ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
      ∃ M : Finset (Finset W), MarkedQuotaConclusion H A M w β

/-- The asymptotically sufficient weakening: the marked quota may lose an
additive `ε |W|`.  This is the natural coloured-nibble target when the marked
mass is small; demanding a multiplicative approximation to an arbitrarily
small colour class is unnecessary for RC01. -/
def AdditiveMarkedQuotaConclusion {W : Type*} [Fintype W] [DecidableEq W]
    (H A M : Finset (Finset W)) (w : Finset W → ℝ) (β ε : ℝ) : Prop :=
  NibblePort.Hypergraph.IsMatching H M ∧
    (1 - β) * (∑ T ∈ H, w T) - ε * (Fintype.card W : ℝ) ≤ (M.card : ℝ) ∧
    (1 - β) * (∑ T ∈ A, w T) - ε * (Fintype.card W : ℝ)
      ≤ ((M.filter (fun T => T ∈ A)).card : ℝ)

/-- Minimal additive marked-colour nibble required by the asymptotic route. -/
def AdditiveMarkedQuotaNibbleAt (r : ℕ) (β ε : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {W : Type} [Fintype W] [DecidableEq W]
      (H A : Finset (Finset W)) (w : Finset W → ℝ) (Exc : Finset W),
      A ⊆ H →
      NibblePort.Hypergraph.IsUniform H r →
      (∀ T, 0 ≤ w T) →
      (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
      (∀ v : W, v ∉ Exc → 1 - γ ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
      (Exc.card : ℝ) ≤ η * (Fintype.card W : ℝ) →
      (∀ x z : W, x ≠ z →
        ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
      ∃ M : Finset (Finset W), AdditiveMarkedQuotaConclusion H A M w β ε

/-- The previously isolated multiplicative gate implies the additive one for
every nonnegative error parameter. -/
theorem additiveMarkedQuotaNibbleAt_of_markedQuotaNibbleAt
    {r : ℕ} {β ε : ℝ} (h : MarkedQuotaNibbleAt r β) (hε : 0 ≤ ε) :
    AdditiveMarkedQuotaNibbleAt r β ε := by
  classical
  obtain ⟨γ, hγ, η, hη, hmain⟩ := h
  refine ⟨γ, hγ, η, hη, ?_⟩
  intro W _ _ H A w Exc hAH huni hw hload hlow hExc hcod
  obtain ⟨M, hmatch, htotal, hmarked⟩ :=
    hmain H A w Exc hAH huni hw hload hlow hExc hcod
  refine ⟨M, hmatch, ?_, ?_⟩
  · exact le_trans (sub_le_self _ (mul_nonneg hε (Nat.cast_nonneg _))) htotal
  · exact le_trans (sub_le_self _ (mul_nonneg hε (Nat.cast_nonneg _))) hmarked

/-- The exact objective bridge for the paired system: every selected six-set
is worth four units, and membership in the marked `K₄` family contributes one
additional unit.  Two additive quota errors of size `ε |W|` therefore cost
only `5 ε |W|` in the physical gain. -/
theorem weightedGain_of_additiveMarkedQuotaConclusion
    {W : Type*} [Fintype W] [DecidableEq W]
    {H A M : Finset (Finset W)} {w : Finset W → ℝ} {β ε : ℝ}
    (h : AdditiveMarkedQuotaConclusion H A M w β ε) :
    (1 - β) *
          (4 * (∑ T ∈ H, w T) + (∑ T ∈ A, w T))
        - 5 * ε * (Fintype.card W : ℝ)
      ≤ 4 * (M.card : ℝ)
        + ((M.filter (fun T => T ∈ A)).card : ℝ) := by
  rcases h with ⟨-, htotal, hmarked⟩
  linarith

/-- At the empty marked family, the marked residue is exactly the Paper III
total-mass conclusion plus a vacuous inequality. -/
theorem markedQuota_bot (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W]
        (H : Finset (Finset W)) (w : Finset W → ℝ) (Exc : Finset W),
        NibblePort.Hypergraph.IsUniform H r →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ v : W, v ∉ Exc → 1 - γ ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
        (Exc.card : ℝ) ≤ η * (Fintype.card W : ℝ) →
        (∀ x z : W, x ≠ z →
          ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        ∃ M : Finset (Finset W), MarkedQuotaConclusion H ∅ M w β := by
  classical
  obtain ⟨γ, hγ, η, hη, hmain⟩ :=
    PaperIIINibbleAdapter.nearPerfectNibbleAt r hr β hβ
  refine ⟨γ, hγ, η, hη, ?_⟩
  intro W _ _ H w Exc huni hw hload hlow hExc hcod
  obtain ⟨M, hM, -, hmass⟩ := hmain H w Exc huni hw hload hlow hExc hcod
  refine ⟨M, hM, hmass, ?_⟩
  simp

/-- At the full marked family, the same Paper III total-mass inequality serves
as both required quotas. -/
theorem markedQuota_top (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W]
        (H : Finset (Finset W)) (w : Finset W → ℝ) (Exc : Finset W),
        NibblePort.Hypergraph.IsUniform H r →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ v : W, v ∉ Exc → 1 - γ ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
        (Exc.card : ℝ) ≤ η * (Fintype.card W : ℝ) →
        (∀ x z : W, x ≠ z →
          ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        ∃ M : Finset (Finset W), MarkedQuotaConclusion H H M w β := by
  classical
  obtain ⟨γ, hγ, η, hη, hmain⟩ :=
    PaperIIINibbleAdapter.nearPerfectNibbleAt r hr β hβ
  refine ⟨γ, hγ, η, hη, ?_⟩
  intro W _ _ H w Exc huni hw hload hlow hExc hcod
  obtain ⟨M, hM, -, hmass⟩ := hmain H w Exc huni hw hload hlow hExc hcod
  have hfilter : M.filter (fun T => T ∈ H) = M :=
    Finset.filter_true_of_mem fun T hT => hM.subset hT
  refine ⟨M, hM, hmass, ?_⟩
  rw [hfilter]
  exact hmass

end PaperIV.MarkedQuotaNibble
