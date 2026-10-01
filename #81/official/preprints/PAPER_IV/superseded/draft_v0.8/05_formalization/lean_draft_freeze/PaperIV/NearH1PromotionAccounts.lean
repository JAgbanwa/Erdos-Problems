import PaperIV.RootEdgeSplit

/-! # Literal accounting under root promotion -/

namespace PaperIV.NearH1PromotionAccounts

open Finset PaperIV.RootVocab

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Enlarging the root shrinks its exterior. -/
theorem outsideVertices_mono {P Q : Finset V} (hPQ : P ⊆ Q) :
    outsideVertices Q ⊆ outsideVertices P := by
  intro x hx
  exact mem_outsideVertices.mpr fun hxP => (mem_outsideVertices.mp hx) (hPQ hxP)

/-- La misma monotonía, en forma de no-pertenencia. -/
theorem notMem_of_notMem_of_subset {P Q : Finset V} (hPQ : P ⊆ Q) {x : V} (hx : x ∉ Q) :
    x ∉ P := fun h => hx (hPQ h)

/-- Enlarging the root can only remove edges from its induced exterior. -/
theorem outsideEdges_mono_of_root_subset {P₀ P : Finset V} (h : P₀ ⊆ P) :
    outsideEdges G P ⊆ outsideEdges G P₀ := by
  intro e he
  obtain ⟨heG, heOut⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨heG, fun x hx =>
    outsideVertices_mono h (heOut hx)⟩

/-- Old missing columns shrink under promotion. -/
theorem missingColumn_mono_of_root_subset {P₀ P : Finset V} (h : P₀ ⊆ P)
    {x : V} (hx : x ∈ P₀) :
    missingColumn G P x ⊆ missingColumn G P₀ x := by
  intro y hy
  have hy' := mem_missingColumn.mp hy
  exact mem_missingColumn.mpr ⟨notMem_of_notMem_of_subset h hy'.1, hy'.2⟩

/-- The final missing-incidence mass is the old mass plus at most one
maximum-column charge for each promoted root vertex. -/
theorem missingIncidences_le_add_promoted_mul
    {P₀ P : Finset V} (hsub : P₀ ⊆ P) {D : ℕ}
    (hD : ∀ x ∈ P, (missingColumn G P x).card ≤ D) :
    missingIncidences G P ≤
      missingIncidences G P₀ + (P.card - P₀.card) * D := by
  rw [← sum_card_missingColumn, ← sum_card_missingColumn]
  have hOld :
      (∑ x ∈ P₀, (missingColumn G P x).card) ≤
        ∑ x ∈ P₀, (missingColumn G P₀ x).card := by
    exact Finset.sum_le_sum fun x hx =>
      Finset.card_le_card (missingColumn_mono_of_root_subset hsub hx)
  have hNew :
      (∑ x ∈ P \ P₀, (missingColumn G P x).card) ≤
        ∑ _x ∈ P \ P₀, D := by
    exact Finset.sum_le_sum fun x hx => hD x (Finset.mem_sdiff.mp hx).1
  calc
    ∑ x ∈ P, (missingColumn G P x).card =
        (∑ x ∈ P₀, (missingColumn G P x).card) +
          ∑ x ∈ P \ P₀, (missingColumn G P x).card := by
            rw [← Finset.sum_sdiff hsub]
            omega
    _ ≤ (∑ x ∈ P₀, (missingColumn G P₀ x).card) +
          ∑ _x ∈ P \ P₀, D := by
            exact Nat.add_le_add hOld hNew
    _ = (∑ x ∈ P₀, (missingColumn G P₀ x).card) +
          (P.card - P₀.card) * D := by
            simp [Finset.card_sdiff_of_subset hsub, Nat.nsmul_eq_mul]

end PaperIV.NearH1PromotionAccounts
