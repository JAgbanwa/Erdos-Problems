import PaperIV.NibblePort
import Nibble.FracNibbleLE

/-!
# Adapter to Paper III's bounded-rank nibble with slack

Unlike the near-perfect interface, this theorem requires no lower load and no
exceptional set.  It is the appropriate certified input after the RC01
physical schedule.  The price is the explicit additive term
`β * |W| + C`, which is admissible for the quadratic RC01 budget.
-/

namespace PaperIV.PaperIIISlackNibbleAdapter

open Finset

/-- Paper III's `fracNibble_leUniform`, restated with Paper IV's local
matching structure and with the load written as the literal filtered sum. -/
theorem boundedRankNibbleAt (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W]
        (H : Finset (Finset W)) (w : Finset W → ℝ),
        (∀ T ∈ H, T.Nonempty ∧ T.card ≤ r) →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ x z : W, x ≠ z →
          ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        ∃ M : Finset (Finset W),
          PaperIV.NibblePort.Hypergraph.IsMatching H M ∧
          (1 - β) * (∑ T ∈ H, w T) - β * (Fintype.card W : ℝ) - C
            ≤ (M.card : ℝ) := by
  obtain ⟨γ, hγ, C, hC, hmain⟩ := Nibble.fracNibble_leUniform r hr β hβ
  refine ⟨γ, hγ, C, hC, ?_⟩
  intro W _ _ H w hsize hnonneg hload hcodeg
  have hload' : ∀ v : W, Nibble.Slack.wLoad H w v ≤ 1 := by
    simpa [Nibble.Slack.wLoad] using hload
  obtain ⟨M, hM, hcard⟩ := hmain H w hsize hnonneg hload' hcodeg
  exact ⟨M, ⟨hM.subset, hM.disjoint⟩, hcard⟩

end PaperIV.PaperIIISlackNibbleAdapter
