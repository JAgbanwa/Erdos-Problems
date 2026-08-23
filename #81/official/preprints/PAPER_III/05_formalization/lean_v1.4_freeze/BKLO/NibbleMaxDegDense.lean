/-
# The dense-regime max-degree nibble input, and its use-site sufficiency

`BKLO.FracToApproxMaxDeg` (Input 2′) is **false as a general statement** — the `K₄`-book witnesses a
fractionally triangle-decomposable graph whose every approximate decomposition leaves a vertex of
degree `Ω(|V|)`.  But the AX2 chain never applies it outside the dense regime: in
`BKLO.nibbleMaxDeg_of_inputs` the only application is to `setGraph S E` with
`∀ v ∈ S, (9/10)|S| ≤ edeg E v`, i.e. minimum degree `≥ (9/10)|V|`.

This file records the honest input actually needed — the **dense** max-degree nibble — and proves it
suffices at that site (`nibbleMaxDeg_of_inputs_dense`), so the general (false) `FracToApproxMaxDeg`
can be replaced by the dense form throughout.  The dense form is discharged separately from the
proved packing engine `Nibble.nibbleTheoremMost_holds` by a Rödl iteration on the triangle
hypergraph (that discharge lives where both libraries are visible).

Everything here is `sorry`-free.
-/
import BKLO.NibbleMaxDeg

open Finset

namespace BKLO

/-- **Input 2′ (dense form).**  For every `η > 0` and every large `G` that is fractionally
triangle-decomposable **and** dense (`minDegree ≥ (9/10)|V|`), there is an approximate triangle
decomposition whose leftover has maximum degree at most `η|V|`.  Unlike `FracToApproxMaxDeg` this is
true — the density hypothesis is exactly what the `K₄`-book counterexample lacks, and it is available
at every use site in the AX2 chain. -/
def FracToApproxMaxDegDense : Prop :=
  ∀ η : ℝ, 0 < η → ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → FracTriangleDecomposable G →
      (9 / 10 : ℝ) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
      ∃ parts : Finset (Finset V), IsApproxTriangleDecompMaxDeg G parts η

/-- **The minimum degree of `setGraph S E` from the edge-degree hypothesis.**  Extracted from the
inline argument of `BKLO.fracTriangleDecomposable_setGraph`. -/
theorem minDegree_setGraph_ge {V : Type} [DecidableEq V] {S : Finset V} {E : Finset (Sym2 V)}
    (hSne : S.Nonempty) (hE : E ⊆ cliqueEdges S)
    (hdeg : ∀ v ∈ S, (9 / 10 : ℝ) * S.card ≤ edeg E v) :
    (9 / 10 : ℝ) * (Fintype.card {x // x ∈ S} : ℝ) ≤ ((setGraph S E).minDegree : ℝ) := by
  classical
  have hne : Nonempty {x // x ∈ S} := ⟨⟨hSne.choose, hSne.choose_spec⟩⟩
  obtain ⟨a, ha⟩ := (setGraph S E).exists_minimal_degree_vertex
  rw [card_coe_eq, ha]
  rw [degree_setGraph hE a]
  exact_mod_cast hdeg (a : V) a.2

/-- **The dense form suffices at the use site.**  Word for word `BKLO.nibbleMaxDeg_of_inputs`, but
consuming the *dense* input `FracToApproxMaxDegDense` instead of the general `FracToApproxMaxDeg`.
The density hypothesis it needs is exactly the minimum-degree hypothesis already present:
`∀ v ∈ S, (9/10)|S| ≤ edeg E v` gives `minDegree (setGraph S E) ≥ (9/10)|S|`. -/
theorem nibbleMaxDeg_of_inputs_dense
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDegDense)
    {η : ℝ} (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ {V : Type} [DecidableEq V] (S : Finset V) (E : Finset (Sym2 V)),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → (∀ v ∈ S, (9 / 10 : ℝ) * S.card ≤ edeg E v) →
      ∃ P : Finset (Finset V), TriFamilyIn E P ∧
        ∀ v : V, (edeg (E \ famEdges P) v : ℝ) ≤ η * (S.card : ℝ) := by
  classical
  obtain ⟨n₀, hn₀⟩ := hNib η hη
  refine ⟨max n₀ 1, ?_⟩
  intro V _ S E hcard hE hdeg
  have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨parts, hcl, hdisj, hlef⟩ :=
    hn₀ (setGraph S E) (by rw [card_coe_eq]; omega)
      (fracTriangleDecomposable_setGraph hDross hE hdeg)
      (minDegree_setGraph_ge hSne hE hdeg)
  refine ⟨parts.image (fun t => t.image Subtype.val), triFamilyIn_image_val hE hcl hdisj, ?_⟩
  intro v
  by_cases hv : v ∈ S
  · have h := hlef ⟨v, hv⟩
    rw [card_coe_eq] at h
    rw [edeg_sdiff_famEdges_image_val hE parts ⟨v, hv⟩]
    exact h
  · have hsub : E \ famEdges (parts.image (fun t => t.image Subtype.val)) ⊆ cliqueEdges S :=
      (Finset.sdiff_subset).trans hE
    rw [edeg_eq_zero_of_notMem hsub hv]
    have : (0:ℝ) ≤ η * (S.card : ℝ) := by positivity
    simpa using this

end BKLO
