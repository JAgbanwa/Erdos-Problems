/-
# `boundedLeftover_confined` — the bounded-CORE absorber (Interface B, standalone)

Extracted `sorry`-free from the absorber development (job 1f978435's `BoundedLeftoverMain.lean`,
whose only `sorry` was the unrelated spread cover-down).  This is the achievable half of the §8
absorber: for a leftover confined to a bounded vertex set `U` (`|U| ≤ C`) — exactly what the vortex
delivers per constant-size cell — a low-degree reservoir `R` (`Δ(R) ≤ γ|S|`, even degrees) absorbs
every even `H ⊆ E \ R` inside `U`.  Built from the proved `coreAbsorberExistence_holds` and the
cover-down reduction `triDecomp_of_coverDown`.
-/
import BKLO.CoreAbsorberExists
import BKLO.CoverDownReduction

open Finset

namespace BKLO

/-- **The bounded-core absorber (Interface B).**  For a leftover confined to a bounded set `U`, a
reservoir `R ⊆ E` of even degrees and maximum degree `≤ γ|S|` absorbs every even `H ⊆ E \ R` inside
`U` with `3 ∣ |R ∪ H|`. -/
theorem boundedLeftover_confined (γ : ℝ) (hγ : 0 < γ) (C : ℕ) : ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S U : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → U ⊆ S → U.card ≤ C →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ R : Finset (Sym2 V), R ⊆ E ∧ EvenDegrees R ∧
        (∀ v : V, (edeg R v : ℝ) ≤ γ * (S.card : ℝ)) ∧
        ∀ H : Finset (Sym2 V), H ⊆ E \ R → H ⊆ cliqueEdges U → EvenDegrees H →
          3 ∣ (R ∪ H).card → TriDecomp (R ∪ H) := by
  classical
  obtain ⟨n₀, hca⟩ := coreAbsorberExistence_holds C γ hγ
  refine ⟨n₀, ?_⟩
  intro V _ E S U hn hES hUS hUC hdeg
  have hSnn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  obtain ⟨R₂, hR₂E, hR₂deg, hcore⟩ :=
    hca E ∅ S U hn hES hUS hUC hdeg (Finset.empty_subset _) (fun v => by
      simp only [edeg_empty, Nat.cast_zero]
      positivity)
  refine ⟨R₂, fun e he => (Finset.mem_sdiff.1 (hR₂E he)).1,
    hcore.triDecomp.triDivisible.1, fun v => ?_, ?_⟩
  · have h := hR₂deg v
    nlinarith [mul_nonneg hγ.le hSnn]
  · intro H hHsub hHU hHeven hdvd
    have hHR₂ : Disjoint H R₂ :=
      Finset.disjoint_left.2 fun e he he' => (Finset.mem_sdiff.1 (hHsub he)).2 he'
    have hdec : TriDecomp (((∅ : Finset (Sym2 V)) ∪ H) \ H) := by
      simpa using (triDecomp_empty : TriDecomp (∅ : Finset (Sym2 V)))
    have hdvd' : 3 ∣ (((∅ : Finset (Sym2 V)) ∪ R₂) ∪ H).card := by simpa using hdvd
    have hmain := triDecomp_of_coverDown (R₁ := ∅) (R₂ := R₂) (H := H) (X := H) (U := U)
      hcore (by simp) (by simp) hHR₂ (fun v => by simp) hHeven hHU
      Finset.subset_union_right hdec hdvd'
    simpa using hmain

end BKLO
