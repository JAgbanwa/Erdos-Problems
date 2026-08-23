/-
# Standalone interface: the bounded-leftover absorber (BKLO §8/§11 absorbing structure)

`AbsorberDenseK3BoundedLeftover` is the SINGLE remaining crux for the dense triangle-decomposition
theorem: the faithful §10.13 vortex (proved) confines the §10 remainder to cells of CONSTANT size,
so its maximum degree is a constant `D`, and only an absorber for **bounded-degree** leftovers is
needed — strictly weaker than the §11 spread absorber `AbsorberDenseK3`.

This standalone copy depends only on the lightweight §8 / basic modules so it builds in a minimal,
clean project.  A proof of `absorberDenseK3BoundedLeftover_holds` here transports verbatim to the
copy consumed by `BKLO.triDecompDense_vortex`.
-/
import BKLO.Transformer
import BKLO.Section10Defs

open Finset

namespace BKLO

/-- **An absorber for leftovers of bounded (constant) maximum degree.**

For every `γ > 0` and every constant `D` there is a threshold beyond which every large dense
triangle-divisible `E ⊆ cliqueEdges S` contains a reservoir `R ⊆ E`: even-degree, of maximum degree
at most `γ|S|`, such that `R ∪ H` is triangle-decomposable for every even-degree `H ⊆ E \ R` of
maximum degree at most `D` with `3 ∣ |R ∪ H|`. -/
def AbsorberDenseK3BoundedLeftover : Prop :=
  ∀ γ : ℝ, 0 < γ → ∀ D : ℕ, ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → TriDivisible E →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ R : Finset (Sym2 V), R ⊆ E ∧ EvenDegrees R ∧
        (∀ v : V, (edeg R v : ℝ) ≤ γ * (S.card : ℝ)) ∧
        ∀ H : Finset (Sym2 V), H ⊆ E \ R → EvenDegrees H → (∀ v : V, edeg H v ≤ D) →
          3 ∣ (R ∪ H).card → TriDecomp (R ∪ H)

end BKLO
