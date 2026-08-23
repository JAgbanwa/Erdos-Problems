/-
# Paper III, AX2 half (dense triangle decomposition), reduced to the named paper ingredients

Composing the faithful §10/§11 chain:
* `BKLO.lemma1012K3'_of_inputs` — the repaired Lemma 10.12 (r=2) in the dense regime, from the four
  paper ingredients `Lemma72K3` (Lemma 7.2), `Lemma93K3` (Lemma 9.3), `Lemma1010K3` (Lemma 10.10) and
  `Lemma106K3Set` (Lemma 10.6 on a vertex set);
* `BKLO.triangleDecomposable_dense_faithful` — the AX2 half of Paper III from `Lemma1012K3' (9/10)`
  and the dense absorber interface `AbsorberDenseK3`.

The result: the AX2 / dense-triangle-decomposition half of Paper III (`δ ≥ 9/10 + ε`) holds from
FIVE explicit, named classical ingredients — with NO `sorry`, no bespoke/refuted route, and the
standard axiom gate `[propext, Classical.choice, Quot.sound]`.  Each ingredient is a published BKLO
lemma; three of them (7.2, 9.3, 10.10) are being discharged separately.
-/
import BKLO.NearOptimalFaithful
import BKLO.Section1012Assembly

open Finset

namespace BKLO

/-- **Paper III, AX2 half (dense), from the five named paper ingredients.**  Every large
`K₃`-divisible graph with `δ(G) ≥ (9/10 + ε)n` is triangle-decomposable, given: Lemma 7.2
(`Lemma72K3`), Lemma 9.3 (`Lemma93K3`), Lemma 10.10 (`Lemma1010K3`), Lemma 10.6 on a vertex set
(`Lemma106K3Set (9/10)`) and the dense absorber (`AbsorberDenseK3`). -/
theorem paperIII_ax2_dense_of_inputs
    (h72 : Lemma72K3) (h93 : Lemma93K3) (h1010 : Lemma1010K3)
    (h106 : Lemma106K3Set (9 / 10)) (habs : AbsorberDenseK3) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → 3 ∣ G.edgeFinset.card → (∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangleDecomposable_dense_faithful
    (lemma1012K3'_of_inputs (le_refl (9 / 10)) h72 h93 h1010 h106) habs ε hε

end BKLO
