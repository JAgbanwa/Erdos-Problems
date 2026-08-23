/-
# The per-step chooser of BKLO Lemma 10.3, discharged (parts A + B2 + the SimpleGraph conversion)

This file assembles, `sorry`-free, the single greedy step of BKLO Lemma 10.3 (r = 2): given the
neighbourhood `N` of an apex `x` (even, condition (i)), the neighbourhood edge set `E` of minimum
degree `≥ |N|/2 + d` (condition (ii), `d` the slack `γ|V|`), and an already-used set `D` of maximum
degree `≤ d` (the budget from condition (iii)), a perfect matching of the unused part exists — a
matching of `N` avoiding `x`.

It wires together three pieces already in place:
* `BKLO.edeg_sdiff_ge_of_slack` (the slack absorbs the used edges, part B2);
* `BKLO.degree_setGraph` (the `SimpleGraph` on `N` with edge set `E \ D` has degree `= edeg (E \ D)`);
* `BKLO.exists_isMatchingAvoiding_of_dirac` (Dirac → matching, part A).

What remains to close Lemma 10.3 in full is only the greedy invariant that the accumulated used set
`D` really keeps `edeg D v ≤ d` along the sweep (each earlier apex uses each neighbour at most once,
and a vertex is a neighbour of at most `d_H(y,U) ≤ γ|V|/2` apices).

Everything here is `sorry`-free.
-/
import BKLO.CoverDownBudget
import BKLO.CoverDownDiracChooser
import BKLO.SetGraph

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-- **The greedy step of Lemma 10.3, discharged.**  An even neighbourhood `N` whose edge set `E`
(inside `N`) has minimum degree `≥ |N|/2 + d`, minus a used set `D` of maximum degree `≤ d`, still
has a perfect matching — a matching of `N` avoiding any `x ∉ N`.  This is the chooser the greedy loop
`BKLO.exists_greedy_triDecomp` consumes, with `d` the slack `γ|V|` of Lemma 10.3(ii). -/
theorem exists_matching_of_budget {N : Finset V} {x : V} (hx : x ∉ N) {E D : Finset (Sym2 V)} {d : ℕ}
    (hne : N.Nonempty) (hEsub : E ⊆ cliqueEdges N) (hEven : Even N.card)
    (hdeg : ∀ v ∈ N, N.card / 2 + d ≤ edeg E v)
    (hDbud : ∀ v ∈ N, edeg D v ≤ d) :
    ∃ M : Finset (Finset V), IsMatchingAvoiding M x := by
  classical
  haveI : Nonempty {v // v ∈ N} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hEDsub : (E \ D) ⊆ cliqueEdges N := (Finset.sdiff_subset).trans hEsub
  -- every vertex has `setGraph`-degree `≥ |N|/2`
  have hdegG : ∀ a : {v // v ∈ N}, N.card / 2 ≤ (setGraph N (E \ D)).degree a := by
    intro a
    rw [degree_setGraph hEDsub a]
    exact edeg_sdiff_ge_of_slack (hdeg (a : V) a.2) (hDbud (a : V) a.2)
  have hmin : N.card / 2 ≤ (setGraph N (E \ D)).minDegree :=
    SimpleGraph.le_minDegree_of_forall_le_degree _ (N.card / 2) hdegG
  refine exists_isMatchingAvoiding_of_dirac hx (setGraph N (E \ D)) ?_ ?_
  · rw [card_coe_eq]; exact hEven
  · rw [card_coe_eq]
    obtain ⟨k, hk⟩ := hEven
    omega

end BKLO
