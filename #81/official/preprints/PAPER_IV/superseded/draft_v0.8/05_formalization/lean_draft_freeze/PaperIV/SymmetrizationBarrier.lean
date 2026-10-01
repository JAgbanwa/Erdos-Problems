import PaperIV.VertexCopyGate
import PaperIV.GraphFamilyDistance

/-!
# First-entry barrier directly on the gated copy reachability relation

The historical H1 route never transports an integral partition backwards.
It uses the copy dynamics only to locate the first state entering a metric
neighbourhood.  `SymmetrizationPath` already stores the finite sequence, but as an
inductive reachability witness rather than a `Fin`-indexed path.  This module
proves the first-entry barrier directly by induction on that witness.

This removes the need to serialize `SymmetrizationPath` before applying the argument.
The scalar step used below was checked independently by Certo (exact Farkas
certificate `certificates/first_entry_reach_step.json`) and by Jacobian as an
UNSAT `QF_LRA` instance (`checks/first_entry_reach_step_qf_lra.json`).
-/

namespace PaperIV.SymmetrizationBarrier

open PaperIV.VertexCopyGate
open PaperIV.EditMetric
open PaperIV.GraphFamilyDistance

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite gated copy path cannot cross a forbidden annulus.  The function
`distance` is intentionally abstract: the graph-specific instantiation is the
normalized edit distance to the fixed critical split family.

`hlocal` is the local contraction theorem.  The strict inequality
`contracted + stepBudget < barrier` ensures that one copy step cannot jump
from outside `barrier` into the locally contracted region. -/
theorem barrier_of_symmetrizationPath
    (distance : SimpleGraph V → ℚ)
    {outer barrier contracted stepBudget : ℚ}
    (hbarrierOuter : barrier ≤ outer)
    (hgap : contracted + stepBudget < barrier)
    (hstep : ∀ (X : SimpleGraph V) {target source : V},
      target ≠ source → ¬ X.Adj target source →
      distance X - distance (PaperIV.VertexCopy.graph X target source) ≤ stepBudget)
    (hlocal : ∀ X : SimpleGraph V, PaperIV.IsChordal X →
      distance X < outer → distance X < contracted)
    {G H : SimpleGraph V}
    (hG : PaperIV.IsChordal G)
    (hreach : SymmetrizationPath G H)
    (hend : distance H < barrier) :
    distance G < barrier := by
  induction hreach with
  | refl G => exact hend
  | @step G H target source hne hnadj hs hchord hF4 hpot htail ih =>
      have hnext : distance (PaperIV.VertexCopy.graph G target source) < barrier :=
        ih hchord hend
      by_contra hnot
      have hcurrent : barrier ≤ distance G := le_of_not_gt hnot
      have hnextOuter : distance (PaperIV.VertexCopy.graph G target source) < outer :=
        lt_of_lt_of_le hnext hbarrierOuter
      have hcontracted :
          distance (PaperIV.VertexCopy.graph G target source) < contracted :=
        hlocal _ hchord hnextOuter
      have hstep' := hstep G hne hnadj
      linarith

/-- Invariant-aware form of `barrier_of_symmetrizationPath`.  The local contraction is
only required at states whose mixed fractional defect is at least that of one
fixed base graph `G₀`.  This is the quantifier needed by the H1 first-entry
route: gated copies carry precisely this invariant, so no contraction theorem
for every nearby chordal graph is required. -/
theorem barrier_of_symmetrizationPath_of_F4'_le
    (distance : SimpleGraph V → ℚ)
    {outer barrier contracted stepBudget : ℚ}
    (hbarrierOuter : barrier ≤ outer)
    (hgap : contracted + stepBudget < barrier)
    (hstep : ∀ (X : SimpleGraph V) {target source : V},
      target ≠ source → ¬ X.Adj target source →
      distance X - distance (PaperIV.VertexCopy.graph X target source) ≤ stepBudget)
    {G₀ G H : SimpleGraph V}
    (hbase : F4' G₀ ≤ F4' G)
    (hlocal : ∀ X : SimpleGraph V, PaperIV.IsChordal X → F4' G₀ ≤ F4' X →
      distance X < outer → distance X < contracted)
    (hG : PaperIV.IsChordal G)
    (hreach : SymmetrizationPath G H)
    (hend : distance H < barrier) :
    distance G < barrier := by
  induction hreach with
  | refl G => exact hend
  | @step G H target source hne hnadj hs hchord hF4 hpot htail ih =>
      have hbaseNext : F4' G₀ ≤ F4' (PaperIV.VertexCopy.graph G target source) :=
        le_trans hbase hF4
      have hnext : distance (PaperIV.VertexCopy.graph G target source) < barrier :=
        ih hbaseNext hchord hend
      by_contra hnot
      have hnextOuter : distance (PaperIV.VertexCopy.graph G target source) < outer :=
        lt_of_lt_of_le hnext hbarrierOuter
      have hcontracted :
          distance (PaperIV.VertexCopy.graph G target source) < contracted :=
        hlocal _ hchord hbaseNext hnextOuter
      have hstep' := hstep G hne hnadj
      linarith

/-! ## Instantiation by normalized edit distance -/

/-- **Graph-specific first-entry barrier for the H1 route.**  Every gated fine
copy changes normalized distance by at most `1 / |V|`.  Therefore a local
contraction from `outer` to `contracted`, with a gap wider than one copy step,
propagates backwards from the split terminal to the original graph.

Unlike the old path interface, this theorem consumes the actual terminating
`SymmetrizationPath` witness returned by `VertexCopyGate.exists_terminal_symmetrizationPath`. -/
theorem graphFamDistNorm_barrier_of_symmetrizationPath
    (F : Finset (Finset (Sym2 V))) (hF : F.Nonempty)
    {outer barrier contracted : ℚ}
    (hn : 2 ≤ Fintype.card V)
    (hbarrierOuter : barrier ≤ outer)
    (hgap : contracted + 1 / (Fintype.card V : ℚ) < barrier)
    (hlocal : ∀ X : SimpleGraph V, PaperIV.IsChordal X →
      graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) < outer →
      graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) < contracted)
    {G H : SimpleGraph V}
    (hG : PaperIV.IsChordal G)
    (hreach : SymmetrizationPath G H)
    (hend : graphFamDistNorm F hF H ((Fintype.card V : ℚ) ^ 2) < barrier) :
    graphFamDistNorm F hF G ((Fintype.card V : ℚ) ^ 2) < barrier := by
  classical
  apply barrier_of_symmetrizationPath
    (distance := fun X => graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2))
    hbarrierOuter hgap ?_ hlocal hG hreach hend
  intro X target source hne hnadj
  have hlip := abs_sub_famDistNorm_le F hF X.edgeFinset
    (PaperIV.VertexCopy.graph X target source).edgeFinset (m := (Fintype.card V : ℚ) ^ 2)
    (by positivity)
  have hedit := PaperIV.VertexCopy.normalized_editDist_le_inv X hn hne hnadj
  have habs :
      |graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) -
        graphFamDistNorm F hF (PaperIV.VertexCopy.graph X target source)
          ((Fintype.card V : ℚ) ^ 2)| ≤ 1 / (Fintype.card V : ℚ) := by
    change
      |famDistNorm F hF (graphEdgeSupport X) ((Fintype.card V : ℚ) ^ 2) -
        famDistNorm F hF (graphEdgeSupport (PaperIV.VertexCopy.graph X target source))
          ((Fintype.card V : ℚ) ^ 2)| ≤ 1 / (Fintype.card V : ℚ)
    rw [graphEdgeSupport_eq_edgeFinset, graphEdgeSupport_eq_edgeFinset]
    exact hlip.trans hedit
  exact (abs_le.mp habs).2

/-- Graph-specific first-entry barrier with the genuine copy-path invariant.
Compared with `graphFamDistNorm_barrier_of_symmetrizationPath`, the local contraction
may depend on `F4' G₀ ≤ F4' X`.  Instantiating `G₀ = G` discharges the initial
condition by reflexivity, while every later occurrence is covered by the
monotonicity field stored in `SymmetrizationPath`. -/
theorem graphFamDistNorm_barrier_of_symmetrizationPath_of_F4'_le
    (F : Finset (Finset (Sym2 V))) (hF : F.Nonempty)
    {outer barrier contracted : ℚ}
    (hn : 2 ≤ Fintype.card V)
    (hbarrierOuter : barrier ≤ outer)
    (hgap : contracted + 1 / (Fintype.card V : ℚ) < barrier)
    {G₀ G H : SimpleGraph V}
    (hbase : F4' G₀ ≤ F4' G)
    (hlocal : ∀ X : SimpleGraph V, PaperIV.IsChordal X → F4' G₀ ≤ F4' X →
      graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) < outer →
      graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) < contracted)
    (hG : PaperIV.IsChordal G)
    (hreach : SymmetrizationPath G H)
    (hend : graphFamDistNorm F hF H ((Fintype.card V : ℚ) ^ 2) < barrier) :
    graphFamDistNorm F hF G ((Fintype.card V : ℚ) ^ 2) < barrier := by
  classical
  apply barrier_of_symmetrizationPath_of_F4'_le
    (distance := fun X => graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2))
    hbarrierOuter hgap ?_ hbase hlocal hG hreach hend
  intro X target source hne hnadj
  have hlip := abs_sub_famDistNorm_le F hF X.edgeFinset
    (PaperIV.VertexCopy.graph X target source).edgeFinset (m := (Fintype.card V : ℚ) ^ 2)
    (by positivity)
  have hedit := PaperIV.VertexCopy.normalized_editDist_le_inv X hn hne hnadj
  have habs :
      |graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) -
        graphFamDistNorm F hF (PaperIV.VertexCopy.graph X target source)
          ((Fintype.card V : ℚ) ^ 2)| ≤ 1 / (Fintype.card V : ℚ) := by
    change
      |famDistNorm F hF (graphEdgeSupport X) ((Fintype.card V : ℚ) ^ 2) -
        famDistNorm F hF (graphEdgeSupport (PaperIV.VertexCopy.graph X target source))
          ((Fintype.card V : ℚ) ^ 2)| ≤ 1 / (Fintype.card V : ℚ)
    rw [graphEdgeSupport_eq_edgeFinset, graphEdgeSupport_eq_edgeFinset]
    exact hlip.trans hedit
  exact (abs_le.mp habs).2

/-- Ready-to-use H1 form: the base graph in the fractional invariant is the
start of the copy path itself. -/
theorem graphFamDistNorm_barrier_from_start
    (F : Finset (Finset (Sym2 V))) (hF : F.Nonempty)
    {outer barrier contracted : ℚ}
    (hn : 2 ≤ Fintype.card V)
    (hbarrierOuter : barrier ≤ outer)
    (hgap : contracted + 1 / (Fintype.card V : ℚ) < barrier)
    {G H : SimpleGraph V}
    (hlocal : ∀ X : SimpleGraph V, PaperIV.IsChordal X → F4' G ≤ F4' X →
      graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) < outer →
      graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) < contracted)
    (hG : PaperIV.IsChordal G)
    (hreach : SymmetrizationPath G H)
    (hend : graphFamDistNorm F hF H ((Fintype.card V : ℚ) ^ 2) < barrier) :
    graphFamDistNorm F hF G ((Fintype.card V : ℚ) ^ 2) < barrier :=
  graphFamDistNorm_barrier_of_symmetrizationPath_of_F4'_le F hF hn hbarrierOuter hgap
    (le_refl _) hlocal hG hreach hend

end PaperIV.SymmetrizationBarrier
