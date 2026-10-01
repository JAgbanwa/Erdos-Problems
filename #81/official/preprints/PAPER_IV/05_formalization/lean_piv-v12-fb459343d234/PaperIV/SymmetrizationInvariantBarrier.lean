import PaperIV.SymmetrizationBarrier

/-!
# Invariant-aware first-entry barrier

`SymmetrizationBarrier.barrier_of_symmetrizationPath` asks for a local contraction
hypothesis of the form

```text
hlocal : ∀ X : SimpleGraph V, IsChordal X → distance X < outer → distance X < contracted
```

which quantifies over *every* chordal graph in the metric neighbourhood.  That
is strictly stronger than what the route can deliver: the physical local
constructor of the near regime only applies to graphs that the gated copy
dynamics can actually reach, and the gate carries a defect invariant.

Along a gated path `SymmetrizationPath G H` the mixed fractional defect never decreases
(`VertexCopyGate.F4'_le_of_symmetrizationPath`), so every intermediate graph `X`
satisfies

```text
F4' G ≤ F4' X ≤ F4' H .
```

This module proves the first-entry barrier with `hlocal` relativized to that
two-sided invariant, so the contraction theorem only has to be established for
graphs whose defect is squeezed between the defect of the original graph and
that of the terminal.  The invariant is *derived* inside the induction, not
assumed: the lower bound propagates through the `hF4` field of each gated step
and the upper bound comes from `F4'_le_of_symmetrizationPath` applied to the remaining
tail.

`barrier_of_symmetrizationPath_invariant` is the general scalar statement,
`graphFamDistNorm_barrier_of_symmetrizationPath_invariant` its instantiation by the
normalized edit distance with its `1/|V|` step budget, and
`graphFamDistNorm_barrier_of_terminal_symmetrizationPath` the packaged form which
produces the terminal itself from `VertexCopyGate.exists_terminal_symmetrizationPath`.
-/

namespace PaperIV.SymmetrizationBarrier

open PaperIV.VertexCopyGate
open PaperIV.EditMetric
open PaperIV.GraphFamilyDistance

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Invariant-aware first-entry barrier.**  Identical to
`barrier_of_symmetrizationPath` except that the local contraction hypothesis `hlocal`
may assume the gated defect invariant `F4' G ≤ F4' X ≤ F4' H` for the graph `X`
it is applied to.  Both parts of the invariant are established inside the
induction from the gate data. -/
theorem barrier_of_symmetrizationPath_invariant
    (distance : SimpleGraph V → ℚ)
    {outer barrier contracted stepBudget : ℚ}
    (hbarrierOuter : barrier ≤ outer)
    (hgap : contracted + stepBudget < barrier)
    (hstep : ∀ (X : SimpleGraph V) {target source : V},
      target ≠ source → ¬ X.Adj target source →
      distance X - distance (PaperIV.VertexCopy.graph X target source) ≤ stepBudget)
    {G H : SimpleGraph V}
    (hlocal : ∀ X : SimpleGraph V, PaperIV.IsChordal X →
      F4' G ≤ F4' X → F4' X ≤ F4' H →
      distance X < outer → distance X < contracted)
    (hreach : SymmetrizationPath G H)
    (hend : distance H < barrier) :
    distance G < barrier := by
  -- We strengthen the statement so that the induction can move both endpoints
  -- while the contraction hypothesis keeps referring to the fixed pair `G`, `H`.
  suffices hmain : ∀ {K K' : SimpleGraph V}, SymmetrizationPath K K' → F4' G ≤ F4' K →
      F4' K' ≤ F4' H → distance K' < barrier → distance K < barrier from
    hmain hreach (le_refl _) (le_refl _) hend
  intro K K' hKK'
  induction hKK' with
  | refl K => intro _ _ hK; exact hK
  | @step K K' target source hne hnadj _hs hchord hF4 _hpot htail ih =>
      intro hGK hK'H hK'
      have hGnext : F4' G ≤ F4' (PaperIV.VertexCopy.graph K target source) :=
        le_trans hGK hF4
      have hnext : distance (PaperIV.VertexCopy.graph K target source) < barrier :=
        ih hGnext hK'H hK'
      by_contra hnot
      have hcurrent : barrier ≤ distance K := le_of_not_gt hnot
      have hnextOuter : distance (PaperIV.VertexCopy.graph K target source) < outer :=
        lt_of_lt_of_le hnext hbarrierOuter
      have hnextUpper : F4' (PaperIV.VertexCopy.graph K target source) ≤ F4' H :=
        le_trans (F4'_le_of_symmetrizationPath htail) hK'H
      have hcontracted :
          distance (PaperIV.VertexCopy.graph K target source) < contracted :=
        hlocal _ hchord hGnext hnextUpper hnextOuter
      have hstep' := hstep K hne hnadj
      linarith

/-- The one-sided form: the contraction hypothesis may assume only
`F4' G ≤ F4' X`, the invariant that the gate guarantees relative to the
starting graph. -/
theorem barrier_of_symmetrizationPath_lower_invariant
    (distance : SimpleGraph V → ℚ)
    {outer barrier contracted stepBudget : ℚ}
    (hbarrierOuter : barrier ≤ outer)
    (hgap : contracted + stepBudget < barrier)
    (hstep : ∀ (X : SimpleGraph V) {target source : V},
      target ≠ source → ¬ X.Adj target source →
      distance X - distance (PaperIV.VertexCopy.graph X target source) ≤ stepBudget)
    {G H : SimpleGraph V}
    (hlocal : ∀ X : SimpleGraph V, PaperIV.IsChordal X →
      F4' G ≤ F4' X → distance X < outer → distance X < contracted)
    (hreach : SymmetrizationPath G H)
    (hend : distance H < barrier) :
    distance G < barrier :=
  barrier_of_symmetrizationPath_invariant distance hbarrierOuter hgap hstep
    (fun X hX hlow _ hout => hlocal X hX hlow hout) hreach hend

/-- The old unrelativized barrier is the special case in which the contraction
hypothesis ignores the invariant; nothing is lost by carrying it. -/
theorem barrier_of_symmetrizationPath_of_unconditional
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
    (hreach : SymmetrizationPath G H)
    (hend : distance H < barrier) :
    distance G < barrier :=
  barrier_of_symmetrizationPath_invariant distance hbarrierOuter hgap hstep
    (fun X hX _ _ hout => hlocal X hX hout) hreach hend

/-! ## Instantiation by the normalized edit distance -/

/-- **Invariant-aware graph-specific first-entry barrier.**  The contraction
input is only required for chordal graphs whose mixed fractional defect lies
between that of `G` and that of the terminal `H`. -/
theorem graphFamDistNorm_barrier_of_symmetrizationPath_invariant
    (F : Finset (Finset (Sym2 V))) (hF : F.Nonempty)
    {outer barrier contracted : ℚ}
    (hn : 2 ≤ Fintype.card V)
    (hbarrierOuter : barrier ≤ outer)
    (hgap : contracted + 1 / (Fintype.card V : ℚ) < barrier)
    {G H : SimpleGraph V}
    (hlocal : ∀ X : SimpleGraph V, PaperIV.IsChordal X →
      F4' G ≤ F4' X → F4' X ≤ F4' H →
      graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) < outer →
      graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) < contracted)
    (hreach : SymmetrizationPath G H)
    (hend : graphFamDistNorm F hF H ((Fintype.card V : ℚ) ^ 2) < barrier) :
    graphFamDistNorm F hF G ((Fintype.card V : ℚ) ^ 2) < barrier := by
  classical
  apply barrier_of_symmetrizationPath_invariant
    (distance := fun X => graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2))
    hbarrierOuter hgap ?_ hlocal hreach hend
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

/-- **The packaged first-entry statement.**  Every chordal `G` gates down to a
universal-core split terminal `H`; if the contraction hypothesis holds along
the defect window `[F4' G, F4' H]` and the terminal is inside the barrier, then
`G` itself is already inside the barrier.

Note what this does *not* claim: it locates `G` in the metric neighbourhood of
the split family, it does not transport any partition backwards. -/
theorem graphFamDistNorm_barrier_of_terminal_symmetrizationPath
    (F : Finset (Finset (Sym2 V))) (hF : F.Nonempty)
    {outer barrier contracted : ℚ}
    (hn : 2 ≤ Fintype.card V)
    (hbarrierOuter : barrier ≤ outer)
    (hgap : contracted + 1 / (Fintype.card V : ℚ) < barrier)
    {G : SimpleGraph V} (hG : PaperIV.IsChordal G)
    (hlocal : ∀ H : SimpleGraph V, ∀ X : SimpleGraph V, PaperIV.IsChordal X →
      F4' G ≤ F4' X → F4' X ≤ F4' H →
      graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) < outer →
      graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) < contracted)
    (hterminal : ∀ H : SimpleGraph V, SymmetrizationPath G H → PaperIV.IsChordal H →
      PaperIV.TerminalSplit.IsUniversalCoreSplit H →
      graphFamDistNorm F hF H ((Fintype.card V : ℚ) ^ 2) < barrier) :
    graphFamDistNorm F hF G ((Fintype.card V : ℚ) ^ 2) < barrier := by
  obtain ⟨H, hreach, hHchord, hHterm, -⟩ := exists_terminal_symmetrizationPath G hG
  exact graphFamDistNorm_barrier_of_symmetrizationPath_invariant F hF hn hbarrierOuter hgap
    (hlocal H) hreach (hterminal H hreach hHchord hHterm)

end PaperIV.SymmetrizationBarrier
