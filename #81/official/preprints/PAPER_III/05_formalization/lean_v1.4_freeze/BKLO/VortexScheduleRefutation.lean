/-
# The vortex-schedule interface is false.

Both §10 vortex-schedule interfaces of this project — the original
`BKLO.VortexScheduleExists` (`BKLO/InputsVortex.lean`) and the variant
`BKLO.VortexScheduleSlack` (`BKLO/CoverDownVortexFaithful.lean`) used by the cover-down vehicle —
contain a **descent clause** of the shape

  for every `E` on `W` of minimum degree `f(|W|)·|W|`, every bottom set `U ⊆ W` with `n₂ ≤ |U|`
  and every `m` with `|U| ≤ m` and `2m ≤ |W|`, there is `U ⊆ W' ⊆ W` with `|W'| = m` on which the
  induced edge set has minimum degree at least `f(m)·m`.

This is false, and for an entirely elementary reason: the clause allows `m = |U|`, which forces
`W' = U`, and it then demands that the edge set *induced on the prescribed bottom set* be dense —
something no hypothesis on `E` guarantees.  The counterexample below takes `E` to be the complete
graph on `100n₂` vertices with the edges inside `U` deleted: `E` has minimum degree `99n₂ - 1`,
comfortably above the `f(|W|)|W| ≤ 91n₂` the clause asks for, while `E ∩ cliqueEdges U` is empty.

The clause is stated for an arbitrary `m ≥ |U|`, so a prover of the interface has no way to avoid
the degenerate case.  The defect is not specific to the cover-down vehicle: it is present in the
original interface, and hence `BKLO.vortexEngineRatio_of_inputs`,
`BKLO.vortexEngineRatioFromInputs_holds` and the old
`BKLO.triangle_decomposition_of_inputs_and_vortex` of `BKLO/MainUnconditional.lean` are all
conditional on a hypothesis that cannot hold.

## What a repaired descent clause must look like

The degenerate instance is blocked by requiring the level to be genuinely larger than the bottom
set (`K|U| ≤ m`) *and* by carrying the density of the vertices of `W` **into** the bottom set —
the `resLink` hypothesis of `BKLO.VortexDescentClauseR2` (`BKLO/ReservoirRepaired2.lean`), which is
exactly the form in which the descent clause is actually *proved* in this project
(`BKLO.vortexDescentClauseR3_of_powerSchedule`).  Without an into-`U` hypothesis no schedule can
work even in the non-degenerate range: a vertex of `W'` with no neighbour in `U` keeps only its
neighbours in the sampled part `W' \ U`, so its density drops by a factor `1 - |U|/m` at every
level, and no `f` with values in `[9/10 + ε/2, 9/10 + ε]` can absorb a constant-factor loss at
each of the `Θ(log |W|)` levels of a vortex.

Everything here is `sorry`-free.
-/
import BKLO.CoverDownVortexFaithful
import BKLO.InputsVortexSat

open Finset

namespace BKLO

/-- **The descent clause of the vortex schedule is false.**  Whatever the schedule `f`, the
degenerate instance `m = |U|` of the descent clause demands that the edge set induced on the
prescribed bottom set be dense, which the hypotheses do not provide.

The clause is taken here with the *strongest* ambient density hypothesis, so that the refutation
applies both to `BKLO.VortexScheduleExists` and — a fortiori, since its descent clause assumes
less — to `BKLO.VortexScheduleSlack`. -/
theorem descent_clause_false {f : ℕ → ℝ} {n₂ : ℕ} (hn₂ : 0 < n₂)
    (hf1 : 0 < f n₂) (hf2 : f (100 * n₂) ≤ 91 / 100)
    (hdesc : ∀ {V : Type} [DecidableEq V] (W U : Finset V) (E : Finset (Sym2 V)) (m : ℕ),
        n₂ ≤ U.card → U ⊆ W → U.card ≤ m → 2 * m ≤ W.card → E ⊆ cliqueEdges W →
        (∀ v ∈ W, f W.card * (W.card : ℝ) ≤ (edeg E v : ℝ)) →
        ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ W'.card = m ∧
          ∀ v ∈ W', f m * (m : ℝ) ≤ (edeg (E ∩ cliqueEdges W') v : ℝ)) :
    False := by
  classical
  set N : ℕ := 100 * n₂ with hN
  have hNcard : (univ : Finset (Fin N)).card = N := by simp
  have hn₂N : n₂ ≤ N := by omega
  -- the bottom set: any `n₂` vertices
  obtain ⟨U, -, hUcard⟩ :=
    Finset.exists_subset_card_eq (s := (univ : Finset (Fin N))) (n := n₂) (by rw [hNcard]; omega)
  -- the edge set: the complete graph with the edges inside `U` deleted
  set E : Finset (Sym2 (Fin N)) := cliqueEdges (univ : Finset (Fin N)) \ cliqueEdges U with hE
  have hEW : E ⊆ cliqueEdges (univ : Finset (Fin N)) := Finset.sdiff_subset
  -- `E` has the density the clause asks for
  have hdens : ∀ v ∈ (univ : Finset (Fin N)),
      f (univ : Finset (Fin N)).card * ((univ : Finset (Fin N)).card : ℝ)
        ≤ (edeg E v : ℝ) := by
    intro v _
    have h1 : edeg (cliqueEdges (univ : Finset (Fin N))) v ≤ edeg E v + edeg (cliqueEdges U) v :=
      edeg_le_edeg_sdiff_add_edeg _ _ v
    have h2 : edeg (cliqueEdges U) v ≤ U.card := edeg_cliqueEdges_le U v
    have h3 : edeg (cliqueEdges (univ : Finset (Fin N))) v = N - 1 := by
      rw [edeg_cliqueEdges_of_mem (Finset.mem_univ v), hNcard]
    have hNpos : 1 ≤ N := by omega
    have h4 : N - 1 ≤ edeg E v + n₂ := by rw [← hUcard]; omega
    have h4R : ((N : ℝ) - 1) ≤ (edeg E v : ℝ) + (n₂ : ℝ) := by
      have : ((N - 1 : ℕ) : ℝ) ≤ ((edeg E v + n₂ : ℕ) : ℝ) := by exact_mod_cast h4
      rw [Nat.cast_sub hNpos, Nat.cast_add] at this
      push_cast at this ⊢
      linarith
    have hNR : (N : ℝ) = 100 * (n₂ : ℝ) := by rw [hN]; push_cast; ring
    have hn₂R : (1 : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast hn₂
    rw [hNcard]
    have h5 : f N * (N : ℝ) ≤ 91 * (n₂ : ℝ) := by
      have := mul_le_mul_of_nonneg_right hf2 (by positivity : (0 : ℝ) ≤ (N : ℝ))
      rw [hNR] at this ⊢
      linarith
    linarith
  -- the degenerate instance `m = |U|`
  obtain ⟨W', hUW', -, hW'card, hW'dens⟩ :=
    hdesc (univ : Finset (Fin N)) U E n₂ (le_of_eq hUcard.symm) (Finset.subset_univ _)
      (le_of_eq hUcard) (by rw [hNcard]; omega) hEW hdens
  -- the level is forced to be the bottom set itself, on which `E` induces nothing
  have hW'U : U = W' := Finset.eq_of_subset_of_card_le hUW' (by rw [hW'card, hUcard])
  have hUne : U.Nonempty := Finset.card_pos.1 (by rw [hUcard]; exact hn₂)
  obtain ⟨v, hv⟩ := hUne
  have hempty : E ∩ cliqueEdges W' = ∅ := by
    rw [← hW'U]
    refine Finset.eq_empty_iff_forall_notMem.2 fun e he => ?_
    obtain ⟨heE, heU⟩ := Finset.mem_inter.1 he
    exact (Finset.mem_sdiff.1 heE).2 heU
  have h0 : (edeg (E ∩ cliqueEdges W') v : ℝ) = 0 := by
    rw [hempty]; simp [edeg]
  have := hW'dens v (hW'U ▸ hv)
  rw [h0] at this
  have hn₂R : (0 : ℝ) < (n₂ : ℝ) := by exact_mod_cast hn₂
  nlinarith

/-- **The original §10 vortex-schedule interface is false.**  In particular
`BKLO.vortexEngineRatio_of_inputs`, `BKLO.vortexEngineRatioFromInputs_holds` and the theorems of
`BKLO/MainUnconditional.lean` derived from it are conditional on a hypothesis that cannot hold. -/
theorem not_vortexScheduleExists : ¬ VortexScheduleExists := by
  intro h
  obtain ⟨f, n₂, -, -, -, hn₂pos, hfbd, -, hdesc⟩ := h (1 / 100) (by norm_num) 1
  refine descent_clause_false hn₂pos ?_ ?_ (fun W U E m h1 h2 h3 h4 h5 h6 =>
    hdesc W U E m h1 h2 h3 h4 h5 h6)
  · have := (hfbd n₂ le_rfl).1
    have hn₂R : (0 : ℝ) < (n₂ : ℝ) := by exact_mod_cast hn₂pos
    linarith
  · have := (hfbd (100 * n₂) (by omega)).2
    linarith

/-- **The vortex-schedule interface used by the cover-down vehicle is false too**, for the same
reason: it inherits the degenerate instance `m = |U|` of the descent clause.  Consequently
`BKLO.triangle_decomposition_of_inputs_via_coverdown` and
`BKLO.coverDownK3Div_iff_triDecompDense`, which carry `VortexScheduleSlack` as a hypothesis, are
vacuously conditional; the cover-down vehicle cannot be closed in this form. -/
theorem not_vortexScheduleSlack : ¬ VortexScheduleSlack := by
  intro h
  obtain ⟨f, n₂, -, -, -, hn₂pos, hfbd, -, hdesc⟩ := h (1 / 100) (by norm_num) 1
  refine descent_clause_false hn₂pos ?_ ?_ (fun W U E m h1 h2 h3 h4 h5 h6 =>
    hdesc W U E m h1 h2 h3 h4 h5 (fun v hv => by linarith only [h6 v hv]))
  · have := (hfbd n₂ le_rfl).1
    have hn₂R : (0 : ℝ) < (n₂ : ℝ) := by exact_mod_cast hn₂pos
    linarith
  · have := (hfbd (100 * n₂) (by omega)).2
    linarith

end BKLO
