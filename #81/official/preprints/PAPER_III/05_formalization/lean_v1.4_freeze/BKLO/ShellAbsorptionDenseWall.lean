/-
# What the level-density hypothesis buys, and what it leaves standing.

`BKLO/ShellAbsorptionDense.lean` adds to `BKLO.ShellAbsorption` the level-density hypothesis the
vortex maintains (`BKLO/CoverDownVortexDense.lean` proves that it really is maintained, at every
level down to the bounded core).  This file records, `sorry`-free, the exact effect of that
addition on the three facts of `BKLO/ShellAbsorptionConfinementWall.lean`.

**Removed — the hollow wall (fact 3).**  `BKLO.levelDensity_fails_of_hollow` excludes every hollow
configuration, and `BKLO.card_levelEdges_ge_of_levelDensity` turns the hypothesis into a positive
statement: the confinement allowance really is a reservoir of `Θ(|W'|²)` edges of `F` inside `W'`,
namely at least `(c - 9/10)|W'|²/2` of them.  Consequently
`BKLO.shellAbsorption_forces_sparse_selfdecomposition` — the degenerate demand that an arbitrarily
sparse graph be decomposed with no outside help — has no dense instance: its proof runs on the
hollow configuration alone.

**Unchanged — the far part (fact 2).**  `BKLO.shellAbsorptionDense_forces_far_cherries` is the
statement of `BKLO.shellAbsorption_forces_far_cherries` for the dense interface: an edge of the
remainder with *both* endpoints outside `W'` still has to be covered by a triangle all three of
whose edges lie in `R ∪ L`, because no edge at a vertex outside `W'` is an edge inside `W'`.  The
density of the level is irrelevant to this: it is a statement about which edges the confinement
clause permits, not about how many of them there are.  What it says is that the *reservation* must
carry the covering cherries of the far part — for instance as reserved cross edges from `W \ W'` to
the dense level `W'` — since the nibble leftover `L` need not carry them.  This is a design
constraint on `R`, not an impossibility: unlike in a hollow instance, cherries with apex in `W'` are
available, and `R` is allowed degree `ρ|W|` at every vertex.

**Unchanged — exactness (fact 1).**  `BKLO.shellAbsorptionDense_forces_reserve_exactness`: the
conclusion demands `R ∪ L ⊆ famEdges Q`, so *every reserved edge must be consumed*, for every
admissible leftover — in particular, if `R` is itself triangle-divisible, for the empty leftover.
So the reservation is not a stock of spare edges that may be left over: it must be exactly
decomposable, jointly with whatever the nibble leaves behind.

**What remains is strength, not a wall.**  `BKLO.coverDownK3DivDense_iff_triDecompDense`
(`BKLO/CoverDownVortexDense.lean`) shows that the density-corrected cover-down step is still
equivalent to the triangle decomposition theorem for dense divisible graphs, and
`BKLO.coverDownK3DivDense_of_denseNibble_shellAbsorptionDense` derives it from
`BKLO.ShellAbsorptionDense`.  So a proof of `ShellAbsorptionDense` is a proof of that theorem: the
level-density hypothesis removes the *degenerate* obstruction identified by the hollow instances,
but it does not reduce the strength of the interface, and no construction assembled from the §8
absorber machinery of this project (whose absorbers are produced *after* the divisible set is known,
`BKLO.sparseAbsorberExistence_nine` being `∀ H, ∃ A`, and on fresh vertices) discharges it.

Everything here is `sorry`-free.
-/
import BKLO.CoverDownVortexDense

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The reservoir the level-density hypothesis guarantees -/

/-- **A dense level is a quadratic reservoir.**  If every vertex of `W'` has at least `c'|W'|`
neighbours inside `W'` in `F`, then `F` has at least `c'|W'|²/2` edges inside `W'`.  This is the
`Θ(|W'|²)` supply of covering edges that the confinement clause
`famEdges Q ⊆ (R ∪ L) ∪ (cliqueEdges W' \ cliqueEdges W'')` may draw on, and which a hollow
instance does not have. -/
theorem card_levelEdges_ge_of_levelDensity {c' : ℝ} {W' : Finset V} {F : Finset (Sym2 V)}
    (hdense : ∀ v ∈ W', c' * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) :
    c' * (W'.card : ℝ) ^ 2 / 2 ≤ ((F ∩ cliqueEdges W').card : ℝ) := by
  classical
  have hsub : F ∩ cliqueEdges W' ⊆ cliqueEdges W' := Finset.inter_subset_right
  have hsum : ∑ v ∈ W', edeg (F ∩ cliqueEdges W') v = 2 * (F ∩ cliqueEdges W').card :=
    sum_edeg_of_subset_cliqueEdges hsub
  have hle : ∑ _v ∈ W', c' * (W'.card : ℝ)
      ≤ ∑ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ) :=
    Finset.sum_le_sum fun v hv => hdense v hv
  have hleft : ∑ _v ∈ W', c' * (W'.card : ℝ) = c' * (W'.card : ℝ) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have hright : ∑ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
      = ((2 * (F ∩ cliqueEdges W').card : ℕ) : ℝ) := by
    rw [← hsum]
    push_cast
    rfl
  rw [hleft, hright] at hle
  push_cast at hle
  linarith only [hle]

/-! ### The far part of the shell: unchanged by the density of the level -/

/-- **The far part must still absorb itself.**  `BKLO.shellAbsorption_forces_far_cherries` for the
density-corrected interface: whatever reservation `R` a proof of `BKLO.ShellAbsorptionDense`
produces at a *dense* level, and whatever admissible leftover `L` it is handed, every edge of
`R ∪ L` with both endpoints outside `W'` lies in a triangle of `R ∪ L`.

The density of `W'` is of no help here — an edge at a vertex outside `W'` is never an edge inside
`W'`, so the confinement clause leaves the covering triangle no edge outside `R ∪ L`.  The content
of the statement is therefore a *design constraint on the reservation*: `R` must already contain the
covering cherries of the far part (for instance reserved cross edges from `W \ W'` into the dense
level), since the nibble leftover `L` need not contain them. -/
theorem shellAbsorptionDense_forces_far_cherries (hAbs : ShellAbsorptionDense) (c γ ρ : ℝ) (K : ℕ)
    (hc : 9 / 10 < c) (hγ : 0 < γ) (hρ : 0 < ρ) (hK : 2 ≤ K) :
    ∃ (η : ℝ) (n₀ : ℕ), 0 < η ∧
      ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
        n₀ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
        K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
        F ⊆ cliqueEdges W → TriDivisible F →
        TriDivisible (F ∩ cliqueEdges W') → TriDivisible (F ∩ cliqueEdges W'') →
        (∀ v ∈ W, c * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
        (∀ v ∈ W', (c - 9 / 10) * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
        ∃ R : Finset (Sym2 V), R ⊆ F \ cliqueEdges W' ∧
          (∀ v : V, (edeg R v : ℝ) ≤ ρ * (W.card : ℝ)) ∧
          ∀ L : Finset (Sym2 V), L ⊆ (F \ cliqueEdges W') \ R →
            (∀ v : V, (edeg L v : ℝ) ≤ η * (W.card : ℝ)) →
            TriDivisible (R ∪ L) →
            ∀ u v : V, u ∉ W' → v ∉ W' → s(u, v) ∈ R ∪ L →
              ∃ w : V, u ≠ w ∧ v ≠ w ∧ s(u, w) ∈ R ∪ L ∧ s(v, w) ∈ R ∪ L := by
  obtain ⟨η, n₀, hη, habs⟩ := hAbs c γ ρ K hc hγ hρ hK
  refine ⟨η, n₀, hη, ?_⟩
  intro V inst W W' W'' F hcard hW' hW'' hKW hKKW hKW'' hFW hdivF hdivF' hdivF'' hdense hdenseW'
  obtain ⟨R, hRsub, hRdeg, habs2⟩ :=
    habs W W' W'' F hcard hW' hW'' hKW hKKW hKW'' hFW hdivF hdivF' hdivF'' hdense hdenseW'
  refine ⟨R, hRsub, hRdeg, ?_⟩
  intro L hL hLdeg hdiv u v hu hv he
  obtain ⟨Q, hQ, hQcov, hQconf, -⟩ := habs2 L hL hLdeg hdiv
  exact far_edge_cherry_of_confined_cover hQ hQcov hQconf hu hv he

/-! ### Exactness of the reservation -/

/-- **The reservation is consumed exactly.**  Taking the empty leftover — admissible whenever the
reservation is itself triangle-divisible — the conclusion of `BKLO.ShellAbsorptionDense` says that
`R` is covered *exactly* by an edge-disjoint family of triangles of `F` which uses, besides `R`,
only edges inside `W'` and none inside `W''`.

So the reserved edges are not spare capacity: every one of them has to be used, and the reservation
has to be decomposable in this confined sense before the leftover is seen.  This is the interface
form of `BKLO.triDivisible_of_isAbsorber` (fact 1 of the confinement wall): absorption is never
per-edge, and the object that must be divisible — and decomposable — is the whole remainder. -/
theorem shellAbsorptionDense_forces_reserve_exactness (hAbs : ShellAbsorptionDense)
    (c γ ρ : ℝ) (K : ℕ) (hc : 9 / 10 < c) (hγ : 0 < γ) (hρ : 0 < ρ) (hK : 2 ≤ K) :
    ∃ n₀ : ℕ,
      ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
        n₀ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
        K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
        F ⊆ cliqueEdges W → TriDivisible F →
        TriDivisible (F ∩ cliqueEdges W') → TriDivisible (F ∩ cliqueEdges W'') →
        (∀ v ∈ W, c * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
        (∀ v ∈ W', (c - 9 / 10) * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
        ∃ R : Finset (Sym2 V), R ⊆ F \ cliqueEdges W' ∧
          (∀ v : V, (edeg R v : ℝ) ≤ ρ * (W.card : ℝ)) ∧
          (TriDivisible R →
            ∃ Q : Finset (Finset V), TriFamilyIn F Q ∧ R ⊆ famEdges Q ∧
              famEdges Q ⊆ R ∪ (cliqueEdges W' \ cliqueEdges W'')) := by
  classical
  obtain ⟨η, n₀, hη, habs⟩ := hAbs c γ ρ K hc hγ hρ hK
  refine ⟨n₀, ?_⟩
  intro V inst W W' W'' F hcard hW' hW'' hKW hKKW hKW'' hFW hdivF hdivF' hdivF'' hdense hdenseW'
  obtain ⟨R, hRsub, hRdeg, habs2⟩ :=
    habs W W' W'' F hcard hW' hW'' hKW hKKW hKW'' hFW hdivF hdivF' hdivF'' hdense hdenseW'
  refine ⟨R, hRsub, hRdeg, fun hdivR => ?_⟩
  have hempty : (∅ : Finset (Sym2 V)) ⊆ (F \ cliqueEdges W') \ R := Finset.empty_subset _
  have hdeg0 : ∀ v : V, (edeg (∅ : Finset (Sym2 V)) v : ℝ) ≤ η * (W.card : ℝ) := by
    intro v
    have h0 : edeg (∅ : Finset (Sym2 V)) v = 0 := by simp [edeg]
    rw [h0]
    have : (0 : ℝ) ≤ η * (W.card : ℝ) := by positivity
    simpa using this
  have hRunion : R ∪ (∅ : Finset (Sym2 V)) = R := Finset.union_empty R
  obtain ⟨Q, hQ, hQcov, hQconf, -⟩ :=
    habs2 ∅ hempty hdeg0 (by rw [hRunion]; exact hdivR)
  rw [hRunion] at hQcov hQconf
  exact ⟨Q, hQ, hQcov, hQconf⟩

/-! ### The far part must be covered from inside the remainder, as a triangle family -/

/-- **A triangle on a far edge lies entirely in the remainder.**  If a triangle `t` of a confined
family contains two vertices outside `W'`, then *all three* of its edges belong to `S`: an edge of
`t` inside `W'` would have both endpoints in the singleton `t \ {u, v}`, hence be a loop. -/
theorem cliqueEdges_subset_of_far_triangle {W' W'' : Finset V} {S : Finset (Sym2 V)}
    {Q : Finset (Finset V)} (hQ3 : ∀ t ∈ Q, t.card = 3)
    (hconf : famEdges Q ⊆ S ∪ (cliqueEdges W' \ cliqueEdges W''))
    {t : Finset V} (ht : t ∈ Q) {u v : V} (hu : u ∉ W') (hv : v ∉ W') (huv : u ≠ v)
    (hut : u ∈ t) (hvt : v ∈ t) : cliqueEdges t ⊆ S := by
  classical
  have hsub : ({u, v} : Finset V) ⊆ t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    exacts [hut, hvt]
  have hcard2 : ({u, v} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using huv), Finset.card_singleton]
  have hone : (t \ ({u, v} : Finset V)).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hQ3 t ht, hcard2]
  obtain ⟨w, hw⟩ := Finset.card_eq_one.1 hone
  intro e he
  have hmem : e ∈ famEdges Q := Finset.subset_biUnion_of_mem cliqueEdges ht he
  rcases Finset.mem_union.1 (hconf hmem) with h | h
  · exact h
  · exfalso
    have hW' : e ∈ cliqueEdges W' := (Finset.mem_sdiff.1 h).1
    have hallt : ∀ x ∈ e, x ∈ t := (mem_cliqueEdgesV.1 he).1
    have hnd : ¬ e.IsDiag := (mem_cliqueEdgesV.1 he).2
    have hallW' : ∀ x ∈ e, x ∈ W' := (mem_cliqueEdgesV.1 hW').1
    have hallw : ∀ x ∈ e, x = w := by
      intro x hx
      have hxt : x ∈ t := hallt x hx
      have hxW' : x ∈ W' := hallW' x hx
      have hxuv : x ∉ ({u, v} : Finset V) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (rfl | rfl)
        exacts [hu hxW', hv hxW']
      have : x ∈ t \ ({u, v} : Finset V) := Finset.mem_sdiff.2 ⟨hxt, hxuv⟩
      rw [hw] at this
      exact Finset.mem_singleton.1 this
    refine hnd ?_
    revert hallw hnd
    induction e using Sym2.ind with
    | _ x y =>
      intro hnd hallw
      have hx : x = w := hallw x (by simp)
      have hy : y = w := hallw y (by simp)
      simp [Sym2.isDiag_iff_proj_eq, hx, hy]

/-- **The far part of the remainder carries its own triangle family.**  Sharpening
`BKLO.shellAbsorptionDense_forces_far_cherries`: whatever reservation a proof of
`BKLO.ShellAbsorptionDense` produces at a dense level, for every admissible leftover there is an
edge-disjoint family of triangles **all of whose edges lie in `R ∪ L`** that covers every edge of
`R ∪ L` with both endpoints outside `W'`.

So the density of the level does not enter the far part at all: the reservation must already
contain a triangle family covering the far edges of the shell remainder.  (It may do so with apexes
inside the dense level `W'`, using reserved cross edges — which is precisely what a hollow instance
forbids and what the level-density hypothesis makes possible.) -/
theorem shellAbsorptionDense_forces_far_triangle_cover (hAbs : ShellAbsorptionDense)
    (c γ ρ : ℝ) (K : ℕ) (hc : 9 / 10 < c) (hγ : 0 < γ) (hρ : 0 < ρ) (hK : 2 ≤ K) :
    ∃ (η : ℝ) (n₀ : ℕ), 0 < η ∧
      ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
        n₀ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
        K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
        F ⊆ cliqueEdges W → TriDivisible F →
        TriDivisible (F ∩ cliqueEdges W') → TriDivisible (F ∩ cliqueEdges W'') →
        (∀ v ∈ W, c * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
        (∀ v ∈ W', (c - 9 / 10) * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
        ∃ R : Finset (Sym2 V), R ⊆ F \ cliqueEdges W' ∧
          (∀ v : V, (edeg R v : ℝ) ≤ ρ * (W.card : ℝ)) ∧
          ∀ L : Finset (Sym2 V), L ⊆ (F \ cliqueEdges W') \ R →
            (∀ v : V, (edeg L v : ℝ) ≤ η * (W.card : ℝ)) →
            TriDivisible (R ∪ L) →
            ∃ Q' : Finset (Finset V), TriFamilyIn (R ∪ L) Q' ∧
              ∀ u v : V, u ∉ W' → v ∉ W' → s(u, v) ∈ R ∪ L → s(u, v) ∈ famEdges Q' := by
  classical
  obtain ⟨η, n₀, hη, habs⟩ := hAbs c γ ρ K hc hγ hρ hK
  refine ⟨η, n₀, hη, ?_⟩
  intro V inst W W' W'' F hcard hW' hW'' hKW hKKW hKW'' hFW hdivF hdivF' hdivF'' hdense hdenseW'
  obtain ⟨R, hRsub, hRdeg, habs2⟩ :=
    habs W W' W'' F hcard hW' hW'' hKW hKKW hKW'' hFW hdivF hdivF' hdivF'' hdense hdenseW'
  refine ⟨R, hRsub, hRdeg, ?_⟩
  intro L hL hLdeg hdiv
  obtain ⟨Q, hQ, hQcov, hQconf, -⟩ := habs2 L hL hLdeg hdiv
  refine ⟨Q.filter (fun t => cliqueEdges t ⊆ R ∪ L), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact fun t ht => hQ.1 t (Finset.mem_of_mem_filter t ht)
  · exact fun t ht => (Finset.mem_filter.1 ht).2
  · exact fun t ht t' ht' hne =>
      hQ.2.2 t (Finset.mem_of_mem_filter t ht) t' (Finset.mem_of_mem_filter t' ht') hne
  · intro u v hu hv he
    obtain ⟨t, htQ, het⟩ := Finset.mem_biUnion.1 (hQcov he)
    obtain ⟨hall, hnd⟩ := mem_cliqueEdgesV.1 het
    have huv : u ≠ v := by
      intro h; exact hnd (by simp [Sym2.isDiag_iff_proj_eq, h])
    have hut : u ∈ t := hall u (by simp)
    have hvt : v ∈ t := hall v (by simp)
    have hts : cliqueEdges t ⊆ R ∪ L :=
      cliqueEdges_subset_of_far_triangle hQ.1 hQconf htQ hu hv huv hut hvt
    exact Finset.mem_biUnion.2 ⟨t, Finset.mem_filter.2 ⟨htQ, hts⟩, het⟩

end BKLO
