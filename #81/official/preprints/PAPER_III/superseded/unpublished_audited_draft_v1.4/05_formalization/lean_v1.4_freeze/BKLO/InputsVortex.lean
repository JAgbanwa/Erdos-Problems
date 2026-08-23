/-
# BKLO §10 — the two external inputs of the vortex, stated as interfaces.

This file is the continuation of `BKLO/Inputs.lean`.  It has to live downstream of
`BKLO/Vortex.lean` because the two interfaces below are phrased in the edge-set vocabulary
(`cliqueEdges`, `edeg`, `TriDivisible`, `TriFamilyIn`, `famEdges`) that is developed there.

Both interfaces are **true theorems** of the BKLO paper (specialised to `F = K₃`), kept here as
*assumed inputs* exactly like Dross's threshold (`FracTriangleThreshold`), the Haxell–Rödl nibble
(`FracToApprox`) and Dirac's theorem (`PerfectMatchingDirac`):

* `VortexScheduleExists` — **BKLO §10, existence of the vortex.**  A graph of large minimum degree
  contains, inside any prescribed small bottom set, a subset of any prescribed size (at most half
  of the ambient one) on which the induced graph still has large minimum degree.  This is the
  standard probabilistic lemma: for a uniformly random `m`-subset `W' ⊆ W` containing `U`, each
  `v` has `deg_{W'}(v) ≥ (deg_W(v)/|W|)·m − O(√(m log m))` except with probability `o(1/m)`, so
  the expected number of vertices of `W'` failing the bound is `< 1`.

  The relative loss `O(√(log m / m))` is decreasing in `m`, which is why the input supplies a
  *density schedule* `f`: the density demanded at a level of size `s` decreases with `s`, a witness
  being `f s = 9/10 + ε − K·√(log s / s)` truncated into `[9/10 + ε/2, 9/10 + ε]`.  Because the
  losses down the vortex are dominated by the loss at the smallest level, a single loss from
  `9/10 + ε` to `9/10 + ε/2` pays for the whole vortex.

  It is precisely this bookkeeping which cannot be done with a *fixed* density: restricting a graph
  of minimum degree `c|W|` to a subset `W'` gives minimum degree `c|W'| − Θ(√|W'|)`, never `c|W'|`
  on the nose.

* `CoverDownK3` — **BKLO §10, the cover-down lemma for `F = K₃`.**  One level of the vortex: a
  triangle-divisible edge set `F` of minimum degree `> (9/10)|W|` spanned by `W` is covered by
  edge-disjoint triangles down to a remainder inside the next level `W'`, in such a way that (i)
  not a single edge inside the level `W''` after the next is touched and (ii) each vertex of `W'`
  keeps all but `γ|W'|` of its edges inside `W'`.

  The size window `|W|/K² ≤ |W'| ≤ |W|/K` is essential and is BKLO's: the nibble is applied to `F`
  minus the edges inside `W'` (and minus a sparse reservoir), and this only keeps the minimum
  degree above `(9/10)|W|` — where Dross's threshold applies — because `|W'| ≤ |W|/K` is a *small*
  fraction of `|W|`, with `1/K` below the density slack `c − 9/10`.  The lower bound `|W'| ≥ |W|/K²`
  is equally necessary: the vertices of `W'` are the apexes covering the nibble's leftover, and
  each of them can serve only `O(|W|)` times.

  The proof is: Dross plus the nibble (`BKLO.nibbleReserving_of_inputs`, proved in
  `BKLO/SetGraph.lean`) for the bulk; the greedy of `BKLO.exists_coverDown_family` (proved in
  `BKLO/CoverDown.lean`) for the sparse leftover, with the leftover edges meeting `W'` covered by
  apexes *outside* `W'` so that no edge inside `W'` is consumed; a bounded parity and
  `3`-divisibility correction using edges inside `W'` but outside `W''` — this is what makes (i)
  available, hence what stops the damage of (ii) from accumulating down the vortex; and perfect
  matchings for the links of the remaining vertices (`PerfectMatchingDirac`; for `F = K₃`, which is
  `2`-regular, the `Kᵣ`-factors of BKLO Thm 10.2 are perfect matchings).

Everything here is `sorry`-free: these are definitions of interface predicates, not claims.
`BKLO/InputsVortexSat.lean` checks that neither interface is vacuous.
-/
import BKLO.Vortex

open Finset

namespace BKLO

/-- Instance-irrelevance for `edeg`: needed because `GoodPred` quantifies over a bare `Type`. -/
theorem edeg_inst_irrel {V : Type*} (i₁ i₂ : DecidableEq V) (E : Finset (Sym2 V)) (v : V) :
    @edeg V i₁ E v = @edeg V i₂ E v := by
  have : i₁ = i₂ := Subsingleton.elim _ _
  subst this; rfl

/-- **Input 4 (BKLO §10, existence of the vortex; Chernoff).**

For every `ε > 0` and every size threshold `n₀` there are a *density schedule* `f`, a bottom size
threshold `n₂ ≥ n₀` and a bound `C` such that

* `f` stays inside `[9/10 + ε/2, 9/10 + ε]` on all sizes `≥ n₂`;
* every large edge set `E` of minimum degree at least `(9/10 + ε)|S|` has a **good bottom set**
  `U ⊆ S` with `n₂ ≤ |U| ≤ C` on which the induced edge set still has minimum degree at least
  `f(|U|)·|U|`;
* **(descent)** for every such `E` on a set `W`, every prescribed bottom set `U ⊆ W` with
  `n₂ ≤ |U|` and every target size `m` with `|U| ≤ m` and `2m ≤ |W|`, there is a **next level**
  `W'` with `U ⊆ W' ⊆ W` of size exactly `m` on which the induced edge set has minimum degree at
  least `f(m)·m`.

Iterating the descent produces the vortex `S ⊇ W₁ ⊇ W₂ ⊇ … ⊇ U`. -/
def VortexScheduleExists : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ n₀ : ℕ, ∃ (f : ℕ → ℝ) (n₂ C : ℕ),
    n₀ ≤ n₂ ∧ n₂ ≤ C ∧ 0 < n₂ ∧
    (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + ε) ∧
    -- good bottom sets of bounded size
    (∀ {V : Type} [DecidableEq V] (S : Finset V) (E : Finset (Sym2 V)),
        n₂ ≤ S.card → E ⊆ cliqueEdges S →
        (∀ v ∈ S, (9 / 10 + ε) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
        ∃ U : Finset V, U ⊆ S ∧ n₂ ≤ U.card ∧ U.card ≤ C ∧
          ∀ v ∈ U, f U.card * (U.card : ℝ) ≤ (edeg (E ∩ cliqueEdges U) v : ℝ)) ∧
    -- one level of descent, of a prescribed size, keeping a prescribed bottom set
    (∀ {V : Type} [DecidableEq V] (W U : Finset V) (E : Finset (Sym2 V)) (m : ℕ),
        n₂ ≤ U.card → U ⊆ W → U.card ≤ m → 2 * m ≤ W.card → E ⊆ cliqueEdges W →
        (∀ v ∈ W, f W.card * (W.card : ℝ) ≤ (edeg E v : ℝ)) →
        ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ W'.card = m ∧
          ∀ v ∈ W', f m * (m : ℝ) ≤ (edeg (E ∩ cliqueEdges W') v : ℝ))

/-- **Input 5 (BKLO §10, the cover-down lemma for `F = K₃`).**

For every ambient density `c > 9/10` and every damage tolerance `γ > 0` there are a size ratio
`K ≥ 2` and a threshold `n₀` such that: for all vertex sets `W'' ⊆ W' ⊆ W` with `|W| ≥ n₀`,
`K|W'| ≤ |W| ≤ K²|W'|` and `K|W''| ≤ |W'|`, every triangle-divisible edge set `F` spanned by `W`
with minimum degree at least `c|W|` admits an edge-disjoint family `P` of triangles inside `F`
such that

* the leftover `F \ famEdges P` lies inside `W'`;
* no edge of `F` inside `W''` is used;
* every vertex of `W'` loses at most `γ|W'|` of its edges inside `W'`. -/
def CoverDownK3 : Prop :=
  ∀ c γ : ℝ, 9 / 10 < c → 0 < γ → ∃ K n₀ : ℕ, 2 ≤ K ∧
    ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
      n₀ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
      K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
      F ⊆ cliqueEdges W → TriDivisible F → (∀ v ∈ W, c * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn F P ∧
        F \ famEdges P ⊆ cliqueEdges W' ∧
        F ∩ cliqueEdges W'' ⊆ F \ famEdges P ∧
        ∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
          ≤ (edeg (F \ famEdges P) v : ℝ) + γ * (W'.card : ℝ)

end BKLO
