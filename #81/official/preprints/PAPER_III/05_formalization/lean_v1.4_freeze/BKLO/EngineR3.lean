/-
# The **thrice-repaired** fused §10 interface.

`BKLO.VortexReservoirEngineR2` (`BKLO/ReservoirRepaired2.lean`) is still false, and the defect is
again in the *descent* clause: see `BKLO.not_vortexDescentClauseR2_window` and
`BKLO.not_vortexReservoirEngineR2` in `BKLO/DescentRefutation2.lean`.

The point is a *budget* one.  `BKLO.VortexDescentClauseR2` allows an avoidance set `D` with
`K|D| ≤ m` and still asks, of every vertex outside `D`, the *full* density `f(m)m` into the new
level.  A level of size `m` must be chosen inside a pool `W \ D` of size `|W| - |D| ≈ 2m`, so a
vertex whose non-neighbourhood is spread over that pool loses, on average,
`(1-f)|W|·m/(|W|-|D|) = (1-f)m·(1 + |D|/(2m))` neighbours, i.e. `(1-f)|D|/2 ≈ m/(20K)` more than
the `(1-f)m` the density at scale `m` provides for.  So the schedule must drop by a *fixed* amount
`≈ 1/(20K)` at every scale — and it only has the window `ε/2` to drop in, while the vortex has
unboundedly many scales.  `BKLO/DescentRefutation2.lean` turns this into an explicit witness (a
circulant complement on the pool) and an explicit contradiction.

The repair is to make the loss `|D|` costs *visible in the conclusion*, and to let the descent
exploit whatever density the level actually has, rather than only the density the schedule
prescribes:

* an explicit density parameter `a ≥ f |W|`: if the current level is denser than the schedule
  demands, the new level inherits the surplus (on all but the forced part `U`);
* the loss `|D|` is subtracted from the conclusion.

With `D = ∅` and `a = f |W|` — the shape the vortex recursion consumes at every level below the
top — the conclusion is exactly the one of `BKLO.VortexDescentClauseR2` (see
`BKLO.descent_of_R3`).  At the *top* level, which is the only place where `D ≠ ∅`, the surplus is
available: the host graph has minimum degree `(9/10 + ε)n` while the schedule only asks
`9/10 + 3ε/4`, and `ε/4·n` pays for `|D|` many times over.  This is carried out in
`BKLO/MainRepaired3.lean`.

Unlike `BKLO.VortexDescentClauseR2`, this clause is a **theorem**
(`BKLO.vortexDescentClauseR3_of_powerSchedule`, `BKLO/ScheduleR3.lean`).

The interface is also restricted to `ε ≤ 1/100`, which costs nothing: the conclusion of §10 for a
small `ε` implies it for every larger one.

Everything here is `sorry`-free: these are definitions plus one elementary lemma about them.
-/
import BKLO.ReservoirRepaired2

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- **The thrice-repaired descent clause**: one level of the vortex, of a prescribed size `m`,
containing a prescribed bottom set `U` with `K|U| ≤ m` and avoiding a prescribed set `D` with
`K|D| ≤ m`.

The current level is assumed to have density `a`, which may exceed the density `f |W|` the
schedule prescribes.  Outside `D` the new level then carries the density `f m` of the schedule,
increased by the surplus `a - f |W|` on all but the forced part `U`, and decreased by the size of
the avoidance set; every vertex of `W`, including the vertices of `D`, is dense into it up to the
`2|U|/m ≤ 2/K` that the forced part and the avoidance set can cost.

With `a = f |W|` and `D = ∅` this is exactly the conclusion of `BKLO.VortexDescentClauseR2`
(`BKLO.descent_of_R3`). -/
def VortexDescentClauseR3 (f : ℕ → ℝ) (n₂ K : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (W U D : Finset V) (E : Finset (Sym2 V)) (m : ℕ) (a : ℝ),
    n₂ ≤ U.card → U ⊆ W → Disjoint U D → K * U.card ≤ m → K * D.card ≤ m →
    2 * m + D.card ≤ W.card → W.card ≤ K * K * m →
    f W.card ≤ a → a ≤ 1 →
    E ⊆ cliqueEdges W →
    (∀ v ∈ W, a * (W.card : ℝ) ≤ (edeg E v : ℝ)) →
    (∀ v ∈ W \ D, f U.card * (U.card : ℝ) ≤ ((resLink E U v).card : ℝ)) →
    ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ Disjoint W' D ∧ W'.card = m ∧
      (∀ v ∈ W \ D, f m * (m : ℝ) + (a - f W.card) * ((m : ℝ) - (U.card : ℝ)) - (D.card : ℝ)
          ≤ ((resLink E W' v).card : ℝ)) ∧
      (∀ v ∈ W, (f m - 2 / (K : ℝ)) * (m : ℝ) ≤ ((resLink E W' v).card : ℝ))

/-- **The thrice-repaired fused §10 interface: vortex + reservoir.**  As
`BKLO.VortexReservoirEngineR2`, with the repaired descent clause, a schedule window narrowed to
the lower three quarters (so that a level of the host graph always carries a surplus over the
schedule), and `ε` restricted to `ε ≤ 1/100`. -/
def VortexReservoirEngineR3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ (n₀ : ℕ) (N : ℝ → ℕ), ∃ (f : ℕ → ℝ) (n₂ C K : ℕ) (η : ℝ),
    2 ≤ K ∧ (8 : ℝ) / ε ≤ (K : ℝ) ∧ 0 < η ∧
    n₀ ≤ n₂ ∧ N η ≤ n₂ ∧ n₂ ≤ C ∧ 0 < n₂ ∧
    (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + 3 * ε / 4) ∧
    VortexBottomClauseR2 ε f n₂ C K ∧ VortexDescentClauseR3 f n₂ K ∧ ReservoirClauseR ε η f n₂ K

/-- Inside the vortex the avoidance set is empty and the level has exactly the density the
schedule prescribes; then the conclusion of the thrice-repaired descent clause is the conclusion
of `BKLO.VortexDescentClauseR2` (compare `BKLO.descent_of_R2`): this is the form the recursion
consumes. -/
theorem descent_of_R3 {f : ℕ → ℝ} {n₂ K : ℕ} (h : VortexDescentClauseR3 f n₂ K)
    {V : Type} [DecidableEq V] (W U : Finset V) (E : Finset (Sym2 V)) (m : ℕ)
    (hU : n₂ ≤ U.card) (hUW : U ⊆ W) (hKU : K * U.card ≤ m) (h2m : 2 * m ≤ W.card)
    (hWm : W.card ≤ K * K * m) (hf1 : f W.card ≤ 1) (hEW : E ⊆ cliqueEdges W)
    (hdeg : ∀ v ∈ W, f W.card * (W.card : ℝ) ≤ (edeg E v : ℝ))
    (hbot : ∀ v ∈ W, f U.card * (U.card : ℝ) ≤ ((resLink E U v).card : ℝ)) :
    ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ W'.card = m ∧
      ∀ v ∈ W, f m * (m : ℝ) ≤ ((resLink E W' v).card : ℝ) := by
  classical
  obtain ⟨W', hUW', hW'W, -, hcard, hstrong, -⟩ :=
    h W U ∅ E m (f W.card) hU hUW (Finset.disjoint_empty_right _) hKU (by simp)
      (by simpa using h2m) hWm le_rfl hf1 hEW hdeg (fun v hv => hbot v (Finset.mem_sdiff.1 hv).1)
  refine ⟨W', hUW', hW'W, hcard, fun v hv => ?_⟩
  have h := hstrong v (by simpa using hv)
  simpa using h

end BKLO
