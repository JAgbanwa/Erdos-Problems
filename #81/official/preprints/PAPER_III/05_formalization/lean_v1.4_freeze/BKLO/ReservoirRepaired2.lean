/-
# The **twice-repaired** fused §10 interface.

`BKLO.VortexReservoirEngine` is false (`BKLO.not_vortexReservoirEngine`), and so is the first
repair `BKLO.VortexReservoirEngineR` (`BKLO.not_vortexReservoirEngineR`): its *descent* clause
asks for a level `U ⊆ W' ⊆ W` of prescribed size `m` into which every vertex of `W` is dense,
while allowing (i) the prescribed bottom set `U` to be as large as the level itself and (ii) the
prescribed avoidance set `D` to be as large as `W`.  Either freedom breaks the clause: `|U| = m`
forces `W' = U`, and a large `D` may hide all the neighbours of a vertex.

This file states the interface with those two defects repaired.  Only the *vortex* clauses change;
the reservoir clause `BKLO.ReservoirClauseR` is unchanged.

7. **The bottom set and the avoidance set must be small compared with the level**: `K|U| ≤ m` and
   `K|D| ≤ m`.  Both hold at every use in the vortex: the levels of a vortex shrink by a factor
   `K` at a time, and the avoidance set is the (bounded) set of vertices met by the reserved edge
   set together with the exceptional set of the bottom clause.

8. **The density into the bottom set is a hypothesis of the descent**, for the vertices outside
   `D`.  It has to be: a random level of size `m` can only inherit the density that `W` has into
   the *forced* part `U` of the level.  This is exactly the invariant the vortex recursion carries
   (`BKLO.coverDown_vortex_denseR2`), and at the top level it is what the bottom clause provides.

   Consequently the conclusion is *graded*: outside `D` the new level carries the full density
   `f(m)m`, while a vertex of `D` — for which nothing is known about its links into `U` — is only
   guaranteed `(f(m) - 1/K)m`, the loss `|U| ≤ m/K` that the forced part can cost.  Both grades
   come from one and the same random level.

9. **The exceptional set of the bottom clause must be smaller than `|S|/(4K²)`**, not `|S|/8`,
   since it is fed to the descent clause as part of the avoidance set `D`, and `K|D| ≤ m ≈ |S|/K`.
   For a random bottom set the exceptional set has density `O(1/(ε²|U|))`, so this costs nothing
   but a larger `C`.

Everything here is `sorry`-free: these are definitions plus one elementary lemma about them.
-/
import BKLO.ReservoirRepaired

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- **The twice-repaired bottom-set clause.**  As `BKLO.VortexBottomClauseR`, with the exceptional
set required to be smaller by a factor `4K²`, so that it can be avoided by the top level of the
vortex. -/
def VortexBottomClauseR2 (ε : ℝ) (f : ℕ → ℝ) (n₂ C K : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (S : Finset V) (E : Finset (Sym2 V)),
    n₂ ≤ S.card → E ⊆ cliqueEdges S →
    (∀ v ∈ S, (9 / 10 + ε) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
    ∃ U B : Finset V, U ⊆ S ∧ B ⊆ S ∧ Disjoint U B ∧ n₂ ≤ U.card ∧ U.card ≤ C ∧
      4 * K * K * B.card ≤ S.card ∧
      ∀ v ∈ S \ B, f U.card * (U.card : ℝ) ≤ ((resLink E U v).card : ℝ)

/-- **The twice-repaired descent clause**: one level of the vortex, of a prescribed size `m`,
containing a prescribed bottom set `U` with `K|U| ≤ m` and avoiding a prescribed set `D` with
`K|D| ≤ m`.

Outside `D` — where the density into `U` is known — the new level carries the full density; every
vertex of `W`, including the vertices of `D`, is dense into it up to the `|U|/m ≤ 1/K` that the
forced part `U` of the level can cost. -/
def VortexDescentClauseR2 (f : ℕ → ℝ) (n₂ K : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (W U D : Finset V) (E : Finset (Sym2 V)) (m : ℕ),
    n₂ ≤ U.card → U ⊆ W → Disjoint U D → K * U.card ≤ m → K * D.card ≤ m →
    2 * m + D.card ≤ W.card → W.card ≤ K * K * m →
    E ⊆ cliqueEdges W →
    (∀ v ∈ W, f W.card * (W.card : ℝ) ≤ (edeg E v : ℝ)) →
    (∀ v ∈ W \ D, f U.card * (U.card : ℝ) ≤ ((resLink E U v).card : ℝ)) →
    ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ Disjoint W' D ∧ W'.card = m ∧
      (∀ v ∈ W \ D, f m * (m : ℝ) ≤ ((resLink E W' v).card : ℝ)) ∧
      (∀ v ∈ W, (f m - 1 / (K : ℝ)) * (m : ℝ) ≤ ((resLink E W' v).card : ℝ))

/-- **The twice-repaired fused §10 interface: vortex + reservoir.** -/
def VortexReservoirEngineR2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ (n₀ : ℕ) (N : ℝ → ℕ), ∃ (f : ℕ → ℝ) (n₂ C K : ℕ) (η : ℝ),
    2 ≤ K ∧ (8 : ℝ) / ε ≤ (K : ℝ) ∧ 0 < η ∧
    n₀ ≤ n₂ ∧ N η ≤ n₂ ∧ n₂ ≤ C ∧ 0 < n₂ ∧
    (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + ε) ∧
    VortexBottomClauseR2 ε f n₂ C K ∧ VortexDescentClauseR2 f n₂ K ∧ ReservoirClauseR ε η f n₂ K

/-- Inside the vortex the avoidance set is empty, and then the two grades of the descent clause's
conclusion coincide: this is the form the recursion consumes. -/
theorem descent_of_R2 {f : ℕ → ℝ} {n₂ K : ℕ} (h : VortexDescentClauseR2 f n₂ K)
    {V : Type} [DecidableEq V] (W U : Finset V) (E : Finset (Sym2 V)) (m : ℕ)
    (hU : n₂ ≤ U.card) (hUW : U ⊆ W) (hKU : K * U.card ≤ m) (h2m : 2 * m ≤ W.card)
    (hWm : W.card ≤ K * K * m) (hEW : E ⊆ cliqueEdges W)
    (hdeg : ∀ v ∈ W, f W.card * (W.card : ℝ) ≤ (edeg E v : ℝ))
    (hbot : ∀ v ∈ W, f U.card * (U.card : ℝ) ≤ ((resLink E U v).card : ℝ)) :
    ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ W'.card = m ∧
      ∀ v ∈ W, f m * (m : ℝ) ≤ ((resLink E W' v).card : ℝ) := by
  classical
  obtain ⟨W', hUW', hW'W, -, hcard, hstrong, -⟩ :=
    h W U ∅ E m hU hUW (Finset.disjoint_empty_right _) hKU (by simp)
      (by simpa using h2m) hWm hEW hdeg (fun v hv => hbot v (Finset.mem_sdiff.1 hv).1)
  exact ⟨W', hUW', hW'W, hcard, fun v hv => hstrong v (by simpa using hv)⟩

end BKLO
