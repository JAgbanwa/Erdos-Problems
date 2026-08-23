/-
# The **repaired** fused §10 interface.

`BKLO.VortexReservoirEngine` is false: `BKLO.not_vortexReservoirEngine` refutes its apex-abundance
clause (nothing forces a vertex of `W \ W'` to have any `F`-neighbour inside `W'`), and
`BKLO.not_reservoirClauseCoDense` refutes its link-cover clause even after that first gap is
closed (nothing stops one vertex of `W'` from being added to *every* link).

This file states the repaired interface.  Six things change.  The first three *add* information
that the derivation of the cover-down step (`BKLO.coverDown_of_reservoirR`) has in its hands
anyway; the last three *weaken* what the vortex asks of its levels, in each case to something that
a random choice can actually deliver.  The repaired clauses are still consumed in the same way and
the main theorem still follows (`BKLO/MainRepaired.lean`).

1. **Between-levels density** is added as a hypothesis of the reservoir clause: every vertex of
   `W` has at least `(9/10 + ε/4)|W'|` `F`-neighbours inside `W'`.  This is what the vortex
   supplies: the levels are chosen so that *every* vertex of the current level, not only the
   vertices of the next one, is dense into the next level.  Accordingly the bottom and descent
   clauses (`BKLO.VortexBottomClauseR`, `BKLO.VortexDescentClauseR`) now produce a level that is
   dense as seen from the *whole* current set — a strengthening of the old conclusions, which are
   recovered by `BKLO.edeg_inter_cliqueEdges_eq_card_resLink` (see
   `BKLO.vortexDescentClause_of_R_ratio`).

2. **A global multiplicity bound** on the link systems: the link cover is demanded only of those
   link systems in which each `a ∈ W'` is *added* to at most `2η|W|` of the links.  Without it the
   clause is false.  The derivation supplies it: the added vertices come from the nibble's
   leftover, whose degree at `a` is at most `η|W|`.

3. **A damage bound at the scale of the protected level**: the link cover uses, at each vertex of
   `W'`, at most `γ|W''|` edges running into `W''`.  This is what keeps the between-levels density
   of hypothesis 1 alive along the vortex: without it, the `γ|W'|` edges a cover-down step is
   allowed to consume at a vertex of `W'` could all run into `W''`, which is `K` times smaller.

4. **An avoidance set for the descent** (see `BKLO.VortexDescentClauseR`): the top level of the
   vortex must be allowed to avoid a prescribed small set of vertices, because the bounded bottom
   set is chosen before the reserved edge set whose deletion damages the links into it.

5. **An exceptional set for the bottom clause** (see `BKLO.VortexBottomClauseR`): only all but a
   `1/8` fraction of `S` is required to be dense into the bottom set.  Asking it of *every* vertex
   is false for `|S|` exponentially large in the size bound `C`.

6. **A size ratio for the descent clause**: `|W| ≤ K²m`, for the same reason.  Every use of the
   clause in the vortex is within that window.

Nothing else changes; in particular the reservoir is still required to be crossing, sparse and
apex-abundant, and the cover is still required to be edge-disjoint, to use only crossing edges of
the system and edges inside `W'`, and to touch no edge inside `W''`.

Everything here is `sorry`-free: these are definitions plus elementary lemmas about them.
-/
import BKLO.CoverDownFused

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Links and degrees -/

/-- Inside a loopless edge set, the degree of `v ∈ U` in the part spanned by `U` is the size of the
link of `v` in `U`. -/
theorem edeg_inter_cliqueEdges_eq_card_resLink {E : Finset (Sym2 V)} {U : Finset V} {v : V}
    (hv : v ∈ U) (hnd : ∀ e ∈ E, ¬ e.IsDiag) :
    edeg (E ∩ cliqueEdges U) v = (resLink E U v).card := by
  classical
  have hfil : (E ∩ cliqueEdges U).filter (fun e => v ∈ e)
      = (resLink E U v).image (fun a => s(v, a)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_image]
    constructor
    · rintro ⟨⟨heE, heU⟩, hve⟩
      obtain ⟨a, rfl⟩ : ∃ a, e = s(v, a) := by
        induction e using Sym2.ind with
        | _ x y =>
          rcases Sym2.mem_iff.1 hve with rfl | rfl
          · exact ⟨y, rfl⟩
          · exact ⟨x, Sym2.eq_swap⟩
      exact ⟨a, mem_resLink.2 ⟨(mem_cliqueEdgesV.1 heU).1 a (by simp), heE⟩, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨haU, haE⟩ := mem_resLink.1 ha
      have hne : v ≠ a := by
        intro h
        exact hnd _ haE (by simp [Sym2.isDiag_iff_proj_eq, h])
      refine ⟨⟨haE, mem_cliqueEdgesV.2 ⟨?_, ?_⟩⟩, by simp⟩
      · intro z hz
        rcases Sym2.mem_iff.1 hz with rfl | rfl
        exacts [hv, haU]
      · simpa [Sym2.isDiag_iff_proj_eq] using hne
  rw [edeg, hfil, card_image_star]

/-- Restricting a loopless edge set to a level does not change the links inside a smaller level. -/
theorem resLink_inter_cliqueEdges {E : Finset (Sym2 V)} {W' W'' : Finset V} (hW'' : W'' ⊆ W')
    {v : V} (hv : v ∈ W') (hnd : ∀ e ∈ E, ¬ e.IsDiag) :
    resLink (E ∩ cliqueEdges W') W'' v = resLink E W'' v := by
  classical
  ext a
  simp only [mem_resLink, Finset.mem_inter]
  constructor
  · rintro ⟨ha, hE, -⟩; exact ⟨ha, hE⟩
  · rintro ⟨ha, hE⟩
    refine ⟨ha, hE, mem_cliqueEdgesV.2 ⟨?_, ?_⟩⟩
    · intro z hz
      rcases Sym2.mem_iff.1 hz with rfl | rfl
      exacts [hv, hW'' ha]
    · exact hnd _ hE

theorem resLink_mono {E E' : Finset (Sym2 V)} (h : E ⊆ E') (W' : Finset V) (v : V) :
    resLink E W' v ⊆ resLink E' W' v := by
  intro a ha
  obtain ⟨h1, h2⟩ := mem_resLink.1 ha
  exact mem_resLink.2 ⟨h1, h h2⟩

/-! ### The repaired clauses -/

/-- **The repaired link cover.**  A link cover which in addition uses, at each vertex of `W'`, at
most `γ|W''|` edges running into the protected level `W''`.  (It already uses no edge *inside*
`W''` at all.) -/
def IsLinkCoverR (F : Finset (Sym2 V)) (W' W'' D : Finset V) (X : V → Finset V) (γ : ℝ)
    (Q : Finset (Finset V)) : Prop :=
  IsLinkCover F W' W'' D X γ Q ∧
    ∀ v ∈ W', ((resLink (famEdges Q) W'' v).card : ℝ) ≤ γ * (W''.card : ℝ)

/-- **The repaired bottom-set clause**: every large dense edge set contains a good bottom set of
bounded size, dense as seen from all of `S` *outside a small exceptional set* `B`.

The exceptional set is unavoidable, and this is the fifth repair.  Asking every vertex of `S` to
be dense into a bottom set of *bounded* size `C` is false once `|S|` is large compared with
`exp(C)`: in a random graph of density `0.95` a fixed `C`-set fails some vertex with a probability
`q = q(C) > 0` that does not depend on `|S|`, and there are only `|S|^C` candidate bottom sets, so
a first-moment bound rules all of them out as soon as `|S| ≫ C log|S| / q`.  What a random bottom
set *does* give, by Chernoff plus Markov, is a bounded exceptional set of density `q`, which is
what is asked here.  The vortex then simply avoids `B`, via the avoidance set of
`BKLO.VortexDescentClauseR`. -/
def VortexBottomClauseR (ε : ℝ) (f : ℕ → ℝ) (n₂ C : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (S : Finset V) (E : Finset (Sym2 V)),
    n₂ ≤ S.card → E ⊆ cliqueEdges S →
    (∀ v ∈ S, (9 / 10 + ε) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
    ∃ U B : Finset V, U ⊆ S ∧ B ⊆ S ∧ Disjoint U B ∧ n₂ ≤ U.card ∧ U.card ≤ C ∧
      8 * B.card ≤ S.card ∧
      ∀ v ∈ S \ B, f U.card * (U.card : ℝ) ≤ ((resLink E U v).card : ℝ)

/-- **The repaired descent clause**: one level of the vortex, of a prescribed size, containing a
prescribed bottom set and avoiding a prescribed small set `D` of forbidden vertices, into which
*every* vertex of the current level is dense.

The avoidance set `D` is the fourth repair.  It is needed because §11 chooses the bottom set `U`
*before* the reserved edge set `A` (`BKLO.NearOptimalConclusion` has the quantifier order
`∃ U, ∀ A`), so the links into `U` of the `≤ 2|A|` vertices met by `A` are destroyed by the
deletion of `A`, at a scale (`|U| ≤ C`) that no constant chosen before `A` can absorb.  Letting the
top level of the vortex avoid those finitely many vertices repairs this, and costs nothing: the
clause is still the plain random-subset statement (a uniformly random `m`-subset of `W \ D`
containing `U`).

The size ratio `W.card ≤ K * K * m` is the sixth repair, and it too is necessary rather than
convenient: the conclusion asks *every* vertex of `W` to be dense into the chosen level, and a
random `m`-set fails a given vertex with probability `exp(-Ω(m))`, so a union bound — and in fact
the statement itself, by the first-moment argument of `BKLO.VortexBottomClauseR` — needs `|W|` to
be at most exponential in `m`.  Every use of the clause in the vortex has `|W| ≤ K²m`. -/
def VortexDescentClauseR (f : ℕ → ℝ) (n₂ K : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (W U D : Finset V) (E : Finset (Sym2 V)) (m : ℕ),
    n₂ ≤ U.card → U ⊆ W → Disjoint U D → U.card ≤ m → 2 * m + D.card ≤ W.card →
    W.card ≤ K * K * m →
    E ⊆ cliqueEdges W →
    (∀ v ∈ W, f W.card * (W.card : ℝ) ≤ (edeg E v : ℝ)) →
    ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ Disjoint W' D ∧ W'.card = m ∧
      ∀ v ∈ W, f m * (m : ℝ) ≤ ((resLink E W' v).card : ℝ)

/-- **The repaired reservoir clause.**  Three changes from `BKLO.ReservoirClause`, all forced (see
`BKLO.not_reservoirClause` and `BKLO.not_reservoirClauseCoDense`): the between-levels density
hypothesis, the global multiplicity bound on the link systems, and the damage bound at the scale
of `W''` in the conclusion. -/
def ReservoirClauseR (ε η : ℝ) (f : ℕ → ℝ) (n₂ K : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
    n₂ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
    K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
    F ⊆ cliqueEdges W → TriDivisible F →
    (∀ v ∈ W, (9 / 10 + ε / 4) * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
    (∀ v ∈ W', f W'.card * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
    (∀ v ∈ W, (9 / 10 + ε / 4) * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ)) →
    ∃ R : Finset (Sym2 V), R ⊆ F ∧ IsCrossing W W' R ∧
      (∀ v : V, (edeg R v : ℝ) ≤ ε / 8 * (W.card : ℝ)) ∧
      (∀ u ∈ W \ W', ∀ v ∈ W \ W',
        2 * η * (W.card : ℝ) ≤ ((apexes R W' u v).card : ℝ)) ∧
      (∀ X : V → Finset V,
        (∀ u ∈ W \ W', X u ⊆ W') →
        (∀ u ∈ W \ W', ∀ a ∈ X u, s(u, a) ∈ F) →
        (∀ u ∈ W \ W', Even (X u).card) →
        (∀ u ∈ W \ W', ((X u \ resLink R W' u).card : ℝ) ≤ 2 * η * (W.card : ℝ)) →
        (∀ u ∈ W \ W', ((resLink R W' u \ X u).card : ℝ) ≤ 2 * η * (W.card : ℝ)) →
        (∀ a ∈ W', (((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℝ)
          ≤ 2 * η * (W.card : ℝ)) →
        ∃ Q : Finset (Finset V), IsLinkCoverR F W' W'' (W \ W') X (ε / 8) Q)

/-- **The repaired fused §10 interface: vortex + reservoir.**  Same shape as
`BKLO.VortexReservoirEngine`, with the three repaired clauses. -/
def VortexReservoirEngineR : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ (n₀ : ℕ) (N : ℝ → ℕ), ∃ (f : ℕ → ℝ) (n₂ C K : ℕ) (η : ℝ),
    2 ≤ K ∧ (8 : ℝ) / ε ≤ (K : ℝ) ∧ 0 < η ∧
    n₀ ≤ n₂ ∧ N η ≤ n₂ ∧ n₂ ≤ C ∧ 0 < n₂ ∧
    (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + ε) ∧
    VortexBottomClauseR ε f n₂ C ∧ VortexDescentClauseR f n₂ K ∧ ReservoirClauseR ε η f n₂ K

/-! ### The repaired clauses imply the old, level-internal densities -/

/-- The repaired descent clause gives the old one, in the size window in which the vortex uses
it. -/
theorem vortexDescentClause_of_R_ratio {f : ℕ → ℝ} {n₂ K : ℕ} (h : VortexDescentClauseR f n₂ K)
    {V : Type} [DecidableEq V] (W U : Finset V) (E : Finset (Sym2 V)) (m : ℕ)
    (hU : n₂ ≤ U.card) (hUW : U ⊆ W) (hUm : U.card ≤ m) (hmW : 2 * m ≤ W.card)
    (hratio : W.card ≤ K * K * m) (hEW : E ⊆ cliqueEdges W)
    (hdeg : ∀ v ∈ W, f W.card * (W.card : ℝ) ≤ (edeg E v : ℝ)) :
    ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ W'.card = m ∧
      ∀ v ∈ W', f m * (m : ℝ) ≤ (edeg (E ∩ cliqueEdges W') v : ℝ) := by
  obtain ⟨W', hUW', hW'W, -, hcard, hW'⟩ :=
    h W U ∅ E m hU hUW (Finset.disjoint_empty_right _) hUm (by simpa using hmW) hratio hEW hdeg
  refine ⟨W', hUW', hW'W, hcard, fun v hv => ?_⟩
  rw [edeg_inter_cliqueEdges_eq_card_resLink hv (fun e he => (mem_cliqueEdgesV.1 (hEW he)).2)]
  exact hW' v (hW'W hv)

end BKLO
