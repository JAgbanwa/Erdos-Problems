/-
# BKLO §10 — the vortex recursion.

This file develops the *iterative absorption* half of §10 as far as it can be developed without
the analytic core, and reduces the residual §10 interface `NearOptimalConclusion` to a single,
strictly smaller and demonstrably satisfiable interface, the **vortex engine** `VortexEngine`:

* a notion `good U E_U` of a *good bottom set* together with
* the existence of a good bottom set of bounded size (`GoodBottomExists`), and
* a single **cover-down step** (`VortexStepFrom`): given the current edge set `E` on a vertex set
  `S` of min degree at least `c|S|`, and a good bottom `U ⊊ S`, one edge-disjoint family of
  triangles inside `E` either covers `E` down to a remainder inside `U`, or covers it down to a
  remainder living on a *strictly smaller* set `W` with `U ⊆ W ⊊ S`, again of min degree at least
  `c|W|`, without touching a single edge inside `U`.

The content proved here is the recursion itself: iterating the step down the vortex
(`coverDown_of_step`), the preservation of triangle-divisibility along the way, and the passage
from the edge-set formulation to the graph formulation of §10, including the treatment of the
bounded reserved edge set `A` (`nearOptimalConclusion_of_engine`).  Note the two places where the
shape of `NearOptimalConclusion` forces the design:

* `U` is produced **before** `A`; this is why the good bottom set is chosen from `G` itself and why
  goodness is required of the edge set *inside* `U` only — deleting `A`, which by hypothesis spans
  no edge inside `U`, leaves that edge set unchanged;
* the step must not damage `U`, which is what keeps the bottom good all the way down the vortex.

Everything in this file is `sorry`-free.  What is *not* proved here is `VortexEngine` itself: that
is the analytic core of §10 (choice of the vortex sets, the Haxell–Rödl nibble at each level, and
the cover-down using Dirac's theorem).  It is isolated as `VortexEngineFromInputs`, and it is
satisfiable — see `BKLO/VortexSat.lean`.

What §10 actually delivers is the *ratio-restricted* form of the engine, `VortexEngineRatio`,
defined at the end of this file together with its own reduction to `NearOptimalConclusion`
(`nearOptimalConclusion_of_engineRatio`): the step always in its first alternative "the leftover is
already inside `U`", and with the extra hypothesis that `U` is at least `K` times smaller than `S`.
That form is *proved* in `BKLO/VortexEngine.lean`
(`BKLO.vortexEngineRatioFromInputs_holds`), from the two §10 inputs of `BKLO/InputsVortex.lean`,
and it is what the unconditional main theorem of `BKLO/MainUnconditional.lean` goes through.  Why
the two hypotheses cannot be dispensed with is discussed at the end of this file, in
`BKLO/VortexEngine.lean` and in `RESIDUAL.md`.
-/
import BKLO.NearOptimal
import BKLO.TransportV
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Positivity

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Triangle families -/

/-- `P` is an edge-disjoint family of triangles all of whose edges lie in `E`. -/
def TriFamilyIn (E : Finset (Sym2 V)) (P : Finset (Finset V)) : Prop :=
  (∀ t ∈ P, t.card = 3) ∧ (∀ t ∈ P, cliqueEdges t ⊆ E) ∧
    (∀ t ∈ P, ∀ t' ∈ P, t ≠ t' → Disjoint (cliqueEdges t) (cliqueEdges t'))

theorem famEdges_subset_of_triFamilyIn {E : Finset (Sym2 V)} {P : Finset (Finset V)}
    (h : TriFamilyIn E P) : famEdges P ⊆ E := by
  intro e he
  obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.1 he
  exact h.2.1 t ht het

/-- The edges of a triangle family form a triangle-decomposable edge set. -/
theorem TriFamilyIn.triDecomp {E : Finset (Sym2 V)} {P : Finset (Finset V)}
    (h : TriFamilyIn E P) : TriDecomp (famEdges P) :=
  ⟨P, h.1, h.2.2, rfl⟩

/-- Removing an edge-disjoint triangle family preserves triangle-divisibility. -/
theorem triDivisible_sdiff_famEdges {E : Finset (Sym2 V)} {P : Finset (Finset V)}
    (hP : TriFamilyIn E P) (hE : TriDivisible E) : TriDivisible (E \ famEdges P) :=
  TriDivisible.sdiff (famEdges_subset_of_triFamilyIn hP) hE hP.triDecomp.triDivisible

/-- Two triangle families, the second one living in the part left over by the first, compose. -/
theorem triFamilyIn_union {E : Finset (Sym2 V)} {P Q : Finset (Finset V)}
    (hP : TriFamilyIn E P) (hQ : TriFamilyIn (E \ famEdges P) Q) : TriFamilyIn E (P ∪ Q) := by
  classical
  have hQE : ∀ t ∈ Q, cliqueEdges t ⊆ E := fun t ht =>
    (hQ.2.1 t ht).trans (Finset.sdiff_subset)
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rcases Finset.mem_union.1 ht with h | h
    exacts [hP.1 t h, hQ.1 t h]
  · intro t ht
    rcases Finset.mem_union.1 ht with h | h
    exacts [hP.2.1 t h, hQE t h]
  · -- across the two families the edge sets are disjoint because `Q` lives in `E \ famEdges P`
    have hcross : ∀ t ∈ P, ∀ t' ∈ Q, Disjoint (cliqueEdges t) (cliqueEdges t') := by
      intro t ht t' ht'
      refine Finset.disjoint_left.2 fun e he he' => ?_
      have h1 : e ∈ famEdges P := Finset.mem_biUnion.2 ⟨t, ht, he⟩
      have h2 : e ∈ E \ famEdges P := hQ.2.1 t' ht' he'
      exact (Finset.mem_sdiff.1 h2).2 h1
    intro t ht t' ht' hne
    rcases Finset.mem_union.1 ht with h | h <;> rcases Finset.mem_union.1 ht' with h' | h'
    · exact hP.2.2 t h t' h' hne
    · exact hcross t h t' h'
    · exact (hcross t' h' t h).symm
    · exact hQ.2.2 t h t' h' hne

theorem famEdges_union (P Q : Finset (Finset V)) :
    famEdges (P ∪ Q) = famEdges P ∪ famEdges Q := by
  ext e
  simp only [famEdges, Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨t, ht | ht, h⟩
    exacts [Or.inl ⟨t, ht, h⟩, Or.inr ⟨t, ht, h⟩]
  · rintro (⟨t, ht, h⟩ | ⟨t, ht, h⟩)
    exacts [⟨t, Or.inl ht, h⟩, ⟨t, Or.inr ht, h⟩]

theorem sdiff_famEdges_union (E : Finset (Sym2 V)) (P Q : Finset (Finset V)) :
    E \ famEdges (P ∪ Q) = (E \ famEdges P) \ famEdges Q := by
  rw [famEdges_union, Finset.sdiff_union_distrib]
  ext e
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-! ### The vortex engine: the residual interface of §10 -/

/-- A notion of *goodness* of a bottom set `U` together with the edge set it induces.  It is left
abstract: the vortex engine is required to supply one. -/
def GoodPred : Type 1 := ∀ V : Type, Finset V → Finset (Sym2 V) → Prop

/-- **Existence of a good bottom set** of bounded size inside any large dense vertex set. -/
def GoodBottomExists (good : GoodPred) (c : ℝ) (n₁ C n₂ : ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) (E : Finset (Sym2 V)),
    n₂ ≤ S.card → E ⊆ cliqueEdges S → (∀ v ∈ S, c * S.card ≤ edeg E v) →
    ∃ U : Finset V, U ⊆ S ∧ n₁ ≤ U.card ∧ U.card ≤ C ∧ good V U (E ∩ cliqueEdges U)

/-- **One cover-down step of the vortex.**

Given a triangle-divisible edge set `E` spanned by `S`, of minimum degree at least `c|S|`, and a
good bottom set `U ⊊ S`, there is an edge-disjoint family `P` of triangles inside `E` such that
either

* the leftover `E \ famEdges P` already lies inside `U`, or
* it lies inside a strictly smaller set `W` with `U ⊆ W ⊊ S`, has minimum degree at least `c|W|`
  on `W`, and contains every edge of `E` inside `U` (the step does not touch the bottom set).

This is the analytic core of BKLO §10: the vortex set `W` is chosen inside `S`, the bulk of `E` is
covered by the Haxell–Rödl nibble (fed by Dross's fractional threshold), and the leftover is
covered down into `W` using Dirac's theorem. -/
def VortexStepFrom (good : GoodPred) (c : ℝ) (n₁ : ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (S U : Finset V) (E : Finset (Sym2 V)),
    E ⊆ cliqueEdges S → (∀ v ∈ S, c * S.card ≤ edeg E v) → TriDivisible E →
    U ⊆ S → U ≠ S → n₁ ≤ U.card → good V U (E ∩ cliqueEdges U) →
    ∃ P : Finset (Finset V), TriFamilyIn E P ∧
      ((E \ famEdges P ⊆ cliqueEdges U) ∨
        ∃ W : Finset V, U ⊆ W ∧ W ⊆ S ∧ W ≠ S ∧
          E \ famEdges P ⊆ cliqueEdges W ∧
          (∀ v ∈ W, c * W.card ≤ edeg (E \ famEdges P) v) ∧
          E ∩ cliqueEdges U ⊆ E \ famEdges P)

/-- **The vortex engine** at density `c`: a notion of goodness for which good bottom sets of
bounded size exist and the cover-down step can be performed. -/
def VortexEngine (c : ℝ) : Prop :=
  ∃ (good : GoodPred) (n₁ C n₂ : ℕ),
    GoodBottomExists good c n₁ C n₂ ∧ VortexStepFrom good c n₁

/-- **The residual interface of §10**: the three external inputs yield the vortex engine at every
density above `9/10`. -/
def VortexEngineFromInputs : Prop :=
  FracTriangleThreshold → FracToApprox → PerfectMatchingDirac →
    ∀ ε : ℝ, 0 < ε → VortexEngine (9 / 10 + ε)

/-! ### The recursion -/

/-- **Iterating the cover-down step down the vortex.**  From the step interface, any
triangle-divisible edge set spanned by `S`, of minimum degree at least `c|S|`, with a good bottom
`U ⊆ S`, is covered by an edge-disjoint family of triangles up to a remainder inside `U`. -/
theorem coverDown_of_step {good : GoodPred} {c : ℝ} {n₁ : ℕ}
    (hstep : VortexStepFrom good c n₁) :
    ∀ (m : ℕ) {V : Type} [Fintype V] [DecidableEq V] (S U : Finset V) (E : Finset (Sym2 V)),
      S.card ≤ m → E ⊆ cliqueEdges S → (∀ v ∈ S, c * S.card ≤ edeg E v) → TriDivisible E →
      U ⊆ S → n₁ ≤ U.card → good V U (E ∩ cliqueEdges U) →
      ∃ P : Finset (Finset V), TriFamilyIn E P ∧ E \ famEdges P ⊆ cliqueEdges U := by
  intro m
  induction m with
  | zero =>
    intro V _ _ S U E hcard hES _ _ hUS _ _
    have hS : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
    refine ⟨∅, ⟨by simp, by simp, by simp⟩, ?_⟩
    have : U = S := by
      rw [hS] at hUS ⊢; exact Finset.subset_empty.1 hUS
    rw [this]
    simpa [famEdges] using hES
  | succ m ih =>
    intro V _ _ S U E hcard hES hdeg hdiv hUS hUn hgood
    by_cases hUeq : U = S
    · refine ⟨∅, ⟨by simp, by simp, by simp⟩, ?_⟩
      rw [hUeq]
      simpa [famEdges] using hES
    · obtain ⟨P, hP, hcase⟩ := hstep S U E hES hdeg hdiv hUS hUeq hUn hgood
      rcases hcase with hdone | ⟨W, hUW, hWS, hWne, hEW, hWdeg, hUkeep⟩
      · exact ⟨P, hP, hdone⟩
      · -- recurse on the strictly smaller set `W`
        set E' := E \ famEdges P with hE'
        have hcardW : W.card ≤ m := by
          have h1 : W.card < S.card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hWS, hWne⟩)
          omega
        have hdiv' : TriDivisible E' := triDivisible_sdiff_famEdges hP hdiv
        have hgood' : good V U (E' ∩ cliqueEdges U) := by
          have : E' ∩ cliqueEdges U = E ∩ cliqueEdges U := by
            apply Finset.Subset.antisymm
            · exact Finset.inter_subset_inter_right (Finset.sdiff_subset)
            · intro e he
              exact Finset.mem_inter.2 ⟨hUkeep he, (Finset.mem_inter.1 he).2⟩
          rwa [this]
        obtain ⟨Q, hQ, hQcover⟩ :=
          ih W U E' hcardW hEW hWdeg hdiv' hUW hUn hgood'
        refine ⟨P ∪ Q, triFamilyIn_union hP hQ, ?_⟩
        rw [sdiff_famEdges_union]
        exact hQcover

/-! ### From the vortex engine to §10 -/

theorem edeg_le_edeg_sdiff_add {E A : Finset (Sym2 V)} (v : V) :
    edeg E v ≤ edeg (E \ A) v + A.card := by
  classical
  have hsub : E.filter (fun e => v ∈ e) ⊆ (E \ A).filter (fun e => v ∈ e) ∪ A := by
    intro e he
    rw [Finset.mem_filter] at he
    by_cases hA : e ∈ A
    · exact Finset.mem_union_right _ hA
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨he.1, hA⟩, he.2⟩)
  calc edeg E v ≤ ((E \ A).filter (fun e => v ∈ e) ∪ A).card := Finset.card_le_card hsub
    _ ≤ edeg (E \ A) v + A.card := Finset.card_union_le _ _

/-- **§10 from the vortex engine.**  The near-optimal decomposition follows from the vortex engine
at every density above `9/10`. -/
theorem nearOptimalConclusion_of_engine
    (hEng : ∀ ε : ℝ, 0 < ε → VortexEngine (9 / 10 + ε)) : NearOptimalConclusion := by
  classical
  intro ε hε
  obtain ⟨good, n₁, C, n₂, hbot, hstep⟩ := hEng (ε / 2) (by linarith)
  refine ⟨C, ?_⟩
  intro K
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (K : ℝ) / ε)
  refine ⟨max n₂ N, ?_⟩
  intro V _ _ G _ hn hδ
  have hn₂ : n₂ ≤ Fintype.card V := le_trans (le_max_left _ _) hn
  have hnN : N ≤ Fintype.card V := le_trans (le_max_right _ _) hn
  have hKsmall : (K : ℝ) ≤ ε / 2 * (Fintype.card V : ℝ) := by
    have h1 : 2 * (K : ℝ) / ε < (Fintype.card V : ℝ) :=
      lt_of_lt_of_le hN (by exact_mod_cast hnN)
    rw [div_lt_iff₀ hε] at h1
    linarith
  -- the ambient edge set
  have hcardu : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
  have hEuniv : G.edgeFinset ⊆ cliqueEdges (Finset.univ : Finset V) := by
    intro e he
    refine mem_cliqueEdgesV.2 ⟨fun x _ => Finset.mem_univ x, ?_⟩
    exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.1 he)
  have hdegG : ∀ v, G.degree v = edeg G.edgeFinset v := by
    intro v
    rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter v, edeg]
  have hdegbig : ∀ v ∈ (Finset.univ : Finset V),
      (9 / 10 + ε) * ((Finset.univ : Finset V).card : ℝ) ≤ (edeg G.edgeFinset v : ℝ) := by
    intro v _
    rw [hcardu, ← hdegG v]
    refine hδ.trans ?_
    exact_mod_cast G.minDegree_le_degree v
  obtain ⟨U, hUS, hUn₁, hUC, hgood⟩ :=
    hbot (Finset.univ : Finset V) G.edgeFinset (by rw [hcardu]; exact hn₂) hEuniv
      (by
        intro v hv
        refine le_trans ?_ (hdegbig v hv)
        have : (0:ℝ) ≤ ((Finset.univ : Finset V).card : ℝ) := by positivity
        nlinarith)
  refine ⟨U, hUC, ?_⟩
  intro A hAsub hAcard hAdisj hAdiv
  set F : Finset (Sym2 V) := G.edgeFinset \ A with hF
  have hFuniv : F ⊆ cliqueEdges (Finset.univ : Finset V) :=
    (Finset.sdiff_subset).trans hEuniv
  have hFdeg : ∀ v ∈ (Finset.univ : Finset V),
      (9 / 10 + ε / 2) * ((Finset.univ : Finset V).card : ℝ) ≤ (edeg F v : ℝ) := by
    intro v hv
    have h1 := hdegbig v hv
    have h2 : (edeg G.edgeFinset v : ℝ) ≤ (edeg F v : ℝ) + (A.card : ℝ) := by
      exact_mod_cast edeg_le_edeg_sdiff_add (E := G.edgeFinset) (A := A) v
    have h3 : (A.card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hAcard
    rw [hcardu] at h1 ⊢
    linarith
  have hgood' : good V U (F ∩ cliqueEdges U) := by
    have : F ∩ cliqueEdges U = G.edgeFinset ∩ cliqueEdges U := by
      apply Finset.Subset.antisymm
      · exact Finset.inter_subset_inter_right (Finset.sdiff_subset)
      · intro e he
        obtain ⟨he1, he2⟩ := Finset.mem_inter.1 he
        refine Finset.mem_inter.2 ⟨Finset.mem_sdiff.2 ⟨he1, ?_⟩, he2⟩
        exact fun hA => (Finset.disjoint_left.1 hAdisj hA) he2
    rwa [this]
  obtain ⟨P, hP, hcover⟩ :=
    coverDown_of_step hstep (Finset.univ : Finset V).card (Finset.univ : Finset V) U F
      le_rfl hFuniv hFdeg hAdiv hUS hUn₁ hgood'
  exact ⟨P, hP.1, hP.2.1, hP.2.2, hcover⟩

/-- **§10 from the residual vortex interface.** -/
theorem nearOptimalDecomp_of_vortex (h : VortexEngineFromInputs) : NearOptimalDecomp := by
  intro hDross hHR hDirac
  exact nearOptimalConclusion_of_engine (h hDross hHR hDirac)

/-! ### The engine in the form in which §10 actually supplies it

`VortexStepFrom` asks for *one* cover-down step, from an arbitrary dense set `S` to an arbitrary
good bottom `U ⊊ S`, at a fixed density constant `c`.  Two features of that shape are not what the
analytic core of §10 delivers.

* The density constant demanded of the intermediate set `W` is the *same* `c` as the one demanded
  of `S`.  Restricting an edge set of minimum degree `c|S|` to a subset `W` gives minimum degree
  `c|W| - Θ(√|W|)`, and the condition `δ ≥ c|·|` is scale invariant, so there is no slack to pay
  the fluctuation with.  What §10 does is choose the *whole* nested vortex at once, with a density
  *schedule*, and cover down along it; so the step is only ever established in its first
  alternative "the leftover already lies inside `U`".
* The cover-down from a set `W` onto the next set `W'` keeps all edges inside `W'` intact, so the
  nibble that covers the bulk has to avoid `cliqueEdges W'`; this only leaves minimum degree above
  the fractional threshold `(9/10)|W|` when `|W'|` is a *small* fraction of `|W|`.  Consequently
  §10 covers down from `S` to `U` only when `U` is small compared with `S`.

The size-ratio hypothesis really is needed, not merely convenient.  The other standard way to cover
every edge meeting `S \ U` is to peel the vertices of `S \ U` one at a time: all edges at a vertex
`x` must be covered by triangles whose apexes lie in the link of `x`, so peeling `x` amounts to a
perfect matching in `E[N(x)]` (Dirac), and each neighbour of `x` then loses exactly two edges while
the ambient size drops by one.  From density `9/10` this can be sustained only for about `17.5%` of
the vertices, i.e. down to `|U| ≈ 0.82|S|`.  For `|S|/K < |U| < 0.82|S|` neither method applies.

The interface below records exactly that: the same statement, always in the first alternative, and
with the size-ratio hypothesis `K|U| ≤ |S|`.  It is all that the reduction to `§10` needs, because
the reduction only ever applies the step with `S` the whole vertex set (of unbounded size) and `U`
of bounded size. -/

/-- **The cover-down of the whole vortex, at a bounded size ratio.**  A triangle-divisible edge set
`E` spanned by `S`, of minimum degree at least `c|S|`, with a good bottom set `U ⊆ S` that is at
least `K` times smaller than `S`, is covered by an edge-disjoint family of triangles inside `E`
down to a remainder inside `U`. -/
def VortexBottomCover (good : GoodPred) (c : ℝ) (n₁ K : ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (S U : Finset V) (E : Finset (Sym2 V)),
    E ⊆ cliqueEdges S → (∀ v ∈ S, c * S.card ≤ edeg E v) → TriDivisible E →
    U ⊆ S → K * U.card ≤ S.card → n₁ ≤ U.card → good V U (E ∩ cliqueEdges U) →
    ∃ P : Finset (Finset V), TriFamilyIn E P ∧ E \ famEdges P ⊆ cliqueEdges U

/-- **The vortex engine** at density `c`, in the ratio-restricted form: a notion of goodness for
which good bottom sets of bounded size exist and the whole vortex can be covered down onto any
sufficiently small good bottom set. -/
def VortexEngineRatio (c : ℝ) : Prop :=
  ∃ (good : GoodPred) (n₁ C n₂ K : ℕ),
    GoodBottomExists good c n₁ C n₂ ∧ VortexBottomCover good c n₁ K

/-- **The residual interface of §10, ratio-restricted form**: the three external inputs yield the
vortex engine at every density above `9/10`. -/
def VortexEngineRatioFromInputs : Prop :=
  FracTriangleThreshold → FracToApprox → PerfectMatchingDirac →
    ∀ ε : ℝ, 0 < ε → VortexEngineRatio (9 / 10 + ε)

/-- The ratio-restricted engine is *weaker* than `VortexEngine`: iterating the step of
`VortexStepFrom` down the vortex covers onto the bottom set whatever the size ratio.  In
particular, the satisfiability of `VortexEngine` (`BKLO/VortexSat.lean`) carries over. -/
theorem vortexEngineRatio_of_vortexEngine {c : ℝ} (h : VortexEngine c) : VortexEngineRatio c := by
  obtain ⟨good, n₁, C, n₂, hbot, hstep⟩ := h
  exact ⟨good, n₁, C, n₂, 1, hbot, fun S U E hES hdeg hdiv hUS _ hUn hgood =>
    coverDown_of_step hstep S.card S U E le_rfl hES hdeg hdiv hUS hUn hgood⟩

/-- **§10 from the ratio-restricted vortex engine.**  Identical to
`nearOptimalConclusion_of_engine`, except that the size threshold is raised to `K·C` so that the
bounded bottom set produced by `GoodBottomExists` really is `K` times smaller than the whole
vertex set, which is the only place the step is applied. -/
theorem nearOptimalConclusion_of_engineRatio
    (hEng : ∀ ε : ℝ, 0 < ε → VortexEngineRatio (9 / 10 + ε)) : NearOptimalConclusion := by
  classical
  intro ε hε
  obtain ⟨good, n₁, C, n₂, Kr, hbot, hcov⟩ := hEng (ε / 2) (by linarith)
  refine ⟨C, ?_⟩
  intro K
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (K : ℝ) / ε)
  refine ⟨max (max n₂ N) (Kr * C), ?_⟩
  intro V _ _ G _ hn hδ
  have hn₂ : n₂ ≤ Fintype.card V := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN : N ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnKC : Kr * C ≤ Fintype.card V := le_trans (le_max_right _ _) hn
  have hKsmall : (K : ℝ) ≤ ε / 2 * (Fintype.card V : ℝ) := by
    have h1 : 2 * (K : ℝ) / ε < (Fintype.card V : ℝ) :=
      lt_of_lt_of_le hN (by exact_mod_cast hnN)
    rw [div_lt_iff₀ hε] at h1
    linarith
  -- the ambient edge set
  have hcardu : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
  have hEuniv : G.edgeFinset ⊆ cliqueEdges (Finset.univ : Finset V) := by
    intro e he
    refine mem_cliqueEdgesV.2 ⟨fun x _ => Finset.mem_univ x, ?_⟩
    exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.1 he)
  have hdegG : ∀ v, G.degree v = edeg G.edgeFinset v := by
    intro v
    rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter v, edeg]
  have hdegbig : ∀ v ∈ (Finset.univ : Finset V),
      (9 / 10 + ε) * ((Finset.univ : Finset V).card : ℝ) ≤ (edeg G.edgeFinset v : ℝ) := by
    intro v _
    rw [hcardu, ← hdegG v]
    refine hδ.trans ?_
    exact_mod_cast G.minDegree_le_degree v
  obtain ⟨U, hUS, hUn₁, hUC, hgood⟩ :=
    hbot (Finset.univ : Finset V) G.edgeFinset (by rw [hcardu]; exact hn₂) hEuniv
      (by
        intro v hv
        refine le_trans ?_ (hdegbig v hv)
        have : (0:ℝ) ≤ ((Finset.univ : Finset V).card : ℝ) := by positivity
        nlinarith)
  refine ⟨U, hUC, ?_⟩
  intro A hAsub hAcard hAdisj hAdiv
  set F : Finset (Sym2 V) := G.edgeFinset \ A with hF
  have hFuniv : F ⊆ cliqueEdges (Finset.univ : Finset V) :=
    (Finset.sdiff_subset).trans hEuniv
  have hFdeg : ∀ v ∈ (Finset.univ : Finset V),
      (9 / 10 + ε / 2) * ((Finset.univ : Finset V).card : ℝ) ≤ (edeg F v : ℝ) := by
    intro v hv
    have h1 := hdegbig v hv
    have h2 : (edeg G.edgeFinset v : ℝ) ≤ (edeg F v : ℝ) + (A.card : ℝ) := by
      exact_mod_cast edeg_le_edeg_sdiff_add (E := G.edgeFinset) (A := A) v
    have h3 : (A.card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hAcard
    rw [hcardu] at h1 ⊢
    linarith
  have hgood' : good V U (F ∩ cliqueEdges U) := by
    have : F ∩ cliqueEdges U = G.edgeFinset ∩ cliqueEdges U := by
      apply Finset.Subset.antisymm
      · exact Finset.inter_subset_inter_right (Finset.sdiff_subset)
      · intro e he
        obtain ⟨he1, he2⟩ := Finset.mem_inter.1 he
        refine Finset.mem_inter.2 ⟨Finset.mem_sdiff.2 ⟨he1, ?_⟩, he2⟩
        exact fun hA => (Finset.disjoint_left.1 hAdisj hA) he2
    rwa [this]
  have hratio : Kr * U.card ≤ (Finset.univ : Finset V).card := by
    rw [hcardu]
    exact le_trans (Nat.mul_le_mul_left _ hUC) hnKC
  obtain ⟨P, hP, hcover⟩ :=
    hcov (Finset.univ : Finset V) U F hFuniv hFdeg hAdiv hUS hratio hUn₁ hgood'
  exact ⟨P, hP.1, hP.2.1, hP.2.2, hcover⟩

/-- **§10 from the ratio-restricted residual vortex interface.** -/
theorem nearOptimalDecomp_of_vortexRatio (h : VortexEngineRatioFromInputs) : NearOptimalDecomp := by
  intro hDross hHR hDirac
  exact nearOptimalConclusion_of_engineRatio (h hDross hHR hDirac)

end BKLO
