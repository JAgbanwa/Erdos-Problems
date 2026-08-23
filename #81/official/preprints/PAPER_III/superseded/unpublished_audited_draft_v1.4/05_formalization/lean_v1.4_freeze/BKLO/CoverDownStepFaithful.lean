/-
# BKLO §10.1, the cover-down step: the faithful assembly with the **bounded-core** absorber

`BKLO.CoverDownStepResidualLarge` (`BKLO/CoverDownEngineR3.lean`) is the single residual of the
dense triangle-decomposition theorem on the cover-down route.  This file assembles it *faithfully*,
i.e. without the vertex-sparse cluster reservoir of `BKLO.ReservoirClauseResidual4`, from

* the **proved** bounded-core absorber `BKLO.boundedLeftover_confined` (itself built on the proved
  `BKLO.coreAbsorberExistence_holds`), and
* one residual clause, `BKLO.ShellCoverDown`, which is BKLO's §10.1 cover-down step for the shell of
  a single vortex level.

## What the assembly does

At a vortex level `W ⊇ W' ⊇ W''` with `K|W'| ≤ |W| ≤ K²|W'|` and `K = max(800, ⌈32/ε⌉)`:

* it works with the **shell** `Sh := F \ cliqueEdges W'`, the edges of `F` meeting `W \ W'`.  Since
  `|W'| ≤ (ε/32)|W|`, the shell still has minimum degree `≥ (9/10 + ε/32)|W|`, and — the point that
  makes the whole assembly work — at every `v ∈ W \ W'` its degree is the *full* degree of `F` at
  `v`, hence **even**, by triangle divisibility of `F`;
* it adds a **mod-3 correction** `D`: at most two edges of `F` forming a star inside `W' \ W''`,
  chosen so that `3 ∣ |Sh ∪ D|` (`BKLO.exists_mod_three_star`);
* it hands `E := Sh ∪ D` to `BKLO.ShellCoverDown`, which returns the bounded core `U ⊆ W \ W'`;
* it then runs the **bounded-core absorber** on the shell, which returns the reservoir `R ⊆ Sh` the
  cover-down is run against;
* the cover-down covers `E \ R` down to a remainder `H` inside `U`.  That remainder is
  automatically even (its vertices lie in `W \ W'`, where the shell degree is the full, even,
  `F`-degree) and `3 ∣ |R ∪ H|` follows from the mod-3 correction together with the congruence the
  residual guarantees for the `W'`-edges it spends.  So the absorber decomposes `R ∪ H` exactly and
  no parity or divisibility hypothesis has to be added anywhere.

The outcome, `BKLO.coverDownStepResidualLarge_of_shellCoverDown`, is a cover-down step of the shape
the vortex needs: the whole shell is covered *exactly*, the damage inside `W'` is at most
`(ε/32)|W'|` per vertex, no edge inside `W''` is touched, and the damage of the links into `W''` is
**zero**.

## What remains, and how tight it is

`BKLO.ShellCoverDown` is the residual.  Two facts locate it precisely.

* Its **approximate form** `BKLO.ShellCoverDownApprox` — same hypotheses, but the leftover is only
  asked to have at most `γ|W|²` edges instead of living inside a bounded core — is *proved* here,
  in `BKLO.shellCoverDownApprox_of_approxTriDecomp`, from the approximate-decomposition threshold
  `BKLO.ApproxTriDecompMinDeg (9/10)` (the `δ_F^η` input, which the dense nibble supplies).  So
  what is missing is exactly the passage from `γ|W|²` uncovered edges to a leftover confined to a
  bounded set of vertices fixed in advance — that is, the completion/absorption content of §10,
  not the approximate decomposition.
* It is genuinely **weaker than the theorem being proved**.  The naive strengthening in which the
  covering triangles are not allowed to use edges inside `W'`, `BKLO.ShellConfinement`, is *not* a
  useful residual: `BKLO.nearOptimalConclusion_of_shellConfinement` shows that it implies
  `BKLO.NearOptimalConclusion` outright (take `W' = ∅`).  `BKLO.ShellCoverDown` avoids this by
  insisting that `W'` be a constant fraction of `W` (`|W| ≤ (1/γ)³|W'|`) and by letting the
  triangles spend edges inside `W'`, within the damage budget — BKLO's apex mechanism.

The residual quantifies over no link system, asks for no apex abundance and reserves no
vertex-sparse cluster, so the sparse-reservoir refutations of this development
(`BKLO.ReservoirClauseResidual4` and the `WebWall` family) do not apply to it.  It is a *new*
statement, not one of the walled ones; the obstruction it still contains is the classical one of
§10.1 — matching the residual link of a vertex inside `W'` — which is why it is stated with the
link hypothesis `(9/10+γ)|W'| ≤ |resLink G W' v|` and with the freedom to choose which `W'`-edges
to spend.

Everything in this file is `sorry`-free, and depends only on `propext`, `Classical.choice` and
`Quot.sound`.
-/

import BKLO.CoverDownEngineR3
import BKLO.BoundedLeftoverConfined
import BKLO.SubtypeTransport

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The shell of a vortex level -/

/-- Outside the next level the shell keeps every edge: for `v ∉ W'` no edge of `F` at `v` lies
inside `W'`. -/
theorem edeg_sdiff_cliqueEdges_of_notMem {F : Finset (Sym2 V)} {W' : Finset V} {v : V}
    (hv : v ∉ W') : edeg (F \ cliqueEdges W') v = edeg F v := by
  classical
  unfold edeg
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨he, -⟩, hve⟩
    exact ⟨he, hve⟩
  · rintro ⟨he, hve⟩
    exact ⟨⟨he, fun hcl => hv ((mem_cliqueEdgesV.1 hcl).1 v hve)⟩, hve⟩

/-- An edge set spanned by a set of vertices contributes nothing to the degree of an outside
vertex. -/
theorem edeg_eq_zero_of_subset_cliqueEdges {E : Finset (Sym2 V)} {U : Finset V} {v : V}
    (hE : E ⊆ cliqueEdges U) (hv : v ∉ U) : edeg E v = 0 := by
  classical
  unfold edeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun e he hve => hv ((mem_cliqueEdgesV.1 (hE he)).1 v hve)

/-- The degree of a vertex is at most the number of edges. -/
theorem edeg_le_card_edges (E : Finset (Sym2 V)) (v : V) : edeg E v ≤ E.card :=
  Finset.card_filter_le _ _

/-! ### The residual: confinement of the shell to a bounded core -/

/-- **The confinement of the shell (BKLO §10, applied at one vortex level).**

For every `γ > 0` there are a bound `C` and a threshold `n₀` such that: for every dense graph `E`
on a large vertex set `W`, and every subset `W'` of `W` of size at most `γ|W|`, there is a set `U`
of at most `C` vertices, *disjoint from* `W'`, such that after removing **any** reserved edge set
`R` of maximum degree at most `γ|W|` the rest of `E` can be covered by edge-disjoint triangles of
`E \ R` down to a remainder inside `U`.

The core `U` is produced **before** the reservation `R` — the quantifier order the absorber needs,
and the one the vortex provides (its bottom set is fixed before anything is reserved).

This is the one statement that this file does not prove.  It is BKLO's near-optimal decomposition
(§10) applied to the shell of a vortex level.  Nothing here asserts it. -/
def ShellConfinement : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ C n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (W W' : Finset V) (E : Finset (Sym2 V)),
      n₀ ≤ W.card → W' ⊆ W → (W'.card : ℝ) ≤ γ * (W.card : ℝ) → E ⊆ cliqueEdges W →
      (∀ v ∈ W, (9 / 10 + γ) * (W.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ U : Finset V, U ⊆ W \ W' ∧ U.card ≤ C ∧
        ∀ R : Finset (Sym2 V), R ⊆ E → (∀ v : V, (edeg R v : ℝ) ≤ γ * (W.card : ℝ)) →
          ∃ P : Finset (Finset V), TriFamilyIn (E \ R) P ∧
            (E \ R) \ famEdges P ⊆ cliqueEdges U


/-- **The cover-down step of §10.1, as a residual (`BKLO.ShellCoverDown`).**

This is the statement this file reduces the cover-down step to.  It is the faithful §10.1 shape: at
a vortex level `W ⊇ W' ⊇ W''` one is given the ambient graph `G` on `W` (minimum degree
`(9/10+γ)|W|`, and every vertex of `W` sees `(9/10+γ)|W'|` of the next level), and a target set `E`
consisting of *all* the edges of `G` outside `W'` together with at most two edges inside `W'` (the
mod-3 correction).  One must produce a bounded core `U ⊆ W \ W'` in advance, and then, after an
arbitrary reservation `R` of maximum degree `γ|W|` outside `W'`, an edge-disjoint triangle family
`P` in `G \ R` covering all of `E \ R` except inside `U`.

The triangles of `P` may use edges of `G` inside `W'` — this is BKLO's apex mechanism, and it is
what makes the statement weaker than the shell confinement `BKLO.ShellConfinement`: it is *not* a
decomposition statement for `G` alone.  The three side conditions are the ones the vortex needs:

* the edges of `W'` that `P` spends avoid the protected level `W''` entirely;
* they have degree at most `γ|W'|` at every vertex (the damage budget of the step);
* their number is congruent mod `3` to the number of `W'`-edges handed over in `E` (the mod-3
  bookkeeping of the step; it is vacuous for a `P` that spends exactly the edges it is given).

Note the hypothesis `|W| ≤ (1/γ)³|W'|`: the next level is a *constant fraction* of the current one,
as in the vortex.  Without it (i.e. with `W' = ∅` allowed) the statement would degenerate into the
near-optimal decomposition itself; compare `BKLO.nearOptimalConclusion_of_shellConfinement`. -/
def ShellCoverDown : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ C n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (G E : Finset (Sym2 V)),
      n₀ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
      (W'.card : ℝ) ≤ γ * (W.card : ℝ) → (W.card : ℝ) ≤ (1 / γ) ^ 3 * (W'.card : ℝ) →
      G ⊆ cliqueEdges W →
      (∀ v ∈ W, (9 / 10 + 3 * γ) * (W.card : ℝ) ≤ (edeg G v : ℝ)) →
      (∀ v ∈ W, (9 / 10 + γ) * (W'.card : ℝ) ≤ ((resLink G W' v).card : ℝ)) →
      G \ cliqueEdges W' ⊆ E → E ⊆ G →
      E ∩ cliqueEdges W' ⊆ cliqueEdges (W' \ W'') → (E ∩ cliqueEdges W').card ≤ 2 →
      ∃ U : Finset V, U ⊆ W \ W' ∧ U.card ≤ C ∧
        ∀ R : Finset (Sym2 V), R ⊆ G \ cliqueEdges W' →
          (∀ v : V, (edeg R v : ℝ) ≤ γ * (W.card : ℝ)) →
          ∃ P : Finset (Finset V), TriFamilyIn (G \ R) P ∧
            (E \ R) \ famEdges P ⊆ cliqueEdges U ∧
            famEdges P ∩ cliqueEdges W' ⊆ cliqueEdges (W' \ W'') ∧
            (∀ v : V, (edeg (famEdges P ∩ cliqueEdges W') v : ℝ) ≤ γ * (W'.card : ℝ)) ∧
            (famEdges P ∩ cliqueEdges W').card % 3 = (E ∩ cliqueEdges W').card % 3

/-- **The shell confinement is too strong to be a useful residual: it implies the conclusion of
§10 outright.**  Taking `W' = ∅`, `W = V` and `R = A` in `BKLO.ShellConfinement` gives
`BKLO.NearOptimalConclusion` directly.  This is why the residual isolated below,
`BKLO.ShellCoverDown`, insists that the next level `W'` be a constant fraction of `W` and allows
the covering triangles to use edges inside it. -/
theorem nearOptimalConclusion_of_shellConfinement (hconf : ShellConfinement) :
    NearOptimalConclusion := by
  classical
  intro ε hε
  obtain ⟨C, n₀, hconf'⟩ := hconf ε hε
  refine ⟨C, fun K => ⟨max n₀ (n₀ + ⌈(K : ℝ) / ε⌉₊), ?_⟩⟩
  intro V _ _ G _ hcard hmin
  have hcardu : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
  have hn₀ : n₀ ≤ (Finset.univ : Finset V).card := by
    rw [hcardu]; exact le_trans (le_max_left n₀ _) hcard
  have hEuniv : G.edgeFinset ⊆ cliqueEdges (Finset.univ : Finset V) := by
    intro e' he'
    exact mem_cliqueEdgesV.2 ⟨fun x _ => Finset.mem_univ x,
      G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.1 he')⟩
  have hdegG : ∀ v : V, G.degree v = edeg G.edgeFinset v := by
    intro v
    rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter v, edeg]
  have hdeg : ∀ v ∈ (Finset.univ : Finset V),
      (9 / 10 + ε) * ((Finset.univ : Finset V).card : ℝ) ≤ (edeg G.edgeFinset v : ℝ) := by
    intro v _
    rw [hcardu, ← hdegG v]
    refine hmin.trans ?_
    exact_mod_cast G.minDegree_le_degree v
  obtain ⟨U, hUsub, hUC, hcov⟩ :=
    hconf' (Finset.univ : Finset V) (∅ : Finset V) G.edgeFinset hn₀ (Finset.empty_subset _)
      (by simp only [Finset.card_empty, Nat.cast_zero]; positivity) hEuniv hdeg
  refine ⟨U, hUC, ?_⟩
  intro A hA hAK _ _
  have hAdeg : ∀ v : V, (edeg A v : ℝ) ≤ ε * ((Finset.univ : Finset V).card : ℝ) := by
    intro v
    have h1 : (edeg A v : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast edeg_le_card_edges A v
    have h2 : (A.card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hAK
    have h3 : (K : ℝ) / ε ≤ (⌈(K : ℝ) / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h4 : ((n₀ + ⌈(K : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ ((Finset.univ : Finset V).card : ℝ) := by
      have : n₀ + ⌈(K : ℝ) / ε⌉₊ ≤ (Finset.univ : Finset V).card := by
        rw [hcardu]; exact le_trans (le_max_right n₀ _) hcard
      exact_mod_cast this
    have h5 : ((⌈(K : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ ((Finset.univ : Finset V).card : ℝ) := by
      push_cast at h4
      have : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
      linarith
    have h6 : (K : ℝ) / ε ≤ ((Finset.univ : Finset V).card : ℝ) := le_trans h3 h5
    rw [div_le_iff₀ hε] at h6
    linarith
  obtain ⟨P, hP, hleft⟩ := hcov A hA hAdeg
  exact ⟨P, hP.1, hP.2.1, hP.2.2, hleft⟩
/-- **The approximate form of the cover-down residual.**  `BKLO.ShellCoverDown` with the bounded
core `U` replaced by the *count* `γ|W|²` of uncovered edges, and with the covering triangles asked
to stay off `W'` altogether (so that all three side conditions of `BKLO.ShellCoverDown` hold
trivially for them).

This one **is** a theorem, `BKLO.shellCoverDownApprox_of_approxTriDecomp`, from the
approximate-decomposition threshold `δ_F^η` at `δ = 9/10`.  Comparing it with
`BKLO.ShellCoverDown` isolates what is missing: not the approximate decomposition of the shell —
reservation and all — but the passage from a leftover of `γ|W|²` edges to a leftover inside a
*bounded* set of vertices fixed in advance, and with it the mod-3 bookkeeping. -/
def ShellCoverDownApprox : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (W W' : Finset V) (G : Finset (Sym2 V)),
      n₀ ≤ W.card → W' ⊆ W → (W'.card : ℝ) ≤ γ * (W.card : ℝ) → G ⊆ cliqueEdges W →
      (∀ v ∈ W, (9 / 10 + 3 * γ) * (W.card : ℝ) ≤ (edeg G v : ℝ)) →
        ∀ R : Finset (Sym2 V), R ⊆ G \ cliqueEdges W' →
          (∀ v : V, (edeg R v : ℝ) ≤ γ * (W.card : ℝ)) →
          ∃ P : Finset (Finset V), TriFamilyIn ((G \ cliqueEdges W') \ R) P ∧
            ((((G \ cliqueEdges W') \ R) \ famEdges P).card : ℝ) ≤ γ * (W.card : ℝ) ^ 2

/-- **The approximate half of the residual is a theorem.**  From the approximate-decomposition
threshold `δ_F^η` at `δ = 9/10` — `BKLO.ApproxTriDecompMinDeg (9/10)`, the input the task allows to
be assumed and which the dense nibble supplies in the full tree — the shell of a vortex level,
with an arbitrary reservation of maximum degree `γ|W|` removed, carries an edge-disjoint triangle
family leaving at most `γ|W|²` of its edges uncovered.  Deleting the next level and the reservation
costs only `2γ|W|` of the minimum degree `(9/10+3γ)|W|`, so the threshold still applies. -/
theorem shellCoverDownApprox_of_approxTriDecomp
    (happ : ApproxTriDecompMinDeg (9 / 10)) : ShellCoverDownApprox := by
  classical
  intro γ hγ
  obtain ⟨n₀, hn₀⟩ := approxTriDecompMinDeg_set happ (η := γ) hγ
  refine ⟨n₀, ?_⟩
  intro V _ W W' G hcard _ hW'small hGW hdeg R hR hRdeg
  have hsub : (G \ cliqueEdges W') \ R ⊆ cliqueEdges W :=
    (Finset.sdiff_subset.trans Finset.sdiff_subset).trans hGW
  have hdeg' : ∀ v ∈ W, (9 / 10 : ℝ) * (W.card : ℝ) ≤ (edeg ((G \ cliqueEdges W') \ R) v : ℝ) := by
    intro v hv
    have h1 : (edeg G v : ℝ)
        ≤ (edeg (G \ cliqueEdges W') v : ℝ) + (edeg (cliqueEdges W') v : ℝ) := by
      exact_mod_cast edeg_le_sdiff_add_edeg G (cliqueEdges W') v
    have h2 : (edeg (G \ cliqueEdges W') v : ℝ)
        ≤ (edeg ((G \ cliqueEdges W') \ R) v : ℝ) + (edeg R v : ℝ) := by
      exact_mod_cast edeg_le_sdiff_add_edeg (G \ cliqueEdges W') R v
    have h3 : (edeg (cliqueEdges W') v : ℝ) ≤ (W'.card : ℝ) := by
      exact_mod_cast edeg_cliqueEdges_le' W' v
    have h4 := hdeg v hv
    have h5 := hRdeg v
    linarith
  exact hn₀ ((G \ cliqueEdges W') \ R) W hcard hsub hdeg'

/-! ### The mod-3 correction -/

/-- **The mod-3 correction.**  Inside `W' \ W''` there is a star `D` of `j ≤ 2` edges of `F`; it is
used to make the number of shell edges divisible by three.  The hypotheses are the ones the
cover-down step provides: the link of a vertex of `W'` inside `W'` is large, and `W''` is at most a
`800`-th of `W'`. -/
theorem exists_mod_three_star {F : Finset (Sym2 V)} {W' W'' : Finset V} {j : ℕ}
    (hW''W' : W'' ⊆ W') (h800 : 800 * W''.card ≤ W'.card) (hW'big : 17 ≤ W'.card)
    (hlink : ∀ v ∈ W', 9 * W'.card ≤ 10 * (resLink F W' v).card) (hj : j ≤ 2) :
    ∃ D : Finset (Sym2 V), D ⊆ F ∧ D ⊆ cliqueEdges (W' \ W'') ∧ D.card = j := by
  classical
  -- a vertex of `W' \ W''`
  have hY : 3 ≤ (W' \ W'').card := by
    have h := Finset.card_sdiff_add_card_eq_card hW''W'
    have h2 : W''.card ≤ W'.card := Finset.card_le_card hW''W'
    omega
  obtain ⟨a, ha⟩ : (W' \ W'').Nonempty := Finset.card_pos.1 (by omega)
  have haW' : a ∈ W' := (Finset.mem_sdiff.1 ha).1
  -- two neighbours of `a` inside `W' \ W''`, distinct from `a`
  set B : Finset V := (resLink F W' a) \ (W'' ∪ {a}) with hBdef
  have hBcard : 2 ≤ B.card := by
    have h1 : (resLink F W' a).card ≤ B.card + (W'' ∪ {a}).card := by
      have := Finset.card_le_card_sdiff_add_card (s := resLink F W' a) (t := W'' ∪ {a})
      omega
    have h2 : (W'' ∪ {a}).card ≤ W''.card + 1 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      simp
    have h3 := hlink a haW'
    omega
  obtain ⟨b₁, hb₁, b₂, hb₂, hb₁₂⟩ := Finset.one_lt_card.1 (by omega : 1 < B.card)
  have hmemB : ∀ b ∈ B, b ∈ W' \ W'' ∧ b ≠ a ∧ s(a, b) ∈ F := by
    intro b hb
    rw [hBdef, Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton] at hb
    obtain ⟨hbr, hbn⟩ := hb
    push_neg at hbn
    rw [mem_resLink] at hbr
    exact ⟨Finset.mem_sdiff.2 ⟨hbr.1, hbn.1⟩, hbn.2, hbr.2⟩
  obtain ⟨hb₁Y, hb₁a, hb₁F⟩ := hmemB b₁ hb₁
  obtain ⟨hb₂Y, hb₂a, hb₂F⟩ := hmemB b₂ hb₂
  -- the two-edge star
  set Dfull : Finset (Sym2 V) := {s(a, b₁), s(a, b₂)} with hDfull
  have hne : s(a, b₁) ≠ s(a, b₂) := by
    simp only [ne_eq, Sym2.eq_iff]
    push_neg
    exact ⟨fun _ => hb₁₂, fun _ => hb₁a⟩
  have hDfullcard : Dfull.card = 2 := by
    rw [hDfull, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have hDfullF : Dfull ⊆ F := by
    intro e he
    rw [hDfull, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    exacts [hb₁F, hb₂F]
  have hDfullY : Dfull ⊆ cliqueEdges (W' \ W'') := by
    intro e he
    rw [hDfull, Finset.mem_insert, Finset.mem_singleton] at he
    have hmk : ∀ b : V, b ∈ W' \ W'' → b ≠ a → s(a, b) ∈ cliqueEdges (W' \ W'') := by
      intro b hbY hba
      refine mem_cliqueEdgesV.2 ⟨?_, ?_⟩
      · intro x hx
        rcases Sym2.mem_iff.1 hx with rfl | rfl
        exacts [ha, hbY]
      · simp only [Sym2.isDiag_iff_proj_eq]
        exact fun h => hba h.symm
    rcases he with rfl | rfl
    exacts [hmk b₁ hb₁Y hb₁a, hmk b₂ hb₂Y hb₂a]
  obtain ⟨D, hDsub, hDcard⟩ := Finset.exists_subset_card_eq (by omega : j ≤ Dfull.card)
  exact ⟨D, hDsub.trans hDfullF, hDsub.trans hDfullY, hDcard⟩

/-! ### The cover-down step -/

set_option maxHeartbeats 2000000 in
/-- **The faithful §10.1 cover-down step.**

The residual `BKLO.CoverDownStepResidualLarge` — the single remaining clause of the dense
triangle-decomposition theorem on the cover-down route — follows from the cover-down residual
`BKLO.ShellCoverDown`.  Everything else is discharged here: the shell of the level, the mod-3
correction, the whole divisibility and parity bookkeeping, the damage accounting inside `W'`, the
protection of the level `W''` and of the links into it, and the absorption, the last through the
*proved* bounded-core absorber `BKLO.boundedLeftover_confined`. -/
theorem coverDownStepResidualLarge_of_shellCoverDown (hcd : ShellCoverDown) :
    CoverDownStepResidualLarge := by
  classical
  intro ε hε hε'
  set γ : ℝ := ε / 32 with hγdef
  have hγ : 0 < γ := by rw [hγdef]; positivity
  obtain ⟨C, n₁, hcd'⟩ := hcd γ hγ
  obtain ⟨n₂abs, habs⟩ := boundedLeftover_confined γ hγ C
  set x : ℝ := (32 : ℝ) / ε with hxdef
  have hx : (3200 : ℝ) ≤ x := by
    rw [hxdef, le_div_iff₀ hε]; linarith
  set K : ℕ := max 800 ⌈x⌉₊ with hKdef
  have hceil : (3200 : ℕ) ≤ ⌈x⌉₊ := by
    have h1 : (3200 : ℝ) ≤ (⌈x⌉₊ : ℝ) := le_trans hx (Nat.le_ceil x)
    exact_mod_cast h1
  have hKeq : K = ⌈x⌉₊ := by rw [hKdef]; exact max_eq_right (by omega)
  have hK800 : 800 ≤ K := by omega
  have hKx : x ≤ (K : ℝ) := by rw [hKeq]; exact Nat.le_ceil x
  have hKup : (K : ℝ) ≤ x + 1 := by
    rw [hKeq]
    exact le_of_lt (Nat.ceil_lt_add_one (by linarith))
  have hKε : (8 : ℝ) / ε ≤ (K : ℝ) := by
    refine le_trans ?_ hKx
    rw [hxdef, div_le_div_iff_of_pos_right hε]
    norm_num
  refine ⟨K, max (max n₁ n₂abs) (K * K * 17), hK800, hKε, ?_⟩
  intro f n₂ hn₂ _hwin V _ W W' W'' F hWn₂ hW'W hW''W' hr1 hr2 hr3 _hbig hFW hdiv hdeg _hclean
    hbetween
  -- the thresholds
  have hn₁W : n₁ ≤ W.card :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans hn₂ hWn₂)
  have hnabsW : n₂abs ≤ W.card :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans hn₂ hWn₂)
  have hKK17 : K * K * 17 ≤ W.card := le_trans (le_max_right _ _) (le_trans hn₂ hWn₂)
  have hKpos : 0 < K := by omega
  have hW'17 : 17 ≤ W'.card := by
    have h : K * K * 17 ≤ K * K * W'.card := le_trans hKK17 hr2
    exact Nat.le_of_mul_le_mul_left h (by positivity)
  have h800 : 800 * W''.card ≤ W'.card :=
    le_trans (Nat.mul_le_mul_right _ hK800) hr3
  have hW'nn : (0 : ℝ) ≤ (W'.card : ℝ) := Nat.cast_nonneg _
  have hWnn : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
  have hεW : (0 : ℝ) ≤ ε * (W.card : ℝ) := mul_nonneg hε.le hWnn
  have hεW' : (0 : ℝ) ≤ ε * (W'.card : ℝ) := mul_nonneg hε.le hW'nn
  -- the two size relations between the levels
  have hxγ : x * γ = 1 := by rw [hxdef, hγdef]; field_simp
  have hW'small : (W'.card : ℝ) ≤ γ * (W.card : ℝ) := by
    have h1 : (K : ℝ) * (W'.card : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hr1
    have h2 : x * (W'.card : ℝ) ≤ (W.card : ℝ) := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 hγ.le
    have h4 : γ * (x * (W'.card : ℝ)) = (W'.card : ℝ) := by
      rw [← mul_assoc, mul_comm γ x, hxγ, one_mul]
    linarith
  have hWbig : (W.card : ℝ) ≤ (1 / γ) ^ 3 * (W'.card : ℝ) := by
    have h1 : (W.card : ℝ) ≤ (K : ℝ) * (K : ℝ) * (W'.card : ℝ) := by exact_mod_cast hr2
    have hinv : (1 : ℝ) / γ = x := by rw [hγdef, hxdef]; field_simp
    rw [hinv]
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
    have hsq : (K : ℝ) * (K : ℝ) ≤ (x + 1) * (x + 1) := by nlinarith
    have hcube : (x + 1) * (x + 1) ≤ x ^ 3 := by nlinarith
    have h3 := mul_le_mul_of_nonneg_right (le_trans hsq hcube) hW'nn
    linarith
  -- the shell
  set Sh : Finset (Sym2 V) := F \ cliqueEdges W' with hShdef
  have hShF : Sh ⊆ F := Finset.sdiff_subset
  have hShW : Sh ⊆ cliqueEdges W := hShF.trans hFW
  have hShW' : ∀ e ∈ Sh, e ∉ cliqueEdges W' := fun _ he => (Finset.mem_sdiff.1 he).2
  have hShdeg : ∀ v ∈ W, (9 / 10 + γ) * (W.card : ℝ) ≤ (edeg Sh v : ℝ) := by
    intro v hv
    have h1 : edeg F v ≤ edeg Sh v + edeg (cliqueEdges W') v :=
      edeg_le_sdiff_add_edeg F (cliqueEdges W') v
    have h1' : (edeg F v : ℝ) ≤ (edeg Sh v : ℝ) + (edeg (cliqueEdges W') v : ℝ) := by
      exact_mod_cast h1
    have h2 : (edeg (cliqueEdges W') v : ℝ) ≤ (W'.card : ℝ) := by
      exact_mod_cast edeg_cliqueEdges_le' W' v
    have h3 := hdeg v hv
    have h4 : (W'.card : ℝ) ≤ ε / 32 * (W.card : ℝ) := by
      rw [hγdef] at hW'small; exact hW'small
    rw [hγdef]
    linarith
  -- the mod-3 correction
  set j : ℕ := (3 - Sh.card % 3) % 3 with hjdef
  have hj2 : j ≤ 2 := by omega
  have hlink : ∀ v ∈ W', 9 * W'.card ≤ 10 * (resLink F W' v).card := by
    intro v hv
    have h := hbetween v (hW'W hv)
    have h9 : (9 : ℝ) * (W'.card : ℝ) ≤ 10 * ((resLink F W' v).card : ℝ) := by nlinarith
    exact_mod_cast h9
  obtain ⟨D, hDF, hDY, hDcard⟩ :=
    exists_mod_three_star (F := F) hW''W' h800 hW'17 hlink hj2
  have hDW' : D ⊆ cliqueEdges W' := hDY.trans (cliqueEdges_mono Finset.sdiff_subset)
  have hShD : Disjoint Sh D :=
    Finset.disjoint_left.2 fun e he heD => hShW' e he (hDW' heD)
  -- the target set of the cover-down step
  set E : Finset (Sym2 V) := Sh ∪ D with hEdef
  have hEF : E ⊆ F := Finset.union_subset hShF hDF
  have hEcard : E.card = Sh.card + j := by
    rw [hEdef, Finset.card_union_of_disjoint hShD, hDcard]
  have hE3 : 3 ∣ E.card := by rw [hEcard]; omega
  have hEinter : E ∩ cliqueEdges W' = D := by
    ext e
    simp only [Finset.mem_inter, hEdef, Finset.mem_union]
    constructor
    · rintro ⟨h | h, hcl⟩
      · exact absurd hcl (hShW' e h)
      · exact h
    · intro h
      exact ⟨Or.inr h, hDW' h⟩
  have hEout : ∀ v : V, v ∉ W' → edeg E v = edeg F v := by
    intro v hv
    have hD0 : edeg D v = 0 := edeg_eq_zero_of_subset_cliqueEdges hDW' hv
    have hSh : edeg Sh v = edeg F v := edeg_sdiff_cliqueEdges_of_notMem hv
    have h1 : edeg E v ≤ edeg Sh v + edeg D v := edeg_union_le Sh D v
    have h2 : edeg Sh v ≤ edeg E v := edeg_mono Finset.subset_union_left v
    omega
  -- the residual cover-down statement, at this level
  obtain ⟨U, hUsub, hUC, hcov⟩ :=
    hcd' W W' W'' F E hn₁W hW'W hW''W' hW'small hWbig hFW
      (fun v hv => by
        have h := hdeg v hv
        rw [hγdef]
        nlinarith)
      (fun v hv => by
        have h := hbetween v hv
        rw [hγdef]
        nlinarith)
      Finset.subset_union_left hEF (by rw [hEinter]; exact hDY)
      (by rw [hEinter, hDcard]; exact hj2)
  have hUW : U ⊆ W := hUsub.trans Finset.sdiff_subset
  have hUW' : ∀ v ∈ U, v ∉ W' := fun v hv => (Finset.mem_sdiff.1 (hUsub hv)).2
  -- the bounded-core absorber, run on the shell
  obtain ⟨R, hRSh, hReven, hRdeg, hRabs⟩ :=
    habs Sh W U hnabsW hShW hUW hUC hShdeg
  have hRE : R ⊆ E := hRSh.trans Finset.subset_union_left
  have hRW' : ∀ e ∈ R, e ∉ cliqueEdges W' := fun e he => hShW' e (hRSh he)
  obtain ⟨P₁, hP₁, hleft, hAY, hAdeg, hAmod⟩ := hcov R hRSh hRdeg
  set A : Finset (Sym2 V) := famEdges P₁ with hAdef
  set H : Finset (Sym2 V) := (E \ R) \ A with hHdef
  have hAF : A ⊆ F \ R := famEdges_subset_of_triFamilyIn hP₁
  have hAnotR : ∀ e ∈ A, e ∉ R := fun e he => (Finset.mem_sdiff.1 (hAF he)).2
  -- an edge of `A` at a vertex outside `W'` lies in the target set
  have hAout : ∀ v : V, v ∉ W' → ∀ e ∈ A, v ∈ e → e ∈ E \ R := by
    intro v hv e he hve
    have h1 : e ∉ cliqueEdges W' := fun hc => hv ((mem_cliqueEdgesV.1 hc).1 v hve)
    exact Finset.mem_sdiff.2
      ⟨Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 (hAF he)).1, h1⟩),
        hAnotR e he⟩
  have hAE : ∀ v : V, v ∉ W' → edeg (A ∩ (E \ R)) v = edeg A v := by
    intro v hv
    unfold edeg
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨⟨h, -⟩, hve⟩
      exact ⟨h, hve⟩
    · rintro ⟨he, hve⟩
      exact ⟨⟨he, hAout v hv e he hve⟩, hve⟩
  -- the decomposition of the target set into reservation, covered part and remainder
  have hunER : R ∪ (E \ R) = E := Finset.union_sdiff_of_subset hRE
  have hdisjER : Disjoint R (E \ R) := Finset.disjoint_sdiff
  have hunAH : (A ∩ (E \ R)) ∪ H = E \ R := by
    rw [hHdef]
    ext e
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hdisjAH : Disjoint (A ∩ (E \ R)) H :=
    Finset.disjoint_right.2 fun e he hm => (Finset.mem_sdiff.1 he).2 (Finset.mem_inter.1 hm).1
  have hkey : ∀ v : V, v ∉ W' → edeg E v = edeg R v + edeg A v + edeg H v := by
    intro v hv
    have h1 : edeg E v = edeg R v + edeg (E \ R) v := by
      conv_lhs => rw [← hunER]
      rw [edeg_union_of_disjoint hdisjER]
    have h2 : edeg (E \ R) v = edeg (A ∩ (E \ R)) v + edeg H v := by
      conv_lhs => rw [← hunAH]
      rw [edeg_union_of_disjoint hdisjAH]
    rw [h1, h2, hAE v hv]
    omega
  -- the remainder lies in the shell, away from the reservation
  have hHsub : H ⊆ Sh \ R := by
    intro e he
    have h1 : e ∈ E \ R := (Finset.mem_sdiff.1 he).1
    have h2 : e ∈ cliqueEdges U := hleft he
    have h3 : e ∉ cliqueEdges W' := by
      intro hc
      obtain ⟨p, hp⟩ : ∃ p : V, p ∈ e := by
        induction e using Sym2.ind with
        | _ a b => exact ⟨a, by simp⟩
      exact hUW' p ((mem_cliqueEdgesV.1 h2).1 p hp) ((mem_cliqueEdgesV.1 hc).1 p hp)
    exact Finset.mem_sdiff.2
      ⟨Finset.mem_sdiff.2 ⟨hEF (Finset.mem_sdiff.1 h1).1, h3⟩, (Finset.mem_sdiff.1 h1).2⟩
  -- the remainder has even degrees
  have hHeven : EvenDegrees H := by
    intro v
    by_cases hvU : v ∈ U
    · have hvW' : v ∉ W' := hUW' v hvU
      have hEv : Even (edeg E v) := by
        rw [hEout v hvW']
        exact hdiv.1 v
      obtain ⟨k1, hk1⟩ := hEv
      obtain ⟨k2, hk2⟩ := hReven v
      obtain ⟨k3, hk3⟩ := (hP₁.triDecomp.triDivisible).1 v
      have hk3' : edeg A v = k3 + k3 := hk3
      have h := hkey v hvW'
      exact ⟨k1 - k2 - k3, by omega⟩
    · have h0 : edeg H v = 0 := edeg_eq_zero_of_subset_cliqueEdges hleft hvU
      exact ⟨0, by omega⟩
  -- the mod-3 bookkeeping
  have hDA : D ⊆ A := by
    intro e he
    by_contra hA
    have h1 : e ∈ E \ R :=
      Finset.mem_sdiff.2 ⟨Finset.mem_union_right _ he, fun hR => hRW' e hR (hDW' he)⟩
    have h2 : e ∈ cliqueEdges U := hleft (Finset.mem_sdiff.2 ⟨h1, hA⟩)
    obtain ⟨p, hp⟩ : ∃ p : V, p ∈ e := by
      induction e using Sym2.ind with
      | _ a b => exact ⟨a, by simp⟩
    exact hUW' p ((mem_cliqueEdgesV.1 h2).1 p hp) ((mem_cliqueEdgesV.1 (hDW' he)).1 p hp)
  have hAEsdiff : A \ E = (A ∩ cliqueEdges W') \ D := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨heA, heE⟩
      have hcl : e ∈ cliqueEdges W' := by
        by_contra hc
        exact heE (Finset.mem_union_left _
          (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 (hAF heA)).1, hc⟩))
      exact ⟨⟨heA, hcl⟩, fun hD => heE (Finset.mem_union_right _ hD)⟩
    · rintro ⟨⟨heA, hcl⟩, hD⟩
      refine ⟨heA, fun heE => hD ?_⟩
      have hmem : e ∈ E ∩ cliqueEdges W' := Finset.mem_inter.2 ⟨heE, hcl⟩
      rwa [hEinter] at hmem
  have hcardA : A.card = (A ∩ (E \ R)).card + (A \ E).card := by
    have hun : (A ∩ (E \ R)) ∪ (A \ E) = A := by
      ext e
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
      · intro he
        by_cases hE : e ∈ E
        · exact Or.inl ⟨he, hE, hAnotR e he⟩
        · exact Or.inr ⟨he, hE⟩
    have hdisj : Disjoint (A ∩ (E \ R)) (A \ E) :=
      Finset.disjoint_right.2 fun e he hm =>
        (Finset.mem_sdiff.1 he).2 (Finset.mem_sdiff.1 (Finset.mem_inter.1 hm).2).1
    conv_lhs => rw [← hun]
    rw [Finset.card_union_of_disjoint hdisj]
  have hcardW' : (A ∩ cliqueEdges W').card = (A \ E).card + D.card := by
    rw [hAEsdiff]
    have hDsub : D ⊆ A ∩ cliqueEdges W' := fun e he => Finset.mem_inter.2 ⟨hDA he, hDW' he⟩
    have h := Finset.card_sdiff_add_card_eq_card hDsub
    omega
  have hcardE : E.card = R.card + ((A ∩ (E \ R)).card + H.card) := by
    have h1 : (E \ R).card = (A ∩ (E \ R)).card + H.card := by
      conv_lhs => rw [← hunAH]
      rw [Finset.card_union_of_disjoint hdisjAH]
    have h2 := Finset.card_sdiff_add_card_eq_card hRE
    omega
  have hdvd : 3 ∣ (R ∪ H).card := by
    have hRH : (R ∪ H).card = R.card + H.card := by
      refine Finset.card_union_of_disjoint (Finset.disjoint_right.2 fun e he hm => ?_)
      exact (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 he).1).2 hm
    obtain ⟨p, hp⟩ := (hP₁.triDecomp.triDivisible).2
    have hp' : A.card = 3 * p := hp
    have hmod : (A ∩ cliqueEdges W').card % 3 = D.card % 3 := by
      rw [hAmod, hEinter]
    omega
  -- the absorption
  obtain ⟨P₂, hP₂card, hP₂disj, hP₂edges⟩ := hRabs H hHsub hleft hHeven hdvd
  -- the two families compose
  have hP₁F : TriFamilyIn F P₁ := hP₁.mono Finset.sdiff_subset
  have hRHsub : R ∪ H ⊆ F \ A := by
    intro e he
    rcases Finset.mem_union.1 he with h | h
    · exact Finset.mem_sdiff.2 ⟨hEF (hRE h), fun hm => hAnotR e hm h⟩
    · exact Finset.mem_sdiff.2 ⟨hEF (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 h).1).1,
        (Finset.mem_sdiff.1 h).2⟩
  have hP₂ : TriFamilyIn (F \ A) P₂ := by
    refine ⟨hP₂card, ?_, hP₂disj⟩
    intro t ht
    have hsub : cliqueEdges t ⊆ R ∪ H := by
      rw [← hP₂edges]
      exact Finset.subset_biUnion_of_mem cliqueEdges ht
    exact hsub.trans hRHsub
  have hP : TriFamilyIn F (P₁ ∪ P₂) := triFamilyIn_union hP₁F hP₂
  have hfam : famEdges (P₁ ∪ P₂) = A ∪ (R ∪ H) := by
    rw [famEdges_union, hP₂edges]
  -- an edge inside `W'` that the assembly covers belongs to `A`
  have hcovW' : ∀ e ∈ famEdges (P₁ ∪ P₂), e ∈ cliqueEdges W' → e ∈ A ∩ cliqueEdges W' := by
    intro e he hcl
    rw [hfam] at he
    rcases Finset.mem_union.1 he with h | h
    · exact Finset.mem_inter.2 ⟨h, hcl⟩
    rcases Finset.mem_union.1 h with h | h
    · exact absurd hcl (hRW' e h)
    · exfalso
      obtain ⟨p, hp⟩ : ∃ p : V, p ∈ e := by
        induction e using Sym2.ind with
        | _ a b => exact ⟨a, by simp⟩
      exact hUW' p ((mem_cliqueEdgesV.1 (hleft h)).1 p hp) ((mem_cliqueEdgesV.1 hcl).1 p hp)
  -- a covered edge inside `W'` has both ends outside the protected level
  have hcovY : ∀ e ∈ famEdges (P₁ ∪ P₂), e ∈ cliqueEdges W' →
      ∀ p : V, p ∈ e → p ∉ W'' := by
    intro e he hcl p hp
    have h := hAY (hcovW' e he hcl)
    exact (Finset.mem_sdiff.1 ((mem_cliqueEdgesV.1 h).1 p hp)).2
  -- the conclusion
  refine ⟨P₁ ∪ P₂, hP, ?_, ?_, ?_, ?_⟩
  · -- the leftover lies inside `W'`
    intro e he
    rw [Finset.mem_sdiff] at he
    obtain ⟨heF, hne⟩ := he
    by_contra hW'e
    have heSh : e ∈ Sh := Finset.mem_sdiff.2 ⟨heF, hW'e⟩
    have heE : e ∈ E := Finset.mem_union_left _ heSh
    refine hne ?_
    rw [hfam]
    by_cases hR : e ∈ R
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hR)
    · by_cases hA : e ∈ A
      · exact Finset.mem_union_left _ hA
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨heE, hR⟩, hA⟩))
  · -- the protected level is untouched
    intro e he
    rw [Finset.mem_inter] at he
    refine Finset.mem_sdiff.2 ⟨he.1, fun hm => ?_⟩
    obtain ⟨p, hp⟩ : ∃ p : V, p ∈ e := by
      induction e using Sym2.ind with
      | _ a b => exact ⟨a, by simp⟩
    exact hcovY e hm (cliqueEdges_mono hW''W' he.2) p hp ((mem_cliqueEdgesV.1 he.2).1 p hp)
  · -- the damage inside `W'` stays within the budget
    intro v hv
    have hsub : F ∩ cliqueEdges W' ⊆
        (F \ famEdges (P₁ ∪ P₂)) ∪ (A ∩ cliqueEdges W') := by
      intro e he
      rw [Finset.mem_inter] at he
      by_cases hm : e ∈ famEdges (P₁ ∪ P₂)
      · exact Finset.mem_union_right _ (hcovW' e hm he.2)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨he.1, hm⟩)
    have h1 : edeg (F ∩ cliqueEdges W') v
        ≤ edeg (F \ famEdges (P₁ ∪ P₂)) v + edeg (A ∩ cliqueEdges W') v :=
      le_trans (edeg_mono hsub v) (edeg_union_le _ _ v)
    have h1' : (edeg (F ∩ cliqueEdges W') v : ℝ)
        ≤ (edeg (F \ famEdges (P₁ ∪ P₂)) v : ℝ) + (edeg (A ∩ cliqueEdges W') v : ℝ) := by
      exact_mod_cast h1
    have h2 := hAdeg v
    rw [hγdef] at h2
    linarith
  · -- the links into the protected level are untouched
    intro v hv
    have hsub : resLink F W'' v ⊆ resLink (F \ famEdges (P₁ ∪ P₂)) W'' v := by
      intro a ha
      rw [mem_resLink] at ha ⊢
      refine ⟨ha.1, Finset.mem_sdiff.2 ⟨ha.2, fun hm => ?_⟩⟩
      have hclW' : s(v, a) ∈ cliqueEdges W' := by
        refine mem_cliqueEdgesV.2 ⟨?_, ?_⟩
        · intro p hp
          rcases Sym2.mem_iff.1 hp with rfl | rfl
          exacts [hv, hW''W' ha.1]
        · exact (mem_cliqueEdgesV.1 (hFW ha.2)).2
      exact hcovY _ hm hclW' a (by simp) ha.1
    have h1 : ((resLink F W'' v).card : ℝ)
        ≤ ((resLink (F \ famEdges (P₁ ∪ P₂)) W'' v).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 : (0 : ℝ) ≤ ε / 8 * (W''.card : ℝ) := by positivity
    linarith

end BKLO
