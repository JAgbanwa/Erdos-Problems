/-
# Reducing the cover-down interface to a *typed pair-covering reservoir*.

`BKLO.BoundedLeftoverCoverDown` (Interface A of `BKLO/BoundedLeftover.lean`) asks for a reservoir
`R₁ ⊆ E` of maximum degree `≤ γ|S|/2` which covers every even leftover `H` of maximum degree `≤ D`
down to a remainder inside a bounded core.

This file reduces it, using the apex machinery of `BKLO/ApexCover.lean`, to a single statement
about the reservoir alone, `BKLO.ApexReservoirExistence`:

* the reserved edges are split into two disjoint parts `Ra`, `Rb`, which — together with an
  arbitrary ranking `rk` of the vertices — decides for each reserved edge which of its endpoints
  may serve as the *apex* of a covering triangle (`apexRel`).  This typing is what makes the
  covering triangles edge-disjoint: a reserved edge can be used in only one of the two roles.
* **pair-covering**: every potential host edge has more than `2D` admissible apexes.  Together
  with `Δ(H) ≤ D` (so that an edge of `H` conflicts with at most `2D` other edges of `H`) the
  greedy theorem `BKLO.exists_apex_fun` then chooses, for every edge of `H` at once, an apex, in
  such a way that the covering triangles are pairwise edge-disjoint.
* **self-repair**: whatever part of the reservoir is left unused (an even-degree subgraph of the
  reservoir, by parity of the triangles) is triangle-decomposable up to a remainder inside the
  bounded core.

The first two items are what the density hypothesis and Hall/greedy give; the third is the
absorption content.  `boundedLeftoverCoverDown_of_apexReservoir` proves that these suffice.
-/
import BKLO.ApexCover
import BKLO.Section10Iteration

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The typed reservoir -/

/-- `apexRel Ra Rb rk u v` : the reserved edge `uv` may be used with `u` as an endpoint of the
covered leftover edge and `v` as the apex of the covering triangle.  The edges of `Ra` are the ones
used "upwards" (apex of larger rank), those of `Rb` "downwards". -/
def apexRel (Ra Rb : Finset (Sym2 V)) (rk : V → ℕ) (u v : V) : Prop :=
  (rk u < rk v ∧ s(u, v) ∈ Ra) ∨ (rk v < rk u ∧ s(u, v) ∈ Rb)

instance apexRel_decidable (Ra Rb : Finset (Sym2 V)) (rk : V → ℕ) (u v : V) :
    Decidable (apexRel Ra Rb rk u v) := by
  unfold apexRel; infer_instance

omit [DecidableEq V] in
/-- The typing makes the role relation asymmetric: a reserved edge cannot be used in both roles. -/
theorem apexRel_asymm {Ra Rb : Finset (Sym2 V)} {rk : V → ℕ} (hab : Disjoint Ra Rb) (u v : V) :
    apexRel Ra Rb rk u v → ¬ apexRel Ra Rb rk v u := by
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) (⟨h3, h4⟩ | ⟨h3, h4⟩)
  · omega
  · rw [Sym2.eq_swap] at h4; exact (Finset.disjoint_left.1 hab h2) h4
  · rw [Sym2.eq_swap] at h4; exact (Finset.disjoint_left.1 hab h4) h2
  · omega

/-- The edge underlying an admissible role is reserved. -/
theorem mem_of_apexRel {Ra Rb : Finset (Sym2 V)} {rk : V → ℕ} {u v : V}
    (h : apexRel Ra Rb rk u v) : s(u, v) ∈ Ra ∪ Rb := by
  rcases h with ⟨_, h⟩ | ⟨_, h⟩
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ h

/-- The admissible apexes for a potential host edge. -/
def apexCandidates (Ra Rb : Finset (Sym2 V)) (rk : V → ℕ) (S : Finset V) (e : Sym2 V) : Finset V :=
  S.filter (fun z => ∀ u ∈ Sym2.toFinset e, apexRel Ra Rb rk u z)

theorem mem_apexCandidates {Ra Rb : Finset (Sym2 V)} {rk : V → ℕ} {S : Finset V} {e : Sym2 V}
    {z : V} : z ∈ apexCandidates Ra Rb rk S e ↔ z ∈ S ∧ ∀ u ∈ e, apexRel Ra Rb rk u z := by
  rw [apexCandidates, Finset.mem_filter]
  simp

/-! ### Parity of the unused reservoir -/

theorem edeg_sdiff_of_subset {R A : Finset (Sym2 V)} (hAR : A ⊆ R) (v : V) :
    edeg R v = edeg A v + edeg (R \ A) v := by
  have hsplit : A ∪ (R \ A) = R := Finset.union_sdiff_of_subset hAR
  calc edeg R v = edeg (A ∪ (R \ A)) v := by rw [hsplit]
    _ = edeg A v + edeg (R \ A) v := edeg_union_of_disjoint Finset.disjoint_sdiff v

-- `evenDegrees_sdiff` is provided by `BKLO.Section10Iteration` (identical statement); the
-- former local duplicate was removed to avoid an environment clash when both branches are
-- imported together (e.g. in `BKLO.CoverDownStepFaithful`).

/-- The apex edges of an apex assignment for an even leftover have even degrees: the covering
triangles have even degrees, and so does the leftover. -/
theorem evenDegrees_apexEdges {H : Finset (Sym2 V)} {f : Sym2 V → V}
    (hass : IsApexAssignment H f) (hHeven : EvenDegrees H) : EvenDegrees (apexEdges H f) := by
  intro v
  have hcov : Even (edeg (apexCover H f) v) := (triDecomp_apexCover hass).triDivisible.1 v
  have hsplit : apexCover H f = H ∪ apexEdges H f := apexCover_eq_union hass.nondiag
  have hdisj : Disjoint H (apexEdges H f) :=
    Finset.disjoint_left.2 fun e he he' => (Finset.mem_sdiff.1 he').2 he
  rw [hsplit, edeg_union_of_disjoint hdisj] at hcov
  rcases hcov with ⟨k, hk⟩
  rcases hHeven v with ⟨m, hm⟩
  exact ⟨k - m, by omega⟩

/-- The unused part of the reservoir has even degrees — which is why the self-repair hypothesis
below is only ever applied to even-degree residues. -/
theorem evenDegrees_residue {R H : Finset (Sym2 V)} {f : Sym2 V → V}
    (hass : IsApexAssignment H f) (hHeven : EvenDegrees H) (hReven : EvenDegrees R)
    (hAR : apexEdges H f ⊆ R) : EvenDegrees (R \ apexEdges H f) :=
  evenDegrees_sdiff hAR hReven (evenDegrees_apexEdges hass hHeven)

/-! ### The reduction -/

/-- **Covering a bounded-degree leftover with a typed pair-covering reservoir.**

Given a reservoir `R = Ra ∪ Rb` (typed, even, reserved inside the host) in which every potential
host edge has more than `2D` admissible apexes, every even leftover `H` of maximum degree at most
`D` outside `R` can be covered by edge-disjoint triangles using reserved apex edges; the only
thing left over is an even-degree subgraph of `R`, and if *that* is decomposable up to a remainder
inside `U`, so is `R ∪ H`. -/
theorem coverDown_of_typedReservoir {E H : Finset (Sym2 V)} {S U : Finset V}
    {Ra Rb : Finset (Sym2 V)} {rk : V → ℕ} {D : ℕ}
    (hES : E ⊆ cliqueEdges S) (hab : Disjoint Ra Rb)
    (hcov : ∀ e ∈ E, 2 * D < (apexCandidates Ra Rb rk S e).card)
    (hrepair : ∀ (H' : Finset (Sym2 V)) (f : Sym2 V → V), H' ⊆ E \ (Ra ∪ Rb) →
      EvenDegrees H' → IsApexAssignment H' f → apexEdges H' f ⊆ Ra ∪ Rb →
      ∃ X : Finset (Sym2 V), X ⊆ cliqueEdges U ∧ X ⊆ (Ra ∪ Rb) \ apexEdges H' f ∧
        TriDecomp (((Ra ∪ Rb) \ apexEdges H' f) \ X))
    (hHE : H ⊆ E \ (Ra ∪ Rb)) (hHeven : EvenDegrees H) (hHdeg : ∀ v : V, edeg H v ≤ D) :
    ∃ X : Finset (Sym2 V), X ⊆ cliqueEdges U ∧ X ⊆ (Ra ∪ Rb) ∪ H ∧
      TriDecomp (((Ra ∪ Rb) ∪ H) \ X) := by
  classical
  set R := Ra ∪ Rb with hR
  have hHR : Disjoint H R :=
    Finset.disjoint_left.2 fun e he he' => (Finset.mem_sdiff.1 (hHE he)).2 he'
  have hHEsub : H ⊆ E := fun e he => (Finset.mem_sdiff.1 (hHE he)).1
  -- every edge of `H` is a genuine edge and has many admissible apexes
  have hnd : ∀ e ∈ H, ¬ e.IsDiag := fun e he => (mem_cliqueEdgesV.1 (hES (hHEsub he))).2
  have hN : ∀ e ∈ H, 2 * D < (apexCandidates Ra Rb rk S e).card :=
    fun e he => hcov e (hHEsub he)
  -- the greedy choice of apexes
  obtain ⟨f, hfN, hfconf⟩ :=
    exists_apex_fun D (apexCandidates Ra Rb rk S) H hHdeg hN
  have hrole : ∀ e ∈ H, ∀ u ∈ e, apexRel Ra Rb rk u (f e) :=
    fun e he u hu => (mem_apexCandidates.1 (hfN e he)).2 u hu
  have hnotH : ∀ e ∈ H, ∀ u ∈ e, s(u, f e) ∉ H := by
    intro e he u hu hmem
    exact (Finset.disjoint_left.1 hHR hmem) (mem_of_apexRel (hrole e he u hu))
  have hass : IsApexAssignment H f :=
    isApexAssignment_of_asymm (P := apexRel Ra Rb rk) hnd hrole
      (fun _ _ _ _ v => apexRel_asymm hab _ v) hnotH hfconf
  -- the apex edges are reserved
  have hAR : apexEdges H f ⊆ R := by
    intro g hg
    obtain ⟨hgcov, hgH⟩ := Finset.mem_sdiff.1 hg
    obtain ⟨t, ht, hgt⟩ := Finset.mem_biUnion.1 hgcov
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 ht
    rcases (mem_cliqueEdges_apexTri_iff (hnd e he) (hass.apex_notMem e he)).1 hgt with rfl | ⟨u, hu, rfl⟩
    · exact absurd he hgH
    · exact mem_of_apexRel (hrole e he u hu)
  obtain ⟨X, hXU, hXsub, hXdec⟩ := hrepair H f hHE hHeven hass hAR
  refine ⟨X, hXU, hXsub.trans ((Finset.sdiff_subset).trans Finset.subset_union_left), ?_⟩
  exact triDecomp_sdiff_of_apexAssignment hass hHR.symm hAR hXsub hXdec

/-! ### The remaining gap, isolated -/

/-- **The remaining gap of the bounded-leftover absorber.**

For every `γ > 0` and every leftover degree bound `D`, every large dense triangle-divisible host
contains a *typed pair-covering reservoir which repairs its own residue*: reserved edges split into
two parts `Ra`, `Rb` of total maximum degree at most `γ|S|/2`, with even degrees, such that

* every potential host edge has more than `2D` admissible apexes (pair covering), and
* the part of the reservoir left unused by any apex assignment for a bounded-degree even leftover
  is triangle-decomposable up to a remainder inside a core `U` of bounded size (self-repair).

By `boundedLeftoverCoverDown_of_apexReservoir` this implies Interface A, hence — with the
already-proved Interface B — the bounded-leftover absorber. -/
def ApexReservoirExistence : Prop :=
  ∀ γ : ℝ, 0 < γ → ∀ D : ℕ, ∃ C n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → TriDivisible E →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ (Ra Rb : Finset (Sym2 V)) (rk : V → ℕ) (U : Finset V),
        Ra ∪ Rb ⊆ E ∧ Disjoint Ra Rb ∧ U ⊆ S ∧ U.card ≤ C ∧
        EvenDegrees (Ra ∪ Rb) ∧
        (∀ v : V, (edeg (Ra ∪ Rb) v : ℝ) ≤ γ * (S.card : ℝ) / 2) ∧
        (∀ e ∈ E, 2 * D < (apexCandidates Ra Rb rk S e).card) ∧
        (∀ (H : Finset (Sym2 V)) (f : Sym2 V → V), H ⊆ E \ (Ra ∪ Rb) →
          EvenDegrees H → IsApexAssignment H f → apexEdges H f ⊆ Ra ∪ Rb →
          ∃ X : Finset (Sym2 V), X ⊆ cliqueEdges U ∧ X ⊆ (Ra ∪ Rb) \ apexEdges H f ∧
            TriDecomp (((Ra ∪ Rb) \ apexEdges H f) \ X))

/-- **Interface A from the typed pair-covering reservoir.** -/
theorem boundedLeftoverCoverDown_of_apexReservoir (h : ApexReservoirExistence) :
    BoundedLeftoverCoverDown := by
  intro γ hγ D
  obtain ⟨C, n₀, hres⟩ := h γ hγ D
  refine ⟨C, n₀, ?_⟩
  intro V _ E S hn hES hdiv hdeg
  obtain ⟨Ra, Rb, rk, U, hRE, hab, hUS, hUC, hReven, hRdeg, hcov, hrepair⟩ :=
    hres E S hn hES hdiv hdeg
  refine ⟨Ra ∪ Rb, U, hRE, hUS, hUC, hReven, hRdeg, ?_⟩
  intro H hHE hHeven hHdeg
  exact coverDown_of_typedReservoir hES hab hcov hrepair hHE hHeven hHdeg

end BKLO
