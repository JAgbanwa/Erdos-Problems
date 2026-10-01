import PaperIV.RD09H1SpokeRealization
import PaperIV.RD09RootExteriorAdapter

/-!
# Canonical vertex accounts for the H1 invalid-candidate family

This module exposes the two literal loads hidden in `canonicalBad`: missing
root--candidate spokes and phase-I spokes already used at a root.  The main
theorem proves the pointwise bound required by the RD09 second-moment lemma.
-/

namespace PaperIV.RD09CanonicalBadAccounts

open Finset PaperIV.Model PaperIV.RD09FactorCandidateMoments
open PaperIV.RD09H1SpokeRealization PaperIV.MultiHostTriangleLift
open PaperIV.RD09RootExteriorAdapter PaperIV.RootVocab

variable {V I Z Cand : Type*}
variable [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable [Fintype Z] [DecidableEq Z]
variable [Fintype Cand] [DecidableEq Cand]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Exterior candidates missing the spoke to a fixed root vertex. -/
def missingCandidates (core : Z ↪ V) (cand : Cand ↪ V) (x : Z) : Finset Cand :=
  Finset.univ.filter fun c => ¬ G.Adj (cand c) (core x)

/-- Exterior candidates whose physical vertex is already an endpoint of a
phase-I base assigned to the host corresponding to `x`. -/
def usedCandidates (cand : Cand ↪ V) (roots : I ≃ Z)
    (E : I → Finset (Sym2 V)) (x : Z) : Finset Cand :=
  Finset.univ.filter fun c => ∃ e ∈ E (roots.symm x), cand c ∈ e

/-- Candidates occurring on one physical base edge. -/
def endpointCandidates (cand : Cand ↪ V) (e : Sym2 V) : Finset Cand :=
  Finset.univ.filter fun c => cand c ∈ e

@[simp] theorem mem_missingCandidates {core : Z ↪ V} {cand : Cand ↪ V}
    {x : Z} {c : Cand} :
    c ∈ missingCandidates (G := G) core cand x ↔ ¬ G.Adj (cand c) (core x) := by
  simp [missingCandidates]

@[simp] theorem mem_usedCandidates {cand : Cand ↪ V} {roots : I ≃ Z}
    {E : I → Finset (Sym2 V)} {x : Z} {c : Cand} :
    c ∈ usedCandidates cand roots E x ↔
      ∃ e ∈ E (roots.symm x), cand c ∈ e := by
  simp [usedCandidates]

/-- Every canonical invalid candidate is charged to one of the two endpoint
accounts.  This is the literal set-theoretic content behind `b_xy ≤ d_x+d_y`. -/
theorem canonicalBad_subset_endpoint_accounts
    [LinearOrder Z]
    (core : Z ↪ V) (cand : Cand ↪ V) (z : I → V)
    (E : I → Finset (Sym2 V)) (roots : I ≃ Z)
    (hroot : ∀ i, z i = core (roots i)) (b : Z × Z) :
    canonicalBad G core cand z E b ⊆
      (missingCandidates (G := G) core cand b.1 ∪ usedCandidates cand roots E b.1) ∪
      (missingCandidates (G := G) core cand b.2 ∪ usedCandidates cand roots E b.2) := by
  intro c hc
  rw [mem_canonicalBad] at hc
  rcases hc with hc | hc | ⟨i, e, he, hz, hce⟩
  · simp [hc]
  · simp [hc]
  · rw [hroot i, Sym2.mem_iff] at hz
    rcases hz with hz | hz
    · have hzi : roots i = b.1 := core.injective hz
      have hii : i = roots.symm b.1 := by
        apply roots.injective
        simpa [hzi]
      apply Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr ?_)))
      rw [mem_usedCandidates]
      exact ⟨e, hii ▸ he, hce⟩
    · have hzi : roots i = b.2 := core.injective hz
      have hii : i = roots.symm b.2 := by
        apply roots.injective
        simpa [hzi]
      apply Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr ?_)))
      rw [mem_usedCandidates]
      exact ⟨e, hii ▸ he, hce⟩

/-- The exact pointwise cardinal bound consumed by
`exists_assign_rd09L2`, with the accounts defined from the physical graph. -/
theorem card_canonicalBad_le_endpoint_accounts
    [LinearOrder Z]
    (core : Z ↪ V) (cand : Cand ↪ V) (z : I → V)
    (E : I → Finset (Sym2 V)) (roots : I ≃ Z)
    (hroot : ∀ i, z i = core (roots i)) (b : Z × Z) :
    (canonicalBad G core cand z E b).card ≤
      ((missingCandidates (G := G) core cand b.1).card +
        (usedCandidates cand roots E b.1).card) +
      ((missingCandidates (G := G) core cand b.2).card +
        (usedCandidates cand roots E b.2).card) := by
  have hsub := canonicalBad_subset_endpoint_accounts
    (G := G) core cand z E roots hroot b
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le
    (missingCandidates (G := G) core cand b.1 ∪ usedCandidates cand roots E b.1)
    (missingCandidates (G := G) core cand b.2 ∪ usedCandidates cand roots E b.2)
  have h3 := Finset.card_union_le
    (missingCandidates (G := G) core cand b.1) (usedCandidates cand roots E b.1)
  have h4 := Finset.card_union_le
    (missingCandidates (G := G) core cand b.2) (usedCandidates cand roots E b.2)
  omega

/-- The candidate endpoints used at a root are at most two per phase-I base.
No disjointness assumption is needed for this upper bound. -/
theorem card_usedCandidates_le_two_mul
    (cand : Cand ↪ V) (roots : I ≃ Z) (E : I → Finset (Sym2 V))
    (hE : ∀ i, ∀ e ∈ E i, e ∈ graphEdges G) (x : Z) :
    (usedCandidates cand roots E x).card ≤ 2 * (E (roots.symm x)).card := by
  classical
  have hunion : usedCandidates cand roots E x =
      (E (roots.symm x)).biUnion (endpointCandidates cand) := by
    ext c
    simp [usedCandidates, endpointCandidates]
  rw [hunion]
  calc
    ((E (roots.symm x)).biUnion (endpointCandidates cand)).card
        ≤ ∑ e ∈ E (roots.symm x), (endpointCandidates cand e).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ E (roots.symm x), 2 := by
      apply Finset.sum_le_sum
      intro e he
      have hmap : (endpointCandidates cand e).card ≤ e.toFinset.card := by
        exact Finset.card_le_card_of_injOn cand
          (by
            intro c hc
            exact (Finset.mem_filter.mp hc).2 |> Sym2.mem_toFinset.mpr)
          (fun _ _ _ _ h => cand.injective h)
      have htwo : e.toFinset.card = 2 :=
        Sym2.card_toFinset_of_not_isDiag e
          (not_isDiag_of_mem_graphEdges G (hE (roots.symm x) e he))
      rwa [htwo] at hmap
    _ = 2 * (E (roots.symm x)).card := by simp [Nat.mul_comm]

/-- The two natural-number loads passed to the RD09 moment engine. -/
def missingLoad (core : Z ↪ V) (cand : Cand ↪ V) (x : Z) : ℕ :=
  (missingCandidates (G := G) core cand x).card

def usedLoad (roots : I ≃ Z) (E : I → Finset (Sym2 V)) (x : Z) : ℕ :=
  2 * (E (roots.symm x)).card

/-- The physical accounts simultaneously provide the pointwise bad-set
bound, the per-root used-spoke bound, and the exact total `2f` identity. -/
theorem canonicalBad_account_package
    [LinearOrder Z]
    (core : Z ↪ V) (cand : Cand ↪ V) (z : I → V)
    (E : I → Finset (Sym2 V)) (roots : I ≃ Z)
    (hroot : ∀ i, z i = core (roots i))
    (h1 : IsMultiExteriorHub G z E) {t : ℕ}
    (ht : ∀ i, (E i).card ≤ t) :
    (∀ b ∈ corePairs Z,
      (canonicalBad G core cand z E b).card ≤
        (missingLoad (G := G) core cand b.1 + usedLoad roots E b.1) +
        (missingLoad (G := G) core cand b.2 + usedLoad roots E b.2)) ∧
    (∀ x, usedLoad roots E x ≤ 2 * t) ∧
    (∑ x, usedLoad roots E x) = 2 * (multiLiftedPacking z E).card := by
  constructor
  · intro b _hb
    exact (card_canonicalBad_le_endpoint_accounts
      (G := G) core cand z E roots hroot b).trans
        (Nat.add_le_add
          (Nat.add_le_add_left
            (card_usedCandidates_le_two_mul (G := G) cand roots E
              (fun i e he => (h1.hub i).edges e he) b.1)
            (missingLoad (G := G) core cand b.1))
          (Nat.add_le_add_left
            (card_usedCandidates_le_two_mul (G := G) cand roots E
              (fun i e he => (h1.hub i).edges e he) b.2)
            (missingLoad (G := G) core cand b.2)))
  · constructor
    · intro x
      exact Nat.mul_le_mul_left 2 (ht (roots.symm x))
    · calc
        (∑ x : Z, usedLoad roots E x) = ∑ i : I, 2 * (E i).card := by
          simpa [usedLoad] using
            (roots.symm.sum_comp (fun i : I => 2 * (E i).card))
        _ = 2 * ∑ i : I, (E i).card := by rw [Finset.mul_sum]
        _ = 2 * (multiLiftedPacking z E).card := by
          rw [card_multiLiftedPacking h1]

section RootExterior

/-- The canonical embedding of the root subtype. -/
def rootEmbedding (P : Finset V) : {x : V // x ∈ P} ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- The canonical missing load at a root vertex is literally the rooted
missing-column cardinality. -/
theorem missingLoad_root_exterior_eq (P : Finset V) (x : {v : V // v ∈ P}) :
    missingLoad (G := G) (rootEmbedding P) (exteriorEmbedding P) x =
      (missingColumn G P x.1).card := by
  classical
  unfold missingLoad
  apply Finset.card_bij (fun c _ => c.1)
  · intro c hc
    rw [mem_missingColumn]
    have hcP : (c : V) ∈ outsideVertices P := c.2
    exact ⟨mem_outsideVertices.mp hcP, by
      rw [mem_missingCandidates] at hc
      simpa [rootEmbedding, exteriorEmbedding] using
        (fun hadj => hc hadj.symm)⟩
  · intro c₁ _ c₂ _ h
    exact Subtype.ext h
  · intro y hy
    have hy' := mem_missingColumn.mp hy
    refine ⟨⟨y, by simpa using hy'.1⟩, ?_, rfl⟩
    rw [mem_missingCandidates]
    simpa [rootEmbedding, exteriorEmbedding] using
      (fun hadj => hy'.2 hadj.symm)

/-- The sum of the canonical missing loads is exactly the global
root--exterior missing-incidence account `A`. -/
theorem sum_missingLoad_root_exterior (P : Finset V) :
    (∑ x : {v : V // v ∈ P},
      missingLoad (G := G) (rootEmbedding P) (exteriorEmbedding P) x) =
      PaperIV.RootVocab.missingIncidences G P := by
  classical
  let S := PaperIV.RD09L1Adapter.missingIncidences G
    (rootVertex P (Equiv.refl {v : V // v ∈ P})) (exteriorEmbedding P)
  have hMaps : (S : Set ({v : V // v ∈ P} × ExteriorVertex P)).MapsTo
      Prod.fst (Finset.univ : Finset {v : V // v ∈ P}) := by
    intro q hq
    exact Finset.mem_univ q.1
  have hFibers : ∀ x : {v : V // v ∈ P},
      (S.filter fun q => q.1 = x).card =
        (missingCandidates (G := G) (rootEmbedding P) (exteriorEmbedding P) x).card := by
    intro x
    apply Finset.card_bij (fun q _ => q.2)
    · intro q hq
      simp only [Finset.mem_filter] at hq
      rw [mem_missingCandidates]
      have hbad := PaperIV.RD09L1Adapter.mem_missingIncidences.mp hq.1
      rw [hq.2] at hbad
      simpa [S, rootVertex, rootEmbedding] using
        (fun hadj => hbad hadj.symm)
    · intro q₁ hq₁ q₂ hq₂ hsnd
      simp only [Finset.mem_filter] at hq₁ hq₂
      exact Prod.ext (hq₁.2.trans hq₂.2.symm) hsnd
    · intro c hc
      refine ⟨(x, c), ?_, rfl⟩
      simp only [Finset.mem_filter]
      refine ⟨?_, by simp⟩
      rw [PaperIV.RD09L1Adapter.mem_missingIncidences]
      have hc' := mem_missingCandidates.mp hc
      simpa [S, rootVertex, rootEmbedding] using
        (fun hadj => hc' hadj.symm)
  have hfiber :
      (∑ x : {v : V // v ∈ P},
        missingLoad (G := G) (rootEmbedding P) (exteriorEmbedding P) x) = S.card := by
    rw [Finset.card_eq_sum_card_fiberwise hMaps]
    apply Finset.sum_congr rfl
    intro x _
    exact (hFibers x).symm
  exact hfiber.trans
    (card_missingIncidences_root_exterior (G := G) P
      (Equiv.refl {v : V // v ∈ P}))

end RootExterior

end PaperIV.RD09CanonicalBadAccounts
