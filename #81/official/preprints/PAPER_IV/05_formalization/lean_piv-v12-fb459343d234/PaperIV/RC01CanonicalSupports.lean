import PaperIV.RC01CanonicalSlots
import PaperIV.K4UniformNibbleCounts

/-!
# Soportes físicos del pool canónico de RC01

`RC01CanonicalSlots` elimina las orientaciones repetidas al nivel de las
cuádruplas de partes. Este módulo hace el paso restante al objeto que consume
el nibble: un candidato es su conjunto literal de seis aristas. No se hace
ningún conteo asintótico aquí; sólo se conserva la semántica física.
-/

namespace PaperIV.RC01CanonicalSupports

open Finset
open PaperIV.FarRounding PaperIV.PatternCounting PaperIV.RegularityFormat
open PaperIV.RC01Candidates PaperIV.RC01CandidatePool PaperIV.RC01CanonicalSlots

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-- Los soportes de aristas de las copias de `K4` de las ranuras canónicas. -/
noncomputable def canonicalSupportPool {δ : ℚ} (R : EqualRegularity G δ) :
    Finset (Finset (Sym2 α)) :=
  (goodK4Slots R).biUnion (fun S =>
    k4CandidateSupports G (canonicalTuple R S))

theorem mem_canonicalSupportPool {δ : ℚ} {R : EqualRegularity G δ}
    {E : Finset (Sym2 α)} :
    E ∈ canonicalSupportPool R ↔
      ∃ S ∈ goodK4Slots R, E ∈ k4CandidateSupports G (canonicalTuple R S) := by
  rw [canonicalSupportPool, Finset.mem_biUnion]

/-- Every canonical support is a literal six-edge support of a physical `K4` in `G`. -/
theorem canonicalSupportPool_subset_k4Supports {δ : ℚ} (R : EqualRegularity G δ) :
    canonicalSupportPool R ⊆ PaperIV.NibblePort.k4Supports G := by
  intro E hE
  obtain ⟨S, hS, hES⟩ := mem_canonicalSupportPool.1 hE
  obtain ⟨hgood, -⟩ := canonicalTuple_spec R hS
  have hparts := (mem_goodK4Tuples.1 hgood).1
  have hdisj : ∀ i j : Fin 4, i ≠ j → Disjoint (canonicalTuple R S i)
      (canonicalTuple R S j) := by
    intro i j hij
    exact R.pairwise_disjoint _ (hparts i) _ (hparts j)
      ((mem_goodK4Tuples.1 hgood).2.1 i j hij)
  exact k4CandidateSupports_subset_k4Supports hdisj hES

/-- Forgetting the canonical orientation only enlarges the pool. This is the
    compatibility map through which deterministic codegree bounds for the old
    pool remain available to the canonical construction. -/
theorem canonicalSupportPool_subset_candidatePool {δ : ℚ} (R : EqualRegularity G δ) :
    canonicalSupportPool R ⊆ candidatePool R := by
  intro E hE
  obtain ⟨S, hS, hES⟩ := mem_canonicalSupportPool.1 hE
  obtain ⟨hgood, -⟩ := canonicalTuple_spec R hS
  exact Finset.mem_biUnion.2 ⟨canonicalTuple R S, hgood, hES⟩

/-- The canonical physical pool is six-uniform, hence is directly admissible as a
hypergraph input for the K4 nibble. -/
theorem canonicalSupportPool_uniform {δ : ℚ} (R : EqualRegularity G δ) :
    PaperIV.NibblePort.Hypergraph.IsUniform (canonicalSupportPool R) 6 := by
  intro E hE
  exact PaperIV.NibblePort.k4Supports_uniform E
    (canonicalSupportPool_subset_k4Supports R hE)

end PaperIV.RC01CanonicalSupports
