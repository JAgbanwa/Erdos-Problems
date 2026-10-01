import PaperIV.RC01CandidatePool

/-!
# Ranuras canónicas de K4 para RC01

La regularidad cuenta cuádruplas ordenadas, mientras que una K4 física no cambia
al permutar sus cuatro partes. Aquí se toma una orientación representante por
conjunto de cuatro partes. No se requiere ordenar vértices ni partes: la
elección se hace sobre un finset no vacío y se acompaña de su certificado.
-/

namespace PaperIV.RC01CanonicalSlots

open Finset
open PaperIV.PatternCounting PaperIV.RegularityFormat PaperIV.RC01Candidates
  PaperIV.RC01CandidatePool

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-- Ranuras no orientadas: los conjuntos de cuatro partes de las cuádruplas buenas. -/
noncomputable def goodK4Slots {δ : ℚ} (R : EqualRegularity G δ) : Finset (Finset (Finset α)) :=
  (goodK4Tuples R).image partImage

/-- Una orientación representante por ranura. Fuera de `goodK4Slots` toma un valor inocuo;
los teoremas siguientes sólo la usan con el certificado de pertenencia. -/
noncomputable def canonicalTuple {δ : ℚ} (R : EqualRegularity G δ)
    (S : Finset (Finset α)) : Fin 4 → Finset α :=
  if h : ∃ V, V ∈ goodK4Tuples R ∧ partImage V = S then Classical.choose h else fun _ => ∅

theorem canonicalTuple_spec {δ : ℚ} (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK4Slots R) :
    canonicalTuple R S ∈ goodK4Tuples R ∧ partImage (canonicalTuple R S) = S := by
  classical
  rw [goodK4Slots] at hS
  obtain ⟨V, hV, hVS⟩ := Finset.mem_image.1 hS
  have hex : ∃ U, U ∈ goodK4Tuples R ∧ partImage U = S := ⟨V, hV, hVS⟩
  rw [canonicalTuple, dif_pos hex]
  exact Classical.choose_spec hex

/-- Pool de candidatos con exactamente una orientación por ranura física. -/
noncomputable def canonicalCandidatePool {δ : ℚ} (R : EqualRegularity G δ) :
    Finset (Finset α) :=
  (goodK4Slots R).biUnion (fun S => candidates G (canonicalTuple R S) patK4)

/-- Las familias de candidatos de dos ranuras canónicas distintas son disjuntas. -/
theorem canonical_slot_candidates_disjoint {δ : ℚ} (R : EqualRegularity G δ)
    {S T : Finset (Finset α)} (hS : S ∈ goodK4Slots R) (hT : T ∈ goodK4Slots R)
    (hST : S ≠ T) :
    Disjoint (candidates G (canonicalTuple R S) patK4)
      (candidates G (canonicalTuple R T) patK4) := by
  have hSdata := canonicalTuple_spec R hS
  have hTdata := canonicalTuple_spec R hT
  have hSparts := (mem_goodK4Tuples.1 hSdata.1).1
  have hTparts := (mem_goodK4Tuples.1 hTdata.1).1
  apply candidates_disjoint_of_partImage_ne R hSparts hTparts
  rw [hSdata.2, hTdata.2]
  exact hST

/-- El pool canónico suma exactamente las masas de las ranuras, sin el factor de las
permutaciones de cuatro partes. -/
theorem card_canonicalCandidatePool {δ : ℚ} (R : EqualRegularity G δ) :
    (canonicalCandidatePool R).card =
      ∑ S ∈ goodK4Slots R, (candidates G (canonicalTuple R S) patK4).card := by
  classical
  have haux : ∀ I : Finset (Finset (Finset α)), I ⊆ goodK4Slots R →
      (I.biUnion (fun S => candidates G (canonicalTuple R S) patK4)).card =
        ∑ S ∈ I, (candidates G (canonicalTuple R S) patK4).card := by
    intro I hI
    induction I using Finset.induction_on with
    | empty => simp
    | insert S I hS ih =>
      have hSI : I ⊆ goodK4Slots R := fun T hT => hI (Finset.mem_insert_of_mem hT)
      have hSgood : S ∈ goodK4Slots R := hI (Finset.mem_insert_self S I)
      have hdisj : Disjoint (candidates G (canonicalTuple R S) patK4)
          (I.biUnion (fun T => candidates G (canonicalTuple R T) patK4)) := by
        rw [Finset.disjoint_left]
        intro K hK hKI
        obtain ⟨T, hTI, hKT⟩ := Finset.mem_biUnion.1 hKI
        exact (Finset.disjoint_left.1
          (canonical_slot_candidates_disjoint R hSgood (hSI hTI) (fun h => hS (h ▸ hTI)))) hK hKT
      rw [Finset.biUnion_insert, Finset.card_union_of_disjoint hdisj, ih hSI, Finset.sum_insert hS]
  simpa [canonicalCandidatePool] using haux (goodK4Slots R) (Finset.Subset.rfl)

end PaperIV.RC01CanonicalSlots
