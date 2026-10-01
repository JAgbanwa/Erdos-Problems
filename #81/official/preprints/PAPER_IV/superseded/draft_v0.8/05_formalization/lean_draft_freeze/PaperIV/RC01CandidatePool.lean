import PaperIV.RC01Candidates
import PaperIV.RegularityFormat

/-!
# El pool físico de cuádruplas buenas de RC01

Partiendo de una `EqualRegularity`, este módulo enumera literalmente todas las
cuádruplas ordenadas de partes distintas cuyas seis parejas no son
excepcionales. Cada uno de sus soportes pertenece al hipergrafo físico de K4 de
`G`. La selección por capas y propietarios se hará después sobre este pool.
-/

namespace PaperIV.RC01CandidatePool

open Finset
open PaperIV.PatternCounting PaperIV.RegularityFormat PaperIV.RC01Candidates

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-- Cuádrupla de partes apta para una copia transversal de `K4`. -/
def K4TupleGood {δ : ℚ} (R : EqualRegularity G δ) (V : Fin 4 → Finset α) : Prop :=
  (∀ i j : Fin 4, i ≠ j → V i ≠ V j) ∧
  (∀ e ∈ patK4, (V e.1, V e.2) ∉ R.bad)

/-- The finite candidate filter is classical only at this boundary; all later
    counting statements remain literal finite-set statements. -/
instance decidableK4TupleGood {δ : ℚ} (R : EqualRegularity G δ) :
    DecidablePred (K4TupleGood R) := by
  intro V
  unfold K4TupleGood
  infer_instance

/-- Todas las cuádruplas de partes buenas del certificado. -/
noncomputable def goodK4Tuples {δ : ℚ} (R : EqualRegularity G δ) :
    Finset (Fin 4 → Finset α) :=
  (Fintype.piFinset (fun _ : Fin 4 => R.parts)).filter (K4TupleGood R)

theorem mem_goodK4Tuples {δ : ℚ} {R : EqualRegularity G δ} {V : Fin 4 → Finset α} :
    V ∈ goodK4Tuples R ↔
      (∀ i, V i ∈ R.parts) ∧ K4TupleGood R V := by
  classical
  rw [goodK4Tuples, Finset.mem_filter, Fintype.mem_piFinset]

/-- La unión literal de los soportes candidatos de todas las cuádruplas buenas. -/
noncomputable def candidatePool {δ : ℚ} (R : EqualRegularity G δ) :
    Finset (Finset (Sym2 α)) :=
  (goodK4Tuples R).biUnion (k4CandidateSupports G)

/-- Todo miembro del pool es una hiperarista física de K4 de `G`. -/
theorem candidatePool_subset_k4Supports {δ : ℚ} (R : EqualRegularity G δ) :
    candidatePool R ⊆ PaperIV.NibblePort.k4Supports G := by
  classical
  intro S hS
  obtain ⟨V, hV, hSV⟩ := Finset.mem_biUnion.1 hS
  have hdata := mem_goodK4Tuples.1 hV
  have hdisj : ∀ i j : Fin 4, i ≠ j → Disjoint (V i) (V j) := by
    intro i j hij
    exact R.pairwise_disjoint _ (hdata.1 i) _ (hdata.1 j) (hdata.2.1 i j hij)
  exact k4CandidateSupports_subset_k4Supports hdisj hSV

/-- El pool que se entregará al nibble es literalmente `6`-uniforme. -/
theorem candidatePool_uniform {δ : ℚ} (R : EqualRegularity G δ) :
    PaperIV.NibblePort.Hypergraph.IsUniform (candidatePool R) 6 := by
  intro S hS
  exact PaperIV.NibblePort.k4Supports_uniform _ (candidatePool_subset_k4Supports R hS)

/-- Todo índice del pool bueno lleva consigo la cota de masa física entregada por la
regularidad; la selección posterior sólo debe decidir cuáles índices conservar. -/
theorem card_candidates_ge_of_mem_goodK4Tuples {δ : ℚ} (hδ : 0 ≤ δ)
    (R : EqualRegularity G δ) {V : Fin 4 → Finset α} (hV : V ∈ goodK4Tuples R) :
    ((∏ e ∈ patK4, G.edgeDensity (V e.1) (V e.2)) - 6 * δ) * (R.size : ℚ) ^ 4
      ≤ ((candidates G V patK4).card : ℚ) := by
  have hdata := mem_goodK4Tuples.1 hV
  exact card_candidates_K4_ge hδ R V hdata.1
    (fun e he => hdata.2.1 e.1 e.2 (patK4_ne e he)) hdata.2.2

/-! ## Capas de propiedad: el objeto `Hσ` -/

/-- `Hσ` es el subhipergrafo de candidatos cuyas seis aristas físicas pertenecen al mismo
propietario `σ`. El mapa `own` puede tomar también el valor `none`, que representa una arista
no asignada; esas copias simplemente no entran en ninguna capa. -/
noncomputable def ownedLayer {κ : Type*} [DecidableEq κ] {δ : ℚ} (R : EqualRegularity G δ)
    (own : Sym2 α → Option κ) (σ : κ) : Finset (Finset (Sym2 α)) :=
  (candidatePool R).filter (fun S => ∀ e ∈ S, own e = some σ)

theorem ownedLayer_subset_pool {κ : Type*} [DecidableEq κ] {δ : ℚ}
    (R : EqualRegularity G δ) (own : Sym2 α → Option κ) (σ : κ) :
    ownedLayer R own σ ⊆ candidatePool R :=
  Finset.filter_subset _ _

theorem ownedLayer_uniform {κ : Type*} [DecidableEq κ] {δ : ℚ}
    (R : EqualRegularity G δ) (own : Sym2 α → Option κ) (σ : κ) :
    PaperIV.NibblePort.Hypergraph.IsUniform (ownedLayer R own σ) 6 := by
  intro S hS
  exact candidatePool_uniform R _ (ownedLayer_subset_pool R own σ hS)

theorem ownedLayer_subset_k4Supports {κ : Type*} [DecidableEq κ] {δ : ℚ}
    (R : EqualRegularity G δ) (own : Sym2 α → Option κ) (σ : κ) :
    ownedLayer R own σ ⊆ PaperIV.NibblePort.k4Supports G :=
  fun S hS => candidatePool_subset_k4Supports R (ownedLayer_subset_pool R own σ hS)

theorem mem_ownedLayer {κ : Type*} [DecidableEq κ] {δ : ℚ}
    {R : EqualRegularity G δ} {own : Sym2 α → Option κ} {σ : κ}
    {S : Finset (Sym2 α)} :
    S ∈ ownedLayer R own σ ↔ S ∈ candidatePool R ∧ ∀ e ∈ S, own e = some σ := by
  rw [ownedLayer, Finset.mem_filter]

/-- Capas con propietarios distintos no comparten ningún recurso físico. -/
theorem ownedLayer_resource_disjoint {κ : Type*} [DecidableEq κ] {δ : ℚ}
    {R : EqualRegularity G δ} {own : Sym2 α → Option κ} {σ τ : κ} (hστ : σ ≠ τ)
    {S T : Finset (Sym2 α)} (hS : S ∈ ownedLayer R own σ)
    (hT : T ∈ ownedLayer R own τ) : Disjoint S T := by
  rw [Finset.disjoint_left]
  intro e heS heT
  have hσ := (mem_ownedLayer.1 hS).2 e heS
  have hτ := (mem_ownedLayer.1 hT).2 e heT
  exact hστ (Option.some.inj (hσ.symm.trans hτ))

/-- Unión de todas las capas de propietarios, antes de ejecutar el nibble. -/
noncomputable def layerUnion {κ : Type*} [Fintype κ] [DecidableEq κ] {δ : ℚ}
    (R : EqualRegularity G δ) (own : Sym2 α → Option κ) : Finset (Finset (Sym2 α)) :=
  Finset.univ.biUnion (ownedLayer R own)

/-- Las capas mismas no se solapan: cada soporte de seis aristas puede pertenecer a lo sumo a
un propietario. -/
theorem card_layerUnion {κ : Type*} [Fintype κ] [DecidableEq κ] {δ : ℚ}
    (R : EqualRegularity G δ) (own : Sym2 α → Option κ) :
    (layerUnion R own).card = ∑ σ, (ownedLayer R own σ).card := by
  classical
  have haux : ∀ I : Finset κ,
      (I.biUnion (ownedLayer R own)).card = ∑ σ ∈ I, (ownedLayer R own σ).card := by
    intro I
    induction I using Finset.induction_on with
    | empty => simp
    | insert σ I hσ ih =>
      have hdisj : Disjoint (ownedLayer R own σ) (I.biUnion (ownedLayer R own)) := by
        rw [Finset.disjoint_left]
        intro S hS hSI
        obtain ⟨τ, hτI, hSτ⟩ := Finset.mem_biUnion.1 hSI
        by_cases hστ : σ = τ
        · exact hσ (hστ ▸ hτI)
        · have hcard : S.card = 6 := ownedLayer_uniform R own σ S hS
          obtain ⟨e, he⟩ := Finset.card_pos.1 (by omega : 0 < S.card)
          exact (Finset.disjoint_left.1 (ownedLayer_resource_disjoint hστ hS hSτ)) he he
      rw [Finset.biUnion_insert, Finset.card_union_of_disjoint hdisj, ih, Finset.sum_insert hσ]
  simpa [layerUnion] using haux Finset.univ

theorem layerUnion_subset_k4Supports {κ : Type*} [Fintype κ] [DecidableEq κ] {δ : ℚ}
    (R : EqualRegularity G δ) (own : Sym2 α → Option κ) :
    layerUnion R own ⊆ PaperIV.NibblePort.k4Supports G := by
  intro S hS
  obtain ⟨σ, -, hSσ⟩ := Finset.mem_biUnion.1 hS
  exact ownedLayer_subset_k4Supports R own σ hSσ

theorem layerUnion_uniform {κ : Type*} [Fintype κ] [DecidableEq κ] {δ : ℚ}
    (R : EqualRegularity G δ) (own : Sym2 α → Option κ) :
    PaperIV.NibblePort.Hypergraph.IsUniform (layerUnion R own) 6 := by
  intro S hS
  exact PaperIV.NibblePort.k4Supports_uniform _ (layerUnion_subset_k4Supports R own hS)

/-- Unión de las salidas del nibble, una por propietario. -/
def matchingUnion {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : κ → Finset (Finset (Sym2 α))) : Finset (Finset (Sym2 α)) :=
  Finset.univ.biUnion M

/-- Los matchings obtenidos dentro de capas de propietario se ensamblan en un único matching
del pool físico. La única interacción posible entre capas sería compartir una arista, y
`ownedLayer_resource_disjoint` la excluye literalmente. -/
theorem matchingUnion_isMatching {κ : Type*} [Fintype κ] [DecidableEq κ] {δ : ℚ}
    (R : EqualRegularity G δ) (own : Sym2 α → Option κ)
    (M : κ → Finset (Finset (Sym2 α)))
    (hM : ∀ σ, PaperIV.NibblePort.Hypergraph.IsMatching (ownedLayer R own σ) (M σ)) :
    PaperIV.NibblePort.Hypergraph.IsMatching (candidatePool R) (matchingUnion M) := by
  constructor
  · intro S hS
    obtain ⟨σ, -, hSσ⟩ := Finset.mem_biUnion.1 hS
    exact ownedLayer_subset_pool R own σ ((hM σ).subset hSσ)
  · intro S hS T hT hST
    obtain ⟨σ, -, hSσ⟩ := Finset.mem_biUnion.1 hS
    obtain ⟨τ, -, hTτ⟩ := Finset.mem_biUnion.1 hT
    by_cases hστ : σ = τ
    · subst τ
      exact (hM σ).disjoint S hSσ T hTτ hST
    · exact ownedLayer_resource_disjoint hστ ((hM σ).subset hSσ) ((hM τ).subset hTτ)

/-- Las familias elegidas en propietarios distintos son disjuntas como familias de
hiperaristas. Esto es más fuerte que la compatibilidad del matching y es la entrada para
sumar cardinalidades y ganancias por capa. -/
theorem layer_matchings_disjoint {κ : Type*} [Fintype κ] [DecidableEq κ] {δ : ℚ}
    (R : EqualRegularity G δ) (own : Sym2 α → Option κ)
    (M : κ → Finset (Finset (Sym2 α)))
    (hM : ∀ σ, PaperIV.NibblePort.Hypergraph.IsMatching (ownedLayer R own σ) (M σ))
    {σ τ : κ} (hστ : σ ≠ τ) : Disjoint (M σ) (M τ) := by
  rw [Finset.disjoint_left]
  intro S hS hT
  have hSLayer := (hM σ).subset hS
  have hTLayer := (hM τ).subset hT
  have hcard : S.card = 6 := ownedLayer_uniform R own σ S hSLayer
  have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨e, he⟩ := hSne
  exact (Finset.disjoint_left.1 (ownedLayer_resource_disjoint hστ hSLayer hTLayer)) he he

/-- La unión de las capas preserva exactamente el número total de hiperaristas elegidas. -/
theorem card_matchingUnion {κ : Type*} [Fintype κ] [DecidableEq κ] {δ : ℚ}
    (R : EqualRegularity G δ) (own : Sym2 α → Option κ)
    (M : κ → Finset (Finset (Sym2 α)))
    (hM : ∀ σ, PaperIV.NibblePort.Hypergraph.IsMatching (ownedLayer R own σ) (M σ)) :
    (matchingUnion M).card = ∑ σ, (M σ).card := by
  classical
  have haux : ∀ I : Finset κ, (I.biUnion M).card = ∑ σ ∈ I, (M σ).card := by
    intro I
    induction I using Finset.induction_on with
    | empty => simp
    | insert σ I hσ ih =>
      have hdisj : Disjoint (M σ) (I.biUnion M) := by
        rw [Finset.disjoint_left]
        intro S hS hSI
        obtain ⟨τ, hτI, hSτ⟩ := Finset.mem_biUnion.1 hSI
        by_cases hστ : σ = τ
        · exact hσ (hστ ▸ hτI)
        · exact (Finset.disjoint_left.1 (layer_matchings_disjoint R own M hM hστ)) hS hSτ
      rw [Finset.biUnion_insert, Finset.card_union_of_disjoint hdisj, ih, Finset.sum_insert hσ]
  simpa [matchingUnion] using haux Finset.univ

/-- La unión también es matching del hipergrafo global de K4 reales, no sólo del pool. -/
theorem matchingUnion_isMatching_k4Supports {κ : Type*} [Fintype κ] [DecidableEq κ] {δ : ℚ}
    (R : EqualRegularity G δ) (own : Sym2 α → Option κ)
    (M : κ → Finset (Finset (Sym2 α)))
    (hM : ∀ σ, PaperIV.NibblePort.Hypergraph.IsMatching (ownedLayer R own σ) (M σ)) :
    PaperIV.NibblePort.Hypergraph.IsMatching (PaperIV.NibblePort.k4Supports G) (matchingUnion M) := by
  let hmatch := matchingUnion_isMatching R own M hM
  exact ⟨fun S hS => candidatePool_subset_k4Supports R (hmatch.subset hS), hmatch.disjoint⟩

/-- Traducción física final de una familia de matchings de capas. -/
theorem exists_packing_of_layer_matchings {κ : Type*} [Fintype κ] [DecidableEq κ] {δ : ℚ}
    (R : EqualRegularity G δ) (own : Sym2 α → Option κ)
    (M : κ → Finset (Finset (Sym2 α)))
    (hM : ∀ σ, PaperIV.NibblePort.Hypergraph.IsMatching (ownedLayer R own σ) (M σ)) :
    ∃ P : PaperIV.FarRounding.Packing G, P.gain = 5 * (matchingUnion M).card :=
  PaperIV.NibblePort.packing_of_matching (matchingUnion M)
    (matchingUnion_isMatching_k4Supports R own M hM)

end PaperIV.RC01CandidatePool
