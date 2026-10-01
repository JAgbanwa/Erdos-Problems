import PaperIV.RC01CanonicalSupports
import PaperIV.TriangleNibblePort

/-!
# El pool canónico de **triángulos**

Gemelo de `PaperIV.RC01CandidatePool` / `RC01CanonicalSlots` / `RC01CanonicalSupports` para
`r = 3`.  Toda la cadena construida hasta ahora es `K₄`-only; para un grafo pobre en `K₄` pero
rico en `K₃` hace falta el mismo objeto con tres aristas por candidato en vez de seis.

## Contenido

* `K3TupleGood`, `goodK3Tuples` — las ternas ordenadas de partes distintas cuyas tres parejas
  no son excepcionales;
* `partImage3`, `goodK3Slots`, `canonicalTripleOf` — una orientación representante por conjunto
  de tres partes;
* `k3CandidateSupports` — los soportes de **tres** aristas de los triángulos transversales;
* `canonicalSupportPoolK3` — el pool canónico, **`3`-uniforme**
  (`canonicalSupportPoolK3_uniform`) y contenido en el hipergrafo físico de los `K₃` de `G`.

Los lemas de disyunción entre ranuras se demuestran aquí en forma **genérica en `ι`**: las
pruebas de `RC01Candidates` para `K₄` no usan nada de `patK4`, sólo que las partes de una
ranura son disjuntas dos a dos.
-/

namespace PaperIV.RC01K3Pool

open Finset
open PaperIV.PatternCounting PaperIV.RegularityFormat PaperIV.RC01Candidates
open PaperIV.FarRounding

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-! ## 0. Las piezas genéricas en `ι` -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- El conjunto de partes usado por una tupla ordenada. -/
def partImageOf (V : ι → Finset α) : Finset (Finset α) := Finset.univ.image V

omit [Fintype α] [DecidableEq ι] in
theorem mem_partImageOf {V : ι → Finset α} {A : Finset α} :
    A ∈ partImageOf V ↔ ∃ i, V i = A := by
  rw [partImageOf, Finset.mem_image]
  constructor
  · rintro ⟨i, -, h⟩
    exact ⟨i, h⟩
  · rintro ⟨i, h⟩
    exact ⟨i, Finset.mem_univ i, h⟩

/-- Si dos copias transversales producen la misma pieza física, toda parte usada por la primera
coincide con alguna parte usada por la segunda. -/
theorem source_part_exists_of_piece_eq' {δ : ℚ} (R : EqualRegularity G δ)
    {V W : ι → Finset α} {F : Finset (ι × ι)}
    (hV : ∀ i, V i ∈ R.parts) (hW : ∀ i, W i ∈ R.parts)
    {φ ψ : ι → α} (hφ : φ ∈ transversal G V F) (hψ : ψ ∈ transversal G W F)
    (heq : piece φ = piece ψ) : ∀ i, ∃ j, V i = W j := by
  intro i
  have hφmem := (mem_transversal.1 hφ).1
  have hψmem := (mem_transversal.1 hψ).1
  have hpin : φ i ∈ piece ψ := by
    rw [← heq]; exact apply_mem_piece φ i
  obtain ⟨j, hj⟩ := mem_piece.1 hpin
  refine ⟨j, ?_⟩
  by_contra hne
  exact (Finset.disjoint_left.1 (R.pairwise_disjoint _ (hV i) _ (hW j) hne))
    (hφmem i) (hj ▸ hψmem j)

theorem partImageOf_eq_of_piece_eq {δ : ℚ} (R : EqualRegularity G δ)
    {V W : ι → Finset α} {F : Finset (ι × ι)}
    (hV : ∀ i, V i ∈ R.parts) (hW : ∀ i, W i ∈ R.parts)
    {φ ψ : ι → α} (hφ : φ ∈ transversal G V F) (hψ : ψ ∈ transversal G W F)
    (heq : piece φ = piece ψ) : partImageOf V = partImageOf W := by
  ext A
  constructor
  · intro hA
    obtain ⟨i, rfl⟩ := mem_partImageOf.1 hA
    obtain ⟨j, hj⟩ := source_part_exists_of_piece_eq' R hV hW hφ hψ heq i
    exact mem_partImageOf.2 ⟨j, hj.symm⟩
  · intro hA
    obtain ⟨j, rfl⟩ := mem_partImageOf.1 hA
    obtain ⟨i, hi⟩ := source_part_exists_of_piece_eq' R hW hV hψ hφ heq.symm j
    exact mem_partImageOf.2 ⟨i, hi.symm⟩

theorem candidates_disjoint_of_partImageOf_ne {δ : ℚ} (R : EqualRegularity G δ)
    {V W : ι → Finset α} {F : Finset (ι × ι)}
    (hV : ∀ i, V i ∈ R.parts) (hW : ∀ i, W i ∈ R.parts)
    (hVW : partImageOf V ≠ partImageOf W) :
    Disjoint (candidates G V F) (candidates G W F) := by
  rw [Finset.disjoint_left]
  intro K hK hL
  obtain ⟨φ, hφ, rfl⟩ := mem_candidates.1 hK
  obtain ⟨ψ, hψ, hψeq⟩ := mem_candidates.1 hL
  exact hVW (partImageOf_eq_of_piece_eq R hV hW hφ hψ hψeq.symm)

end Generic

/-! ## 1. Ternas buenas -/

/-- Terna de partes apta para una copia transversal de `K₃`. -/
def K3TupleGood {δ : ℚ} (R : EqualRegularity G δ) (V : Fin 3 → Finset α) : Prop :=
  (∀ i j : Fin 3, i ≠ j → V i ≠ V j) ∧ (∀ e ∈ patK3, (V e.1, V e.2) ∉ R.bad)

instance decidableK3TupleGood {δ : ℚ} (R : EqualRegularity G δ) :
    DecidablePred (K3TupleGood R) := by
  intro V
  unfold K3TupleGood
  infer_instance

/-- Todas las ternas de partes buenas del certificado. -/
noncomputable def goodK3Tuples {δ : ℚ} (R : EqualRegularity G δ) :
    Finset (Fin 3 → Finset α) :=
  (Fintype.piFinset (fun _ : Fin 3 => R.parts)).filter (K3TupleGood R)

theorem mem_goodK3Tuples {δ : ℚ} {R : EqualRegularity G δ} {V : Fin 3 → Finset α} :
    V ∈ goodK3Tuples R ↔ (∀ i, V i ∈ R.parts) ∧ K3TupleGood R V := by
  classical
  rw [goodK3Tuples, Finset.mem_filter, Fintype.mem_piFinset]

theorem disjoint_of_mem_goodK3Tuples {δ : ℚ} {R : EqualRegularity G δ} {V : Fin 3 → Finset α}
    (hV : V ∈ goodK3Tuples R) {i j : Fin 3} (hij : i ≠ j) : Disjoint (V i) (V j) := by
  obtain ⟨hparts, hne, -⟩ := mem_goodK3Tuples.1 hV
  exact R.pairwise_disjoint _ (hparts i) _ (hparts j) (hne i j hij)

/-! ## 2. Los soportes de tres aristas -/

/-- Los recursos de los candidatos `K₃`: sus tres aristas físicas. -/
def k3CandidateSupports (G : SimpleGraph α) [DecidableRel G.Adj] (V : Fin 3 → Finset α) :
    Finset (Finset (Sym2 α)) :=
  (candidates G V patK3).image pairs

theorem k3CandidateSupports_subset_k3Supports {V : Fin 3 → Finset α}
    (hdisj : ∀ i j : Fin 3, i ≠ j → Disjoint (V i) (V j)) :
    k3CandidateSupports G V ⊆ PaperIV.NibblePort.k3Supports G := by
  intro S hS
  obtain ⟨K, hK, rfl⟩ := Finset.mem_image.1 hS
  refine PaperIV.NibblePort.mem_k3Supports.2 ⟨K, candidates_K3_isItem hdisj hK, ?_, rfl⟩
  obtain ⟨φ, hφ, rfl⟩ := mem_candidates.1 hK
  rw [card_piece hdisj (mem_transversal.1 hφ).1]
  decide

/-! ## 3. Ranuras canónicas -/

/-- Ranuras no orientadas: los conjuntos de tres partes de las ternas buenas. -/
noncomputable def goodK3Slots {δ : ℚ} (R : EqualRegularity G δ) : Finset (Finset (Finset α)) :=
  (goodK3Tuples R).image partImageOf

/-- Una orientación representante por ranura. -/
noncomputable def canonicalTripleOf {δ : ℚ} (R : EqualRegularity G δ)
    (S : Finset (Finset α)) : Fin 3 → Finset α :=
  if h : ∃ V, V ∈ goodK3Tuples R ∧ partImageOf V = S then Classical.choose h else fun _ => ∅

theorem canonicalTripleOf_spec {δ : ℚ} (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK3Slots R) :
    canonicalTripleOf R S ∈ goodK3Tuples R ∧ partImageOf (canonicalTripleOf R S) = S := by
  classical
  rw [goodK3Slots] at hS
  obtain ⟨V, hV, hVS⟩ := Finset.mem_image.1 hS
  have hex : ∃ U, U ∈ goodK3Tuples R ∧ partImageOf U = S := ⟨V, hV, hVS⟩
  rw [canonicalTripleOf, dif_pos hex]
  exact Classical.choose_spec hex

theorem canonicalTripleOf_mem_parts {δ : ℚ} (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK3Slots R) (i : Fin 3) : canonicalTripleOf R S i ∈ R.parts :=
  (mem_goodK3Tuples.1 (canonicalTripleOf_spec R hS).1).1 i

theorem canonicalTripleOf_card {δ : ℚ} (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK3Slots R) (i : Fin 3) : (canonicalTripleOf R S i).card = R.size :=
  R.card_part _ (canonicalTripleOf_mem_parts R hS i)

theorem canonicalTripleOf_ne {δ : ℚ} (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK3Slots R) {i j : Fin 3} (hij : i ≠ j) :
    canonicalTripleOf R S i ≠ canonicalTripleOf R S j :=
  (mem_goodK3Tuples.1 (canonicalTripleOf_spec R hS).1).2.1 i j hij

theorem canonicalTripleOf_disjoint {δ : ℚ} (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK3Slots R) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (canonicalTripleOf R S i) (canonicalTripleOf R S j) :=
  disjoint_of_mem_goodK3Tuples (canonicalTripleOf_spec R hS).1 hij

/-! ## 4. El pool canónico de triángulos -/

/-- Los soportes de aristas de las copias de `K₃` de las ranuras canónicas. -/
noncomputable def canonicalSupportPoolK3 {δ : ℚ} (R : EqualRegularity G δ) :
    Finset (Finset (Sym2 α)) :=
  (goodK3Slots R).biUnion (fun S => k3CandidateSupports G (canonicalTripleOf R S))

theorem mem_canonicalSupportPoolK3 {δ : ℚ} {R : EqualRegularity G δ} {E : Finset (Sym2 α)} :
    E ∈ canonicalSupportPoolK3 R ↔
      ∃ S ∈ goodK3Slots R, E ∈ k3CandidateSupports G (canonicalTripleOf R S) := by
  rw [canonicalSupportPoolK3, Finset.mem_biUnion]

theorem k3CandidateSupports_subset_pool {δ : ℚ} (R : EqualRegularity G δ)
    {S : Finset (Finset α)} (hS : S ∈ goodK3Slots R) :
    k3CandidateSupports G (canonicalTripleOf R S) ⊆ canonicalSupportPoolK3 R :=
  fun _ hE => mem_canonicalSupportPoolK3.2 ⟨S, hS, hE⟩

theorem canonicalSupportPoolK3_subset_k3Supports {δ : ℚ} (R : EqualRegularity G δ) :
    canonicalSupportPoolK3 R ⊆ PaperIV.NibblePort.k3Supports G := by
  intro E hE
  obtain ⟨S, hS, hES⟩ := mem_canonicalSupportPoolK3.1 hE
  exact k3CandidateSupports_subset_k3Supports
    (fun i j hij => canonicalTripleOf_disjoint R hS hij) hES

/-- **El pool de triángulos es `3`-uniforme.** -/
theorem canonicalSupportPoolK3_uniform {δ : ℚ} (R : EqualRegularity G δ) :
    PaperIV.NibblePort.Hypergraph.IsUniform (canonicalSupportPoolK3 R) 3 :=
  fun E hE => PaperIV.NibblePort.k3Supports_uniform E
    (canonicalSupportPoolK3_subset_k3Supports R hE)

/-- **Toda arista de una hiperarista del pool es arista de `G`.** -/
theorem mem_edgeFinset_of_mem_poolK3 {δ : ℚ} {R : EqualRegularity G δ} {E : Finset (Sym2 α)}
    (hE : E ∈ canonicalSupportPoolK3 R) {e : Sym2 α} (he : e ∈ E) : e ∈ G.edgeFinset := by
  obtain ⟨K, hK, -, rfl⟩ :=
    PaperIV.NibblePort.mem_k3Supports.1 (canonicalSupportPoolK3_subset_k3Supports R hE)
  exact PaperIV.FarRounding.pairs_subset_edgeFinset hK he

/-- Las familias de candidatos de dos ranuras canónicas distintas son disjuntas. -/
theorem canonical_slot_candidates_disjointK3 {δ : ℚ} (R : EqualRegularity G δ)
    {S T : Finset (Finset α)} (hS : S ∈ goodK3Slots R) (hT : T ∈ goodK3Slots R) (hST : S ≠ T) :
    Disjoint (candidates G (canonicalTripleOf R S) patK3)
      (candidates G (canonicalTripleOf R T) patK3) := by
  refine candidates_disjoint_of_partImageOf_ne R
    (canonicalTripleOf_mem_parts R hS) (canonicalTripleOf_mem_parts R hT) ?_
  rw [(canonicalTripleOf_spec R hS).2, (canonicalTripleOf_spec R hT).2]
  exact hST

end PaperIV.RC01K3Pool
