import PaperIV.PatternCounting
import PaperIV.FarRounding
import PaperIV.NibblePort
import PaperIV.WeightedCodegree

/-!
# Candidatos físicos transversales para RC01

Los conteos de RC01 están expresados como funciones `φ` que escogen un vértice
en cada parte regular. Este módulo conserva su significado físico: una copia
transversal de `K₃` determina una pieza literal de `G`, y no se pierde
multiplicidad al olvidar el orden de sus tres vértices.

No construye todavía la familia global `Hσ`; ésa debe seleccionar triples y
cuádruplas de partes. Aquí se formaliza el adaptador local que esa construcción
debe usar.
-/

namespace PaperIV.RC01Candidates

open Finset
open PaperIV.PatternCounting PaperIV.RegularityFormat PaperIV.FarRounding

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-- Copias transversales: una elección por parte que realiza todas las aristas de `F`. -/
def transversal (G : SimpleGraph α) [DecidableRel G.Adj] (V : ι → Finset α)
    (F : Finset (ι × ι)) : Finset (ι → α) :=
  (Fintype.piFinset V).filter (fun φ => ∀ e ∈ F, G.Adj (φ e.1) (φ e.2))

theorem mem_transversal {V : ι → Finset α} {F : Finset (ι × ι)} {φ : ι → α} :
    φ ∈ transversal G V F ↔ (∀ i, φ i ∈ V i) ∧ ∀ e ∈ F, G.Adj (φ e.1) (φ e.2) := by
  rw [transversal, Finset.mem_filter, Fintype.mem_piFinset]

theorem patCount_eq_card_transversal (V : ι → Finset α) (F : Finset (ι × ι)) :
    patCount G V F = ((transversal G V F).card : ℚ) :=
  patCount_eq_card V F

/-- La pieza física subyacente a una copia transversal. -/
def piece (φ : ι → α) : Finset α := Finset.image φ Finset.univ

theorem mem_piece {φ : ι → α} {a : α} : a ∈ piece φ ↔ ∃ i, φ i = a := by
  simp [piece]

theorem apply_mem_piece (φ : ι → α) (i : ι) : φ i ∈ piece φ :=
  mem_piece.2 ⟨i, rfl⟩

section Disjointness

variable {V : ι → Finset α} (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
include hdisj

theorem injective_of_mem_piFinset {φ : ι → α} (hφ : ∀ i, φ i ∈ V i) : Function.Injective φ := by
  intro i j hij
  by_contra hne
  exact (Finset.disjoint_left.1 (hdisj i j hne)) (hφ i) (hij ▸ hφ j)

theorem card_piece {φ : ι → α} (hφ : ∀ i, φ i ∈ V i) :
    (piece φ).card = Fintype.card ι := by
  rw [piece, Finset.card_image_of_injective _ (injective_of_mem_piFinset hdisj hφ),
    Finset.card_univ]

theorem piece_injOn (F : Finset (ι × ι)) :
    Set.InjOn piece (transversal G V F : Set (ι → α)) := by
  intro φ hφ ψ hψ heq
  rw [Finset.mem_coe, mem_transversal] at hφ hψ
  funext i
  obtain ⟨j, hj⟩ : ∃ j, ψ j = φ i := by
    rw [← mem_piece, ← heq]
    exact apply_mem_piece φ i
  have hij : j = i := by
    by_contra hne
    exact (Finset.disjoint_left.1 (hdisj j i hne)) (hψ.1 j) (hj ▸ hφ.1 i)
  rw [← hj, hij]

end Disjointness

/-- Las copias transversales vistas como piezas candidatas. -/
def candidates (G : SimpleGraph α) [DecidableRel G.Adj] (V : ι → Finset α)
    (F : Finset (ι × ι)) : Finset (Finset α) :=
  (transversal G V F).image piece

theorem mem_candidates {V : ι → Finset α} {F : Finset (ι × ι)} {K : Finset α} :
    K ∈ candidates G V F ↔ ∃ φ ∈ transversal G V F, piece φ = K := by
  rw [candidates, Finset.mem_image]

theorem card_candidates {V : ι → Finset α} (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (F : Finset (ι × ι)) :
    (candidates G V F).card = (transversal G V F).card :=
  Finset.card_image_of_injOn (piece_injOn hdisj F)

theorem card_candidates_eq_patCount {V : ι → Finset α}
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) (F : Finset (ι × ι)) :
    ((candidates G V F).card : ℚ) = patCount G V F := by
  rw [card_candidates hdisj, patCount_eq_card_transversal]

/-- **Grado físico de una arista.**  Entre los candidatos de un patrón
transversal sobre `r` partes iguales, una arista fija pertenece a lo sumo a
`t^(r-2)` candidatos.  El filtro de adyacencia del patrón sólo puede disminuir
el número de asignaciones. -/
theorem card_candidates_containing_edge_le {V : ι → Finset α}
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (F : Finset (ι × ι)) (t : ℕ) (hV : ∀ i, (V i).card = t) (ht : 1 ≤ t)
    {a b : α} {i j : ι} (ha : a ∈ V i) (hb : b ∈ V j) (hij : i ≠ j) :
    ((candidates G V F).filter (fun K => a ∈ K ∧ b ∈ K)).card
      ≤ t ^ (Fintype.card ι - 2) := by
  classical
  let U := (transversal G V F).filter
    (fun φ => (∃ q, φ q = a) ∧ (∃ q, φ q = b))
  have hEq : (candidates G V F).filter (fun K => a ∈ K ∧ b ∈ K) =
      U.image piece := by
    ext K
    simp only [Finset.mem_filter, mem_candidates, Finset.mem_image, U]
    constructor
    · rintro ⟨⟨φ, hφ, rfl⟩, haK, hbK⟩
      exact ⟨φ, ⟨hφ, mem_piece.1 haK, mem_piece.1 hbK⟩, rfl⟩
    · rintro ⟨φ, ⟨hφ, haφ, hbφ⟩, rfl⟩
      exact ⟨⟨φ, hφ, rfl⟩, mem_piece.2 haφ, mem_piece.2 hbφ⟩
  rw [hEq]
  have hinj : Set.InjOn piece (U : Set (ι → α)) := by
    apply (piece_injOn (G := G) (V := V) hdisj F).mono
    intro φ hφ
    exact (Finset.mem_filter.1 hφ).1
  rw [Finset.card_image_of_injOn hinj]
  have hsub : U ⊆ (Fintype.piFinset V).filter
      (fun φ => (∃ q, φ q = a) ∧ (∃ q, φ q = b)) := by
    intro φ hφ
    change φ ∈ (transversal G V F).filter
      (fun ψ => (∃ q, ψ q = a) ∧ (∃ q, ψ q = b)) at hφ
    rw [Finset.mem_filter] at hφ
    exact Finset.mem_filter.2
      ⟨Fintype.mem_piFinset.2 (mem_transversal.1 hφ.1).1, hφ.2⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  exact PaperIV.WeightedCodegree.card_one_resource_le V
    (fun i _ j _ hij => hdisj i j hij) t hV ht ha hb hij

/-- Coordinate-free form of `card_candidates_containing_edge_le`: every
physical resource belongs to at most `t^(r-2)` candidates.  If the resource
does not occur the statement is vacuous; otherwise one candidate determines
the two unique regularity parts of its endpoints. -/
theorem card_candidates_containing_resource_le {V : ι → Finset α}
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (F : Finset (ι × ι)) (t : ℕ) (hV : ∀ i, (V i).card = t) (ht : 1 ≤ t)
    (e : Sym2 α) :
    ((candidates G V F).filter (fun K => e ∈ pairs K)).card
      ≤ t ^ (Fintype.card ι - 2) := by
  classical
  induction e using Sym2.ind with
  | _ a b =>
    by_cases hab : a = b
    · subst b
      have hempty : (candidates G V F).filter (fun K => s(a, a) ∈ pairs K) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 ?_
        intro K hK
        rw [mk_mem_pairs]
        tauto
      rw [hempty]
      simp
    · rcases ((candidates G V F).filter
          (fun K => s(a, b) ∈ pairs K)).eq_empty_or_nonempty with hemp | ⟨K₀, hK₀⟩
      · rw [hemp]
        simp
      · rw [Finset.mem_filter, mk_mem_pairs] at hK₀
        obtain ⟨φ, hφ, hpiece⟩ := mem_candidates.1 hK₀.1
        obtain ⟨i, hi⟩ := mem_piece.1 (hpiece ▸ hK₀.2.1)
        obtain ⟨j, hj⟩ := mem_piece.1 (hpiece ▸ hK₀.2.2.1)
        have hij : i ≠ j := by
          intro h
          apply hab
          rw [← hi, ← hj, h]
        have ha : a ∈ V i := by
          rw [← hi]
          exact (mem_transversal.1 hφ).1 i
        have hb : b ∈ V j := by
          rw [← hj]
          exact (mem_transversal.1 hφ).1 j
        refine le_trans (Finset.card_le_card ?_)
          (card_candidates_containing_edge_le (G := G) hdisj F t hV ht ha hb hij)
        intro K hK
        rw [Finset.mem_filter, mk_mem_pairs] at hK
        exact Finset.mem_filter.2 ⟨hK.1, hK.2.1, hK.2.2.1⟩

/-! ## Triángulos: los candidatos son piezas reales -/

theorem adj_of_transversal_K3 {V : Fin 3 → Finset α} {φ : Fin 3 → α}
    (hφ : φ ∈ transversal G V patK3) {i j : Fin 3} (hij : i ≠ j) : G.Adj (φ i) (φ j) := by
  have h := (mem_transversal.1 hφ).2
  have h01 : G.Adj (φ 0) (φ 1) := h (0, 1) (by decide)
  have h02 : G.Adj (φ 0) (φ 2) := h (0, 2) (by decide)
  have h12 : G.Adj (φ 1) (φ 2) := h (1, 2) (by decide)
  fin_cases i <;> fin_cases j <;>
    first | exact absurd rfl hij | assumption | exact h01.symm | exact h02.symm | exact h12.symm

theorem candidates_K3_isItem {V : Fin 3 → Finset α}
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) {K : Finset α}
    (hK : K ∈ candidates G V patK3) : IsItem G K := by
  obtain ⟨φ, hφ, rfl⟩ := mem_candidates.1 hK
  have hmem := (mem_transversal.1 hφ).1
  refine ⟨?_, Or.inl ?_⟩
  · intro a ha b hb hab
    obtain ⟨i, rfl⟩ := mem_piece.1 ha
    obtain ⟨j, rfl⟩ := mem_piece.1 hb
    exact adj_of_transversal_K3 hφ (fun h => hab (by rw [h]))
  · rw [card_piece hdisj hmem]
    decide

/-! ## Cuádruplas: el formato que consume el nibble -/

theorem adj_of_transversal_K4 {V : Fin 4 → Finset α} {φ : Fin 4 → α}
    (hφ : φ ∈ transversal G V patK4) {i j : Fin 4} (hij : i ≠ j) : G.Adj (φ i) (φ j) := by
  have h := (mem_transversal.1 hφ).2
  have h01 : G.Adj (φ 0) (φ 1) := h (0, 1) (by decide)
  have h02 : G.Adj (φ 0) (φ 2) := h (0, 2) (by decide)
  have h03 : G.Adj (φ 0) (φ 3) := h (0, 3) (by decide)
  have h12 : G.Adj (φ 1) (φ 2) := h (1, 2) (by decide)
  have h13 : G.Adj (φ 1) (φ 3) := h (1, 3) (by decide)
  have h23 : G.Adj (φ 2) (φ 3) := h (2, 3) (by decide)
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | exact h01
    | exact h02
    | exact h03
    | exact h01.symm
    | exact h12
    | exact h13
    | exact h02.symm
    | exact h12.symm
    | exact h23
    | exact h03.symm
    | exact h13.symm
    | exact h23.symm

theorem candidates_K4_isItem {V : Fin 4 → Finset α}
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) {K : Finset α}
    (hK : K ∈ candidates G V patK4) : IsItem G K := by
  obtain ⟨φ, hφ, rfl⟩ := mem_candidates.1 hK
  have hmem := (mem_transversal.1 hφ).1
  refine ⟨?_, Or.inr ?_⟩
  · intro a ha b hb hab
    obtain ⟨i, rfl⟩ := mem_piece.1 ha
    obtain ⟨j, rfl⟩ := mem_piece.1 hb
    exact adj_of_transversal_K4 hφ (fun h => hab (by rw [h]))
  · rw [card_piece hdisj hmem]
    decide

/-- Los recursos de los candidatos `K₄`: sus seis aristas físicas. -/
def k4CandidateSupports (G : SimpleGraph α) [DecidableRel G.Adj] (V : Fin 4 → Finset α) :
    Finset (Finset (Sym2 α)) :=
  (candidates G V patK4).image pairs

/-- El constructor transversal no inventa hiperaristas: cada soporte candidato pertenece al
hipergrafo literal de los `K₄` de `G` usado por el nibble. -/
theorem k4CandidateSupports_subset_k4Supports {V : Fin 4 → Finset α}
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) :
    k4CandidateSupports G V ⊆ PaperIV.NibblePort.k4Supports G := by
  intro S hS
  obtain ⟨K, hK, rfl⟩ := Finset.mem_image.1 hS
  refine PaperIV.NibblePort.mem_k4Supports.2 ⟨K, candidates_K4_isItem hdisj hK, ?_, rfl⟩
  obtain ⟨φ, hφ, rfl⟩ := mem_candidates.1 hK
  rw [card_piece hdisj (mem_transversal.1 hφ).1]
  decide

/-- Masa literal de las K4 candidatas de una cuádrupla regular buena. Ésta es la versión
física del conteo de patrón: la regularidad da una cota para copias ordenadas y la inyectividad
entre partes disjuntas la convierte en una cota para hiperaristas distintas. -/
theorem card_candidates_K4_ge {δ : ℚ} (hδ : 0 ≤ δ) (R : EqualRegularity G δ)
    (V : Fin 4 → Finset α) (hV : ∀ i, V i ∈ R.parts)
    (hVne : ∀ e ∈ patK4, V e.1 ≠ V e.2)
    (hgood : ∀ e ∈ patK4, (V e.1, V e.2) ∉ R.bad) :
    ((∏ e ∈ patK4, G.edgeDensity (V e.1) (V e.2)) - 6 * δ) * (R.size : ℚ) ^ 4
      ≤ ((candidates G V patK4).card : ℚ) := by
  classical
  have hdisj : ∀ i j : Fin 4, i ≠ j → Disjoint (V i) (V j) := by
    intro i j hij
    refine R.pairwise_disjoint _ (hV i) _ (hV j) ?_
    have hkey : ∀ a b : Fin 4, a ≠ b → ((a, b) ∈ patK4 ∨ (b, a) ∈ patK4) := by decide
    rcases hkey i j hij with h | h
    · exact hVne (i, j) h
    · exact fun hEq => hVne (j, i) h hEq.symm
  have hprod : ∏ i, ((V i).card : ℚ) = (R.size : ℚ) ^ 4 := by
    have hcard : ∀ i : Fin 4, ((V i).card : ℚ) = (R.size : ℚ) := by
      intro i
      rw [R.card_part _ (hV i)]
    rw [Finset.prod_congr rfl (fun i _ => hcard i)]
    simp [Finset.prod_const, pow_succ]
  have hcount := counting_of_regular hδ R V patK4 hV patK4_ne patK4_sym hVne hgood
  rw [card_patK4, hprod] at hcount
  have habs := abs_le.1 hcount
  rw [card_candidates_eq_patCount hdisj]
  have hlow := habs.1
  push_cast at hlow ⊢
  linarith [hlow]

/-! ## Colisiones entre orientaciones de una misma ranura -/

/-- El conjunto de partes usado por una cuádrupla ordenada. -/
def partImage (V : Fin 4 → Finset α) : Finset (Finset α) := Finset.univ.image V

/-- Si dos copias transversales producen la misma pieza física, toda parte usada por la
primera coincide con alguna parte usada por la segunda. La disjunción de las partes del
certificado es la razón por la que no puede ocurrir una colisión entre ranuras distintas. -/
theorem source_part_exists_of_piece_eq {δ : ℚ} (R : EqualRegularity G δ)
    {V W : Fin 4 → Finset α} (hV : ∀ i, V i ∈ R.parts) (hW : ∀ i, W i ∈ R.parts)
    {φ : Fin 4 → α} {ψ : Fin 4 → α}
    (hφ : φ ∈ transversal G V patK4) (hψ : ψ ∈ transversal G W patK4)
    (heq : piece φ = piece ψ) : ∀ i, ∃ j, V i = W j := by
  intro i
  have hφmem := (mem_transversal.1 hφ).1
  have hψmem := (mem_transversal.1 hψ).1
  have hpin : φ i ∈ piece ψ := by
    rw [← heq]
    exact apply_mem_piece φ i
  obtain ⟨j, hj⟩ := mem_piece.1 hpin
  refine ⟨j, ?_⟩
  by_contra hne
  exact (Finset.disjoint_left.1 (R.pairwise_disjoint _ (hV i) _ (hW j) hne))
    (hφmem i) (hj ▸ hψmem j)

/-- Una pieza K4 no puede aparecer en dos conjuntos de cuatro partes distintos; las únicas
duplicaciones posibles del conteo orientado son permutaciones de la misma ranura. -/
theorem partImage_eq_of_piece_eq {δ : ℚ} (R : EqualRegularity G δ)
    {V W : Fin 4 → Finset α} (hV : ∀ i, V i ∈ R.parts) (hW : ∀ i, W i ∈ R.parts)
    {φ : Fin 4 → α} {ψ : Fin 4 → α}
    (hφ : φ ∈ transversal G V patK4) (hψ : ψ ∈ transversal G W patK4)
    (heq : piece φ = piece ψ) : partImage V = partImage W := by
  ext A
  change A ∈ Finset.univ.image V ↔ A ∈ Finset.univ.image W
  constructor
  · intro hA
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hA
    obtain ⟨j, hj⟩ := source_part_exists_of_piece_eq R hV hW hφ hψ heq i
    exact Finset.mem_image.2 ⟨j, Finset.mem_univ j, hj.symm⟩
  · intro hA
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hA
    obtain ⟨i, hi⟩ := source_part_exists_of_piece_eq R hW hV hψ hφ heq.symm j
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, hi.symm⟩

/-- Los candidatos de dos ranuras de partes distintas son disjuntos como piezas físicas. -/
theorem candidates_disjoint_of_partImage_ne {δ : ℚ} (R : EqualRegularity G δ)
    {V W : Fin 4 → Finset α} (hV : ∀ i, V i ∈ R.parts) (hW : ∀ i, W i ∈ R.parts)
    (hVW : partImage V ≠ partImage W) :
    Disjoint (candidates G V patK4) (candidates G W patK4) := by
  rw [Finset.disjoint_left]
  intro K hK hL
  obtain ⟨φ, hφ, rfl⟩ := mem_candidates.1 hK
  obtain ⟨ψ, hψ, hψeq⟩ := mem_candidates.1 hL
  exact hVW (partImage_eq_of_piece_eq R hV hW hφ hψ hψeq.symm)

end PaperIV.RC01Candidates
