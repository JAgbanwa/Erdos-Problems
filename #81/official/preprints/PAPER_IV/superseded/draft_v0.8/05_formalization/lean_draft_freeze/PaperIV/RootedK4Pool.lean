import PaperIV.RootedK4Counting

/-!
# De la cota local a `hdeg` sobre el pool canónico

`RootedK4Counting` da la cota inferior del grado para las aristas entre las partes `V 0` y
`V 1` de **una** cuádrupla.  Aquí se monta sobre el pool canónico entero:

* `canonicalTuple_*` — la cuádrupla canónica de una ranura buena cumple las hipótesis del
  conteo local (tamaños iguales, partes disjuntas, discrepancia en las seis parejas **en los
  dos órdenes**, gracias a `discrepAt_symm`);
* `poolBadEdges` — la unión de las raíces malas sobre todas las ranuras y las `24`
  orientaciones;
* `card_poolBadEdges_le` — su cardinal;
* `exists_canonicalPool_deg_lower_bound` — **`hdeg`**, en la forma que consume
  `TrimScheduleEdge.canonicalOwnerLowerBoundOnEdges_of_schedule`.

La única entrada que queda es el **recubrimiento**: que casi toda arista de `G` sea arista raíz
de alguna ranura buena con las cinco densidades restantes acotadas por debajo.  Es una
propiedad de `(G, R)`, no una hipótesis sobre el resultado; se demuestra en
`PaperIV.ReducedSlotCover` a partir de la densidad de `G`.
-/

namespace PaperIV.RootedK4Degree

open Finset
open PaperIV.OneStepEstimate
open PaperIV.PatternCounting PaperIV.RegularityFormat PaperIV.RC01Candidates
open PaperIV.RC01CandidatePool PaperIV.RC01CanonicalSlots PaperIV.RC01CanonicalSupports
open PaperIV.FarRounding
open PaperIV.NibbleHypotheses (deg)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]
variable {δ : ℚ}

/-! ## 1. La cuádrupla canónica de una ranura buena -/

theorem canonicalTuple_mem_parts (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK4Slots R) (i : Fin 4) : canonicalTuple R S i ∈ R.parts :=
  (mem_goodK4Tuples.1 (canonicalTuple_spec R hS).1).1 i

theorem canonicalTuple_card (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK4Slots R) (i : Fin 4) : (canonicalTuple R S i).card = R.size :=
  R.card_part _ (canonicalTuple_mem_parts R hS i)

theorem canonicalTuple_ne (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK4Slots R) {i j : Fin 4} (hij : i ≠ j) :
    canonicalTuple R S i ≠ canonicalTuple R S j :=
  (mem_goodK4Tuples.1 (canonicalTuple_spec R hS).1).2.1 i j hij

theorem canonicalTuple_disjoint (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK4Slots R) {i j : Fin 4} (hij : i ≠ j) :
    Disjoint (canonicalTuple R S i) (canonicalTuple R S j) :=
  R.pairwise_disjoint _ (canonicalTuple_mem_parts R hS i) _ (canonicalTuple_mem_parts R hS j)
    (canonicalTuple_ne R hS hij)

/-- Las seis parejas de una cuádrupla buena cumplen (3.2) **en los dos órdenes**. -/
theorem canonicalTuple_discrep (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK4Slots R) {i j : Fin 4} (hij : i ≠ j) :
    DiscrepAt G δ (G.edgeDensity (canonicalTuple R S i) (canonicalTuple R S j))
      (canonicalTuple R S i) (canonicalTuple R S j) := by
  have hgood := (mem_goodK4Tuples.1 (canonicalTuple_spec R hS).1).2.2
  have hor : ∀ a b : Fin 4, a ≠ b → ((a, b) ∈ patK4 ∨ (b, a) ∈ patK4) := by decide
  rcases hor i j hij with h | h
  · exact R.discrep _ (canonicalTuple_mem_parts R hS i) _ (canonicalTuple_mem_parts R hS j)
      (canonicalTuple_ne R hS hij) (hgood (i, j) h)
  · have hsymm := R.discrep _ (canonicalTuple_mem_parts R hS j) _
      (canonicalTuple_mem_parts R hS i) (canonicalTuple_ne R hS (Ne.symm hij)) (hgood (j, i) h)
    have := discrepAt_symm hsymm
    rwa [G.edgeDensity_comm (canonicalTuple R S j) (canonicalTuple R S i)] at this

theorem k4CandidateSupports_subset_pool (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK4Slots R) :
    k4CandidateSupports G (canonicalTuple R S) ⊆ canonicalSupportPool R := by
  intro E hE
  exact mem_canonicalSupportPool.2 ⟨S, hS, hE⟩

/-! ## 2. Las mismas hipótesis tras permutar los índices -/

theorem canonicalTuple_perm_card (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK4Slots R) (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    ((canonicalTuple R S ∘ σ) i).card = R.size :=
  canonicalTuple_card R hS (σ i)

theorem canonicalTuple_perm_disjoint (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK4Slots R) (σ : Equiv.Perm (Fin 4)) {i j : Fin 4} (hij : i ≠ j) :
    Disjoint ((canonicalTuple R S ∘ σ) i) ((canonicalTuple R S ∘ σ) j) :=
  canonicalTuple_disjoint R hS (fun h => hij (σ.injective h))

theorem canonicalTuple_perm_discrep (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK4Slots R) (σ : Equiv.Perm (Fin 4)) {i j : Fin 4} (hij : i ≠ j) :
    DiscrepAt G δ
      (G.edgeDensity ((canonicalTuple R S ∘ σ) i) ((canonicalTuple R S ∘ σ) j))
      ((canonicalTuple R S ∘ σ) i) ((canonicalTuple R S ∘ σ) j) :=
  canonicalTuple_discrep R hS (fun h => hij (σ.injective h))

/-- Permutar los índices no cambia los soportes: siguen siendo los del pool canónico. -/
theorem k4CandidateSupports_perm_subset_pool (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK4Slots R) (σ : Equiv.Perm (Fin 4)) :
    k4CandidateSupports G (canonicalTuple R S ∘ σ) ⊆ canonicalSupportPool R := by
  have heq : k4CandidateSupports G (canonicalTuple R S ∘ σ)
      = k4CandidateSupports G (canonicalTuple R S) := by
    rw [k4CandidateSupports, k4CandidateSupports, candidates_comp_perm]
  rw [heq]
  exact k4CandidateSupports_subset_pool R hS

/-! ## 3. Una ranura por **pareja de partes**, no por ranura

Es el punto donde se decide la escala del excepcional.  Si se tomara la unión de las raíces
malas sobre **todas** las ranuras buenas, el excepcional crecería como `|ranuras|·t² ≍ k⁴t²`,
es decir `k²n²`, y como `k` lo fija Szemerédi **después** de `δ` la condición sobre `δ` se
volvería circular.

Cada arista sólo necesita **una** ranura.  Se elige por tanto una ranura (y una orientación)
**por pareja ordenada de partes**: el excepcional queda acotado por `k²·t² ≍ n²` y la
condición sobre `δ` no depende de `n`. -/

/-- Una ranura buena con una orientación que pone la pareja `q` en la raíz y tiene las cinco
densidades restantes por encima de `d₀⁵`. -/
def SlotFor (R : EqualRegularity G δ) (d₀ : ℚ) (q : Finset α × Finset α)
    (Sσ : Finset (Finset α) × Equiv.Perm (Fin 4)) : Prop :=
  Sσ.1 ∈ goodK4Slots R ∧
    (canonicalTuple R Sσ.1 ∘ Sσ.2) 0 = q.1 ∧ (canonicalTuple R Sσ.1 ∘ Sσ.2) 1 = q.2 ∧
    d₀ ^ 5 ≤ rootProd G (canonicalTuple R Sσ.1 ∘ Sσ.2)

/-- Las aristas físicas entre las dos partes de `q`. -/
def pairRootEdges (G : SimpleGraph α) [DecidableRel G.Adj] (q : Finset α × Finset α) :
    Finset (Sym2 α) :=
  (G.interedges q.1 q.2).image (fun p => s(p.1, p.2))

theorem rootEdges_of_slotFor {R : EqualRegularity G δ} {d₀ : ℚ} {q : Finset α × Finset α}
    {Sσ : Finset (Finset α) × Equiv.Perm (Fin 4)} (h : SlotFor R d₀ q Sσ) :
    rootEdges G (canonicalTuple R Sσ.1 ∘ Sσ.2) = pairRootEdges G q := by
  rw [rootEdges, pairRootEdges, h.2.1, h.2.2.1]

open scoped Classical in
/-- Las raíces malas de la ranura elegida para la pareja `q`. -/
noncomputable def pairBadEdges (R : EqualRegularity G δ) (u d₀ : ℚ)
    (q : Finset α × Finset α) : Finset (Sym2 α) :=
  if h : ∃ Sσ : Finset (Finset α) × Equiv.Perm (Fin 4), SlotFor R d₀ q Sσ then
    badRootEdges G (canonicalTuple R h.choose.1 ∘ h.choose.2)
      ((1 - u) * (d₀ ^ 5 * (R.size : ℚ) ^ 2))
  else ∅

/-- **El excepcional de conteo**: las raíces malas, una ranura por pareja de partes. -/
noncomputable def poolBadEdges (R : EqualRegularity G δ) (u d₀ : ℚ) : Finset (Sym2 α) :=
  (R.parts ×ˢ R.parts).biUnion (pairBadEdges R u d₀)

theorem card_pairBadEdges_le (R : EqualRegularity G δ) {u d₀ : ℚ} (hδ : 0 ≤ δ)
    (hu : 0 < u) (hu1 : u ≤ 1) (hd₀ : 0 < d₀) (q : Finset α × Finset α) :
    ((pairBadEdges R u d₀ q).card : ℚ)
      ≤ 23 * δ * (R.size : ℚ) ^ 2 / (u * d₀ ^ 5) ^ 2 := by
  classical
  have hK0 : (0 : ℚ) ≤ 23 * δ * (R.size : ℚ) ^ 2 / (u * d₀ ^ 5) ^ 2 := by
    have hpos : (0 : ℚ) < (u * d₀ ^ 5) ^ 2 := by positivity
    positivity
  rw [pairBadEdges]
  by_cases h : ∃ Sσ : Finset (Finset α) × Equiv.Perm (Fin 4), SlotFor R d₀ q Sσ
  · rw [dif_pos h]
    obtain ⟨hS, -, -, hrp⟩ := h.choose_spec
    have hp5 : (0 : ℚ) < d₀ ^ 5 := by positivity
    exact card_badRootEdges_le hδ hu hu1 hp5
      (canonicalTuple_perm_card R hS h.choose.2)
      (fun i j hij => canonicalTuple_perm_disjoint R hS h.choose.2 hij)
      (fun i j hij => canonicalTuple_perm_discrep R hS h.choose.2 hij) R.size_pos hrp le_rfl
  · rw [dif_neg h]
    simpa using hK0

theorem card_poolBadEdges_le (R : EqualRegularity G δ) {u d₀ : ℚ} (hδ : 0 ≤ δ)
    (hu : 0 < u) (hu1 : u ≤ 1) (hd₀ : 0 < d₀) :
    ((poolBadEdges R u d₀).card : ℚ)
      ≤ (R.parts.card : ℚ) ^ 2 * (23 * δ * (R.size : ℚ) ^ 2 / (u * d₀ ^ 5) ^ 2) := by
  classical
  have hcb : ((poolBadEdges R u d₀).card : ℚ)
      ≤ ∑ q ∈ R.parts ×ˢ R.parts, ((pairBadEdges R u d₀ q).card : ℚ) := by
    have := Finset.card_biUnion_le (s := R.parts ×ˢ R.parts) (t := pairBadEdges R u d₀)
    rw [poolBadEdges]
    exact_mod_cast this
  refine hcb.trans ?_
  refine (Finset.sum_le_sum
    (fun q _ => card_pairBadEdges_le R hδ hu hu1 hd₀ q)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_product]
  have hK0 : (0 : ℚ) ≤ 23 * δ * (R.size : ℚ) ^ 2 / (u * d₀ ^ 5) ^ 2 := by
    have hpos : (0 : ℚ) < (u * d₀ ^ 5) ^ 2 := by positivity
    positivity
  have hcast : ((R.parts.card * R.parts.card : ℕ) : ℚ) = (R.parts.card : ℚ) ^ 2 := by
    push_cast; ring
  rw [hcast]

/-! ## 4. `hdeg`, dado el recubrimiento -/

/-- **`hdeg`.**  Si fuera de un excepcional `Eexc` toda arista de `G` está entre dos partes que
admiten una ranura buena con las cinco densidades restantes `≥ d₀⁵`, entonces fuera de un
excepcional apenas mayor el grado del pool canónico está acotado por debajo. -/
theorem exists_canonicalPool_deg_lower_bound (R : EqualRegularity G δ) {u d₀ : ℚ}
    (hδ : 0 ≤ δ) (hu : 0 < u) (hu1 : u ≤ 1) (hd₀ : 0 < d₀)
    (Eexc : Finset (Sym2 α))
    (hcover : ∀ e ∈ G.edgeFinset, e ∉ Eexc → ∃ q ∈ R.parts ×ˢ R.parts,
        (∃ Sσ : Finset (Finset α) × Equiv.Perm (Fin 4), SlotFor R d₀ q Sσ) ∧
        e ∈ pairRootEdges G q)
    (hthr : 1 ≤ (1 - u) * (d₀ ^ 5 * (R.size : ℚ) ^ 2)) :
    ∃ E0 : Finset (Sym2 α), ∃ d : ℕ, 0 < d ∧
      (E0.card : ℚ) ≤ (Eexc.card : ℚ)
        + (R.parts.card : ℚ) ^ 2 * (23 * δ * (R.size : ℚ) ^ 2 / (u * d₀ ^ 5) ^ 2) ∧
      (1 - u) * (d₀ ^ 5 * (R.size : ℚ) ^ 2) - 1 ≤ (d : ℚ) ∧
      ∀ e ∈ G.edgeFinset, e ∉ E0 → d ≤ deg (canonicalSupportPool R) e := by
  classical
  set thr : ℚ := (1 - u) * (d₀ ^ 5 * (R.size : ℚ) ^ 2) with hthrdef
  refine ⟨Eexc ∪ poolBadEdges R u d₀, ⌊thr⌋₊, ?_, ?_, ?_, ?_⟩
  · exact Nat.floor_pos.2 hthr
  · have hunion : (((Eexc ∪ poolBadEdges R u d₀).card : ℕ) : ℚ)
        ≤ (Eexc.card : ℚ) + ((poolBadEdges R u d₀).card : ℚ) := by
      exact_mod_cast Finset.card_union_le Eexc (poolBadEdges R u d₀)
    linarith [card_poolBadEdges_le R hδ hu hu1 hd₀]
  · have h := Nat.sub_one_lt_floor thr
    linarith [h.le]
  · intro e heG hE0
    rw [Finset.mem_union, not_or] at hE0
    obtain ⟨q, hq, hex, hroot⟩ := hcover e heG hE0.1
    have hnotpair : e ∉ pairBadEdges R u d₀ q := by
      intro hbad
      exact hE0.2 (Finset.mem_biUnion.2 ⟨q, hq, hbad⟩)
    rw [pairBadEdges, dif_pos hex] at hnotpair
    obtain ⟨hS, h0, h1, hrp⟩ := hex.choose_spec
    have hrootEdges : e ∈ rootEdges G (canonicalTuple R hex.choose.1 ∘ hex.choose.2) := by
      rw [rootEdges_of_slotFor hex.choose_spec]
      exact hroot
    have hdegq : thr ≤ (deg (canonicalSupportPool R) e : ℚ) :=
      deg_ge_of_notMem_badRootEdges
        (fun i j hij => canonicalTuple_perm_disjoint R hS hex.choose.2 hij)
        (k4CandidateSupports_perm_subset_pool R hS hex.choose.2) hrootEdges hnotpair
    have hfl : ((⌊thr⌋₊ : ℕ) : ℚ) ≤ thr := Nat.floor_le (by linarith)
    have hle : ((⌊thr⌋₊ : ℕ) : ℚ) ≤ ((deg (canonicalSupportPool R) e : ℕ) : ℚ) :=
      le_trans hfl hdegq
    exact_mod_cast hle

end PaperIV.RootedK4Degree
