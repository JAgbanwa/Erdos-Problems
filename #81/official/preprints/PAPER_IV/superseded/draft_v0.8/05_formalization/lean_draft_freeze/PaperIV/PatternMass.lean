import PaperIV.FarRounding
import PaperIV.CopyCleanup

/-!
# Masa por patrones: descartes y capacidad agregada (RC01 §15)

## Lo que se demuestra

* `sum_weight_le_card_of_meets` — **el principio de cobertura por incidencias**: si cada pieza
  de una subfamilia del soporte fraccional toca al menos una arista de `B ⊆ E(G)`, su masa
  total no excede `|B|`.  Sale de las capacidades, una por arista de `B`.
* `gain_of_discards_le` — **(15.2)**: la ganancia de los ítems descartados es a lo sumo
  `5·|B_desc|`.
* `mass_le_card_cross` — **(15.5)**: la masa de los patrones que usan una pareja fija está
  acotada por el número de aristas reales de esa pareja.
* `sum_small_le` — **(15.2), patrones pequeños**: descartar los de masa `< θ` cuesta a lo sumo
  `#patrones · θ`.

## La forma exacta del argumento

La fuente subraya que *«la cobertura por incidencias es literal: cada ítem retirado tiene al
menos una arista en `B_desc`. No se utiliza una pérdida constante por vértice.»*  Eso es
justamente lo que hace `sum_weight_le_card_of_meets`: la desigualdad

```
∑_{K ∈ D} x_K  ≤  ∑_{f ∈ B} ∑_{K ∈ D, f ∈ soporte(K)} x_K  ≤  ∑_{f ∈ B} 1 = |B|
```

usa en el primer paso que cada `K` aporta su peso en **al menos** una columna `f`, y en el
segundo la restricción de capacidad de `x` en esa arista.  El doble conteo sólo ayuda.

## Nivel de abstracción

`B` es un conjunto arbitrario de aristas reales y `D` una subfamilia arbitraria de ítems que
las toca.  Ni la partición regular ni las densidades aparecen: la aritmética de (15.1)
—`|B_desc| ≤ (2δ + 1/(2k₀) + d/2)n²`— es contabilidad de la partición y entra al instanciar.
-/

namespace PaperIV.PatternMass

open Finset
open PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. La ganancia de un ítem está entre 2 y 5 -/

theorem gainF_nonneg {K : Finset V} (h : IsItem G K) : (0 : ℚ) ≤ gainF ℚ K := by
  rcases h.2 with h3 | h4
  · have e : Nat.choose 3 2 = 3 := by decide
    rw [gainF, h3, e]; norm_num
  · have e : Nat.choose 4 2 = 6 := by decide
    rw [gainF, h4, e]; norm_num

theorem gainF_le_five {K : Finset V} (h : IsItem G K) : gainF ℚ K ≤ 5 := by
  rcases h.2 with h3 | h4
  · have e : Nat.choose 3 2 = 3 := by decide
    rw [gainF, h3, e]; norm_num
  · have e : Nat.choose 4 2 = 6 := by decide
    rw [gainF, h4, e]; norm_num

/-! ## 2. Cobertura por incidencias -/

/-- **El principio de cobertura (RC01 §15.1).**  Si cada pieza de `D` toca alguna arista de
`B`, la masa fraccional de `D` no excede `|B|`.

Es exactamente «cada ítem retirado tiene al menos una arista en `B_desc`», sin pérdida
constante por vértice. -/
theorem sum_weight_le_card_of_meets (x : FracPacking G ℚ) (B : Finset (Sym2 V))
    (hB : ∀ f ∈ B, f ∈ G.edgeFinset) (D : Finset (Finset V)) (hD : ∀ K ∈ D, K ∈ items G)
    (hmeet : ∀ K ∈ D, ∃ f ∈ B, f ∈ pairs K) :
    ∑ K ∈ D, x.weight K ≤ (B.card : ℚ) := by
  classical
  -- cada pieza aporta su peso en al menos una columna
  have hrow : ∀ K ∈ D,
      x.weight K ≤ ∑ f ∈ B, (if f ∈ pairs K then x.weight K else 0) := by
    intro K hK
    obtain ⟨f₀, hf₀B, hf₀K⟩ := hmeet K hK
    have hsingle : (if f₀ ∈ pairs K then x.weight K else 0)
        ≤ ∑ f ∈ B, (if f ∈ pairs K then x.weight K else 0) := by
      refine Finset.single_le_sum (f := fun f => if f ∈ pairs K then x.weight K else 0) ?_ hf₀B
      intro f _
      dsimp only
      by_cases hf : f ∈ pairs K
      · rw [if_pos hf]; exact x.weight_nonneg K
      · rw [if_neg hf]
    rwa [if_pos hf₀K] at hsingle
  calc ∑ K ∈ D, x.weight K
      ≤ ∑ K ∈ D, ∑ f ∈ B, (if f ∈ pairs K then x.weight K else 0) :=
        Finset.sum_le_sum hrow
    _ = ∑ f ∈ B, ∑ K ∈ D, (if f ∈ pairs K then x.weight K else 0) := Finset.sum_comm
    _ ≤ ∑ f ∈ B, ∑ K ∈ items G, (if f ∈ pairs K then x.weight K else 0) := by
        refine Finset.sum_le_sum ?_
        intro f _
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun K hK => hD K hK) ?_
        intro K _ _
        by_cases hf : f ∈ pairs K
        · rw [if_pos hf]; exact x.weight_nonneg K
        · rw [if_neg hf]
    _ ≤ ∑ _f ∈ B, (1 : ℚ) := Finset.sum_le_sum (fun f hf => x.capacity f (hB f hf))
    _ = (B.card : ℚ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **(15.2).**  La ganancia de los ítems descartados es a lo sumo `5·|B_desc|`. -/
theorem gain_of_discards_le (x : FracPacking G ℚ) (B : Finset (Sym2 V))
    (hB : ∀ f ∈ B, f ∈ G.edgeFinset) (D : Finset (Finset V)) (hD : ∀ K ∈ D, K ∈ items G)
    (hmeet : ∀ K ∈ D, ∃ f ∈ B, f ∈ pairs K) :
    ∑ K ∈ D, gainF ℚ K * x.weight K ≤ 5 * (B.card : ℚ) := by
  classical
  have hstep : ∀ K ∈ D, gainF ℚ K * x.weight K ≤ 5 * x.weight K := by
    intro K hK
    exact mul_le_mul_of_nonneg_right (gainF_le_five (mem_items.1 (hD K hK)))
      (x.weight_nonneg K)
  calc ∑ K ∈ D, gainF ℚ K * x.weight K ≤ ∑ K ∈ D, 5 * x.weight K :=
        Finset.sum_le_sum hstep
    _ = 5 * ∑ K ∈ D, x.weight K := by rw [Finset.mul_sum]
    _ ≤ 5 * (B.card : ℚ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact sum_weight_le_card_of_meets x B hB D hD hmeet

/-! ## 3. Capacidad agregada por pareja -/

/-- Las aristas reales entre dos partes, como conjunto de `Sym2`. -/
def crossEdges (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) : Finset (Sym2 V) :=
  (G.interedges A B).image (fun p => s(p.1, p.2))

theorem crossEdges_subset (A B : Finset V) {f : Sym2 V} (hf : f ∈ crossEdges G A B) :
    f ∈ G.edgeFinset := by
  classical
  rw [crossEdges, Finset.mem_image] at hf
  obtain ⟨p, hp, rfl⟩ := hf
  rw [SimpleGraph.interedges_def, Finset.mem_filter] at hp
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact hp.2

/-- **El número de aristas cruzadas es `d_ij·|V_i|·|V_j|`**, exactamente.  Para partes
disjuntas el paso de parejas ordenadas a `Sym2` es inyectivo. -/
theorem card_crossEdges (A B : Finset V) (hdisj : Disjoint A B) :
    ((crossEdges G A B).card : ℚ) = G.edgeDensity A B * (A.card : ℚ) * (B.card : ℚ) := by
  classical
  have hinj : Set.InjOn (fun p : V × V => s(p.1, p.2)) (G.interedges A B) := by
    intro p hp q hq hpq
    rw [Finset.mem_coe, SimpleGraph.interedges_def, Finset.mem_filter,
      Finset.mem_product] at hp hq
    rw [Sym2.eq_iff] at hpq
    rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exact absurd (h1 ▸ hq.1.2) (Finset.disjoint_left.1 hdisj hp.1.1)
  rw [crossEdges, Finset.card_image_of_injOn hinj]
  exact PaperIV.OneStepEstimate.card_interedges_eq A B

/-- **(15.5) Capacidad agregada por pareja.**  Si cada ítem de `D` usa alguna arista real de
la pareja `(A,B)`, la masa total de `D` es a lo sumo `d_{AB}·|A|·|B|`.

Con partes de tamaño `t` eso es `d_ij·t²`, que es la forma de la fuente. -/
theorem mass_le_density (x : FracPacking G ℚ) (A B : Finset V) (hdisj : Disjoint A B)
    (D : Finset (Finset V)) (hD : ∀ K ∈ D, K ∈ items G)
    (hone : ∀ K ∈ D, ∃ f ∈ crossEdges G A B, f ∈ pairs K) :
    ∑ K ∈ D, x.weight K ≤ G.edgeDensity A B * (A.card : ℚ) * (B.card : ℚ) := by
  rw [← card_crossEdges A B hdisj]
  exact sum_weight_le_card_of_meets x (crossEdges G A B)
    (fun f hf => crossEdges_subset A B hf) D hD hone

/-! ## 4. Los patrones pequeños se descartan barato -/

/-- **(15.2), patrones pequeños.**  Descartar los patrones de masa `< θ` cuesta a lo sumo
`#patrones · θ`. -/
theorem sum_small_le {ι : Type*} [DecidableEq ι] (Pats : Finset ι) (μ : ι → ℚ) (θ : ℚ)
    (hθ : 0 ≤ θ) :
    ∑ σ ∈ Pats.filter (fun σ => μ σ < θ), μ σ ≤ (Pats.card : ℚ) * θ := by
  classical
  calc ∑ σ ∈ Pats.filter (fun σ => μ σ < θ), μ σ
      ≤ ∑ _σ ∈ Pats.filter (fun σ => μ σ < θ), θ := by
        refine Finset.sum_le_sum ?_
        intro σ hσ
        exact le_of_lt (Finset.mem_filter.1 hσ).2
    _ = ((Pats.filter (fun σ => μ σ < θ)).card : ℚ) * θ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Pats.card : ℚ) * θ := by
        refine mul_le_mul_of_nonneg_right ?_ hθ
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-- Y su ganancia, a lo sumo `5` veces eso. -/
theorem gain_small_le {ι : Type*} [DecidableEq ι] (Pats : Finset ι) (μ gainOfPat : ι → ℚ)
    (θ : ℚ) (hθ : 0 ≤ θ) (hnn : ∀ σ, 0 ≤ μ σ) (hle : ∀ σ, gainOfPat σ ≤ 5 * μ σ) :
    ∑ σ ∈ Pats.filter (fun σ => μ σ < θ), gainOfPat σ ≤ 5 * ((Pats.card : ℚ) * θ) := by
  classical
  calc ∑ σ ∈ Pats.filter (fun σ => μ σ < θ), gainOfPat σ
      ≤ ∑ σ ∈ Pats.filter (fun σ => μ σ < θ), 5 * μ σ :=
        Finset.sum_le_sum (fun σ _ => hle σ)
    _ = 5 * ∑ σ ∈ Pats.filter (fun σ => μ σ < θ), μ σ := by rw [Finset.mul_sum]
    _ ≤ 5 * ((Pats.card : ℚ) * θ) := by
        refine mul_le_mul_of_nonneg_left (sum_small_le Pats μ θ hθ) (by norm_num)

end PaperIV.PatternMass
