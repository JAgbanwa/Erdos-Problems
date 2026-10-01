import PaperIV.EighthMoment

/-!
# Varianza enraizada de triángulos (RC01 §13.3)

Segunda mitad del bloque «Conteos».  Conecta lo que ya estaba —el álgebra del segundo momento
(`RootedCounting`), la identificación de los dos momentos como conteos de patrón
(`RootedCountingBridge`) y los conteos mismos (`PatternCounting`)— en el enunciado (13.7).

## La plomería que faltaba

`RootedCountingBridge.sum_fiber_card_sq` dice que `∑_e c_e²` es el número de **pares ordenados
de copias con la misma raíz**.  `PatternCounting.counting_doubledK3` acota el conteo del
**patrón doblado**.  Que esos dos números sean el mismo es una biyección concreta:

```
(φ, ψ)  ↦  ![φ 0, φ 1, φ 2, ψ 2]
```

con inversa `χ ↦ (![χ 0, χ 1, χ 2], ![χ 0, χ 1, χ 3])`.  Eso es `card_pairs_eq_card_doubled`.

## Alcance

Se hace para `r = 3` (triángulos).  Para `r = 4` es la misma plomería con más índices
(`Fin 4 → Fin 6`); no está aquí.
-/

namespace PaperIV.RootedVariance

open Finset
open PaperIV.PatternCounting

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-! ## 1. Las copias como funciones -/

/-- Las copias transversales del patrón `F` sobre las partes `V`. -/
def copies (G : SimpleGraph α) [DecidableRel G.Adj] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Finset α) (F : Finset (ι × ι)) : Finset (ι → α) :=
  (Fintype.piFinset V).filter (fun φ => ∀ e ∈ F, G.Adj (φ e.1) (φ e.2))

theorem card_copies {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Finset α) (F : Finset (ι × ι)) :
    ((copies G V F).card : ℚ) = patCount G V F :=
  (patCount_eq_card V F).symm

/-! ## 2. Las partes del patrón doblado -/

/-- Las partes del doblado de `K₃`: la tercera se repite. -/
def dparts (V : Fin 3 → Finset α) : Fin 4 → Finset α := ![V 0, V 1, V 2, V 2]

/-! ## 3. La biyección -/

/-- **Pares de copias con raíz común = copias del patrón doblado.**

La raíz de un triángulo transversal es su arista en `(V₀, V₁)`; dos triángulos la comparten
exactamente cuando coinciden en las coordenadas `0` y `1`. -/
theorem card_pairs_eq_card_doubled (V : Fin 3 → Finset α) :
    (((copies G V patK3) ×ˢ (copies G V patK3)).filter
        (fun p => (p.1 0, p.1 1) = (p.2 0, p.2 1))).card
      = (copies G (dparts V) doubledK3).card := by
  classical
  refine Finset.card_nbij'
    (fun p => ![p.1 0, p.1 1, p.1 2, p.2 2])
    (fun χ => (![χ 0, χ 1, χ 2], ![χ 0, χ 1, χ 3])) ?_ ?_ ?_ ?_
  · -- va al patrón doblado
    intro p hp
    simp only [Finset.mem_coe] at hp ⊢
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨h1, h2⟩, hroot⟩ := hp
    rw [copies, Finset.mem_filter, Fintype.mem_piFinset] at h1 h2
    have hr0 : p.1 0 = p.2 0 := congrArg Prod.fst hroot
    have hr1 : p.1 1 = p.2 1 := congrArg Prod.snd hroot
    rw [copies, Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · intro i
      fin_cases i <;> simp [dparts] <;> first
        | exact h1.1 0 | exact h1.1 1 | exact h1.1 2 | exact h2.1 2
    · intro e he
      have hK3 := h1.2
      have hK3' := h2.2
      simp only [patK3, Finset.mem_insert, Finset.mem_singleton] at hK3 hK3'
      simp only [doubledK3, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl <;> simp <;>
        [ exact hK3 (0, 1) (by decide);
          exact hK3 (0, 2) (by decide);
          exact hK3 (1, 2) (by decide);
          (rw [hr0]; exact hK3' (0, 2) (by decide));
          (rw [hr1]; exact hK3' (1, 2) (by decide)) ]
  · -- vuelve a los pares
    intro χ hχ
    simp only [Finset.mem_coe] at hχ ⊢
    rw [copies, Finset.mem_filter, Fintype.mem_piFinset] at hχ
    obtain ⟨hmem, hadj⟩ := hχ
    simp only [doubledK3, Finset.mem_insert, Finset.mem_singleton] at hadj
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [copies, Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨?_, ?_⟩
      · intro i
        fin_cases i <;> simp <;> first
          | simpa [dparts] using hmem 0
          | simpa [dparts] using hmem 1
          | simpa [dparts] using hmem 2
      · intro e he
        simp only [patK3, Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl <;> simp <;>
          [ exact hadj (0, 1) (by decide);
            exact hadj (0, 2) (by decide);
            exact hadj (1, 2) (by decide) ]
    · rw [copies, Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨?_, ?_⟩
      · intro i
        fin_cases i <;> simp <;> first
          | simpa [dparts] using hmem 0
          | simpa [dparts] using hmem 1
          | simpa [dparts] using hmem 3
      · intro e he
        simp only [patK3, Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl <;> simp <;>
          [ exact hadj (0, 1) (by decide);
            exact hadj (0, 3) (by decide);
            exact hadj (1, 3) (by decide) ]
    · simp
  · -- inversa por la izquierda: la segunda componente usa que la raíz es común
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter] at hp
    have hr0 : p.1 0 = p.2 0 := congrArg Prod.fst hp.2
    have hr1 : p.1 1 = p.2 1 := congrArg Prod.snd hp.2
    dsimp only
    refine Prod.ext ?_ ?_ <;> funext i <;> fin_cases i <;> simp [hr0, hr1]
  · -- inversa por la derecha
    intro χ _
    dsimp only
    funext i
    fin_cases i <;> simp


/-! ## 4. La varianza enraizada (13.7) -/

open PaperIV.OneStepEstimate

theorem prod_patK3 (d : Fin 3 × Fin 3 → ℚ) :
    ∏ e ∈ patK3, d e = d (0, 1) * (d (0, 2) * d (1, 2)) := by
  rw [show patK3 = {((0 : Fin 3), (1 : Fin 3)), (0, 2), (1, 2)} from rfl,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]

theorem prod_doubledK3 (d : Fin 4 × Fin 4 → ℚ) :
    ∏ e ∈ doubledK3, d e
      = d (0, 1) * (d (0, 2) * (d (1, 2) * (d (0, 3) * d (1, 3)))) := by
  rw [show doubledK3 = {((0 : Fin 4), (1 : Fin 4)), (0, 2), (1, 2), (0, 3), (1, 3)} from rfl,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]

set_option maxHeartbeats 1000000 in
/-- **Varianza enraizada de triángulos (RC01 §13.3, ec. (13.7)).**

Con las tres parejas del patrón en el formato (3.2), la desviación cuadrática del conteo
enraizado respecto de su valor esperado `A = d₀₂·d₁₂·|V₂|` está acotada por

```
∑_e (c_e − A)²  ≤  11 · ε · |V₀| · |V₁| · |V₂|².
```

La constante `11 = 4ℓ − 1` con `ℓ = 3` es exactamente la que anuncia la fuente: sale de
`5` (patrón doblado, `2ℓ − 1`) más `2·3` (patrón simple, `ℓ`, pesado por `A ≤ |V₂|`). -/
theorem rooted_variance_K3 {ε : ℚ} (hε : 0 ≤ ε) (V : Fin 3 → Finset α)
    (h01 : DiscrepAt G ε (G.edgeDensity (V 0) (V 1)) (V 0) (V 1))
    (h02 : DiscrepAt G ε (G.edgeDensity (V 0) (V 2)) (V 0) (V 2))
    (h12 : DiscrepAt G ε (G.edgeDensity (V 1) (V 2)) (V 1) (V 2)) :
    ∑ e ∈ G.interedges (V 0) (V 1),
        (((PaperIV.RootedCountingBridge.fiber (copies G V patK3)
              (fun φ => (φ 0, φ 1)) e).card : ℚ)
          - G.edgeDensity (V 0) (V 2) * G.edgeDensity (V 1) (V 2) * ((V 2).card : ℚ)) ^ 2
      ≤ 11 * ε * ((V 0).card : ℚ) * ((V 1).card : ℚ) * ((V 2).card : ℚ) ^ 2 := by
  classical
  set a : ℚ := ((V 0).card : ℚ) with ha
  set b : ℚ := ((V 1).card : ℚ) with hb
  set c : ℚ := ((V 2).card : ℚ) with hc
  set d01 : ℚ := G.edgeDensity (V 0) (V 1) with hd01
  set d02 : ℚ := G.edgeDensity (V 0) (V 2) with hd02
  set d12 : ℚ := G.edgeDensity (V 1) (V 2) with hd12
  have ha0 : (0 : ℚ) ≤ a := by positivity
  have hb0 : (0 : ℚ) ≤ b := by positivity
  have hc0 : (0 : ℚ) ≤ c := by positivity
  have hd020 : 0 ≤ d02 := G.edgeDensity_nonneg _ _
  have hd021 : d02 ≤ 1 := G.edgeDensity_le_one _ _
  have hd120 : 0 ≤ d12 := G.edgeDensity_nonneg _ _
  have hd121 : d12 ≤ 1 := G.edgeDensity_le_one _ _
  -- (1) el conteo simple
  have hprod3 : ∏ i, ((V i).card : ℚ) = a * b * c := by
    rw [Fin.prod_univ_three]
  have hCs : |patCount G V patK3 - d01 * (d02 * d12) * (a * b * c)| ≤ 3 * ε * (a * b * c) := by
    have h := patCount_approx hε V (fun e => G.edgeDensity (V e.1) (V e.2)) patK3
      patK3_sym patK3_ne (fun e _ => G.edgeDensity_nonneg _ _)
      (fun e _ => G.edgeDensity_le_one _ _)
      (fun e he => by
        fin_cases he
        · exact h01
        · exact h02
        · exact h12)
    rw [prod_patK3, hprod3, card_patK3] at h
    push_cast at h
    convert h using 3 <;> ring
  -- (2) el conteo doblado
  have hdp0 : dparts V 0 = V 0 := by simp [dparts]
  have hdp1 : dparts V 1 = V 1 := by simp [dparts]
  have hdp2 : dparts V 2 = V 2 := by simp [dparts]
  have hdp3 : dparts V 3 = V 2 := by simp [dparts]
  have hprod4 : ∏ i, ((dparts V i).card : ℚ) = a * b * c * c := by
    rw [Fin.prod_univ_four, hdp0, hdp1, hdp2, hdp3]
  have hD : |patCount G (dparts V) doubledK3
        - d01 * (d02 * (d12 * (d02 * d12))) * (a * b * c * c)|
      ≤ 5 * ε * (a * b * c * c) := by
    have h := patCount_approx hε (dparts V)
      (fun e => G.edgeDensity (dparts V e.1) (dparts V e.2)) doubledK3
      doubledK3_sym doubledK3_ne (fun e _ => G.edgeDensity_nonneg _ _)
      (fun e _ => G.edgeDensity_le_one _ _)
      (fun e he => by
        fin_cases he
        · rw [hdp0, hdp1]; exact h01
        · rw [hdp0, hdp2]; exact h02
        · rw [hdp1, hdp2]; exact h12
        · rw [hdp0, hdp3]; exact h02
        · rw [hdp1, hdp3]; exact h12)
    rw [prod_doubledK3, hprod4, card_doubledK3] at h
    simp only [hdp0, hdp1, hdp2, hdp3] at h
    push_cast at h
    convert h using 3 <;> ring
  -- (3) el número de raíces es exacto
  have hE : ((G.interedges (V 0) (V 1)).card : ℚ) = d01 * a * b :=
    PaperIV.OneStepEstimate.card_interedges_eq (V 0) (V 1)
  -- (4) las raíces de las copias son aristas reales
  have hroot : ∀ φ ∈ copies G V patK3, (φ 0, φ 1) ∈ G.interedges (V 0) (V 1) := by
    intro φ hφ
    rw [copies, Finset.mem_filter, Fintype.mem_piFinset] at hφ
    rw [SimpleGraph.interedges_def, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hφ.1 0, hφ.1 1⟩, hφ.2 (0, 1) (by decide)⟩
  -- (5) el segundo momento
  have hmain := PaperIV.RootedCountingBridge.second_moment_of_pattern_counts
    (copies G V patK3) (fun φ => (φ 0, φ 1)) (G.interedges (V 0) (V 1))
    (d02 * d12 * c) (3 * ε * (a * b * c)) (5 * ε * (a * b * c * c)) hroot
    (by
      rw [card_copies, hE]
      calc |patCount G V patK3 - d02 * d12 * c * (d01 * a * b)|
          = |patCount G V patK3 - d01 * (d02 * d12) * (a * b * c)| := by ring_nf
        _ ≤ 3 * ε * (a * b * c) := hCs)
    (by
      rw [card_pairs_eq_card_doubled, card_copies, hE]
      calc |patCount G (dparts V) doubledK3 - (d02 * d12 * c) ^ 2 * (d01 * a * b)|
          = |patCount G (dparts V) doubledK3
              - d01 * (d02 * (d12 * (d02 * d12))) * (a * b * c * c)| := by ring_nf
        _ ≤ 5 * ε * (a * b * c * c) := hD)
  -- (6) `A ≤ |V₂|`
  have hA : |d02 * d12 * c| ≤ c := by
    have hprod : d02 * d12 ≤ 1 := by
      calc d02 * d12 ≤ d02 * 1 := mul_le_mul_of_nonneg_left hd121 hd020
        _ = d02 := mul_one d02
        _ ≤ 1 := hd021
    rw [abs_of_nonneg (by positivity)]
    calc d02 * d12 * c ≤ 1 * c := mul_le_mul_of_nonneg_right hprod hc0
      _ = c := one_mul c
  have hN1 : (0 : ℚ) ≤ 3 * ε * (a * b * c) := by positivity
  calc ∑ e ∈ G.interedges (V 0) (V 1),
        (((PaperIV.RootedCountingBridge.fiber (copies G V patK3)
              (fun φ => (φ 0, φ 1)) e).card : ℚ) - d02 * d12 * c) ^ 2
      ≤ 5 * ε * (a * b * c * c) + 2 * |d02 * d12 * c| * (3 * ε * (a * b * c)) := hmain
    _ ≤ 5 * ε * (a * b * c * c) + 2 * c * (3 * ε * (a * b * c)) := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA (by norm_num : (0:ℚ) ≤ 2)) hN1
        linarith
    _ = 11 * ε * a * b * c ^ 2 := by ring


/-! ## 5. Lo mismo para `K₄` -/

/-- Las partes del doblado de `K₄`: las dos que no son raíz se repiten. -/
def dparts4 (V : Fin 4 → Finset α) : Fin 6 → Finset α := ![V 0, V 1, V 2, V 3, V 2, V 3]

/-- **Pares de copias de `K₄` con raíz común = copias del patrón doblado de `K₄`.** -/
theorem card_pairs_eq_card_doubledK4 (V : Fin 4 → Finset α) :
    (((copies G V patK4) ×ˢ (copies G V patK4)).filter
        (fun p => (p.1 0, p.1 1) = (p.2 0, p.2 1))).card
      = (copies G (dparts4 V) doubledK4).card := by
  classical
  refine Finset.card_nbij'
    (fun p => ![p.1 0, p.1 1, p.1 2, p.1 3, p.2 2, p.2 3])
    (fun χ => (![χ 0, χ 1, χ 2, χ 3], ![χ 0, χ 1, χ 4, χ 5])) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_coe] at hp ⊢
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨h1, h2⟩, hroot⟩ := hp
    rw [copies, Finset.mem_filter, Fintype.mem_piFinset] at h1 h2
    have hr0 : p.1 0 = p.2 0 := congrArg Prod.fst hroot
    have hr1 : p.1 1 = p.2 1 := congrArg Prod.snd hroot
    rw [copies, Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · intro i
      fin_cases i <;> simp [dparts4] <;> first
        | exact h1.1 0 | exact h1.1 1 | exact h1.1 2 | exact h1.1 3
        | exact h2.1 2 | exact h2.1 3
    · intro e he
      have hK4 := h1.2
      have hK4' := h2.2
      simp only [patK4, Finset.mem_insert, Finset.mem_singleton] at hK4 hK4'
      simp only [doubledK4, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;>
        [ exact hK4 (0, 1) (by decide);
          exact hK4 (0, 2) (by decide);
          exact hK4 (0, 3) (by decide);
          exact hK4 (1, 2) (by decide);
          exact hK4 (1, 3) (by decide);
          exact hK4 (2, 3) (by decide);
          (rw [hr0]; exact hK4' (0, 2) (by decide));
          (rw [hr0]; exact hK4' (0, 3) (by decide));
          (rw [hr1]; exact hK4' (1, 2) (by decide));
          (rw [hr1]; exact hK4' (1, 3) (by decide));
          exact hK4' (2, 3) (by decide) ]
  · intro χ hχ
    simp only [Finset.mem_coe] at hχ ⊢
    rw [copies, Finset.mem_filter, Fintype.mem_piFinset] at hχ
    obtain ⟨hmem, hadj⟩ := hχ
    simp only [doubledK4, Finset.mem_insert, Finset.mem_singleton] at hadj
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [copies, Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨?_, ?_⟩
      · intro i
        fin_cases i <;> simp <;> first
          | simpa [dparts4] using hmem 0 | simpa [dparts4] using hmem 1
          | simpa [dparts4] using hmem 2 | simpa [dparts4] using hmem 3
      · intro e he
        simp only [patK4, Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;>
          [ exact hadj (0, 1) (by decide);
            exact hadj (0, 2) (by decide);
            exact hadj (0, 3) (by decide);
            exact hadj (1, 2) (by decide);
            exact hadj (1, 3) (by decide);
            exact hadj (2, 3) (by decide) ]
    · rw [copies, Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨?_, ?_⟩
      · intro i
        fin_cases i <;> simp <;> first
          | simpa [dparts4] using hmem 0 | simpa [dparts4] using hmem 1
          | simpa [dparts4] using hmem 4 | simpa [dparts4] using hmem 5
      · intro e he
        simp only [patK4, Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;>
          [ exact hadj (0, 1) (by decide);
            exact hadj (0, 4) (by decide);
            exact hadj (0, 5) (by decide);
            exact hadj (1, 4) (by decide);
            exact hadj (1, 5) (by decide);
            exact hadj (4, 5) (by decide) ]
    · simp
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter] at hp
    have hr0 : p.1 0 = p.2 0 := congrArg Prod.fst hp.2
    have hr1 : p.1 1 = p.2 1 := congrArg Prod.snd hp.2
    dsimp only
    refine Prod.ext ?_ ?_ <;> funext i <;> fin_cases i <;> simp [hr0, hr1]
  · intro χ _
    dsimp only
    funext i
    fin_cases i <;> simp

theorem prod_patK4 (d : Fin 4 × Fin 4 → ℚ) :
    ∏ e ∈ patK4, d e
      = d (0, 1) * (d (0, 2) * (d (0, 3) * (d (1, 2) * (d (1, 3) * d (2, 3))))) := by
  rw [show patK4 = {((0 : Fin 4), (1 : Fin 4)), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} from rfl,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]

theorem prod_doubledK4 (d : Fin 6 × Fin 6 → ℚ) :
    ∏ e ∈ doubledK4, d e
      = d (0, 1) * (d (0, 2) * (d (0, 3) * (d (1, 2) * (d (1, 3) * (d (2, 3) *
          (d (0, 4) * (d (0, 5) * (d (1, 4) * (d (1, 5) * d (4, 5)))))))))) := by
  rw [show doubledK4 = {((0 : Fin 6), (1 : Fin 6)), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3),
      (0, 4), (0, 5), (1, 4), (1, 5), (4, 5)} from rfl,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]

set_option maxHeartbeats 2000000 in
/-- **Varianza enraizada de `K₄` (RC01 §13.3, ec. (13.7)).**

```
∑_e (c_e − A)²  ≤  23 · ε · |V₀| · |V₁| · |V₂|² · |V₃|²,
A = d₀₂·d₀₃·d₁₂·d₁₃·d₂₃ · |V₂| · |V₃|.
```

La constante `23 = 4ℓ − 1` con `ℓ = 6` es la que anuncia la fuente (y la que verifica
`CountingTelescope.constant_K4`): sale de `11` (patrón doblado, `2ℓ − 1`) más `2·6` (patrón
simple, `ℓ`, pesado por `A ≤ |V₂||V₃|`). -/
theorem rooted_variance_K4 {ε : ℚ} (hε : 0 ≤ ε) (V : Fin 4 → Finset α)
    (h01 : DiscrepAt G ε (G.edgeDensity (V 0) (V 1)) (V 0) (V 1))
    (h02 : DiscrepAt G ε (G.edgeDensity (V 0) (V 2)) (V 0) (V 2))
    (h03 : DiscrepAt G ε (G.edgeDensity (V 0) (V 3)) (V 0) (V 3))
    (h12 : DiscrepAt G ε (G.edgeDensity (V 1) (V 2)) (V 1) (V 2))
    (h13 : DiscrepAt G ε (G.edgeDensity (V 1) (V 3)) (V 1) (V 3))
    (h23 : DiscrepAt G ε (G.edgeDensity (V 2) (V 3)) (V 2) (V 3)) :
    ∑ e ∈ G.interedges (V 0) (V 1),
        (((PaperIV.RootedCountingBridge.fiber (copies G V patK4)
              (fun φ => (φ 0, φ 1)) e).card : ℚ)
          - G.edgeDensity (V 0) (V 2) * G.edgeDensity (V 0) (V 3)
              * G.edgeDensity (V 1) (V 2) * G.edgeDensity (V 1) (V 3)
              * G.edgeDensity (V 2) (V 3) * ((V 2).card : ℚ) * ((V 3).card : ℚ)) ^ 2
      ≤ 23 * ε * ((V 0).card : ℚ) * ((V 1).card : ℚ)
          * ((V 2).card : ℚ) ^ 2 * ((V 3).card : ℚ) ^ 2 := by
  classical
  set a : ℚ := ((V 0).card : ℚ) with ha
  set b : ℚ := ((V 1).card : ℚ) with hb
  set c : ℚ := ((V 2).card : ℚ) with hc
  set f : ℚ := ((V 3).card : ℚ) with hf
  set d01 : ℚ := G.edgeDensity (V 0) (V 1) with hd01
  set d02 : ℚ := G.edgeDensity (V 0) (V 2) with hd02
  set d03 : ℚ := G.edgeDensity (V 0) (V 3) with hd03
  set d12 : ℚ := G.edgeDensity (V 1) (V 2) with hd12
  set d13 : ℚ := G.edgeDensity (V 1) (V 3) with hd13
  set d23 : ℚ := G.edgeDensity (V 2) (V 3) with hd23
  have ha0 : (0 : ℚ) ≤ a := by positivity
  have hb0 : (0 : ℚ) ≤ b := by positivity
  have hc0 : (0 : ℚ) ≤ c := by positivity
  have hf0 : (0 : ℚ) ≤ f := by positivity
  have hn : ∀ x y : Finset α, 0 ≤ G.edgeDensity x y := fun x y => G.edgeDensity_nonneg _ _
  have hu : ∀ x y : Finset α, G.edgeDensity x y ≤ 1 := fun x y => G.edgeDensity_le_one _ _
  -- (1) el conteo simple
  have hprod4 : ∏ i, ((V i).card : ℚ) = a * b * c * f := by rw [Fin.prod_univ_four]
  have hCs : |patCount G V patK4
        - d01 * (d02 * (d03 * (d12 * (d13 * d23)))) * (a * b * c * f)|
      ≤ 6 * ε * (a * b * c * f) := by
    have h := patCount_approx hε V (fun e => G.edgeDensity (V e.1) (V e.2)) patK4
      patK4_sym patK4_ne (fun e _ => hn _ _) (fun e _ => hu _ _)
      (fun e he => by
        fin_cases he
        · exact h01
        · exact h02
        · exact h03
        · exact h12
        · exact h13
        · exact h23)
    rw [prod_patK4, hprod4, card_patK4] at h
    push_cast at h
    convert h using 3 <;> ring
  -- (2) el conteo doblado
  have hq0 : dparts4 V 0 = V 0 := by simp [dparts4]
  have hq1 : dparts4 V 1 = V 1 := by simp [dparts4]
  have hq2 : dparts4 V 2 = V 2 := by simp [dparts4]
  have hq3 : dparts4 V 3 = V 3 := by simp [dparts4]
  have hq4 : dparts4 V 4 = V 2 := by simp [dparts4]
  have hq5 : dparts4 V 5 = V 3 := by simp [dparts4]
  have hprod6 : ∏ i, ((dparts4 V i).card : ℚ) = a * b * c * f * c * f := by
    rw [Fin.prod_univ_six, hq0, hq1, hq2, hq3, hq4, hq5]
  have hD : |patCount G (dparts4 V) doubledK4
        - d01 * (d02 * (d03 * (d12 * (d13 * (d23 *
            (d02 * (d03 * (d12 * (d13 * d23))))))))) * (a * b * c * f * c * f)|
      ≤ 11 * ε * (a * b * c * f * c * f) := by
    have h := patCount_approx hε (dparts4 V)
      (fun e => G.edgeDensity (dparts4 V e.1) (dparts4 V e.2)) doubledK4
      doubledK4_sym doubledK4_ne (fun e _ => hn _ _) (fun e _ => hu _ _)
      (fun e he => by
        fin_cases he
        · rw [hq0, hq1]; exact h01
        · rw [hq0, hq2]; exact h02
        · rw [hq0, hq3]; exact h03
        · rw [hq1, hq2]; exact h12
        · rw [hq1, hq3]; exact h13
        · rw [hq2, hq3]; exact h23
        · rw [hq0, hq4]; exact h02
        · rw [hq0, hq5]; exact h03
        · rw [hq1, hq4]; exact h12
        · rw [hq1, hq5]; exact h13
        · rw [hq4, hq5]; exact h23)
    rw [prod_doubledK4, hprod6, card_doubledK4] at h
    simp only [hq0, hq1, hq2, hq3, hq4, hq5] at h
    push_cast at h
    convert h using 3 <;> ring
  -- (3) el número de raíces es exacto
  have hE : ((G.interedges (V 0) (V 1)).card : ℚ) = d01 * a * b :=
    PaperIV.OneStepEstimate.card_interedges_eq (V 0) (V 1)
  have hroot : ∀ φ ∈ copies G V patK4, (φ 0, φ 1) ∈ G.interedges (V 0) (V 1) := by
    intro φ hφ
    rw [copies, Finset.mem_filter, Fintype.mem_piFinset] at hφ
    rw [SimpleGraph.interedges_def, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hφ.1 0, hφ.1 1⟩, hφ.2 (0, 1) (by decide)⟩
  -- (4) el segundo momento
  have hmain := PaperIV.RootedCountingBridge.second_moment_of_pattern_counts
    (copies G V patK4) (fun φ => (φ 0, φ 1)) (G.interedges (V 0) (V 1))
    (d02 * d03 * d12 * d13 * d23 * c * f)
    (6 * ε * (a * b * c * f)) (11 * ε * (a * b * c * f * c * f)) hroot
    (by
      rw [card_copies, hE]
      calc |patCount G V patK4 - d02 * d03 * d12 * d13 * d23 * c * f * (d01 * a * b)|
          = |patCount G V patK4
              - d01 * (d02 * (d03 * (d12 * (d13 * d23)))) * (a * b * c * f)| := by ring_nf
        _ ≤ 6 * ε * (a * b * c * f) := hCs)
    (by
      rw [card_pairs_eq_card_doubledK4, card_copies, hE]
      calc |patCount G (dparts4 V) doubledK4
              - (d02 * d03 * d12 * d13 * d23 * c * f) ^ 2 * (d01 * a * b)|
          = |patCount G (dparts4 V) doubledK4
              - d01 * (d02 * (d03 * (d12 * (d13 * (d23 *
                  (d02 * (d03 * (d12 * (d13 * d23))))))))) * (a * b * c * f * c * f)| := by
            ring_nf
        _ ≤ 11 * ε * (a * b * c * f * c * f) := hD)
  -- (5) `A ≤ |V₂||V₃|`
  have hprod5 : d02 * d03 * d12 * d13 * d23 ≤ 1 := by
    have k02 : 0 ≤ d02 := hn _ _
    have k03 : 0 ≤ d03 := hn _ _
    have k12 : 0 ≤ d12 := hn _ _
    have k13 : 0 ≤ d13 := hn _ _
    have p2 : 0 ≤ d02 * d03 := mul_nonneg k02 k03
    have p3 : 0 ≤ d02 * d03 * d12 := mul_nonneg p2 k12
    have p4 : 0 ≤ d02 * d03 * d12 * d13 := mul_nonneg p3 k13
    calc d02 * d03 * d12 * d13 * d23
        ≤ d02 * d03 * d12 * d13 * 1 := mul_le_mul_of_nonneg_left (hu _ _) p4
      _ = d02 * d03 * d12 * d13 := mul_one _
      _ ≤ d02 * d03 * d12 * 1 := mul_le_mul_of_nonneg_left (hu _ _) p3
      _ = d02 * d03 * d12 := mul_one _
      _ ≤ d02 * d03 * 1 := mul_le_mul_of_nonneg_left (hu _ _) p2
      _ = d02 * d03 := mul_one _
      _ ≤ d02 * 1 := mul_le_mul_of_nonneg_left (hu _ _) k02
      _ = d02 := mul_one _
      _ ≤ 1 := hu _ _
  have hA : |d02 * d03 * d12 * d13 * d23 * c * f| ≤ c * f := by
    have hnn : 0 ≤ d02 * d03 * d12 * d13 * d23 * c * f :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (hn _ _) (hn _ _)) (hn _ _)) (hn _ _)) (hn _ _)) hc0) hf0
    rw [abs_of_nonneg hnn]
    calc d02 * d03 * d12 * d13 * d23 * c * f
        = (d02 * d03 * d12 * d13 * d23) * (c * f) := by ring
      _ ≤ 1 * (c * f) := mul_le_mul_of_nonneg_right hprod5 (mul_nonneg hc0 hf0)
      _ = c * f := one_mul _
  have hN1 : (0 : ℚ) ≤ 6 * ε * (a * b * c * f) := by positivity
  calc ∑ e ∈ G.interedges (V 0) (V 1),
        (((PaperIV.RootedCountingBridge.fiber (copies G V patK4)
              (fun φ => (φ 0, φ 1)) e).card : ℚ)
          - d02 * d03 * d12 * d13 * d23 * c * f) ^ 2
      ≤ 11 * ε * (a * b * c * f * c * f)
          + 2 * |d02 * d03 * d12 * d13 * d23 * c * f| * (6 * ε * (a * b * c * f)) := hmain
    _ ≤ 11 * ε * (a * b * c * f * c * f) + 2 * (c * f) * (6 * ε * (a * b * c * f)) := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA (by norm_num : (0:ℚ) ≤ 2)) hN1
        linarith
    _ = 23 * ε * a * b * c ^ 2 * f ^ 2 := by ring

end PaperIV.RootedVariance
