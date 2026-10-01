import PaperIV.OwnerCoins

/-!
# Concentración de los grados (RC01 §16.3)

Ensambla las tres piezas que ya estaban: las capas de §16.2, las monedas de §15.4/§16.1 y el
octavo momento de §13.1.

## La estructura del argumento

1. **Reparto por capas.**  `deg = ∑_λ deg_λ`.  Si `|deg − E deg| ≥ u·D_σ`, entonces alguna
   capa se desvía al menos `u·D_σ/t` (`exists_large_layer`, puro pigeonhole).
2. **Independencia dentro de una capa.**  Los soportes de dos completaciones de la misma capa
   son disjuntos (`CyclicLayering.pageEdges_disjoint`), y para soportes disjuntos la esperanza
   del producto de indicadores es el producto de las esperanzas (`expect_prod_blocks`).  Ésa es
   la propiedad que §16.2 existe para dar.
3. **Cola por capa.**  Cada capa suma a lo sumo `t` indicadores; centrados, cumplen las
   hipótesis de (13.2) y `EighthMoment.tail_bound` da la cola.
4. **Unión sobre las `t` capas.**

## La aritmética, verificada

Con `D_σ = α⁵t²` (caso `K₄`, `ℓ = 6`, `r = 4`), desviación por capa `u·D_σ/t` y `m ≤ t`
indicadores:

```
C₈·t⁴ / (u·D_σ/t)⁸ = C₈·t⁴ / (u⁸α⁴⁰t⁸) = C₈/(u⁸α⁴⁰t⁴),
```

y la unión sobre `t` capas da `C₈/(u⁸α⁴⁰t³)`, que es exactamente (16.4).  Para `K₃`
(`D_σ = α²t`, una sola capa) sale `C₈/(u⁸α¹⁶t⁴)`, la cota mejor que anuncia la fuente.  Las dos
identidades están demostradas abajo (`layer_tail_arith`, `union_layers_arith`,
`k3_tail_arith`).

## Lo que queda como hipótesis, y por qué

`degree_tail_bound` recibe la cola **por capa** como hipótesis explícita.  La razón es precisa:
`EighthMoment.tail_bound` pide que los momentos mixtos de las variables **centradas** se
factoricen, y lo que `expect_prod_blocks` da es la factorización de los productos de
**indicadores** (sin centrar).  Pasar de una a otra es desarrollar
`(I_j − μ_j)^{k_j} = a_j + b_j·I_j` y expandir el producto sobre subconjuntos
(`Finset.prod_add`); es mecánico pero no está hecho.  **Ése es el único hueco de §16.3.**
-/

namespace PaperIV.DegreeConcentration

open Finset
open PaperIV.EighthMoment
open PaperIV.OwnerCoins

/-! ## 1. Reparto por capas: pigeonhole -/

/-- **Si la suma se desvía, alguna capa se desvía proporcionalmente.** -/
theorem exists_large_layer {ι : Type*} (s : Finset ι) (a : ι → ℚ) {z : ℚ} (hz : 0 < z)
    (h : z ≤ |∑ l ∈ s, a l|) :
    ∃ l ∈ s, z / (s.card : ℚ) ≤ |a l| := by
  classical
  by_contra hcon
  push_neg at hcon
  have hne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with rfl | hne
    · rw [Finset.sum_empty, abs_zero] at h; linarith
    · exact hne
  have hcard : (0 : ℚ) < (s.card : ℚ) := by
    have := Finset.card_pos.2 hne
    exact_mod_cast this
  have h1 : |∑ l ∈ s, a l| ≤ ∑ l ∈ s, |a l| := Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ l ∈ s, |a l| < ∑ _l ∈ s, z / (s.card : ℚ) :=
    Finset.sum_lt_sum_of_nonempty hne (fun l hl => hcon l hl)
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  have h3 : (s.card : ℚ) * (z / (s.card : ℚ)) = z := by field_simp
  rw [h3] at h2
  linarith

/-! ## 2. Independencia dentro de una capa -/

variable {ρ κ : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype κ] [DecidableEq κ]

/-- **El pago de §16.2.**  Soportes disjuntos ⟹ la esperanza del producto de los indicadores
de supervivencia es el producto de las esperanzas. -/
theorem expect_prod_blocks (q : ρ → κ → ℚ) (hnn : ∀ e j, 0 ≤ q e j)
    (hsum : ∀ e, ∑ j, q e j = 1) {ι : Type*} [DecidableEq ι] (T : Finset ι) (S : ι → Finset ρ)
    (hdisj : (T : Set ι).PairwiseDisjoint S) (σ : κ) :
    (coinSpace q hnn hsum).expect
        (fun ω => ∏ i ∈ T, ∏ f ∈ S i, (if ω f = σ then (1 : ℚ) else 0))
      = ∏ i ∈ T, (coinSpace q hnn hsum).expect
          (fun ω => ∏ f ∈ S i, (if ω f = σ then (1 : ℚ) else 0)) := by
  classical
  have hcollapse : ∀ ω : ρ → κ,
      (∏ i ∈ T, ∏ f ∈ S i, (if ω f = σ then (1 : ℚ) else 0))
        = ∏ f ∈ T.biUnion S, (if ω f = σ then (1 : ℚ) else 0) := by
    intro ω
    rw [Finset.prod_biUnion hdisj]
  have hfun : (fun ω : ρ → κ => ∏ i ∈ T, ∏ f ∈ S i, (if ω f = σ then (1 : ℚ) else 0))
      = (fun ω : ρ → κ => ∏ f ∈ T.biUnion S, (if ω f = σ then (1 : ℚ) else 0)) :=
    funext hcollapse
  rw [hfun, expect_indicator q hnn hsum (T.biUnion S) (fun _ => σ),
    Finset.prod_biUnion hdisj]
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [expect_indicator q hnn hsum (S i) (fun _ => σ)]

/-! ## 3. La aritmética de (16.4) -/

/-- La cola de **una** capa: con `D = α⁵t²`, `m ≤ t` indicadores y desviación `u·D/t`. -/
theorem layer_tail_arith (C u α t : ℚ) (hu : u ≠ 0) (hα : α ≠ 0) (ht : t ≠ 0) :
    C * t ^ 4 / (u * (α ^ 5 * t ^ 2) / t) ^ 8 = C / (u ^ 8 * α ^ 40 * t ^ 4) := by
  field_simp

/-- La unión sobre las `t` capas da exactamente (16.4). -/
theorem union_layers_arith (C u α t : ℚ) (hu : u ≠ 0) (hα : α ≠ 0) (ht : t ≠ 0) :
    t * (C / (u ^ 8 * α ^ 40 * t ^ 4)) = C / (u ^ 8 * α ^ 40 * t ^ 3) := by
  field_simp

/-- El caso `K₃`: una sola capa, `D = α²t`, y sale la cota mejor que anuncia la fuente. -/
theorem k3_tail_arith (C u α t : ℚ) (hu : u ≠ 0) (hα : α ≠ 0) (ht : t ≠ 0) :
    C * t ^ 4 / (u * (α ^ 2 * t)) ^ 8 = C / (u ^ 8 * α ^ 16 * t ^ 4) := by
  field_simp

/-! ## 4. El ensamblaje -/

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **(16.4), ensamblado.**  Dado el reparto del grado en capas y la cola **por capa**, la
probabilidad de que el grado se desvíe está acotada por la suma de las colas.

La hipótesis `hlayer` es exactamente el punto 3 de la estructura: la cola de una capa por
`EighthMoment.tail_bound`.  Todo lo demás —pigeonhole, unión, aritmética— es lo de arriba. -/
theorem degree_tail_bound (P : FinProb Ω) {ι : Type*} [DecidableEq ι] (Layers : Finset ι)
    (dev : ι → Ω → ℚ) {z p : ℚ} (hz : 0 < z) (hcard : 0 < Layers.card)
    (hlayer : ∀ l ∈ Layers,
      P.prob (univ.filter (fun ω => z / (Layers.card : ℚ) ≤ |dev l ω|)) ≤ p) :
    P.prob (univ.filter (fun ω => z ≤ |∑ l ∈ Layers, dev l ω|))
      ≤ (Layers.card : ℚ) * p := by
  classical
  -- el suceso está contenido en la unión de los sucesos por capa
  have hsub : univ.filter (fun ω => z ≤ |∑ l ∈ Layers, dev l ω|)
      ⊆ Layers.biUnion
          (fun l => univ.filter (fun ω => z / (Layers.card : ℚ) ≤ |dev l ω|)) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    obtain ⟨l, hlL, hl⟩ := exists_large_layer Layers (fun l => dev l ω) hz hω.2
    exact Finset.mem_biUnion.2 ⟨l, hlL, Finset.mem_filter.2 ⟨Finset.mem_univ ω, hl⟩⟩
  calc P.prob (univ.filter (fun ω => z ≤ |∑ l ∈ Layers, dev l ω|))
      ≤ P.prob (Layers.biUnion
          (fun l => univ.filter (fun ω => z / (Layers.card : ℚ) ≤ |dev l ω|))) :=
        P.prob_mono hsub
    _ ≤ ∑ l ∈ Layers,
          P.prob (univ.filter (fun ω => z / (Layers.card : ℚ) ≤ |dev l ω|)) :=
        PaperIV.SimultaneousSelection.prob_biUnion_le P Layers _
    _ ≤ ∑ _l ∈ Layers, p := Finset.sum_le_sum hlayer
    _ = (Layers.card : ℚ) * p := by rw [Finset.sum_const, nsmul_eq_mul]

end PaperIV.DegreeConcentration
