import PaperIV.RegularityFormat

/-!
# El patrón doblado de `K₃`, y el enganche regularidad → conteo

Dos bloques del contrato de RC01 (§20.5): «Conteos» —la mitad del segundo momento— y el
enganche de «Regularidad adaptada» con los lemas de conteo.

## El patrón doblado

`RootedCountingBridge.sum_fiber_card_sq` reduce el segundo momento enraizado al conteo de
**pares de copias con la misma raíz**, que es el conteo de un patrón:

```
K₃ :  patrón r=3, ℓ=3   →  doblado: 4 vértices, 5 parejas
K₄ :  patrón r=4, ℓ=6   →  doblado: 6 vértices, 11 parejas
```

El doblado de `K₃` sobre la arista raíz `cd` es: dos triángulos `acd` y `bcd` que comparten
`cd`.  Sus cinco parejas son `CD, AC, AD, BC, BD`.

**Ese patrón ya estaba construido**: es `TelescopeK4Step2.books`, el objeto intermedio del
telescopado de `K₄` (un `K₄` al que le falta la pareja `AB`).  El lema de conteo para él sale
de las piezas ya demostradas —`step_two_K4`, `step_three_K4` y `counting_lemma_K3`— con
constante `4`.

Obsérvese que la pareja raíz `CD` **no** necesita hipótesis de discrepancia: entra exacta por
`TelescopeK3.last_step_free`.  Sólo se piden las cuatro parejas «de página».

## Lo que queda

El doblado de `K₄` (6 vértices, 11 parejas) **no** está aquí.  Su telescopado son diez pasos
y no se obtiene por recorte del de `K₄`.  Lo natural sería un lema de conteo de patrón
general por inducción sobre el conjunto de parejas, que subsumiría los cuatro casos.
-/

namespace PaperIV.DoubledPattern

open Finset
open PaperIV.OneStepEstimate
open PaperIV.TelescopeK3
open PaperIV.TelescopeK4
open PaperIV.TelescopeK4Step2
open PaperIV.TelescopeK4Full
open PaperIV.RegularityFormat

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α} [DecidableRel G.Adj]

/-! ## 1. El lema de conteo del patrón doblado -/

set_option maxHeartbeats 1000000 in
/-- **Conteo del patrón doblado de `K₃`.**  Dos triángulos que comparten la arista raíz, con
las cuatro parejas de página en el formato (3.2).  Constante `4`.

Es el conteo que consume `RootedCountingBridge.second_moment_of_pattern_counts` en su segundo
argumento. -/
theorem counting_lemma_book {ε : ℚ} (hε : 0 ≤ ε) {A B C D : Finset α}
    (hAC : DiscrepAt G ε (G.edgeDensity A C) A C)
    (hAD : DiscrepAt G ε (G.edgeDensity A D) A D)
    (hBC : DiscrepAt G ε (G.edgeDensity B C) B C)
    (hBD : DiscrepAt G ε (G.edgeDensity B D) B D) :
    |((books G A B C D).card : ℚ)
        - G.edgeDensity A C * G.edgeDensity A D
            * (G.edgeDensity B C * G.edgeDensity B D * G.edgeDensity C D)
            * A.card * B.card * C.card * D.card|
      ≤ 4 * (ε * A.card * B.card * C.card * D.card) := by
  classical
  set T : ℚ := (((B ×ˢ C ×ˢ D).filter
      fun p => G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2).card : ℚ) with hT
  set Bk : ℚ := ((books G A B C D).card : ℚ) with hBk
  set Fn : ℚ := ((fans G A B C D).card : ℚ) with hFn
  set dAC : ℚ := G.edgeDensity A C with hdAC
  set dAD : ℚ := G.edgeDensity A D with hdAD
  set dBC : ℚ := G.edgeDensity B C with hdBC
  set dBD : ℚ := G.edgeDensity B D with hdBD
  set dCD : ℚ := G.edgeDensity C D with hdCD
  set a : ℚ := (A.card : ℚ) with ha
  set b : ℚ := (B.card : ℚ) with hb
  set c : ℚ := (C.card : ℚ) with hc
  set d : ℚ := (D.card : ℚ) with hd
  have dAC0 : 0 ≤ dAC := G.edgeDensity_nonneg A C
  have dAC1 : dAC ≤ 1 := G.edgeDensity_le_one A C
  have dAD0 : 0 ≤ dAD := G.edgeDensity_nonneg A D
  have dAD1 : dAD ≤ 1 := G.edgeDensity_le_one A D
  have ha0 : (0 : ℚ) ≤ a := by positivity
  -- paso 1: sustituir la pareja `AC`
  have h2 := step_two_K4 (G := G) hε hAC (A := A) (B := B) (C := C) (D := D)
  have e2 : ∑ q ∈ G.interedges B D,
      (((nbrs G A q.2).card : ℚ) * ((nbrs2 G C q).card : ℚ)) = Fn := by
    rw [hFn, fans_eq_sum_bd]; push_cast; ring
  rw [e2] at h2
  -- paso 2: sustituir la pareja `AD`
  have h3 := step_three_K4 (G := G) hε hAD (A := A) (B := B) (C := C) (D := D)
  -- paso 3: el triángulo restante, por el lema de `K₃`
  have h4 := PaperIV.TelescopeK3Full.counting_lemma_K3 (G := G) hε hBC hBD
  have b1 : |Bk - dAC * Fn| ≤ ε * a * b * c * d := by
    calc |Bk - dAC * Fn| ≤ b * d * (ε * a * c) := h2
      _ = ε * a * b * c * d := by ring
  have b2 : |dAC * Fn - dAC * (dAD * a * T)| ≤ ε * a * b * c * d := by
    have hfac : dAC * Fn - dAC * (dAD * a * T) = dAC * (Fn - dAD * a * T) := by ring
    rw [hfac, abs_mul, abs_of_nonneg dAC0]
    have habs : (0 : ℚ) ≤ |Fn - dAD * a * T| := abs_nonneg _
    calc dAC * |Fn - dAD * a * T| ≤ 1 * |Fn - dAD * a * T| :=
          mul_le_mul_of_nonneg_right dAC1 habs
      _ = |Fn - dAD * a * T| := one_mul _
      _ ≤ b * c * (ε * a * d) := h3
      _ = ε * a * b * c * d := by ring
  have b3 : |dAC * (dAD * a * T) - dAC * dAD * (dBC * dBD * dCD) * a * b * c * d|
      ≤ 2 * (ε * a * b * c * d) := by
    have hfac : dAC * (dAD * a * T) - dAC * dAD * (dBC * dBD * dCD) * a * b * c * d
        = (dAC * dAD * a) * (T - dBC * dBD * dCD * b * c * d) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (mul_nonneg (mul_nonneg dAC0 dAD0) ha0)]
    have habs : (0 : ℚ) ≤ |T - dBC * dBD * dCD * b * c * d| := abs_nonneg _
    have hd2 : dAC * dAD ≤ 1 := by
      calc dAC * dAD ≤ dAC * 1 := mul_le_mul_of_nonneg_left dAD1 dAC0
        _ = dAC := mul_one _
        _ ≤ 1 := dAC1
    have hp : dAC * dAD * a ≤ a := by
      calc dAC * dAD * a ≤ 1 * a := mul_le_mul_of_nonneg_right hd2 ha0
        _ = a := one_mul a
    calc (dAC * dAD * a) * |T - dBC * dBD * dCD * b * c * d|
        ≤ a * |T - dBC * dBD * dCD * b * c * d| := mul_le_mul_of_nonneg_right hp habs
      _ ≤ a * (2 * (ε * b * c * d)) := mul_le_mul_of_nonneg_left h4 ha0
      _ = 2 * (ε * a * b * c * d) := by ring
  obtain ⟨l1, u1⟩ := abs_le.1 b1
  obtain ⟨l2, u2⟩ := abs_le.1 b2
  obtain ⟨l3, u3⟩ := abs_le.1 b3
  rw [abs_le]
  constructor <;> linarith

/-! ## 2. Enganche: de la partición regular a los conteos -/

variable {β : Type*} [DecidableEq β] [Fintype β] {H : SimpleGraph β} [DecidableRel H.Adj]

/-- **`K₃` sobre partes de una partición regular.**  Tres partes buenas, dos parejas no
excepcionales, y el conteo de triángulos transversales queda determinado. -/
theorem counting_K3_of_regular {δ : ℚ} (hδ : 0 ≤ δ) (R : EqualRegularity H δ)
    {A B C : Finset β} (hA : A ∈ R.parts) (hB : B ∈ R.parts) (hC : C ∈ R.parts)
    (hAB : A ≠ B) (hAC : A ≠ C)
    (nAB : (A, B) ∉ R.bad) (nAC : (A, C) ∉ R.bad) :
    |((((A ×ˢ B ×ˢ C).filter
          fun p => H.Adj p.1 p.2.1 ∧ H.Adj p.1 p.2.2 ∧ H.Adj p.2.1 p.2.2).card : ℚ))
        - H.edgeDensity A B * H.edgeDensity A C * H.edgeDensity B C
            * A.card * B.card * C.card|
      ≤ 2 * (δ * A.card * B.card * C.card) :=
  PaperIV.TelescopeK3Full.counting_lemma_K3 hδ
    (R.discrep A hA B hB hAB nAB) (R.discrep A hA C hC hAC nAC)

/-- **`K₄` sobre partes de una partición regular.** -/
theorem counting_K4_of_regular {δ : ℚ} (hδ : 0 ≤ δ) (R : EqualRegularity H δ)
    {A B C D : Finset β} (hA : A ∈ R.parts) (hB : B ∈ R.parts) (hC : C ∈ R.parts)
    (hD : D ∈ R.parts)
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C) (hBD : B ≠ D)
    (nAB : (A, B) ∉ R.bad) (nAC : (A, C) ∉ R.bad) (nAD : (A, D) ∉ R.bad)
    (nBC : (B, C) ∉ R.bad) (nBD : (B, D) ∉ R.bad) :
    |((PaperIV.TelescopeK4.k4s H A B C D).card : ℚ)
        - H.edgeDensity A B * H.edgeDensity A C * H.edgeDensity A D
            * (H.edgeDensity B C * H.edgeDensity B D * H.edgeDensity C D)
            * A.card * B.card * C.card * D.card|
      ≤ 5 * (δ * A.card * B.card * C.card * D.card) :=
  PaperIV.TelescopeK4Full.counting_lemma_K4 hδ
    (R.discrep A hA B hB hAB nAB) (R.discrep A hA C hC hAC nAC)
    (R.discrep A hA D hD hAD nAD) (R.discrep B hB C hC hBC nBC)
    (R.discrep B hB D hD hBD nBD)

/-- **Patrón doblado sobre partes de una partición regular.**  Es el conteo que cierra el
segundo momento para `K₃`. -/
theorem counting_book_of_regular {δ : ℚ} (hδ : 0 ≤ δ) (R : EqualRegularity H δ)
    {A B C D : Finset β} (hA : A ∈ R.parts) (hB : B ∈ R.parts) (hC : C ∈ R.parts)
    (hD : D ∈ R.parts)
    (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C) (hBD : B ≠ D)
    (nAC : (A, C) ∉ R.bad) (nAD : (A, D) ∉ R.bad)
    (nBC : (B, C) ∉ R.bad) (nBD : (B, D) ∉ R.bad) :
    |((books H A B C D).card : ℚ)
        - H.edgeDensity A C * H.edgeDensity A D
            * (H.edgeDensity B C * H.edgeDensity B D * H.edgeDensity C D)
            * A.card * B.card * C.card * D.card|
      ≤ 4 * (δ * A.card * B.card * C.card * D.card) :=
  counting_lemma_book hδ
    (R.discrep A hA C hC hAC nAC) (R.discrep A hA D hD hAD nAD)
    (R.discrep B hB C hC hBC nBC) (R.discrep B hB D hD hBD nBD)

end PaperIV.DoubledPattern
