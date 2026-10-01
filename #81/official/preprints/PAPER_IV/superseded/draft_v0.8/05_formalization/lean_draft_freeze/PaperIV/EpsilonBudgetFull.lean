import Mathlib.Tactic

/-!
# El presupuesto `ε` completo: las seis pérdidas, y dónde se paga cada una

El objetivo es `x.value − P.gain ≤ ε·n²`. La ruta de regularidad pierde en **seis** sitios, y
conviene verlos juntos porque cada uno se paga en una moneda distinta y sólo el total tiene
que caber:

| | pérdida | coeficiente de `n²` | de dónde |
|---|---|---|---|
| `L1` | truncado por patrón | `ε₁` | descartar `ψ′ < η` cuesta `k²·η·n²`; con `η = ε₁/k²` sale `ε₁` |
| `L2` | conjunto excepcional | `η_E` | `\|Exc\| ≤ η_E·\|Sym2 V\|` y `\|Sym2 V\| ≤ n²` |
| `L3` | parejas irregulares | `δ` | `≤ δk²` parejas × `t²` aristas `= δn²` |
| `L4` | basura `V₀` | `δ` | `≤ δn` vértices × `n` aristas `= δn²` |
| `L5` | **aristas dentro de partes** | `1/(2k)` | `k` partes × `C(t,2) = n²/(2k)` |
| `L6` | pérdida multiplicativa | `5β/12` | `β·x.value`, con `x.value ≤ (5/12)n²` |

## `L5` es el que se olvida

Un par de vértices de la **misma** parte no cruza dos partes, luego
`PatternTransfer.servingT` le asigna el conjunto vacío: **no recibe color, no entra en ninguna
capa, y su masa se pierde entera**. No depende de `δ` ni de `η` —no es un término de error de
la regularidad— sino sólo de `k`. Obliga a

```
k ≥ 5/(2ε)
```

que es legítimo porque Szemerédi fija `k` **después** de `ε`: `exists_equalRegularity` toma
`k₀` como parámetro. Pero si uno escribe el presupuesto sin este término, el reparto cuadra y
la prueba es falsa.

## Una corrección a lo que escribí primero

La primera versión puso `L2 = η_E/2`, suponiendo `|Sym2 V| ≈ n²/2`. **Es falso**:
`|Sym2 V| = n(n+1)/2 > n²/2`. La diferencia es `O(n)` y por tanto asintóticamente
irrelevante, pero la desigualdad tal cual estaba escrita **no es cierta para `n` finito**, y
este módulo es precisamente el que no puede permitirse eso. La cota honesta y ya demostrada en
el árbol es `PaperIV.RC01MarkedRounding.card_sym2_fin_le_sq` —`|Sym2 (Fin n)| ≤ n²` para
`n ≥ 1`—, luego `L2 = η_E`, y el reparto pasa de `η_E = 2ε/5` a `η_E = ε/5`.

## Contenido

* `inside_parts_loss` — la identidad que justifica `L5`: `k·(t²/2) = n²/(2k)` cuando `k·t = n`;
* `budget_closes` — las seis pérdidas caben en `ε·n²` bajo el reparto de `ε/5` por grupo;
* `budget_allocation` — el reparto concreto, exhibido.

Certificado aparte con `certo prove checks/epsilon_budget_full.py` (PROVED, 7 de 13 hipótesis).
`certo farkas --nonlinear` sobre el mismo sistema informa de que **no existe certificado de
grado 2**, es decir que `nlinarith` a secas no lo cierra; de ahí el paso intermedio explícito
`five_mul_inv_le` de abajo, que es exactamente lo que falta.
-/

namespace PaperIV.EpsilonBudgetFull

/-! ## 1. La pérdida que se olvida: las aristas dentro de las partes -/

/-- **`L5`, exacta.**  Con `k` partes de tamaño `t = n/k`, los pares dentro de partes son
`k·C(t,2) ≤ k·t²/2 = n²/(2k)`.

Ninguno de ellos recibe color: `servingT` sólo sirve a los pares que cruzan **dos** partes
distintas. Es una pérdida estructural, no un término de error. -/
theorem inside_parts_loss {n k t : ℚ} (hk : 0 < k) (ht : k * t = n) :
    k * (t ^ 2 / 2) = n ^ 2 / (2 * k) := by
  have hk' : k ≠ 0 := ne_of_gt hk
  have hn : n = k * t := ht.symm
  subst hn
  field_simp

/-! ## 2. El paso que `nlinarith` no encuentra solo -/

/-- Si `5 ≤ 2kε` y `invk` es el inverso de `2k`, entonces `5·invk ≤ ε`.

`certo farkas --nonlinear` certifica que el sistema completo **no** tiene certificado de grado
`2`; aislar este paso es lo que lo vuelve lineal. -/
theorem five_mul_inv_le {ε k invk : ℚ} (hL5 : 5 ≤ 2 * k * ε)
    (hinv : invk * (2 * k) = 1) (hinvnn : 0 ≤ invk) :
    5 * invk ≤ ε := by
  have h := mul_le_mul_of_nonneg_left hL5 hinvnn
  have he : invk * (2 * k * ε) = ε := by
    calc invk * (2 * k * ε) = (invk * (2 * k)) * ε := by ring
      _ = 1 * ε := by rw [hinv]
      _ = ε := one_mul ε
  rw [he] at h
  linarith

/-! ## 3. El presupuesto -/

/-- **Las seis pérdidas caben en `ε·n²`.**

El reparto es `ε/5` por grupo: truncado, excepcional, (irregulares + basura), dentro de partes,
y multiplicativa. No se pide `ε` pequeño ni las pérdidas no negativas: `certo` señaló que
sobran, y aquí no se piden. -/
theorem budget_closes {ε ε₁ ηE δ β k invk total : ℚ}
    (hL1 : ε₁ ≤ ε / 5)
    (hL2 : ηE ≤ ε / 5)
    (hL34 : 2 * δ ≤ ε / 5)
    (hL5 : 5 ≤ 2 * k * ε)
    (hinv : invk * (2 * k) = 1)
    (hinvnn : 0 ≤ invk)
    (hL6 : 5 * β / 12 ≤ ε / 5)
    (htot : total = ε₁ + ηE + 2 * δ + invk + 5 * β / 12) :
    total ≤ ε := by
  have h5 : 5 * invk ≤ ε := five_mul_inv_le hL5 hinv hinvnn
  linarith

/-- **El reparto concreto existe.**  Con `ε₁ = ε/5`, `η_E = ε/5`, `δ = ε/10`, `β = 12ε/25` y
`k` cualquiera con `k ≥ 5/(2ε)`, las cinco condiciones se cumplen con igualdad o de sobra. -/
theorem budget_allocation {ε : ℚ} (hε : 0 < ε) :
    (ε / 5 ≤ ε / 5)
      ∧ (ε / 5 ≤ ε / 5)
      ∧ (2 * (ε / 10) ≤ ε / 5)
      ∧ (5 * (12 * ε / 25) / 12 ≤ ε / 5) := by
  refine ⟨le_rfl, le_rfl, by linarith, by linarith⟩

/-- **El umbral de `k` que `L5` obliga.**  Es una condición sobre `k` y `ε` sola, y Szemerédi
la admite porque `exists_equalRegularity` recibe `k₀` como parámetro. -/
theorem k_threshold {ε k : ℚ} (hε : 0 < ε) (hk : 5 / (2 * ε) ≤ k) :
    5 ≤ 2 * k * ε := by
  rw [div_le_iff₀ (by linarith : (0:ℚ) < 2 * ε)] at hk
  linarith

end PaperIV.EpsilonBudgetFull
