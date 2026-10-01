import PaperIV.SplitCompleteRigidity

/-!
# La identidad de reserva

El manuscrito contiene dos veces la misma identidad, a ciento treinta líneas de distancia y sin
decir que lo son:

* como completación de cuadrado, `B_n(p) = (2n+1)²/24 − (6p−2n−1)²/24`, usada para concluir
  `B_n(p) ≤ M(n)`;
* como hecho aritmético, `6·B_n(k) + (n−3k)(n−3k+1) = n(n+1)`, usada para clasificar los núcleos.

Escrita una sola vez en su forma natural dice algo que ninguna de las dos apariciones deja ver:

```text
M(n) = B_n(k) + M(d),      d = |distancia del núcleo al centro|.
```

**El centro `k ≈ n/3` consume todo el presupuesto; cada paso que se aleja genera una reserva
`M(d)`.** De ahí salen, en una línea cada una, la cota `B_n(k) ≤ M(n)` —la reserva es no
negativa— y la clasificación de los núcleos óptimos —la reserva se anula exactamente ahí—.

## Sobre los pisos

La identidad vale **exactamente en `ℕ`, con los pisos puestos**, y por eso este módulo existe: la
versión del manuscrito pasa por la envolvente racional y toma piso después, que es informal. La
razón por la que no hay pérdida es que `6 ∣ n(n+1) − d(d+1)`, luego `n(n+1)` y `d(d+1)` tienen el
mismo resto módulo seis y los dos pisos se cancelan.

La forma **racional** es otra cosa y hay que mantenerlas separadas. Con `Mq x = x(x+1)/6` sin
piso vale la identidad de residuo

```text
(6k − 2n − 1)² = 24·Mq(d) + 1,
```

y por tanto la hipótesis de calibración de la localización, `residual² ≤ 24·δ`, **es exactamente**
`Mq(d) + 1/24 ≤ δ`: la reserva que genera salirse del centro nunca supera el defecto certificado.
Ese `1/24` no es un residuo técnico: es el término que mide por qué la cancelación no es exacta.
-/

namespace PaperIV.ReserveIdentity

open PaperIV PaperIV.SplitCompleteRigidity

/-! ## 1. El defecto central -/

/-- La distancia del núcleo `k` al centro, en la forma que hace invariante el producto
`d·(d+1)` al cambiar de rama: `n − 3k` cuando el núcleo es pequeño, `3k − n − 1` cuando es
grande. -/
def centreDefect (n k : ℕ) : ℕ := if 3 * k ≤ n then n - 3 * k else 3 * k - n - 1

/-- Las dos ramas dan el mismo producto. Es la simetría de `(n−3k)(n−3k+1)` respecto del
centro. -/
theorem centreDefect_mul_succ (n k : ℕ) :
    ((centreDefect n k : ℤ)) * ((centreDefect n k : ℤ) + 1)
      = ((n : ℤ) - 3 * k) * ((n : ℤ) - 3 * k + 1) := by
  unfold centreDefect
  by_cases h : 3 * k ≤ n
  · rw [if_pos h]
    have : ((n - 3 * k : ℕ) : ℤ) = (n : ℤ) - 3 * (k : ℤ) := by
      have : (3 * k : ℕ) ≤ n := h
      push_cast [Nat.cast_sub this]
      ring
    rw [this]
  · rw [if_neg h]
    have hk : n + 1 ≤ 3 * k := by omega
    have : ((3 * k - n - 1 : ℕ) : ℤ) = 3 * (k : ℤ) - (n : ℤ) - 1 := by
      have h1 : (n + 1 : ℕ) ≤ 3 * k := hk
      omega
    rw [this]
    ring

/-! ## 2. La identidad, exacta en `ℕ` -/

/-- El reparto exacto del presupuesto entre el valor del núcleo y la reserva. -/
theorem six_mul_baseline_add_defect (n k : ℕ) (hk : k ≤ n)
    (hle : k.choose 2 ≤ k * (n - k)) :
    n * (n + 1) = centreDefect n k * (centreDefect n k + 1) + 6 * baseline n k := by
  have hZ := six_mul_baseline_add_sq n k hk hle
  have hD := centreDefect_mul_succ n k
  have : ((n * (n + 1) : ℕ) : ℤ)
      = ((centreDefect n k * (centreDefect n k + 1) + 6 * baseline n k : ℕ) : ℤ) := by
    push_cast
    rw [hD]
    push_cast at hZ
    linarith
  exact_mod_cast this

/-- **La identidad de reserva.**  `M(n) = B_n(k) + M(d)`, con los pisos puestos y sin pérdida.

No hay redondeo informal: `n(n+1)` y `d(d+1)` difieren en un múltiplo de seis, luego tienen el
mismo resto y los dos pisos se cancelan. -/
theorem targetSize_eq_baseline_add_reserve (n k : ℕ) (hk : k ≤ n)
    (hle : k.choose 2 ≤ k * (n - k)) :
    targetSize n = baseline n k + targetSize (centreDefect n k) := by
  have h := six_mul_baseline_add_defect n k hk hle
  unfold targetSize
  rw [h, Nat.add_mul_div_left _ _ (by norm_num : 0 < 6)]
  omega

/-! ## 3. Las dos consecuencias inmediatas -/

/-- **La reserva es no negativa**, luego el valor del núcleo nunca supera el objetivo.  Es
`baseline_le_targetSize`, ahora en una línea y sin envolvente racional. -/
theorem baseline_le_targetSize_of_reserve (n k : ℕ) (hk : k ≤ n)
    (hle : k.choose 2 ≤ k * (n - k)) :
    baseline n k ≤ targetSize n := by
  rw [targetSize_eq_baseline_add_reserve n k hk hle]
  omega

/-- La reserva se anula exactamente cuando el defecto es `0` o `1`. -/
theorem targetSize_eq_zero_iff (d : ℕ) : targetSize d = 0 ↔ d ≤ 1 := by
  unfold targetSize
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨j, rfl⟩ : ∃ j, d = j + 2 := ⟨d - 2, by omega⟩
    have : 6 ≤ (j + 2) * (j + 2 + 1) := by nlinarith
    omega
  · intro h
    interval_cases d <;> norm_num

/-- **Los núcleos óptimos son exactamente los de reserva nula.**  La clasificación deja de
depender de un cálculo modular sobre los tamaños y pasa a ser una lectura de la identidad. -/
theorem baseline_eq_targetSize_iff_reserve (n k : ℕ) (hk : k ≤ n)
    (hle : k.choose 2 ≤ k * (n - k)) :
    baseline n k = targetSize n ↔ centreDefect n k ≤ 1 := by
  rw [targetSize_eq_baseline_add_reserve n k hk hle, ← targetSize_eq_zero_iff]
  omega

/-- **Coincide con `optimal_cores`.**  Reserva nula y la clasificación modular del manuscrito son
el mismo conjunto de núcleos: uno, salvo cuando `n ≡ 1 (mod 3)`, donde son dos y consecutivos.

Es la comprobación de que la lectura por reserva no cambia el enunciado, sólo su demostración. -/
theorem centreDefect_le_one_iff (n k : ℕ) :
    centreDefect n k ≤ 1 ↔ (k = (n + 1) / 3 ∨ (n % 3 = 1 ∧ k = (n + 1) / 3 + 1)) := by
  unfold centreDefect
  split <;> omega

/-! ## 4. La forma racional, y el `1/24` -/

/-- El objetivo **sin piso**.  Se mantiene separado de `targetSize` a propósito: la identidad de
residuo de abajo es falsa con el piso puesto. -/
def Mq (x : ℚ) : ℚ := x * (x + 1) / 6

/-- **La identidad de residuo.**  El residuo de la calibración es, salvo el `1`, veinticuatro
veces la reserva racional. -/
theorem sq_residual_eq (n k : ℚ) :
    (6 * k - 2 * n - 1) ^ 2 = 24 * Mq (n - 3 * k) + 1 := by
  unfold Mq
  ring

/-- **La hipótesis de calibración, leída.**  `residual² ≤ 24·δ` **es** `Mq(d) + 1/24 ≤ δ`: la
reserva que genera salirse del centro nunca supera el defecto certificado.

Con esto, la Sección 4 del manuscrito y la contabilidad de la Sección 5 son la misma afirmación
escrita en dos variables. -/
theorem residual_sq_le_iff (n k delta : ℚ) :
    (6 * k - 2 * n - 1) ^ 2 ≤ 24 * delta ↔ Mq (n - 3 * k) + 1 / 24 ≤ delta := by
  rw [sq_residual_eq]
  constructor <;> intro h <;> linarith

/-- El piso no destruye la lectura: la reserva entera nunca excede la racional. -/
theorem targetSize_le_Mq (d : ℕ) : (targetSize d : ℚ) ≤ Mq (d : ℚ) :=
  PaperIV.targetSize_cast_le_continuous d

end PaperIV.ReserveIdentity
