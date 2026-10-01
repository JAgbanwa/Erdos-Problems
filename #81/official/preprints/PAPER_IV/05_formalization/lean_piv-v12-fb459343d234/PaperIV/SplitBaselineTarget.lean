import PaperIV.SharpEnvelope
import PaperIV.TargetEnvelope

/-!
# La línea de base del split nunca supera el objetivo

Este módulo cierra el último paso numérico de `NearPackingSupplyAt`: el que pide

```
|completion G P| ≤ targetSize n
```

a partir de la cuenta física de RD09.

## El hecho

`sharpEnvelope n = (2n+1)²/24` y `targetSize n = ⌊n(n+1)/6⌋`, y sobre los racionales

```
sharpEnvelope n − n(n+1)/6 = 1/24
```

**exactamente** — una constante, independiente de `n`. Como toda `splitBaseline n p` con `p`
entero es un entero y está por debajo de `sharpEnvelope n`, ese `1/24` nunca alcanza para cruzar
al siguiente entero. Por tanto

```
splitBaseline n p ≤ targetSize n        para todo p
```

y la desigualdad es **ajustada**: hay igualdad en el `p` óptimo (comprobado en `n = 7, 100, 1001,
99999`).

## Por qué importa para `NearPackingSupplyAt`

`NearRegimePackingInterface.exists_cliquePartition_of_physicalAccounts` pide hoy una hipótesis
numérica `hbound`:

```
splitBaseline order split − |missingEdges|/20 − |rootLossEdges|/2 ≤ t
```

Con `t = targetSize n` esa hipótesis **sobra**: el descuento `−m/20 − A/2` es no positivo y la
línea de base ya está por debajo del objetivo. El constructor local no tiene que demostrar
ninguna cota numérica sobre `targetSize`; le basta entregar el packing con sus cuentas.

## La prueba, en una línea

`24·S ≤ (2n+1)² = 4·n(n+1) + 1`, y de la división natural `n(n+1) ≤ 6·T + 5`, luego
`24·S ≤ 24·T + 21`. Como `S` y `T` son enteros y `21 < 24`, sale `S ≤ T`. La integralidad es
esencial: sobre los racionales la desigualdad es falsa por ese `1/24`.
-/

namespace PaperIV.SplitBaselineTarget

open PaperIV

/-! ## 1. El envelope, en la forma que hace falta -/

/-- `24·sharpEnvelope n = 4·n(n+1) + 1`. -/
theorem sharpEnvelope_mul_24 (n : ℚ) :
    24 * sharpEnvelope n = 4 * (n * (n + 1)) + 1 := by
  rw [sharpEnvelope]
  ring

/-- Toda línea de base está bajo el envelope: la diferencia es un cuadrado. -/
theorem splitBaseline_le_sharpEnvelope (n p : ℚ) :
    splitBaseline n p ≤ sharpEnvelope n := by
  have h := sharpEnvelope_sub_splitBaseline n p
  have hsq : (0 : ℚ) ≤ (6 * p - 2 * n - 1) ^ 2 / 24 := by positivity
  linarith

/-! ## 2. El paso de integralidad -/

/-- **La línea de base no supera el objetivo.**

`S` es cualquier entero que realice `splitBaseline n p`; en la construcción es el número de
piezas de la partición del split, que es entero por serlo `p(p−1)/2`.

La hipótesis de integralidad no es técnica: sobre `ℚ` el enunciado es **falso**, porque
`sharpEnvelope n` excede `n(n+1)/6` en exactamente `1/24`. -/
theorem splitBaseline_le_targetSize {n : ℕ} {p : ℚ} {S : ℤ}
    (hS : (S : ℚ) = splitBaseline (n : ℚ) p) :
    S ≤ (targetSize n : ℤ) := by
  -- la división natural: n(n+1) = 6·T + r con r < 6
  have hdiv := Nat.div_add_mod (n * (n + 1)) 6
  have hmod : (n * (n + 1)) % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hTnat : n * (n + 1) ≤ 6 * targetSize n + 5 := by
    rw [targetSize]; omega
  have hTnatQ : ((n : ℚ) * ((n : ℚ) + 1)) ≤ 6 * (targetSize n : ℚ) + 5 := by
    have : ((n * (n + 1) : ℕ) : ℚ) ≤ ((6 * targetSize n + 5 : ℕ) : ℚ) := by
      exact_mod_cast hTnat
    push_cast at this
    linarith
  -- 24·S ≤ 4·n(n+1) + 1
  have hup : (24 : ℚ) * (S : ℚ) ≤ 4 * ((n : ℚ) * ((n : ℚ) + 1)) + 1 := by
    rw [hS, ← sharpEnvelope_mul_24]
    have := splitBaseline_le_sharpEnvelope (n : ℚ) p
    linarith
  -- luego 24·S ≤ 24·T + 21
  have hchain : (24 : ℚ) * (S : ℚ) ≤ 24 * (targetSize n : ℚ) + 21 := by
    linarith
  -- integralidad
  have hZ : (24 : ℤ) * S ≤ 24 * (targetSize n : ℤ) + 21 := by
    exact_mod_cast hchain
  omega

/-! ## 3. La forma que el constructor consume -/

/-- **El descuento RD09 no hace falta para llegar al objetivo.**

Si el recuento de la partición está bajo `splitBaseline − m/20 − A/2`, está bajo `targetSize n`
sin más hipótesis: el descuento es no positivo y la línea de base ya cabe.

Es la eliminación de la hipótesis `hbound` de
`NearRegimePackingInterface.exists_cliquePartition_of_physicalAccounts` cuando `t = targetSize n`. -/
theorem count_le_targetSize_of_paid {n : ℕ} {p m A : ℚ} {S count : ℤ}
    (hS : (S : ℚ) = splitBaseline (n : ℚ) p)
    (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hpaid : (count : ℚ) ≤ (S : ℚ) - m / 20 - A / 2) :
    count ≤ (targetSize n : ℤ) := by
  have hbase := splitBaseline_le_targetSize hS
  have hQ : (count : ℚ) ≤ (S : ℚ) := by linarith
  have hZ : count ≤ S := by exact_mod_cast hQ
  omega

end PaperIV.SplitBaselineTarget
