import PaperIV.MixedRoundingAdapter
import PaperIV.UniformDual

/-!
# El régimen de pocos triángulos: tapando el umbral del emparejamiento

`PaperIV.JointTwoQuotaPhysical.mixed_physical_packing_of_partitionQuota` concluye

```
(1 − β)·(2·mass₃ x + 5·mass₄ x) ≤ P.gain
```

—que es exactamente `(1 − β)·x.value`, porque `IsItem` sólo admite `card = 3` o `card = 4` y
`gainF K = C(|K|,2) − 1` vale `2` y `5`— pero **bajo la hipótesis `C ≤ mass₃ x`**.

Ese umbral es inocuo para RC01, donde la masa de triángulos es cuadrática en `n`. Para
`MixedRounding.UniformRoundingTarget ε`, que cuantifica sobre **todo** `x`, no lo es: un packing
fraccional puro de `K₄` tiene `mass₃ x = 0` y la conclusión no dice nada. El emparejamiento de
triples necesita triples que emparejar.

## Lo que este módulo demuestra

Que el hueco cuesta `O(1)` y se tapa sin matemática nueva:

* `value_eq_masses` — `x.value = 2·mass₃ x + 5·mass₄ x`, sin hipótesis;
* `restrictToK4` — el mismo packing con los triángulos puestos a cero; sigue siendo un
  `FracPacking` porque la capacidad sólo puede bajar;
* `value_eq_restrict_add` — `x.value = (restrictToK4 x).value + 2·mass₃ x`, **con igualdad**:
  tirar los triángulos cuesta exactamente el doble de su masa;
* `lowTriangle_transfer` — **el tapón**: si `mass₃ x ≤ C` y el brazo puro de `K₄` entrega un
  packing con `(1−β)·(restrictToK4 x).value ≤ P.gain`, entonces

  ```
  x.value − P.gain ≤ β·x.value + 2·C
  ```

* `lowTriangle_target` — y con la cota dual `x.value ≤ (5/12)·n²` el presupuesto cierra: la
  pérdida `2C` es **constante en `n`**, luego se absorbe en `ε·n²` en cuanto
  `n² ≥ 4C/ε` (con `β ≤ 6ε/5`).

La aritmética está certificada aparte con `certo prove checks/low_triangle_plug.py` (PROVED,
z3, 5 de 11 hipótesis; certo señaló que `β ≤ 1` y `0 ≤ x.value` sobran, y aquí no se piden).

En el régimen `mass₃ x ≤ C` el sistema restringido es `6`-uniforme puro, y ahí el residuo
`PartitionQuotaNibbleAt 6 β` degenera al caso frontera `A = H`, que
`TwoQuotaNibble.partitionQuota_top` **demuestra** desde el freeze de Paper III. El emparejamiento
de triángulos —y con él su umbral— sólo hace falta cuando los dos brazos tienen masa.
-/

namespace PaperIV.LowTriangleReduction

open Finset
open MixedRounding

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. Las dos masas -/

/-- La masa fraccional que llevan los triángulos. -/
noncomputable def triMass (x : FracPacking G) : ℚ :=
  ∑ K ∈ (items G).filter (fun K => K.card = 3), x.weight K

/-- La masa fraccional que llevan los `K₄`. -/
noncomputable def quadMass (x : FracPacking G) : ℚ :=
  ∑ K ∈ (items G).filter (fun K => K.card = 4), x.weight K

theorem triMass_nonneg (x : FracPacking G) : 0 ≤ triMass x :=
  Finset.sum_nonneg fun K _ => x.weight_nonneg K

theorem quadMass_nonneg (x : FracPacking G) : 0 ≤ quadMass x :=
  Finset.sum_nonneg fun K _ => x.weight_nonneg K

/-- Un item que no es un triángulo es un `K₄`. -/
theorem filter_not_three (G : SimpleGraph V) [DecidableRel G.Adj] :
    (items G).filter (fun K => ¬ K.card = 3) = (items G).filter (fun K => K.card = 4) := by
  classical
  refine Finset.filter_congr ?_
  intro K hK
  have h : K.card = 3 ∨ K.card = 4 := (mem_items.1 hK).2
  constructor
  · intro _; rcases h with h3 | h4
    · exact absurd h3 (by simpa using ‹¬ K.card = 3›)
    · exact h4
  · intro h4 h3; omega

/-- **El valor del LP es `2·mass₃ + 5·mass₄`.**  Sin hipótesis: sale de que `IsItem` sólo
admite `card = 3` o `card = 4` y de que `gainF K = C(|K|,2) − 1`. -/
theorem value_eq_masses (x : FracPacking G) :
    x.value = 2 * triMass x + 5 * quadMass x := by
  classical
  rw [FracPacking.value, ← Finset.sum_filter_add_sum_filter_not (items G) (fun K => K.card = 3)]
  have h3 : ∑ K ∈ (items G).filter (fun K => K.card = 3), gainF ℚ K * x.weight K
      = 2 * triMass x := by
    rw [triMass, Finset.mul_sum]
    refine Finset.sum_congr rfl fun K hK => ?_
    have hc : K.card = 3 := (Finset.mem_filter.1 hK).2
    have hch : Nat.choose 3 2 = 3 := by decide
    have hg : gainF ℚ K = 2 := by simp only [gainF, hc, hch]; norm_num
    rw [hg]
  have h4 : ∑ K ∈ (items G).filter (fun K => ¬ K.card = 3), gainF ℚ K * x.weight K
      = 5 * quadMass x := by
    rw [filter_not_three, quadMass, Finset.mul_sum]
    refine Finset.sum_congr rfl fun K hK => ?_
    have hc : K.card = 4 := (Finset.mem_filter.1 hK).2
    have hch : Nat.choose 4 2 = 6 := by decide
    have hg : gainF ℚ K = 5 := by simp only [gainF, hc, hch]; norm_num
    rw [hg]
  rw [h3, h4]

/-! ## 2. Tirar los triángulos -/

/-- **El packing restringido al brazo `K₄`.**  Los pesos de los triángulos se ponen a cero; la
capacidad sólo puede bajar, luego sigue siendo un `FracPacking`. -/
noncomputable def restrictToK4 (x : FracPacking G) : FracPacking G where
  weight := fun K => if K.card = 4 then x.weight K else 0
  weight_nonneg := by
    intro K; by_cases h : K.card = 4
    · simpa [h] using x.weight_nonneg K
    · simp [h]
  capacity := by
    intro e he
    refine le_trans (Finset.sum_le_sum ?_) (x.capacity e he)
    intro K _
    by_cases hp : e ∈ pairs K
    · by_cases h4 : K.card = 4
      · simp [hp, h4]
      · simp [hp, h4, x.weight_nonneg K]
    · simp [hp]

theorem triMass_restrictToK4 (x : FracPacking G) : triMass (restrictToK4 x) = 0 := by
  classical
  refine Finset.sum_eq_zero fun K hK => ?_
  have hc : K.card = 3 := (Finset.mem_filter.1 hK).2
  have : ¬ K.card = 4 := by omega
  simp [restrictToK4, this]

theorem quadMass_restrictToK4 (x : FracPacking G) :
    quadMass (restrictToK4 x) = quadMass x := by
  classical
  refine Finset.sum_congr rfl fun K hK => ?_
  have hc : K.card = 4 := (Finset.mem_filter.1 hK).2
  simp [restrictToK4, hc]

/-- **Tirar los triángulos cuesta exactamente el doble de su masa.** -/
theorem value_eq_restrict_add (x : FracPacking G) :
    x.value = (restrictToK4 x).value + 2 * triMass x := by
  rw [value_eq_masses x, value_eq_masses (restrictToK4 x),
    triMass_restrictToK4, quadMass_restrictToK4]
  ring

/-! ## 3. El tapón -/

/-- **El régimen de pocos triángulos no necesita el emparejamiento.**

Si la masa de triángulos no pasa de `C` y el brazo puro de `K₄` entrega un packing con
`(1−β)·(restrictToK4 x).value ≤ P.gain`, entonces el déficit del `x` original es

```
x.value − P.gain  ≤  β·x.value + 2·C
```

La pérdida adicional `2·C` es **constante en `n`**. -/
theorem lowTriangle_transfer {x : FracPacking G} {P : Packing G} {β C : ℚ}
    (hβ0 : 0 ≤ β) (hlow : triMass x ≤ C)
    (hP : (1 - β) * (restrictToK4 x).value ≤ (P.gain : ℚ)) :
    x.value - (P.gain : ℚ) ≤ β * x.value + 2 * C := by
  have hsplit := value_eq_restrict_add x
  have htri := triMass_nonneg x
  nlinarith [hP, hsplit, htri, hlow, hβ0]

/-- **Y el presupuesto cierra.**  Con la cota dual `x.value ≤ (5/12)·n²`, basta `β ≤ (6/5)·ε`
y `4·C ≤ ε·n²` para que el déficit quepa en `ε·n²`.

Obsérvese que la segunda condición es sobre `n`, no sobre `G`: `C` es una constante absoluta del
emparejamiento, luego se cumple para todo `n ≥ √(4C/ε)`. Ése es el contenido del tapón. -/
theorem lowTriangle_target {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x : FracPacking G} {P : Packing G} {β C ε : ℚ}
    (hβ0 : 0 ≤ β) (hβε : β ≤ (6 / 5) * ε)
    (hC : 4 * C ≤ ε * (n : ℚ) ^ 2)
    (hlow : triMass x ≤ C)
    (hP : (1 - β) * (restrictToK4 x).value ≤ (P.gain : ℚ)) :
    x.value - (P.gain : ℚ) ≤ ε * (n : ℚ) ^ 2 := by
  have hval : x.value ≤ (5 / 12 : ℚ) * (n : ℚ) ^ 2 := by
    have h := PaperIV.UniformDual.value_le_of_card
      (PaperIV.MixedRoundingAdapter.toFarFrac x)
    rwa [PaperIV.MixedRoundingAdapter.value_toFarFrac] at h
  have hstep := lowTriangle_transfer hβ0 hlow hP
  nlinarith [hstep, hval, hC, hβε, hβ0]

end PaperIV.LowTriangleReduction
