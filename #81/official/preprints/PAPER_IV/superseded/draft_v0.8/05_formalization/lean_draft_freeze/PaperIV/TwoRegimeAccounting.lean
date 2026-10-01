import PaperIV.AssignmentEquivalence

/-!
# La contabilidad en DOS regímenes

Corrige un error de método de `DenseBagClosure.loss_le_of_local_fraction`, no de su
enunciado: allí **todas** las bolsas se contabilizaban con la misma cota `(5/6)|E_b|` y con
una **única** `β`, que quedaba forzada por la peor bolsa. Como las bolsas split tienen
`W*(H_b) = 2·C(p,2)`, muy por debajo de `(5/6)|E_b|`, esa `β` se iba a `1` y la cota se
vaciaba — pero el culpable era la contabilidad uniforme, no la ruta.

La ruta ya tiene **dos** teoremas de redondeo, uno por tipo de bolsa, y cada uno quiere su
propio `bagVal`:

* **split** — `SplitBagExact.split_bag_exact` es **exacto**: con `bagVal_b = W*(H_b)` la
  pérdida de redondeo de esa bolsa es **cero**.
* **densa** — `DenseBagClosure.DenseBagNibbleAt` da una fracción `1-β` de
  `bagVal_b = (5/6)|E_b|`.

`loss_le_two_regimes` hace esa contabilidad. No hay mínimo sobre bolsas y no hay una `β`
global: la `β` sólo la ven las bolsas densas.

## Efecto medido (`checks/a_dos_casos.py`)

Cota de pérdida garantizada, `/n²`:

| familia · regla | un caso | **dos casos** |
|---|---|---|
| split `p=4` · R1 | 0.2199 | **0.0486** |
| split `p=4` · R5 | 0.2199 | **0.0000** |
| split `p=5` · R1 | 0.2222 | **0.0519** |
| cadena sep4 · R1 | 0.1869 | **0.1157** |
| estrella · R1 | 0.0828 | **0.0710** |
| estrella · R5 | 0.0350 | **0.0168** |

En la familia **split** —la extremal de Erdős #81— con `R5` la cota en dos casos es
**exactamente cero**, frente a `0.22·n²` en un caso. Y la `β` forzada pasa de `1.000` a
`0.000` en casi todas las filas.

**Una fila empeora:** cadena sep4 con `R5` (0.1116 frente a 0.1019), porque allí las
bolsas densas ya fuerzan `β = 0.4` y tratar las split por `W*` pierde la holgura de
`(5/6)`. La lectura correcta es que el tipo de bolsa **no** debe fijar el tratamiento: hay
que tomar por bolsa el `bagVal` que minimice su contribución. `loss_le_two_regimes` lo
permite —`bagVal` es un parámetro libre y la partición `Bs`/`Bd` la elige quien aplica el
teorema— pero elegirlo bien es trabajo de la regla, no del teorema.

## Relación con la equivalencia

Esto **no contradice** `AssignmentEquivalence.assignmentLossOwnAt_iff_gap`. Aquella es una
equivalencia de *enunciados*: cerrar (A) es lo mismo que probar el gap cordal. Ésta es una
*estrategia de prueba* para ese enunciado, y dividir en casos es una simplificación
legítima y —según la tabla— cuantitativamente grande. Que dos afirmaciones sean
equivalentes no dice nada sobre la dificultad de sus demostraciones.
-/

namespace PaperIV.TwoRegimeAccounting

open Finset
open PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {ι : Type*} [DecidableEq ι]

/-- **Contabilidad en dos regímenes.**  Las bolsas se parten en `Bs` (tratadas de forma
**exacta**: su `bagVal` se alcanza) y `Bd` (tratadas por **fracción**: se alcanza `1-β` de
su `bagVal`).  La pérdida total es la pérdida de asignación más `β` veces el `bagVal`
**sólo de las bolsas densas**.

Ninguna `β` global, ningún mínimo sobre bolsas: ése era el defecto de
`DenseBagClosure.loss_le_of_local_fraction`. -/
theorem loss_le_two_regimes {β a : ℚ} (hβ : 0 ≤ β) {w : ℚ}
    (Bs Bd : Finset ι) (hdisj : Disjoint Bs Bd)
    (bagVal : ι → ℚ) (P : ι → Packing G)
    (hassign : w - ∑ b ∈ Bs ∪ Bd, bagVal b ≤ a)
    (hexact : ∀ b ∈ Bs, bagVal b ≤ ((P b).gain : ℚ))
    (hround : ∀ b ∈ Bd, bagVal b - ((P b).gain : ℚ) ≤ β * bagVal b) :
    w - ∑ b ∈ Bs ∪ Bd, ((P b).gain : ℚ) ≤ a + β * ∑ b ∈ Bd, bagVal b := by
  classical
  have hsplitS : ∑ b ∈ Bs ∪ Bd, bagVal b = ∑ b ∈ Bs, bagVal b + ∑ b ∈ Bd, bagVal b :=
    Finset.sum_union hdisj
  have hsplitG : ∑ b ∈ Bs ∪ Bd, ((P b).gain : ℚ)
      = ∑ b ∈ Bs, ((P b).gain : ℚ) + ∑ b ∈ Bd, ((P b).gain : ℚ) :=
    Finset.sum_union hdisj
  have hS : ∑ b ∈ Bs, bagVal b ≤ ∑ b ∈ Bs, ((P b).gain : ℚ) :=
    Finset.sum_le_sum hexact
  have hD : ∑ b ∈ Bd, bagVal b - ∑ b ∈ Bd, ((P b).gain : ℚ) ≤ β * ∑ b ∈ Bd, bagVal b := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum hround
  rw [hsplitG]
  rw [hsplitS] at hassign
  linarith

/-- El caso que usa la ruta: `Bs` son las bolsas **split**, donde
`SplitBagExact.split_bag_exact` hace que la pérdida de redondeo sea **cero**, y `Bd` las
**densas**, donde el nibble a `r = 6` da la fracción `1-β` de `(5/6)|E_b|`.

La `β` aparece multiplicando **sólo** `∑_{b ∈ Bd} (5/6)|E_b|`: las bolsas split no la ven.
Ésa es toda la diferencia con la contabilidad en un caso. -/
theorem loss_le_split_dense {β a : ℚ} (hβ : 0 ≤ β) {w : ℚ}
    (Bs Bd : Finset ι) (hdisj : Disjoint Bs Bd)
    (part : ι → Finset (Sym2 V)) (bagVal : ι → ℚ) (P : ι → Packing G)
    (hassign : w - ∑ b ∈ Bs ∪ Bd, bagVal b ≤ a)
    (hsplitExact : ∀ b ∈ Bs, bagVal b ≤ ((P b).gain : ℚ))
    (hdenseVal : ∀ b ∈ Bd, bagVal b = (5 / 6 : ℚ) * ((part b).card : ℚ))
    (hdenseGain : ∀ b ∈ Bd,
      (1 - β) * ((5 / 6 : ℚ) * ((part b).card : ℚ)) ≤ ((P b).gain : ℚ)) :
    w - ∑ b ∈ Bs ∪ Bd, ((P b).gain : ℚ)
      ≤ a + β * ∑ b ∈ Bd, (5 / 6 : ℚ) * ((part b).card : ℚ) := by
  classical
  have hround : ∀ b ∈ Bd, bagVal b - ((P b).gain : ℚ) ≤ β * bagVal b := by
    intro b hb
    rw [hdenseVal b hb]
    linarith [hdenseGain b hb]
  have h := loss_le_two_regimes hβ Bs Bd hdisj bagVal P hassign hsplitExact hround
  have hval : ∑ b ∈ Bd, bagVal b = ∑ b ∈ Bd, (5 / 6 : ℚ) * ((part b).card : ℚ) :=
    Finset.sum_congr rfl hdenseVal
  rwa [hval] at h

/-- **Todas las bolsas split.**  Si la regla de asignación produce *sólo* bolsas split
—como hace la canónica (`E01_BRIDGE_STATUS.md` §11.3)— entonces `β` desaparece por
completo y la pérdida total **es** la pérdida de asignación.

Es el caso límite que la contabilidad en un caso no sabía ver: allí la `β` forzada era `1`
y la cota quedaba vacía, mientras que aquí es exacta. -/
theorem loss_eq_assignment_of_all_split {a : ℚ} {w : ℚ}
    (Bs : Finset ι) (bagVal : ι → ℚ) (P : ι → Packing G)
    (hassign : w - ∑ b ∈ Bs, bagVal b ≤ a)
    (hexact : ∀ b ∈ Bs, bagVal b ≤ ((P b).gain : ℚ)) :
    w - ∑ b ∈ Bs, ((P b).gain : ℚ) ≤ a := by
  have hS : ∑ b ∈ Bs, bagVal b ≤ ∑ b ∈ Bs, ((P b).gain : ℚ) :=
    Finset.sum_le_sum hexact
  linarith

end PaperIV.TwoRegimeAccounting
