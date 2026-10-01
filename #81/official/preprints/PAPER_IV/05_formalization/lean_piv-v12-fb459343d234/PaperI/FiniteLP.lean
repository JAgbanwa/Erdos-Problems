import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic.Positivity

/-!
# El programa lineal finito de empaquetamiento y cubrimiento, sobre ℚ

Interfaz mínima del PL que usa el funcional mixto `K₃`/`K₄`: una matriz de incidencia
racional `incidence : Item → Resource → ℚ`, una ganancia por ítem, y las dos familias
factibles duales entre sí.

Todo es racional a propósito. El valor óptimo tiene que ser un **número racional** porque el
modelo mixto del desarrollo está tipado en `ℚ`; una dualidad sobre `ℝ` obtenida por conos
cerrados no sirve aquí sin un argumento extra de racionalidad.

La dualidad **fuerte** con alcance está en `PaperI.FiniteLPDuality`, sobre el lema de Farkas
racional de `PaperI.RationalFarkas`. Este módulo sólo fija el vocabulario y la desigualdad
débil, que es la que orienta las dos.

El resultado de dualidad fuerte en forma cubrimiento/empaquetamiento es de Paper I; la
demostración racional de este desarrollo es independiente de aquélla, que va sobre `ℝ`.

**Procedencia.**  El *resultado* --dualidad fuerte finita en forma cubrimiento/empaquetamiento--
es de Paper I.  La *demostracion* de este fichero no lo es: Paper I la establece sobre `R`
(`EuclideanSpace`, conos simpliciales cerrados, Caratheodory conico), y el modelo mixto de
Paper IV necesita que el valor optimo sea **racional**.  Por eso aqui se reprueba sobre `Q`
por eliminacion de Fourier--Motzkin.  Se cita Paper I por el resultado; la prueba racional es
material nuevo de Paper IV.
-/

open scoped BigOperators

namespace PaperI.FiniteLP

variable {Item Resource : Type*} [Fintype Item] [Fintype Resource]

/-- Empaquetamiento fraccionario factible: pesos no negativos que respetan la capacidad
unidad de cada recurso. -/
structure PrimalFeasible (incidence : Item → Resource → ℚ) where
  /-- Peso asignado a cada ítem. -/
  weight : Item → ℚ
  /-- Los pesos son no negativos. -/
  weight_nonnegative : ∀ i, 0 ≤ weight i
  /-- Cada recurso soporta carga a lo sumo uno. -/
  capacity : ∀ e, ∑ i, incidence i e * weight i ≤ 1

/-- Cubrimiento fraccionario factible: precios no negativos que pagan la ganancia de cada
ítem. -/
structure DualFeasible (incidence : Item → Resource → ℚ) (gain : Item → ℚ) where
  /-- Precio asignado a cada recurso. -/
  price : Resource → ℚ
  /-- Los precios son no negativos. -/
  price_nonnegative : ∀ e, 0 ≤ price e
  /-- Cada ítem queda pagado por los recursos que usa. -/
  demand : ∀ i, gain i ≤ ∑ e, incidence i e * price e

/-- Valor de un empaquetamiento factible. -/
def primalValue (gain : Item → ℚ) {incidence : Item → Resource → ℚ}
    (p : PrimalFeasible incidence) : ℚ :=
  ∑ i, gain i * p.weight i

/-- Valor de un cubrimiento factible. -/
def dualValue {incidence : Item → Resource → ℚ} {gain : Item → ℚ}
    (d : DualFeasible incidence gain) : ℚ :=
  ∑ e, d.price e

/-! ## La cantidad intermedia

Las dos desigualdades de la dualidad débil pasan por la misma suma doble, leída por filas y
por columnas. Aislarla deja el argumento en dos pasos de monotonía y una conmutación. -/

/-- La carga total ponderada, `∑ᵢ ∑ₑ Aᵢₑ · pₑ · wᵢ`. -/
private def crossLoad (incidence : Item → Resource → ℚ)
    (weight : Item → ℚ) (price : Resource → ℚ) : ℚ :=
  ∑ i, ∑ e, incidence i e * price e * weight i

/-- Lectura por columnas de la misma suma doble. -/
private theorem crossLoad_comm (incidence : Item → Resource → ℚ)
    (weight : Item → ℚ) (price : Resource → ℚ) :
    crossLoad incidence weight price
      = ∑ e, price e * ∑ i, incidence i e * weight i := by
  classical
  unfold crossLoad
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- El valor primal no supera la carga cruzada: cada ítem cuesta al menos su ganancia. -/
private theorem primalValue_le_crossLoad
    {incidence : Item → Resource → ℚ} {gain : Item → ℚ}
    (p : PrimalFeasible incidence) (d : DualFeasible incidence gain) :
    primalValue gain p ≤ crossLoad incidence p.weight d.price := by
  classical
  unfold primalValue crossLoad
  refine Finset.sum_le_sum fun i _ => ?_
  have hsum : (∑ e, incidence i e * d.price e * p.weight i)
      = (∑ e, incidence i e * d.price e) * p.weight i := by
    rw [Finset.sum_mul]
  rw [hsum]
  exact mul_le_mul_of_nonneg_right (d.demand i) (p.weight_nonnegative i)

/-- La carga cruzada no supera el valor dual: cada recurso está saturado a lo sumo. -/
private theorem crossLoad_le_dualValue
    {incidence : Item → Resource → ℚ} {gain : Item → ℚ}
    (p : PrimalFeasible incidence) (d : DualFeasible incidence gain) :
    crossLoad incidence p.weight d.price ≤ dualValue d := by
  classical
  rw [crossLoad_comm]
  unfold dualValue
  refine Finset.sum_le_sum fun e _ => ?_
  have := mul_le_mul_of_nonneg_left (p.capacity e) (d.price_nonnegative e)
  simpa using this

/-- **Dualidad débil.** Todo empaquetamiento factible vale a lo sumo lo que cualquier
cubrimiento factible. -/
theorem weak_duality
    {incidence : Item → Resource → ℚ} {gain : Item → ℚ}
    (p : PrimalFeasible incidence) (d : DualFeasible incidence gain) :
    primalValue gain p ≤ dualValue d :=
  (primalValue_le_crossLoad p d).trans (crossLoad_le_dualValue p d)

end PaperI.FiniteLP
