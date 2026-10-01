import FarExploration.CleanupThreshold

/-!
# La cota inferior del umbral, para **cualquier** familia rígida de grafos

`FarExploration.CleanupThreshold.threshold_gt` obtiene una cota inferior del umbral de la
limpieza a partir de una familia concreta —la unión de triángulos disjuntos—.  El argumento no
usa nada de esa familia salvo tres cosas:

1. que su sistema de items sea **rígido** (cada arista en un único item),
2. que todos sus items sean **triángulos**, y
3. cuántos items tiene.

Este módulo aísla exactamente eso: `rigid_threshold_gt` es la misma cota inferior enunciada para
un grafo arbitrario con esas dos propiedades.  De ese modo la cota mejora automáticamente en
cuanto se exhibe una familia rígida con más triángulos, que es lo que hace
`FarExploration.CleanupRigidVerdict` con el grafo de Ruzsa–Szemerédi.

**Régimen.**  El enunciado no pide nada a `gam`, `Cst`, `m`, `xi` salvo `gam ≤ 1` y las dos
desigualdades numéricas que aparecen como hipótesis (masa suficiente y pérdida forzada); en
particular cubre el régimen de la aplicación `m = eps/30`, `xi = eps/4`, `gam` pequeño.
-/

namespace FarExploration.RigidThreshold

open Finset MixedRounding FarExploration.CleanupLP FarExploration.CleanupBridge
open FarExploration.CleanupThreshold

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- **El empaquetamiento rígido de un grafo**: peso `1` sobre cada item.  Es admisible porque,
por rigidez, cada arista soporta un único item. -/
noncomputable def rigidPacking (hrigid : (graphSystem G).Rigid) : FracPacking G :=
  toPacking ((graphSystem G).rigidFrac hrigid)

lemma rigidPacking_value (hrigid : (graphSystem G).Rigid)
    (hthree : ∀ S ∈ (graphSystem G).supports, S.card = 3) :
    (rigidPacking G hrigid).value = 2 * ((graphSystem G).supports.card : ℚ) := by
  rw [rigidPacking, toPacking_value, ItemSystem.rigidFrac_value _ _ hthree]

lemma rigidPacking_mass (hrigid : (graphSystem G).Rigid)
    (hthree : ∀ S ∈ (graphSystem G).supports, S.card = 3) :
    PaperIV.JointTwoQuotaPhysical.triangleMass (rigidPacking G hrigid)
      = ((graphSystem G).supports.card : ℝ) := by
  rw [rigidPacking, toPacking_mass, ItemSystem.rigidFrac_mass _ _ hthree]
  push_cast
  ring

/-- **La rigidez aplasta el valor.**  En un grafo rígido de items triangulares, todo
empaquetamiento fraccional con codegrado ponderado `≤ gam` tiene valor `≤ 2·gam·(número de
items)`: la restricción de codegrado sobre dos aristas del mismo triángulo dice literalmente que
el peso del triángulo es `≤ gam`. -/
lemma value_le_of_codeg (hrigid : (graphSystem G).Rigid)
    (hthree : ∀ S ∈ (graphSystem G).supports, S.card = 3) (gam : ℝ) (y : FracPacking G)
    (hcod : ∀ e f : Sym2 (Fin n), e ≠ f →
      ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter
        (fun S => e ∈ S ∧ f ∈ S), inducedWeight y S ≤ gam) :
    ((y.value : ℚ) : ℝ) ≤ 2 * gam * ((graphSystem G).supports.card : ℝ) := by
  have hcod' : ∀ e f : Sym2 (Fin n), e ≠ f → (((ofPacking y).codeg e f : ℚ) : ℝ) ≤ gam := by
    intro e f hef
    rw [← ofPacking_codeg]
    exact hcod e f hef
  have h := Frac.value_le_of_rigid_three hrigid hthree (ofPacking y) gam hcod'
  rwa [ofPacking_value] at h

/-- **Cota inferior del umbral a partir de una familia rígida arbitraria.**

Si `N₀` es un umbral válido para la limpieza y `G` es un grafo sobre `Fin n` cuyo sistema de
items es rígido y de rango tres, con al menos `T` items, y si en ese `n`

* la masa `T` cumple la hipótesis cuadrática de `CodegreeCleanupAt`, y
* la pérdida forzada `2(1-gam)·T` supera la pérdida admitida `xi·n²`,

entonces `n < N₀`.  Ningún umbral válido puede llegar tan abajo. -/
theorem rigid_threshold_gt (gam Cst : ℝ) (m xi : ℚ) (hgam : gam ≤ 1) (N₀ : ℕ)
    (hN : CleanupAtWith gam Cst m xi N₀)
    (hrigid : (graphSystem G).Rigid)
    (hthree : ∀ S ∈ (graphSystem G).supports, S.card = 3)
    (T : ℝ) (hT : T ≤ ((graphSystem G).supports.card : ℝ))
    (hmass : (m : ℝ) * (n : ℝ) ^ 2 - 1 ≤ T)
    (hloss : (xi : ℝ) * (n : ℝ) ^ 2 < 2 * (1 - gam) * T) :
    n < N₀ := by
  classical
  by_contra hcon
  push_neg at hcon
  set B : ℝ := ((graphSystem G).supports.card : ℝ) with hB
  have hmass' : (m : ℝ) * (n : ℝ) ^ 2 - 1
      ≤ PaperIV.JointTwoQuotaPhysical.triangleMass (rigidPacking G hrigid) := by
    rw [rigidPacking_mass G hrigid hthree]
    linarith
  obtain ⟨y, hcod, -, hlossy⟩ := hN n hcon G (rigidPacking G hrigid) hmass'
  have hyval : ((y.value : ℚ) : ℝ) ≤ 2 * gam * B := value_le_of_codeg G hrigid hthree gam y hcod
  have hxval : (((rigidPacking G hrigid).value : ℚ) : ℝ) = 2 * B := by
    rw [rigidPacking_value G hrigid hthree]
    push_cast
    ring
  have hlossR : (((rigidPacking G hrigid).value : ℚ) : ℝ) - ((y.value : ℚ) : ℝ)
      ≤ (xi : ℝ) * (n : ℝ) ^ 2 := by
    have hq := (Rat.cast_le (K := ℝ)).2 hlossy
    push_cast at hq
    linarith
  have hscale : 2 * (1 - gam) * T ≤ 2 * (1 - gam) * B :=
    mul_le_mul_of_nonneg_left hT (by linarith)
  linarith

end FarExploration.RigidThreshold
