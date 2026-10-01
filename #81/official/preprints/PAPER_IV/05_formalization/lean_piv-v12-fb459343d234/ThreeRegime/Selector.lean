import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Capa de selección: desigualdad agregada frente a disyunción

Esta biblioteca examina la propuesta de sustituir la tricotomía

`C_centro(G) ≤ M ∨ C_extremo(G) ≤ M ∨ C_separador(G) ≤ M`

por la desigualdad **agregada**

`C_centro(G) + C_extremo(G) + C_separador(G) ≤ 3 · M(|G|)`.

Aquí se aísla exactamente lo que la capa de selección aporta y lo que no:

* la agregada (incluso en su forma con pesos arbitrarios) implica la disyunción;
* la disyunción **no** implica la agregada: la agregada es estrictamente más
  fuerte, luego es un objetivo de investigación estrictamente más difícil;
* lo único que la selección/Bellman consume es la disyunción (equivalente a
  `min ≤ M`), de modo que la agregada añade obligaciones que nadie usa.

Los módulos `CompleteState*` muestran que ese exceso de fuerza no es teórico:
en los estados completos `K_n` dos de las tres rutas fallan de verdad.
-/

namespace ThreeRegime
namespace Selector

/-- **La agregada implica la disyunción, incluso con pesos.** Si una
combinación con pesos positivos de los tres costes no supera el mismo
presupuesto ponderado, alguno de los tres costes cabe en el presupuesto. -/
theorem exists_le_of_weighted_aggregate (c₁ c₂ c₃ w₁ w₂ w₃ M : ℕ)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw₃ : 0 < w₃)
    (h : w₁ * c₁ + w₂ * c₂ + w₃ * c₃ ≤ (w₁ + w₂ + w₃) * M) :
    c₁ ≤ M ∨ c₂ ≤ M ∨ c₃ ≤ M := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h₁, h₂, h₃⟩ := hcon
  have e₁ : w₁ * M < w₁ * c₁ := Nat.mul_lt_mul_of_pos_left h₁ hw₁
  have e₂ : w₂ * M < w₂ * c₂ := Nat.mul_lt_mul_of_pos_left h₂ hw₂
  have e₃ : w₃ * M < w₃ * c₃ := Nat.mul_lt_mul_of_pos_left h₃ hw₃
  have hsum : (w₁ + w₂ + w₃) * M = w₁ * M + w₂ * M + w₃ * M := by ring
  omega

/-- Caso uniforme: la forma que se usa en un estado de Bellman. -/
theorem exists_le_of_aggregate (c₁ c₂ c₃ M : ℕ)
    (h : c₁ + c₂ + c₃ ≤ 3 * M) : c₁ ≤ M ∨ c₂ ≤ M ∨ c₃ ≤ M := by
  omega

/-- La disyunción es literalmente la forma `min ≤ M`: es lo único que la capa
de selección necesita. -/
theorem disjunction_iff_min_le (c₁ c₂ c₃ M : ℕ) :
    (c₁ ≤ M ∨ c₂ ≤ M ∨ c₃ ≤ M) ↔ min c₁ (min c₂ c₃) ≤ M := by
  simp [min_le_iff]

/-- **La agregada no es necesaria.** Hay perfiles de coste en los que una ruta
cierra y la agregada falla; por tanto la agregada es estrictamente más fuerte
que lo que el principio de Bellman consume. -/
theorem aggregate_not_necessary :
    ∃ c₁ c₂ c₃ M : ℕ,
      (c₁ ≤ M ∨ c₂ ≤ M ∨ c₃ ≤ M) ∧ ¬ (c₁ + c₂ + c₃ ≤ 3 * M) :=
  ⟨0, 3, 3, 1, Or.inl (by norm_num), by norm_num⟩

/-- Tampoco se rescata con pesos: una única ruta cara por encima del
presupuesto ponderado total destruye cualquier agregada con pesos positivos,
aunque otra ruta sí cierre. -/
theorem weighted_aggregate_fails_of_one_expensive
    (c₁ c₂ c₃ w₁ w₂ w₃ M : ℕ) (hw₃ : 0 < w₃)
    (hbig : (w₁ + w₂ + w₃) * M < c₃) :
    ¬ (w₁ * c₁ + w₂ * c₂ + w₃ * c₃ ≤ (w₁ + w₂ + w₃) * M) := by
  intro h
  have hle : c₃ ≤ w₃ * c₃ := Nat.le_mul_of_pos_left _ hw₃
  omega

/-- Forma lista para Bellman a partir de la disyunción: no hace falta la
agregada para escoger una acción admisible. -/
theorem exists_action_of_disjunction {α : Type*} (cost : α → ℕ) (M : ℕ)
    (a b c : α) (h : cost a ≤ M ∨ cost b ≤ M ∨ cost c ≤ M) :
    ∃ x : α, cost x ≤ M := by
  rcases h with h | h | h
  · exact ⟨a, h⟩
  · exact ⟨b, h⟩
  · exact ⟨c, h⟩

end Selector
end ThreeRegime
