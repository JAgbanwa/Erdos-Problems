import ExactReduction.ShellObstruction
import ThreeRegime.CentreDefectArithmetic

/-!
# El presupuesto de la acción "borrar una clique"

La acción del separador borra una clique `S` y recurre sobre lo que queda.
Con la convención de no interferencia —las piezas locales no pueden consumir
aristas internas de un hijo, porque ésas las paga el hijo— cada pieza local
tiene a lo sumo un vértice del hijo.  Eso es exactamente la noción
`ExactReduction.ShellObstruction.ShellCover R S` con el hijo `R` en el papel
protegido y la clique borrada `S` en el papel consumible.

Aquí se demuestra la cota de presupuesto complementaria a
`leafShell_reduction_fails` (que cubre el régimen `|R| ≤ |S|`): en el régimen
opuesto `|R| ≥ |S| + 2`, la acción tampoco cabe:

```text
M(|S| + |R|) < (número de piezas locales) + M(|R|).
```

Es decir, en cuanto el hijo es dos vértices mayor que la clique borrada, pagar
las aristas cruzadas sin consumir aristas del hijo excede el presupuesto agudo,
para cualquier cubrimiento admisible y sin ninguna cota de orden sobre las
piezas.
-/

namespace ThreeRegime

open PaperIV ExactReduction.ShellObstruction Finset

/-- Comparación aritmética: coste cruzado mínimo frente al presupuesto
disponible tras la recursión. -/
theorem crossing_cost_exceeds_budget (s r : ℕ) (hs : 1 ≤ s) (hr : s + 2 ≤ r) :
    PaperIV.targetSize (s + r) + Nat.choose s 2 < s * r + PaperIV.targetSize r := by
  have hchoose : 2 * Nat.choose s 2 = s * (s - 1) := two_mul_choose_two s
  have h1 : 6 * PaperIV.targetSize (s + r) ≤ (s + r) * (s + r + 1) := by
    rw [PaperIV.targetSize, Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  have h2 : r * (r + 1) = 6 * PaperIV.targetSize r + r * (r + 1) % 6 := by
    rw [PaperIV.targetSize]
    omega
  have h3 : r * (r + 1) % 6 < 6 := Nat.mod_lt _ (by norm_num)
  obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hchoose
  have key : (j + 1 + r) * (j + 1 + r + 1) + 3 * ((j + 1) * j) + 6 ≤
      6 * ((j + 1) * r) + r * (r + 1) := by nlinarith [hr]
  omega

/-- **La acción de borrar una clique excede el presupuesto cuando el hijo es
mayor.**  Cota inferior válida para cualquier cubrimiento local admisible, sin
restricción de orden en las piezas. -/
theorem clique_removal_over_budget {V : Type*} [DecidableEq V] {S R : Finset V}
    (hd : Disjoint R S) (C : ShellCover R S)
    (hs : 1 ≤ S.card) (hr : S.card + 2 ≤ R.card) :
    PaperIV.targetSize (S.card + R.card) <
      C.pieces.card + PaperIV.targetSize R.card := by
  have hlow := shellCover_card_ge hd C
  have hcomm : R.card * S.card = S.card * R.card := Nat.mul_comm _ _
  have harith := crossing_cost_exceeds_budget S.card R.card hs hr
  omega

end ThreeRegime
