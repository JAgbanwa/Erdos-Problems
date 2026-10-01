import ThreeRegime.TrianglePackingParity

/-!
# La cota de empaquetamiento de ternas, para todo orden

`ThreeRegime.TrianglePackingParity.six_mul_card_pieces_le` demuestra `6·|P| ≤ n(n−2)` **para `n`
par**.  Aquí se generaliza el mismo conteo por vértice a **todo `n`**:

```text
3 · |P| ≤ n · ⌊(n−1)/2⌋.
```

Con `n` par esto es exactamente `6·|P| ≤ n(n−2)`; con `n` impar da `6·|P| ≤ n(n−1)`.  Es decir:

* para `n` **par** la cota superior coincide con la obligación `n(n−2) ≤ 6·|P|`, que por tanto
  sólo puede cumplirse con igualdad —y `n ≡ 4 (mod 6)` la hace imposible, que es el contenido de
  `not_triangle_obligation_of_four_mod_six`—;
* para `n` **impar** la cota superior es `n(n−1)`, holgada frente a `n(n−2)`: el conteo por
  vértice no obstruye ningún orden impar.
-/

namespace ThreeRegime.TriplePackingBound

open Finset PaperIV PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem sum_card_filter_mem (S : Finset (Finset V)) :
    ∑ v : V, (S.filter (fun K => v ∈ K)).card = ∑ K ∈ S, K.card := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, Nat.mul_one]

/-- **La cota de empaquetamiento de ternas, sin hipótesis de paridad.**

Cada vértice soporta a lo sumo `⌊(n−1)/2⌋` triángulos, y cada triángulo se cuenta tres veces. -/
theorem three_mul_card_pieces_le (P : Packing (⊤ : SimpleGraph V))
    (htri : ∀ K ∈ P.pieces, K.card = 3) :
    3 * P.pieces.card ≤ Fintype.card V * ((Fintype.card V - 1) / 2) := by
  classical
  set n := Fintype.card V with hn
  have hper : ∀ v : V, (P.pieces.filter (fun K => v ∈ K)).card ≤ (n - 1) / 2 := by
    intro v
    have h := TrianglePackingParity.two_mul_card_pieces_at_le P htri v
    omega
  have hsum : ∑ v : V, (P.pieces.filter (fun K => v ∈ K)).card ≤ ∑ _v : V, ((n - 1) / 2) :=
    Finset.sum_le_sum fun v _ => hper v
  rw [sum_card_filter_mem, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← hn] at hsum
  have hthree : ∑ K ∈ P.pieces, K.card = 3 * P.pieces.card := by
    rw [Finset.sum_congr rfl htri, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  rw [hthree] at hsum
  exact hsum

/-- Con `n` impar la cota es `6·|P| ≤ n(n−1)`: el conteo por vértice no obstruye. -/
theorem six_mul_card_pieces_le_of_odd (P : Packing (⊤ : SimpleGraph V))
    (htri : ∀ K ∈ P.pieces, K.card = 3) (hodd : Fintype.card V % 2 = 1) :
    6 * P.pieces.card ≤ Fintype.card V * (Fintype.card V - 1) := by
  have h := three_mul_card_pieces_le P htri
  have hhalf : Fintype.card V * ((Fintype.card V - 1) / 2) * 2
      = Fintype.card V * (Fintype.card V - 1) := by
    rw [Nat.mul_assoc]
    congr 1
    omega
  omega

/-- Con `n` par se recupera `6·|P| ≤ n(n−2)`. -/
theorem six_mul_card_pieces_le_of_even (P : Packing (⊤ : SimpleGraph V))
    (htri : ∀ K ∈ P.pieces, K.card = 3) (heven : Fintype.card V % 2 = 0) :
    6 * P.pieces.card ≤ Fintype.card V * (Fintype.card V - 2) := by
  have h := three_mul_card_pieces_le P htri
  have hhalf : Fintype.card V * ((Fintype.card V - 1) / 2) * 2
      = Fintype.card V * (Fintype.card V - 2) := by
    rw [Nat.mul_assoc]
    congr 1
    omega
  omega

end ThreeRegime.TriplePackingBound
