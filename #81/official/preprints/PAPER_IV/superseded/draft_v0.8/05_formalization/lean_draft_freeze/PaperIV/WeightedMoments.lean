import PaperIV.OwnerCoinMoments

/-!
# La cota de varianza **sin uniformidad**: el calendario admite la moneda pesada

`PaperIV.OwnerCoinMoments.variance_le` pide

```lean
(hp : ∀ f : ρ, q f σ = p)
```

—que la probabilidad del valor `σ` sea **la misma en todos los recursos**—. La moneda pesada de
`PaperIV.WeightedCoin` no lo cumple: `x.weight K` varía de arista a arista. Ése era el único
obstáculo localizado para instanciar el calendario sobre el coloreo pesado de Yuster.

## La observación

`hp` **no se usa en ninguna parte esencial de la prueba**. Lo que la prueba usa es:

1. la media de un bloque es `∏_{f ∈ S} q f σ` — y eso es `OwnerCoins.expect_indicator`, que ya
   está enunciado para `q` arbitraria;
2. los bloques **disjuntos** tienen covarianza exactamente cero — y eso es `Finset.prod_union`,
   que no sabe nada de uniformidad;
3. un bloque que se corta con otro tiene peso `≤` el del primero — y eso es que cada factor es
   `≤ 1`, que sale de `∑_j q f j = 1` y de la no negatividad.

`hp` sólo servía para *escribir* `p ^ |S|`. Sustituyéndolo por el peso de bloque

```
blockWeight q σ S = ∏ f ∈ S, q f σ
```

la cota sobrevive palabra por palabra, con `p ^ k` reemplazado por cualquier cota superior `B`
de los pesos de los bloques de la familia.

## Contenido

* `coin_le_one` — una moneda legal no pasa de `1` en ningún valor;
* `blockWeight`, con `blockWeight_nonneg`, `blockWeight_le_one`,
  `blockWeight_union_of_disjoint` (la covarianza cero) y `blockWeight_union_le_left`;
* `expect_block_gen`, `expect_count_gen`, `expect_count_sq_gen` — los momentos, sin `hp`;
* **`variance_le_gen`** — la cota de varianza para monedas arbitrarias;
* `blockWeight_const` y `variance_le_of_const` — la especialización que recupera
  `OwnerCoinMoments.variance_le` literalmente, como control de que la generalización es fiel.

Con esto, `PaperIV.WeightedCoin.weightedCoins` entra en el aparato de segundo momento sin
cambiar nada más.
-/

namespace PaperIV.WeightedMoments

open Finset
open PaperIV.EighthMoment
open PaperIV.OwnerCoins
open PaperIV.OwnerCoinMoments

variable {ρ V : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype V] [DecidableEq V]
variable (q : ρ → V → ℚ) (hnn : ∀ e j, 0 ≤ q e j) (hsum : ∀ e, ∑ j, q e j = 1)

/-! ## 1. El peso de un bloque -/

include hnn hsum in
/-- **Una moneda legal no pasa de `1`.**  Es un sumando de una suma de términos no negativos
que vale `1`. -/
theorem coin_le_one (e : ρ) (j : V) : q e j ≤ 1 :=
  calc q e j ≤ ∑ j' : V, q e j' :=
        Finset.single_le_sum (fun j' _ => hnn e j') (Finset.mem_univ j)
    _ = 1 := hsum e

/-- **El peso de un bloque**: la probabilidad de que todas las monedas del bloque caigan en
`σ`.  Con moneda uniforme es `p ^ |S|`; en general no se factoriza más. -/
noncomputable def blockWeight (σ : V) (S : Finset ρ) : ℚ := ∏ f ∈ S, q f σ

include hnn in
theorem blockWeight_nonneg (σ : V) (S : Finset ρ) : 0 ≤ blockWeight q σ S :=
  Finset.prod_nonneg fun f _ => hnn f σ

include hnn hsum in
theorem blockWeight_le_one (σ : V) (S : Finset ρ) : blockWeight q σ S ≤ 1 :=
  Finset.prod_le_one (fun f _ => hnn f σ) (fun f _ => coin_le_one q hnn hsum f σ)

omit [Fintype ρ] [Fintype V] [DecidableEq V] in
/-- **La covarianza cero, en forma de producto.**  Ésta es la única propiedad estructural que
la cota de varianza necesita, y no depende de la uniformidad. -/
theorem blockWeight_union_of_disjoint (σ : V) {S T : Finset ρ} (h : Disjoint S T) :
    blockWeight q σ (S ∪ T) = blockWeight q σ S * blockWeight q σ T :=
  Finset.prod_union h

include hnn hsum in
/-- **Añadir recursos no aumenta el peso**, porque cada factor es `≤ 1`. -/
theorem blockWeight_union_le_left (σ : V) (S T : Finset ρ) :
    blockWeight q σ (S ∪ T) ≤ blockWeight q σ S := by
  classical
  have hdisj : Disjoint S (T \ S) := Finset.disjoint_sdiff
  have hun : S ∪ T = S ∪ (T \ S) := Finset.union_sdiff_self_eq_union.symm
  rw [hun, blockWeight_union_of_disjoint q σ hdisj]
  have h1 : blockWeight q σ (T \ S) ≤ 1 := blockWeight_le_one q hnn hsum σ _
  have h0 : 0 ≤ blockWeight q σ S := blockWeight_nonneg q hnn σ S
  nlinarith

omit [Fintype ρ] [DecidableEq ρ] [Fintype V] [DecidableEq V] in
/-- La especialización uniforme: el peso de bloque es `p ^ |S|`. -/
theorem blockWeight_const {σ : V} {p : ℚ} (hp : ∀ f : ρ, q f σ = p) (S : Finset ρ) :
    blockWeight q σ S = p ^ S.card := by
  rw [blockWeight, Finset.prod_congr rfl (fun f _ => hp f), Finset.prod_const]

/-! ## 2. Los momentos, sin `hp` -/

/-- **La media de un bloque**, para moneda arbitraria.  Es `expect_indicator` tal cual. -/
theorem expect_block_gen (σ : V) (S : Finset ρ) :
    (coinSpace q hnn hsum).expect (fun ω => ∏ f ∈ S, (if ω f = σ then (1 : ℚ) else 0))
      = blockWeight q σ S :=
  expect_indicator q hnn hsum S (fun _ => σ)

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- **La media del conteo**, para moneda arbitraria. -/
theorem expect_count_gen (σ : V) (S : ι → Finset ρ) (T : Finset ι) :
    (coinSpace q hnn hsum).expect (blockCount S σ T)
      = ∑ i ∈ T, blockWeight q σ (S i) := by
  unfold blockCount
  rw [(coinSpace q hnn hsum).expect_sum T
    (fun i ω => ∏ f ∈ S i, (if ω f = σ then (1 : ℚ) else 0))]
  exact Finset.sum_congr rfl (fun i _ => expect_block_gen q hnn hsum σ (S i))

omit [DecidableEq ι] in
/-- **El segundo momento del conteo**, para moneda arbitraria.  El término `(i,j)` es el peso
de la **unión** de los dos bloques; sólo se factoriza cuando son disjuntos. -/
theorem expect_count_sq_gen (σ : V) (S : ι → Finset ρ) (T : Finset ι) :
    (coinSpace q hnn hsum).expect (fun ω => (blockCount S σ T ω) ^ 2)
      = ∑ i ∈ T, ∑ j ∈ T, blockWeight q σ (S i ∪ S j) := by
  classical
  have hsq : ∀ ω : ρ → V, (blockCount S σ T ω) ^ 2
      = ∑ i ∈ T, ∑ j ∈ T, ∏ f ∈ S i ∪ S j, (if ω f = σ then (1 : ℚ) else 0) := by
    intro ω
    unfold blockCount
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
      (fun j _ => prod_ind_mul ω (S i) (S j) σ))
  have hfun : (fun ω => (blockCount S σ T ω) ^ 2)
      = fun ω => ∑ i ∈ T, ∑ j ∈ T, ∏ f ∈ S i ∪ S j, (if ω f = σ then (1 : ℚ) else 0) :=
    funext hsq
  rw [hfun, (coinSpace q hnn hsum).expect_sum T
    (fun i ω => ∑ j ∈ T, ∏ f ∈ S i ∪ S j, (if ω f = σ then (1 : ℚ) else 0))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [(coinSpace q hnn hsum).expect_sum T
    (fun j ω => ∏ f ∈ S i ∪ S j, (if ω f = σ then (1 : ℚ) else 0))]
  exact Finset.sum_congr rfl (fun j _ => expect_block_gen q hnn hsum σ (S i ∪ S j))

/-! ## 3. La cota de varianza para monedas arbitrarias -/

omit [DecidableEq ι] in
/-- **La cota de varianza, sin uniformidad.**

Los pares de bloques disjuntos contribuyen **exactamente cero** —por
`blockWeight_union_of_disjoint`, que es `Finset.prod_union`— y cada par que se corta contribuye
a lo sumo una cota superior `B` del peso de bloque.

Con `q f σ = p` constante y `|S i| = k` se recupera `OwnerCoinMoments.variance_le` tomando
`B = p ^ k`; ver `variance_le_of_const`. -/
theorem variance_le_gen {σ : V} {B : ℚ} (S : ι → Finset ρ) (T : Finset ι)
    (hB : ∀ i ∈ T, blockWeight q σ (S i) ≤ B) :
    (coinSpace q hnn hsum).expect
        (fun ω => (blockCount S σ T ω - ∑ i ∈ T, blockWeight q σ (S i)) ^ 2)
      ≤ ((meetingPairs S T).card : ℚ) * B := by
  classical
  set P := coinSpace q hnn hsum with hP
  set μ : ℚ := ∑ i ∈ T, blockWeight q σ (S i) with hμ
  rw [expect_sq_dev P (blockCount S σ T) μ, expect_count_gen q hnn hsum σ S T, ← hμ,
    expect_count_sq_gen q hnn hsum σ S T]
  have hμsq : μ ^ 2
      = ∑ i ∈ T, ∑ j ∈ T, blockWeight q σ (S i) * blockWeight q σ (S j) := by
    rw [hμ, sq, Finset.sum_mul_sum]
  have hsplit : ∑ x ∈ T ×ˢ T,
        (blockWeight q σ (S x.1 ∪ S x.2)
          - blockWeight q σ (S x.1) * blockWeight q σ (S x.2))
      = (∑ i ∈ T, ∑ j ∈ T, blockWeight q σ (S i ∪ S j)) - μ ^ 2 := by
    have h1 : ∑ x ∈ T ×ˢ T, blockWeight q σ (S x.1 ∪ S x.2)
        = ∑ i ∈ T, ∑ j ∈ T, blockWeight q σ (S i ∪ S j) :=
      Finset.sum_product T T (fun x : ι × ι => blockWeight q σ (S x.1 ∪ S x.2))
    have h2 : ∑ x ∈ T ×ˢ T, blockWeight q σ (S x.1) * blockWeight q σ (S x.2)
        = ∑ i ∈ T, ∑ j ∈ T, blockWeight q σ (S i) * blockWeight q σ (S j) :=
      Finset.sum_product T T
        (fun x : ι × ι => blockWeight q σ (S x.1) * blockWeight q σ (S x.2))
    rw [Finset.sum_sub_distrib, hμsq, h1, h2]
  have hbound : ∀ x ∈ meetingPairs S T,
      blockWeight q σ (S x.1 ∪ S x.2)
        - blockWeight q σ (S x.1) * blockWeight q σ (S x.2) ≤ B := by
    intro x hx
    have hx' := Finset.mem_filter.1 hx
    have hmem := Finset.mem_product.1 hx'.1
    have h1 : blockWeight q σ (S x.1 ∪ S x.2) ≤ blockWeight q σ (S x.1) :=
      blockWeight_union_le_left q hnn hsum σ (S x.1) (S x.2)
    have h2 : blockWeight q σ (S x.1) ≤ B := hB x.1 hmem.1
    have h3 : 0 ≤ blockWeight q σ (S x.1) * blockWeight q σ (S x.2) :=
      mul_nonneg (blockWeight_nonneg q hnn σ _) (blockWeight_nonneg q hnn σ _)
    linarith
  have hmeet : ∑ x ∈ meetingPairs S T,
      (blockWeight q σ (S x.1 ∪ S x.2)
        - blockWeight q σ (S x.1) * blockWeight q σ (S x.2))
      ≤ ((meetingPairs S T).card : ℚ) * B := by
    calc ∑ x ∈ meetingPairs S T,
          (blockWeight q σ (S x.1 ∪ S x.2)
            - blockWeight q σ (S x.1) * blockWeight q σ (S x.2))
        ≤ (meetingPairs S T).card • B := Finset.sum_le_card_nsmul _ _ _ hbound
      _ = ((meetingPairs S T).card : ℚ) * B := by rw [nsmul_eq_mul]
  have hpairs : ∑ x ∈ T ×ˢ T,
      (blockWeight q σ (S x.1 ∪ S x.2)
        - blockWeight q σ (S x.1) * blockWeight q σ (S x.2))
      ≤ ((meetingPairs S T).card : ℚ) * B := by
    rw [← Finset.sum_filter_add_sum_filter_not (T ×ˢ T)
      (fun x => ¬ Disjoint (S x.1) (S x.2))]
    have hzero : ∑ x ∈ (T ×ˢ T).filter (fun x => ¬ ¬ Disjoint (S x.1) (S x.2)),
        (blockWeight q σ (S x.1 ∪ S x.2)
          - blockWeight q σ (S x.1) * blockWeight q σ (S x.2)) = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      have hd : Disjoint (S x.1) (S x.2) := not_not.1 (Finset.mem_filter.1 hx).2
      rw [blockWeight_union_of_disjoint q σ hd, sub_self]
    rw [hzero, add_zero]
    exact hmeet
  rw [hsplit] at hpairs
  have hsqμ : μ * μ = μ ^ 2 := (sq μ).symm
  linarith

omit [DecidableEq ι] in
/-- **Control: la generalización es fiel.**  Con moneda uniforme y bloques de tamaño `k`,
`variance_le_gen` da exactamente `OwnerCoinMoments.variance_le`. -/
theorem variance_le_of_const {σ : V} {p : ℚ} (hp : ∀ f : ρ, q f σ = p)
    (S : ι → Finset ρ) (T : Finset ι) {k : ℕ}
    (hk : ∀ i ∈ T, (S i).card = k) :
    (coinSpace q hnn hsum).expect
        (fun ω => (blockCount S σ T ω - ∑ i ∈ T, p ^ (S i).card) ^ 2)
      ≤ ((meetingPairs S T).card : ℚ) * p ^ k := by
  have hw : ∀ i ∈ T, blockWeight q σ (S i) ≤ p ^ k := by
    intro i hi
    rw [blockWeight_const q hp (S i), hk i hi]
  have hsum' : ∑ i ∈ T, blockWeight q σ (S i) = ∑ i ∈ T, p ^ (S i).card :=
    Finset.sum_congr rfl fun i _ => blockWeight_const q hp (S i)
  have h := variance_le_gen q hnn hsum S T hw
  rwa [hsum'] at h

end PaperIV.WeightedMoments
