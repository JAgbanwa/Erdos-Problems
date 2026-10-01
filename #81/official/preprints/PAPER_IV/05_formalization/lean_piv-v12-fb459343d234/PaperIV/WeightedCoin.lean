import PaperIV.OwnerCoins
import MixedRounding.Defs

/-!
# La moneda pesada: el coloreo por la masa del LP, y su legalidad

`PaperIV.WeightedColouring` explica por qué la cadena necesita colorear las aristas
**proporcionalmente al peso fraccional** en vez de uniformemente, y certifica la aritmética.
Este módulo da el primer paso constructivo: **la moneda pesada existe y es legal**.

## La observación que lo hace barato

`OwnerCoins.coinSpace` ya está enunciado para

```
q : ρ → κ → ℚ
```

—una probabilidad **por recurso y por valor**—, no para una constante. La infraestructura
soporta el coloreo pesado de forma nativa; lo único uniforme es la instanciación
`ownerCoin κ = 1/(|κ|+1)`. No hay que rehacer `coinSpace`, `expect_indicator` ni el espacio
producto.

## La moneda

El color de una arista es **qué item se la queda**:

```
q e (some K) = si K es item de G y e ∈ pairs K entonces x.weight K, si no 0
q e none     = 1 − ∑_{K ∈ items G} [e ∈ pairs K] · x.weight K
```

## Por qué es legal, y de dónde sale

Exactamente de la restricción de capacidad del LP:

```
x.capacity : ∀ e ∈ G.edgeFinset, ∑_{K ∈ items G} [e ∈ pairs K]·x.weight K ≤ 1
```

Esa desigualdad **es** la no-negatividad de `q e none`. Y para un par que no es arista de `G`
la suma vale `0` —ningún item lo contiene, porque `pairs K ⊆ G.edgeFinset`— luego `q e none = 1`:
**los no-vecinos quedan sin color automáticamente**, sin hipótesis de densidad y sin consumir
excepcional.

Eso es, en una línea, el mecanismo que hace innecesaria la hipótesis de densidad de
`RootedK4Hdeg.hdeg_of_dense`.

## Lo que este módulo **no** hace

No rehace el calendario. `OwnerCoinMoments.variance_le` pide `hp : ∀ f, q f σ = p`, es decir que
la probabilidad de un valor sea **la misma en todos los recursos**, y la moneda pesada no cumple
eso: `x.weight K` varía de arista a arista. Generalizar esa cota —de «constante» a «acotada
inferiormente por `p`»— es el trabajo que queda, y es donde vive el resto de la corrección.
-/

namespace PaperIV.WeightedCoin

open Finset
open MixedRounding

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **La moneda pesada.**  El color de una arista es qué item se la queda; `none` es «sin
color», que es donde va la masa que el LP no usa. -/
noncomputable def weightedCoin (x : FracPacking G) (e : Sym2 V) :
    Option (Finset V) → ℚ := fun c =>
  match c with
  | some K => if K ∈ items G ∧ e ∈ pairs K then x.weight K else 0
  | none => 1 - ∑ K ∈ items G, (if e ∈ pairs K then x.weight K else 0)

/-- La masa total que los items ponen sobre una arista. -/
noncomputable def load (x : FracPacking G) (e : Sym2 V) : ℚ :=
  ∑ K ∈ items G, (if e ∈ pairs K then x.weight K else 0)

theorem load_nonneg (x : FracPacking G) (e : Sym2 V) : 0 ≤ load x e := by
  refine Finset.sum_nonneg fun K _ => ?_
  by_cases h : e ∈ pairs K
  · simpa [h] using x.weight_nonneg K
  · simp [h]

/-- **Un par que no es arista de `G` no recibe masa.**  Ningún item lo contiene, porque los
pares de un item son aristas reales. -/
theorem load_eq_zero_of_not_edge (x : FracPacking G) {e : Sym2 V}
    (he : e ∉ G.edgeFinset) : load x e = 0 := by
  classical
  refine Finset.sum_eq_zero fun K hK => ?_
  have hnot : e ∉ pairs K := fun hmem =>
    he (pairs_subset_edgeFinset (mem_items.1 hK) hmem)
  simp [hnot]

/-- **La capacidad del LP es exactamente la legalidad de la moneda.** -/
theorem load_le_one (x : FracPacking G) (e : Sym2 V) : load x e ≤ 1 := by
  classical
  by_cases he : e ∈ G.edgeFinset
  · exact x.capacity e he
  · rw [load_eq_zero_of_not_edge x he]; norm_num

/-- **La moneda pesada es no negativa.**  En `some K` porque los pesos lo son; en `none`
porque lo es la capacidad. -/
theorem weightedCoin_nonneg (x : FracPacking G) (e : Sym2 V) (c : Option (Finset V)) :
    0 ≤ weightedCoin x e c := by
  classical
  cases c with
  | none =>
      have := load_le_one x e
      simpa [weightedCoin, load] using (by linarith : (0 : ℚ) ≤ 1 - load x e)
  | some K =>
      by_cases h : K ∈ items G ∧ e ∈ pairs K
      · simpa [weightedCoin, h] using x.weight_nonneg K
      · simp [weightedCoin, h]

/-- **Y suma uno.**  Los `some K` suman la carga y `none` se lleva el resto. -/
theorem weightedCoin_sum (x : FracPacking G) (e : Sym2 V) :
    ∑ c : Option (Finset V), weightedCoin x e c = 1 := by
  classical
  have hsub : ∑ K ∈ items G, weightedCoin x e (some K)
      = ∑ K : Finset V, weightedCoin x e (some K) :=
    Finset.sum_subset (Finset.subset_univ _)
      (by intro K _ hK; simp [weightedCoin, hK])
  have hval : ∑ K ∈ items G, weightedCoin x e (some K) = load x e := by
    rw [load]
    refine Finset.sum_congr rfl fun K hK => ?_
    by_cases h : e ∈ pairs K
    · simp [weightedCoin, hK, h]
    · simp [weightedCoin, h]
  have hsome : ∑ K : Finset V, weightedCoin x e (some K) = load x e := hsub.symm.trans hval
  rw [Fintype.sum_option, hsome]
  show (1 - load x e) + load x e = 1
  ring

/-- **El espacio de monedas pesado.**  Una elección independiente por arista, con la
probabilidad de cada color proporcional al peso fraccional del item correspondiente.

Es `OwnerCoins.coinSpace` instanciado con `weightedCoin` en vez de con la constante
`ownerCoin`; la infraestructura no cambia. -/
noncomputable def weightedCoins (x : FracPacking G) :
    PaperIV.EighthMoment.FinProb (Sym2 V → Option (Finset V)) :=
  PaperIV.OwnerCoins.coinSpace (weightedCoin x)
    (weightedCoin_nonneg x) (weightedCoin_sum x)

end PaperIV.WeightedCoin
