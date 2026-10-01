import PaperIV.PatternTransfer

/-!
# El packing esparcido `x′`, y la condición exacta que lo hace legal

El gate con holgura (`RC01MarkedRounding.exists_packing_loss_le_of_slackMarkedQuota`) pide
**codegrado pesado pequeño**, y eso es falso para un `x` arbitrario: un solo `K₄` de peso `1`
es un packing fraccional legal con codegrado `1`. Hay que sustituir `x` por un `x′` que reparta
la masa.

`x′` reparte la masa transferida de cada patrón **uniformemente entre sus copias**:

```
x′(K)  =  ∑_{H patrón superviviente}  [K es copia de H] · ψ′(H) / #copias(H)
```

## La cuenta, y por qué la condición de reparto no es opcional

La carga de una arista bajo `x′` es

```
load(e)  =  ∑_H  ψ′(H) · #{copias de H por e} / #copias(H)
```

y `PatternTransfer.transfer_capacity` da `∑_{H sirve a e} ψ′(H) ≤ densT(e)`. Luego

```
load(e)  ≤  máx_H ( #{copias por e} / #copias(H) ) · densT(e)
```

y la capacidad sale **si y sólo si** ese máximo no pasa de `1/densT(e)`, es decir

```
#{copias de H por e} · densT(e)  ≤  #copias(H)                    (†)
```

**`(†)` dice que las copias se reparten uniformemente entre las aristas de la pareja**, y es
justo lo que hace falta. Con las cotas crudas no se cumple: `#{copias por e} ≤ t²`,
`densT(e) ≤ t²` y `#copias(H) ≥ (d₀⁶−6δ)t⁴` sólo dan `t⁴ ≤ (d₀⁶−6δ)t⁴`, que es **falso**
porque `d₀⁶−6δ < 1`.

### Una corrección a lo que estimé primero

En el primer feedback acoté `ψ′(H) ≤ 1`. **Es falso**: `ψ′(H)` es una **masa**, del orden de
`t²` —la masa total es `Θ(n²)` repartida entre `≤ k⁴` patrones—. Rehecha la cuenta:

* el **codegrado** del esparcido es `≤ k²/((d₀⁶−6δ)·n)`, que sigue tendiendo a cero: la
  conclusión se sostiene, el exponente que escribí no;
* la **capacidad**, en cambio, sale `≤ 1/(d₀⁶−6δ) > 1` sin `(†)`: el esparcido ingenuo **no es
  legal**. Escalarlo por `(d₀⁶−6δ)` lo arregla pero cuesta una **fracción constante** del
  valor, y el objetivo necesita `(1−β)` con `β → 0`.

Por eso `(†)` —una cota **superior** de conteo, complementaria de la inferior
`PatternPoolGeometry.patCount_K4_ge`— es la pieza que falta, y no un tecnicismo.

## Lo que este módulo da

* `spreadWeight`, `spreadFiber` — la construcción;
* `spread_capacity_of_spread` — la capacidad **a partir de `(†)`**, que es el contenido;
* `spreadPacking` — el `FracPacking` ya montado.

`(†)` entra como hipótesis con nombre, no escondida.
-/

namespace PaperIV.SpreadPacking

open Finset
open PaperIV.PatternTransfer
open MixedRounding

variable {V P : Type*} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. La construcción -/

/-- Las copias de `H` que pasan por la arista `e`. -/
noncomputable def spreadFiber (copies : Finset P → Finset (Finset V))
    (H : Finset P) (e : Sym2 V) : Finset (Finset V) :=
  (copies H).filter (fun K => e ∈ pairs K)

/-- **El packing esparcido.**  La masa transferida de cada patrón, repartida por igual entre
sus copias. -/
noncomputable def spreadWeight (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (copies : Finset P → Finset (Finset V))
    (K : Finset V) : ℚ :=
  ∑ H ∈ Pats, (if K ∈ copies H then psiT x part H / ((copies H).card : ℚ) else 0)

theorem spreadWeight_nonneg (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (copies : Finset P → Finset (Finset V)) (K : Finset V) :
    0 ≤ spreadWeight x part Pats copies K := by
  refine Finset.sum_nonneg fun H _ => ?_
  by_cases h : K ∈ copies H
  · simp only [h, if_pos]
    exact div_nonneg (psiT_nonneg x part H) (by positivity)
  · simp [h]

/-! ## 2. La capacidad, desde la condición de reparto -/

/-- **La carga de una arista, reagrupada por patrón.** -/
theorem load_eq_sum_over_patterns (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (copies : Finset P → Finset (Finset V)) (e : Sym2 V) :
    ∑ K ∈ items G, (if e ∈ pairs K then spreadWeight x part Pats copies K else 0)
      = ∑ H ∈ Pats, ∑ K ∈ items G,
          (if e ∈ pairs K ∧ K ∈ copies H then psiT x part H / ((copies H).card : ℚ) else 0) := by
  classical
  have h1 : ∀ K ∈ items G,
      (if e ∈ pairs K then spreadWeight x part Pats copies K else 0)
        = ∑ H ∈ Pats,
            (if e ∈ pairs K ∧ K ∈ copies H then psiT x part H / ((copies H).card : ℚ)
             else 0) := by
    intro K _
    by_cases he : e ∈ pairs K
    · rw [if_pos he, spreadWeight]
      refine Finset.sum_congr rfl fun H _ => ?_
      by_cases hK : K ∈ copies H
      · rw [if_pos hK, if_pos ⟨he, hK⟩]
      · rw [if_neg hK, if_neg (fun h => hK h.2)]
    · rw [if_neg he]
      refine (Finset.sum_eq_zero fun H _ => ?_).symm
      rw [if_neg (fun h => he h.1)]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]

/-- **La capacidad del packing esparcido, desde `(†)`.**

`hspread` es `(†)`: el número de copias por una arista, por el número de aristas de su pareja,
no pasa del número total de copias. `hserve` dice que una copia por `e` obliga a que su patrón
sirva a `e` —es lo que permite bajar la suma a los patrones que `transfer_capacity` cubre—. -/
theorem spread_capacity (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (copies : Finset P → Finset (Finset V))
    (hsub : ∀ H ∈ Pats, copies H ⊆ items G)
    (hserve : ∀ H ∈ Pats, ∀ K ∈ copies H, ∀ e : Sym2 V, e ∈ pairs K → H ∈ servingT part e)
    (hspread : ∀ H ∈ Pats, ∀ e : Sym2 V,
      ((spreadFiber copies H e).card : ℚ) * densT G part e ≤ ((copies H).card : ℚ))
    (hne : ∀ H ∈ Pats, (copies H).Nonempty)
    (e : Sym2 V) :
    ∑ K ∈ items G, (if e ∈ pairs K then spreadWeight x part Pats copies K else 0) ≤ 1 := by
  classical
  rw [load_eq_sum_over_patterns]
  have hdens : 0 < densT G part e := densT_pos part e
  set S : Finset (Finset P) := Pats.filter (fun H => H ∈ servingT part e) with hS
  -- el sumando de un patrón que no sirve a `e` es cero
  have hzero : ∀ H ∈ Pats, H ∉ S →
      ∑ K ∈ items G,
        (if e ∈ pairs K ∧ K ∈ copies H then psiT x part H / ((copies H).card : ℚ) else 0) = 0 := by
    intro H hH hnS
    refine Finset.sum_eq_zero fun K _ => ?_
    by_cases hc : e ∈ pairs K ∧ K ∈ copies H
    · exact absurd (Finset.mem_filter.2 ⟨hH, hserve H hH K hc.2 e hc.1⟩) hnS
    · simp [hc]
  -- y el de uno que sí sirve no pasa de `ψ′(H)/densT e`
  have hterm : ∀ H ∈ S,
      ∑ K ∈ items G,
          (if e ∈ pairs K ∧ K ∈ copies H then psiT x part H / ((copies H).card : ℚ) else 0)
        ≤ psiT x part H / densT G part e := by
    intro H hHS
    have hH : H ∈ Pats := (Finset.mem_filter.1 hHS).1
    have hpos : (0 : ℚ) < ((copies H).card : ℚ) := by
      have := Finset.card_pos.2 (hne H hH)
      exact_mod_cast this
    have hpsi : 0 ≤ psiT x part H := psiT_nonneg x part H
    have hcard : ∑ K ∈ items G,
        (if e ∈ pairs K ∧ K ∈ copies H then psiT x part H / ((copies H).card : ℚ) else 0)
          = ((spreadFiber copies H e).card : ℚ) * (psiT x part H / ((copies H).card : ℚ)) := by
      have hsets : (items G).filter (fun K => e ∈ pairs K ∧ K ∈ copies H)
          = spreadFiber copies H e := by
        ext K
        simp only [spreadFiber, Finset.mem_filter]
        constructor
        · rintro ⟨_, hp, hK⟩; exact ⟨hK, hp⟩
        · rintro ⟨hK, hp⟩; exact ⟨hsub H hH hK, hp, hK⟩
      rw [← Finset.sum_filter, hsets, Finset.sum_const, nsmul_eq_mul]
    rw [hcard]
    have e1 : ((spreadFiber copies H e).card : ℚ) * (psiT x part H / ((copies H).card : ℚ))
        = (((spreadFiber copies H e).card : ℚ) * psiT x part H) / ((copies H).card : ℚ) := by
      ring
    rw [e1, div_le_iff₀ hpos, div_mul_eq_mul_div, le_div_iff₀ hdens]
    nlinarith [hspread H hH e, hpsi, hdens.le]
  -- se suma sobre `S` y se cierra con la capacidad transferida
  have hSsub : S ⊆ servingT part e := fun H hH => (Finset.mem_filter.1 hH).2
  have hnn : ∀ H ∈ servingT part e, 0 ≤ psiT x part H / densT G part e :=
    fun H _ => div_nonneg (psiT_nonneg x part H) hdens.le
  calc ∑ H ∈ Pats, ∑ K ∈ items G,
        (if e ∈ pairs K ∧ K ∈ copies H then psiT x part H / ((copies H).card : ℚ) else 0)
      = ∑ H ∈ S, ∑ K ∈ items G,
        (if e ∈ pairs K ∧ K ∈ copies H then psiT x part H / ((copies H).card : ℚ) else 0) :=
        (Finset.sum_subset (Finset.filter_subset _ _) hzero).symm
    _ ≤ ∑ H ∈ S, psiT x part H / densT G part e := Finset.sum_le_sum hterm
    _ ≤ ∑ H ∈ servingT part e, psiT x part H / densT G part e :=
        Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun H hH _ => hnn H hH)
    _ = (∑ H ∈ servingT part e, psiT x part H) / densT G part e := by rw [Finset.sum_div]
    _ ≤ 1 := by
        rw [div_le_one hdens]
        exact transfer_capacity x part e

/-- **El packing esparcido, ya montado.** -/
noncomputable def spreadPacking (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (copies : Finset P → Finset (Finset V))
    (hsub : ∀ H ∈ Pats, copies H ⊆ items G)
    (hserve : ∀ H ∈ Pats, ∀ K ∈ copies H, ∀ e : Sym2 V, e ∈ pairs K → H ∈ servingT part e)
    (hspread : ∀ H ∈ Pats, ∀ e : Sym2 V,
      ((spreadFiber copies H e).card : ℚ) * densT G part e ≤ ((copies H).card : ℚ))
    (hne : ∀ H ∈ Pats, (copies H).Nonempty) : FracPacking G where
  weight := spreadWeight x part Pats copies
  weight_nonneg := spreadWeight_nonneg x part Pats copies
  capacity := fun e _ => spread_capacity x part Pats copies hsub hserve hspread hne e

end PaperIV.SpreadPacking
