import PaperIV.SpreadRestricted
import PaperIV.PatternMass
import PaperIV.MixedRoundingAdapter
import PaperIV.EpsilonBudgetFull
import MixedRounding.Lift

/-!
# La transferencia de valor `x.value − x′.value`

`PaperIV.SpreadRestricted` construye el packing esparcido `x′` que evita el excepcional `E₀` y
demuestra que es **legal**.  Lo que faltaba para poder usarlo era **el precio**: cuánto valor se
pierde al pasar de `x` a `x′`.  Eso es lo que hace este módulo, y lo hace **instanciando** el
reparto de `PaperIV.EpsilonBudgetFull`, no re-demostrando una cantidad parecida.

## La identidad de la que sale todo

Con el normalizador libre, el valor de `x′` se calcula **exactamente**
(`value_spreadWeightNorm`):

```
x′.value  =  ∑_{H ∈ Pats}  (∑_{K ∈ copies′ H} gainF K) · ψ′(H) / norm H
```

y en un patrón `K₄` todas las copias tienen `gainF = 5`, luego
`x′.value = ∑_H 5·#copies′(H)·ψ′(H)/norm H`.  No hay que suponer nada sobre la familia de
patrones: `copies` y `Pats` quedan **abstractos**, como pide el encargo.

## La descomposición, en dos bloques

`x.value` se parte por patrón en lo que **entra en el pool** y lo que **no**
(`value_eq_pool_add_offPool`):

* **fuera del pool** (`offPoolValue`): los items cuyo perfil de partes no es un patrón
  superviviente.  Ahí viven `L1` (truncado), `L3` (parejas irregulares), `L4` (basura `V₀`) y
  `L5` (aristas **dentro** de partes).  `offPoolValue_le_of_cover` los instancia de golpe: si
  cada item fuera del pool o bien tiene patrón ligero o bien toca una arista de un conjunto
  `Bad`, entonces `offPoolValue ≤ 5·(#ligeros·η) + 5·|Bad|`.
* **dentro del pool**: la pérdida es **multiplicativa**, y se parte en dos
  (`pattern_loss_le`):

  ```
  5ψ(H) − 5·#copies′(H)·ψ(H)/((1+ε₆)·N_H)  ≤  (ε₆ + κ)·5ψ(H)
  ```

  con `ε₆` el normalizador (`L6`) y `κ` la fracción de copias que `E₀` mata (`L2`).

El resultado es `value_transfer_le`, y `value_transfer_budget` lo cierra en `(ε/2)·n²`.

## §1.1 del encargo: `#copies′(H)` frente a `N_H` — la cuenta **cierra**, con un precio

La pérdida por `E₀` está acotada por `card_copies_le`:

```
N_H − #copies′(H)  ≤  ∑_{e ∈ E₀} #fibra(H, e)
```

y —esto es lo que el encargo señalaba— para acotar esa suma hace falta la cota **superior** de
copias por arista, no la media: dentro de `E₀` la condición de reparto `(†ε)` no dice nada.
`sum_fiber_le_of_support` es justamente eso, y deja ver que sólo cuentan las aristas de `E₀`
que caen en el soporte del patrón (sus seis parejas), no las `|E₀|` globales.

Con la cota superior trivial —`#fibra ≤ t²`, elegidos los otros dos vértices— y
`|E₀ ∩ pareja| ≤ ε_C·m ≤ ε_C·t²` por pareja, salen `6·ε_C·t⁴` copias muertas frente a
`N_H ≥ (d₀⁶−6δ)·t⁴` (`PatternPoolGeometry.patCount_K4_ge`), o sea

```
κ  ≤  6·ε_C / (d₀⁶ − 6δ)                       (kappa_of_K4)
```

**Cierra**, pero **no** con `ε_C = ε`: hay un factor `d₀⁻⁶`.  Hay que tomar el umbral de
Chebyshev `ε_C = ε·d₀⁶/100` (`kappa_le_of_threshold`, `threshold_of_density`), y eso **no**
gasta un sexto grupo del presupuesto —`κ` se paga en `L2`, que ya estaba— pero **sí** endurece
la condición sobre `δ`: `RootedChebyshev.card_badSet_le` se aplica con `ε_C`, luego
`checks/second_moment_rho.py` pide `δ ≤ ε_C³·d¹²/100`, que es

```
δ  ≤  ε³ · d³⁰ / 10⁸                            (delta_suffices_for_spread)
```

en vez de `δ ≤ ε³·d¹²/100`.  Es una condición **sobre `δ`**, no sobre `ε`, y `δ` se elige
después de `ε` y de `d₀`, así que es legítima; pero hay que escribirla donde toca.
-/

namespace PaperIV.SpreadValueTransfer

open Finset
open MixedRounding
open PaperIV.PatternTransfer
open PaperIV.SpreadPacking
open PaperIV.SpreadRestricted

variable {V P : Type*} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. El valor del esparcido, exacto -/

omit [Fintype P] in
/-- **El valor del esparcido con normalizador libre, exacto.**

No es una cota: es la identidad de la que sale todo el resto.  La única hipótesis es que las
copias sean items. -/
theorem value_spreadWeightNorm (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (C : Finset P → Finset (Finset V)) (norm : Finset P → ℚ)
    (hsub : ∀ H ∈ Pats, C H ⊆ items G) :
    ∑ K ∈ items G, gainF ℚ K * spreadWeightNorm x part Pats C norm K
      = ∑ H ∈ Pats, (∑ K ∈ C H, gainF ℚ K) * (psiT x part H / norm H) := by
  classical
  have h1 : ∀ K ∈ items G, gainF ℚ K * spreadWeightNorm x part Pats C norm K
      = ∑ H ∈ Pats,
          (if K ∈ C H then gainF ℚ K * (psiT x part H / norm H) else 0) := by
    intro K _
    rw [spreadWeightNorm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun H _ => ?_
    by_cases hK : K ∈ C H
    · rw [if_pos hK, if_pos hK]
    · rw [if_neg hK, if_neg hK, mul_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun H hH => ?_
  have hfil : (items G).filter (fun K => K ∈ C H) = C H := by
    ext K
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub H hH h, h⟩⟩
  rw [← Finset.sum_filter, hfil, Finset.sum_mul]

omit [Fintype P] in
/-- **El caso de ganancia constante `5`**, que es el del patrón `K₄`: todas las copias son
`K₄`, luego el valor sólo ve el **número** de copias supervivientes. -/
theorem value_spreadWeightNorm_gain_five (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (C : Finset P → Finset (Finset V)) (norm : Finset P → ℚ)
    (hsub : ∀ H ∈ Pats, C H ⊆ items G)
    (hgain : ∀ H ∈ Pats, ∀ K ∈ C H, gainF ℚ K = 5) :
    ∑ K ∈ items G, gainF ℚ K * spreadWeightNorm x part Pats C norm K
      = ∑ H ∈ Pats, 5 * ((C H).card : ℚ) * (psiT x part H / norm H) := by
  rw [value_spreadWeightNorm x part Pats C norm hsub]
  refine Finset.sum_congr rfl fun H hH => ?_
  have : ∑ K ∈ C H, gainF ℚ K = 5 * ((C H).card : ℚ) := by
    rw [Finset.sum_congr rfl (fun K hK => hgain H hH K hK), Finset.sum_const, nsmul_eq_mul]
    ring
  rw [this]

/-! ## 2. `x.value`, partido por patrón: dentro y fuera del pool -/

/-- El valor de `x` que llevan los items cuyo perfil de partes **es** un patrón del pool. -/
noncomputable def poolValue (x : FracPacking G) (part : V → P) (Pats : Finset (Finset P)) : ℚ :=
  ∑ K ∈ (items G).filter (fun K => K.image part ∈ Pats), gainF ℚ K * x.weight K

/-- El valor de `x` que llevan los items **fuera** del pool: truncados, irregulares, basura y
dentro de partes.  Es donde viven `L1`, `L3`, `L4` y `L5`. -/
noncomputable def offPoolValue (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) : ℚ :=
  ∑ K ∈ (items G).filter (fun K => K.image part ∉ Pats), gainF ℚ K * x.weight K

omit [Fintype P] in
theorem value_eq_pool_add_offPool (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) :
    x.value = poolValue x part Pats + offPoolValue x part Pats := by
  classical
  rw [poolValue, offPoolValue, FracPacking.value]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

omit [Fintype P] in
theorem offPoolValue_nonneg (x : FracPacking G) (part : V → P) (Pats : Finset (Finset P)) :
    0 ≤ offPoolValue x part Pats := by
  refine Finset.sum_nonneg fun K hK => ?_
  exact mul_nonneg (gainF_nonneg (mem_items.1 (Finset.mem_filter.1 hK).1)) (x.weight_nonneg K)

omit [Fintype P] in
/-- La masa de los patrones del pool es la masa de los items del pool. -/
theorem sum_psiT_pool_eq (x : FracPacking G) (part : V → P) (Pats : Finset (Finset P)) :
    ∑ H ∈ Pats, psiT x part H
      = ∑ K ∈ (items G).filter (fun K => K.image part ∈ Pats), x.weight K := by
  classical
  simp only [psiT]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun K _ => ?_
  exact Finset.sum_ite_eq Pats (K.image part) (fun _ => x.weight K)

omit [Fintype P] in
/-- **Dentro del pool, `x` no vale más que `5` veces la masa transferida.** -/
theorem poolValue_le_five_mul (x : FracPacking G) (part : V → P) (Pats : Finset (Finset P)) :
    poolValue x part Pats ≤ 5 * ∑ H ∈ Pats, psiT x part H := by
  classical
  rw [sum_psiT_pool_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun K hK => ?_
  exact mul_le_mul_of_nonneg_right (gainF_le_five (mem_items.1 (Finset.mem_filter.1 hK).1))
    (x.weight_nonneg K)

/-! ## 3. Lo que `E₀` mata: la cota con la **cota superior** de copias por arista -/

/-- **Las copias muertas están cubiertas por las fibras del excepcional.**

Toda copia que no sobrevive tiene alguna de sus aristas en `E₀`, luego vive en la fibra de esa
arista. -/
theorem card_copies_le (copies : Finset P → Finset (Finset V)) (E₀ : Finset (Sym2 V))
    (H : Finset P) :
    ((copies H).card : ℚ) ≤ ((restrictedCopies copies E₀ H).card : ℚ)
      + ∑ e ∈ E₀, ((spreadFiber copies H e).card : ℚ) := by
  classical
  have hcover : (copies H) \ (restrictedCopies copies E₀ H)
      ⊆ E₀.biUnion (fun e => spreadFiber copies H e) := by
    intro K hK
    rw [Finset.mem_sdiff] at hK
    obtain ⟨hK1, hK2⟩ := hK
    have hex : ¬ (∀ e ∈ pairs K, e ∉ E₀) := by
      intro h
      exact hK2 (Finset.mem_filter.2 ⟨hK1, h⟩)
    push_neg at hex
    obtain ⟨e, he, heE⟩ := hex
    exact Finset.mem_biUnion.2 ⟨e, heE, Finset.mem_filter.2 ⟨hK1, he⟩⟩
  have hsplit : ((copies H) \ (restrictedCopies copies E₀ H)).card
      + (restrictedCopies copies E₀ H).card = (copies H).card :=
    Finset.card_sdiff_add_card_eq_card (restrictedCopies_subset copies E₀ H)
  have hbi : ((copies H) \ (restrictedCopies copies E₀ H)).card
      ≤ ∑ e ∈ E₀, (spreadFiber copies H e).card :=
    le_trans (Finset.card_le_card hcover) (Finset.card_biUnion_le)
  have hnat : (copies H).card
      ≤ (restrictedCopies copies E₀ H).card + ∑ e ∈ E₀, (spreadFiber copies H e).card := by
    omega
  calc ((copies H).card : ℚ)
      ≤ (((restrictedCopies copies E₀ H).card
            + ∑ e ∈ E₀, (spreadFiber copies H e).card : ℕ) : ℚ) := by exact_mod_cast hnat
    _ = ((restrictedCopies copies E₀ H).card : ℚ)
          + ∑ e ∈ E₀, ((spreadFiber copies H e).card : ℚ) := by push_cast; ring

/-- **La cota superior por arista, y sólo en el soporte del patrón.**

`f` es el tamaño de la fibra.  Fuera del soporte `S` del patrón —sus seis parejas— la fibra es
vacía, luego **no** cuentan las `|E₀|` aristas globales sino sólo `|E₀ ∩ S|`; y dentro hay que
usar la cota **superior** `B` de copias por arista, porque la media es justo lo que `(†ε)` no
da dentro de `E₀`. -/
theorem sum_fiber_le_of_support {W : Type*} [DecidableEq W] (E₀ S : Finset W) (f : W → ℚ)
    (B c : ℚ) (hf0 : ∀ e ∈ E₀, e ∉ S → f e = 0)
    (hfB : ∀ e ∈ S, f e ≤ B) (hB : 0 ≤ B) (hc : ((E₀ ∩ S).card : ℚ) ≤ c) :
    ∑ e ∈ E₀, f e ≤ c * B := by
  classical
  have hzero : ∑ e ∈ E₀ ∩ S, f e = ∑ e ∈ E₀, f e := by
    refine Finset.sum_subset Finset.inter_subset_left ?_
    intro e he hne
    exact hf0 e he (fun hS => hne (Finset.mem_inter.2 ⟨he, hS⟩))
  rw [← hzero]
  calc ∑ e ∈ E₀ ∩ S, f e
      ≤ ∑ _e ∈ E₀ ∩ S, B :=
        Finset.sum_le_sum fun e he => hfB e (Finset.mem_inter.1 he).2
    _ = ((E₀ ∩ S).card : ℚ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ c * B := mul_le_mul_of_nonneg_right hc hB

/-! ## 4. La pérdida por patrón: normalizador (`L6`) y copias muertas (`L2`) -/

/-- **La pérdida multiplicativa de un patrón.**

`ε₆` es el normalizador libre y `κ` la fracción de copias que `E₀` mata; la pérdida relativa es
la suma de las dos, sin términos cruzados.  Es pura aritmética: no toca el grafo. -/
theorem pattern_loss_le {psi N c eps kap : ℚ} (hpsi : 0 ≤ psi) (hN : 0 < N)
    (heps : 0 ≤ eps) (hkap : 0 ≤ kap) (hc : N - kap * N ≤ c) :
    5 * psi - 5 * c * (psi / ((1 + eps) * N)) ≤ (eps + kap) * (5 * psi) := by
  have h1 : (0 : ℚ) < 1 + eps := by linarith
  have hD : (0 : ℚ) < (1 + eps) * N := mul_pos h1 hN
  have key : 5 * psi - 5 * c * (psi / ((1 + eps) * N))
      = (5 * psi * ((1 + eps) * N) - 5 * c * psi) / ((1 + eps) * N) := by
    field_simp
  rw [key, div_le_iff₀ hD]
  have hgap : 0 ≤ 5 * psi * (c - (N - kap * N)) := by
    have : 0 ≤ c - (N - kap * N) := by linarith
    positivity
  have hsq : 0 ≤ 5 * psi * N * (eps * (eps + kap)) := by
    have : 0 ≤ eps * (eps + kap) := mul_nonneg heps (by linarith)
    have h5 : 0 ≤ 5 * psi * N := by positivity
    exact mul_nonneg h5 this
  nlinarith [hgap, hsq]

/-! ## 5. La transferencia de valor -/

/-- **El encargo: `x.value − x′.value ≤ Δ`, con `Δ` partido en los sumandos del presupuesto.**

`Δ` es la suma de
* `offPoolValue` — los items fuera del pool: `L1` (truncado), `L3` (irregulares), `L4`
  (basura) y `L5` (aristas dentro de partes);
* `(ε₆ + κ)·5·∑ψ′` — la pérdida multiplicativa: `L6` (el normalizador `(1+ε₆)`) y `L2` (la
  fracción de copias que `E₀` mata).

`copies` y `Pats` quedan abstractos: la instanciación con los dos brazos no se toca aquí. -/
theorem value_transfer_le (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (copies : Finset P → Finset (Finset V))
    (E₀ : Finset (Sym2 V)) (norm : Finset P → ℚ) {eps kap : ℚ}
    (hsub : ∀ H ∈ Pats, copies H ⊆ items G)
    (hserve : ∀ H ∈ Pats, ∀ K ∈ copies H, ∀ e : Sym2 V, e ∈ pairs K → H ∈ servingT part e)
    (hnorm : ∀ H ∈ Pats, 0 < norm H)
    (hdagger : ∀ H ∈ Pats, ∀ e : Sym2 V, e ∉ E₀ →
      ((spreadFiber copies H e).card : ℚ) * densT G part e ≤ norm H)
    (heps : 0 ≤ eps) (hkap : 0 ≤ kap)
    (hgain : ∀ H ∈ Pats, ∀ K ∈ copies H, gainF ℚ K = 5)
    (hpos : ∀ H ∈ Pats, 0 < ((copies H).card : ℚ))
    (hnormeq : ∀ H ∈ Pats, norm H = (1 + eps) * ((copies H).card : ℚ))
    (hkilled : ∀ H ∈ Pats,
      ∑ e ∈ E₀, ((spreadFiber copies H e).card : ℚ) ≤ kap * ((copies H).card : ℚ)) :
    x.value
        - (spreadPackingRestricted x part Pats copies E₀ norm hsub hserve hnorm hdagger).value
      ≤ offPoolValue x part Pats + (eps + kap) * (5 * ∑ H ∈ Pats, psiT x part H) := by
  classical
  have hsub' : ∀ H ∈ Pats, restrictedCopies copies E₀ H ⊆ items G :=
    fun H hH => Finset.Subset.trans (restrictedCopies_subset copies E₀ H) (hsub H hH)
  have hgain' : ∀ H ∈ Pats, ∀ K ∈ restrictedCopies copies E₀ H, gainF ℚ K = 5 :=
    fun H hH K hK => hgain H hH K (restrictedCopies_subset copies E₀ H hK)
  have hval : (spreadPackingRestricted x part Pats copies E₀ norm
        hsub hserve hnorm hdagger).value
      = ∑ H ∈ Pats,
          5 * ((restrictedCopies copies E₀ H).card : ℚ) * (psiT x part H / norm H) := by
    rw [FracPacking.value]
    exact value_spreadWeightNorm_gain_five x part Pats _ norm hsub' hgain'
  -- la pérdida de cada patrón del pool
  have hterm : ∀ H ∈ Pats,
      5 * psiT x part H
          - 5 * ((restrictedCopies copies E₀ H).card : ℚ) * (psiT x part H / norm H)
        ≤ (eps + kap) * (5 * psiT x part H) := by
    intro H hH
    have hc : ((copies H).card : ℚ) - kap * ((copies H).card : ℚ)
        ≤ ((restrictedCopies copies E₀ H).card : ℚ) := by
      have h1 := card_copies_le copies E₀ H
      have h2 := hkilled H hH
      linarith
    have := pattern_loss_le (psi := psiT x part H) (N := ((copies H).card : ℚ))
      (c := ((restrictedCopies copies E₀ H).card : ℚ)) (eps := eps) (kap := kap)
      (psiT_nonneg x part H) (hpos H hH) heps hkap hc
    rwa [← hnormeq H hH] at this
  have hsum : (5 * ∑ H ∈ Pats, psiT x part H)
      - ∑ H ∈ Pats, 5 * ((restrictedCopies copies E₀ H).card : ℚ) * (psiT x part H / norm H)
      ≤ (eps + kap) * (5 * ∑ H ∈ Pats, psiT x part H) := by
    have hle := Finset.sum_le_sum hterm
    calc (5 * ∑ H ∈ Pats, psiT x part H)
          - ∑ H ∈ Pats, 5 * ((restrictedCopies copies E₀ H).card : ℚ)
              * (psiT x part H / norm H)
        = ∑ H ∈ Pats, (5 * psiT x part H
            - 5 * ((restrictedCopies copies E₀ H).card : ℚ) * (psiT x part H / norm H)) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      _ ≤ ∑ H ∈ Pats, (eps + kap) * (5 * psiT x part H) := hle
      _ = (eps + kap) * (5 * ∑ H ∈ Pats, psiT x part H) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hpool := poolValue_le_five_mul x part Pats
  rw [value_eq_pool_add_offPool x part Pats, hval]
  linarith

/-! ## 6. Cerrar el presupuesto en `(ε/2)·n²` -/

/-- **La masa total de un empaquetamiento fraccional es a lo sumo `e(G)/3`.**

Cada item tiene al menos tres aristas y cada arista lleva carga `≤ 1`. -/
theorem three_mul_mass_le_card_edges (x : FracPacking G) :
    3 * ∑ K ∈ items G, x.weight K ≤ (G.edgeFinset.card : ℚ) := by
  classical
  have hload : ∑ e ∈ G.edgeFinset, PaperIV.WeightedCoin.load x e
      = ∑ K ∈ items G, ((pairs K).card : ℚ) * x.weight K := by
    simp only [PaperIV.WeightedCoin.load]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun K hK => ?_
    have hfil : G.edgeFinset.filter (fun e => e ∈ pairs K) = pairs K := by
      ext e
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,
        fun h => ⟨pairs_subset_edgeFinset (mem_items.1 hK) h, h⟩⟩
    rw [← Finset.sum_filter, hfil, Finset.sum_const, nsmul_eq_mul]
  have hthree : ∀ K ∈ items G, 3 * x.weight K ≤ ((pairs K).card : ℚ) * x.weight K := by
    intro K hK
    have hitem := mem_items.1 hK
    have h3 : (3 : ℚ) ≤ ((pairs K).card : ℚ) := by
      rw [MixedRounding.card_pairs]
      rcases hitem.2 with h | h
      · rw [h]; norm_num
      · rw [h, show Nat.choose 4 2 = 6 from by decide]; norm_num
    exact mul_le_mul_of_nonneg_right h3 (x.weight_nonneg K)
  have hcap : ∑ e ∈ G.edgeFinset, PaperIV.WeightedCoin.load x e ≤ (G.edgeFinset.card : ℚ) := by
    calc ∑ e ∈ G.edgeFinset, PaperIV.WeightedCoin.load x e
        ≤ ∑ _e ∈ G.edgeFinset, (1 : ℚ) :=
          Finset.sum_le_sum fun e _ => PaperIV.WeightedCoin.load_le_one x e
      _ = (G.edgeFinset.card : ℚ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  calc 3 * ∑ K ∈ items G, x.weight K
      = ∑ K ∈ items G, 3 * x.weight K := by rw [Finset.mul_sum]
    _ ≤ ∑ K ∈ items G, ((pairs K).card : ℚ) * x.weight K := Finset.sum_le_sum hthree
    _ = ∑ e ∈ G.edgeFinset, PaperIV.WeightedCoin.load x e := hload.symm
    _ ≤ (G.edgeFinset.card : ℚ) := hcap

omit [Fintype P] in
theorem sum_psiT_le_mass (x : FracPacking G) (part : V → P) (Pats : Finset (Finset P)) :
    ∑ H ∈ Pats, psiT x part H ≤ ∑ K ∈ items G, x.weight K := by
  classical
  rw [sum_psiT_pool_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun K _ _ => x.weight_nonneg K)

omit [Fintype P] in
/-- **La masa del pool, en unidades de `n²`.**  `5·∑ψ′ ≤ (5/6)·n²`, que es la forma en la que
la pérdida multiplicativa entra en el presupuesto. -/
theorem five_sum_psiT_le {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (x : FracPacking G) (part : Fin n → P) (Pats : Finset (Finset P)) :
    5 * ∑ H ∈ Pats, psiT x part H ≤ (5 / 6) * (n : ℚ) ^ 2 := by
  have hn0 : (0 : ℚ) ≤ (n : ℚ) := by positivity
  have hchoose : ((n.choose 2 : ℕ) : ℚ) ≤ (n : ℚ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith [hn0]
  have hcard : (G.edgeFinset.card : ℚ) ≤ (n : ℚ) ^ 2 / 2 := by
    have h := G.card_edgeFinset_le_card_choose_two
    have hn : (G.edgeFinset.card : ℚ) ≤ (((Fintype.card (Fin n)).choose 2 : ℕ) : ℚ) := by
      exact_mod_cast h
    rw [Fintype.card_fin] at hn
    exact hn.trans hchoose
  have hmass := three_mul_mass_le_card_edges x
  have hpsi := sum_psiT_le_mass x part Pats
  linarith

/-- **El cierre: la transferencia de valor cabe en `(ε/2)·n²`.**

El reparto es el de `EpsilonBudgetFull.budget_closes` con `ε/2`: cada uno de los cinco grupos
—`L1`, `L2`, `L3+L4`, `L5`, `L6`— a `(ε/2)/5 = ε/10` de `n²`.  Los tres primeros sumandos son
`offPoolValue`; `κ ≤ 3ε/25` es `L2` y `ε₆ ≤ 3ε/25` es `L6`, porque la masa del pool entra con
factor `5/6`:  `(5/6)·(3ε/25) = ε/10`.

**No hace falta un sexto grupo.** -/
theorem value_transfer_budget {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (x : FracPacking G) (part : Fin n → P)
    (Pats : Finset (Finset P)) (copies : Finset P → Finset (Finset (Fin n)))
    (E₀ : Finset (Sym2 (Fin n))) (norm : Finset P → ℚ) {eps kap ε L1 L34 L5 : ℚ}
    (hsub : ∀ H ∈ Pats, copies H ⊆ items G)
    (hserve : ∀ H ∈ Pats, ∀ K ∈ copies H, ∀ e : Sym2 (Fin n), e ∈ pairs K →
      H ∈ servingT part e)
    (hnorm : ∀ H ∈ Pats, 0 < norm H)
    (hdagger : ∀ H ∈ Pats, ∀ e : Sym2 (Fin n), e ∉ E₀ →
      ((spreadFiber copies H e).card : ℚ) * densT G part e ≤ norm H)
    (heps : 0 ≤ eps) (hkap : 0 ≤ kap)
    (hgain : ∀ H ∈ Pats, ∀ K ∈ copies H, gainF ℚ K = 5)
    (hpos : ∀ H ∈ Pats, 0 < ((copies H).card : ℚ))
    (hnormeq : ∀ H ∈ Pats, norm H = (1 + eps) * ((copies H).card : ℚ))
    (hkilled : ∀ H ∈ Pats,
      ∑ e ∈ E₀, ((spreadFiber copies H e).card : ℚ) ≤ kap * ((copies H).card : ℚ))
    (hoff : offPoolValue x part Pats ≤ L1 + L34 + L5)
    (hL1 : L1 ≤ ε / 10 * (n : ℚ) ^ 2)
    (hL34 : L34 ≤ ε / 10 * (n : ℚ) ^ 2)
    (hL5 : L5 ≤ ε / 10 * (n : ℚ) ^ 2)
    (hL2 : kap ≤ 3 * ε / 25) (hL6 : eps ≤ 3 * ε / 25) :
    x.value
        - (spreadPackingRestricted x part Pats copies E₀ norm hsub hserve hnorm hdagger).value
      ≤ ε / 2 * (n : ℚ) ^ 2 := by
  have hmain := value_transfer_le x part Pats copies E₀ norm hsub hserve hnorm hdagger
    heps hkap hgain hpos hnormeq hkilled
  have hmass := five_sum_psiT_le x part Pats
  have hfac : (eps + kap) * (5 * ∑ H ∈ Pats, psiT x part H)
      ≤ (eps + kap) * ((5 / 6) * (n : ℚ) ^ 2) :=
    mul_le_mul_of_nonneg_left hmass (by linarith)
  have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := by positivity
  have hlast : (eps + kap) * ((5 / 6) * (n : ℚ) ^ 2) ≤ (ε / 5) * (n : ℚ) ^ 2 := by
    nlinarith [hn2, hL2, hL6]
  linarith

/-! ## 7. `L1`, `L3`, `L4`, `L5`: los items de fuera del pool, instanciados -/

omit [Fintype P] in
/-- **Todo lo de fuera del pool, de una vez.**

Si cada item fuera del pool o bien tiene un patrón **ligero** (masa `< η`, el truncado `L1`) o
bien toca una arista del conjunto `Bad` (`L3` irregulares, `L4` basura, `L5` dentro de partes),
entonces

```
offPoolValue  ≤  5·(#ligeros·η)  +  5·|Bad|
```

Es `PatternMass.gain_small_le` y `PatternMass.gain_of_discards_le` puestos a trabajar sobre la
partición en patrones: ninguno de los cuatro sumandos se estima por separado dos veces. -/
theorem offPoolValue_le_of_cover (x : FracPacking G) (part : V → P)
    (Pats Light : Finset (Finset P)) (Bad : Finset (Sym2 V)) {η : ℚ}
    (hBad : ∀ f ∈ Bad, f ∈ G.edgeFinset)
    (hlight : ∀ H ∈ Light, psiT x part H ≤ η)
    (hcover : ∀ K ∈ items G, K.image part ∉ Pats →
      K.image part ∈ Light ∨ ∃ f ∈ Bad, f ∈ pairs K) :
    offPoolValue x part Pats ≤ 5 * ((Light.card : ℚ) * η) + 5 * (Bad.card : ℚ) := by
  classical
  set D : Finset (Finset V) :=
    (items G).filter (fun K => K.image part ∉ Pats) with hD
  set DL : Finset (Finset V) := D.filter (fun K => K.image part ∈ Light) with hDL
  set DB : Finset (Finset V) := D.filter (fun K => K.image part ∉ Light) with hDB
  have hsplit : offPoolValue x part Pats
      = ∑ K ∈ DL, gainF ℚ K * x.weight K + ∑ K ∈ DB, gainF ℚ K * x.weight K := by
    rw [offPoolValue, hDL, hDB, ← hD]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- los ligeros: su masa no pasa de `#ligeros · η`
  have hLbound : ∑ K ∈ DL, gainF ℚ K * x.weight K ≤ 5 * ((Light.card : ℚ) * η) := by
    have hmass : ∑ K ∈ DL, x.weight K ≤ ∑ H ∈ Light, psiT x part H := by
      have hpsi : ∑ H ∈ Light, psiT x part H
          = ∑ K ∈ (items G).filter (fun K => K.image part ∈ Light), x.weight K :=
        sum_psiT_pool_eq x part Light
      rw [hpsi]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun K _ _ => x.weight_nonneg K)
      intro K hK
      rw [hDL, Finset.mem_filter, hD, Finset.mem_filter] at hK
      exact Finset.mem_filter.2 ⟨hK.1.1, hK.2⟩
    have hηsum : ∑ H ∈ Light, psiT x part H ≤ (Light.card : ℚ) * η := by
      calc ∑ H ∈ Light, psiT x part H ≤ ∑ _H ∈ Light, η := Finset.sum_le_sum hlight
        _ = (Light.card : ℚ) * η := by rw [Finset.sum_const, nsmul_eq_mul]
    have hgain : ∑ K ∈ DL, gainF ℚ K * x.weight K ≤ 5 * ∑ K ∈ DL, x.weight K := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun K hK => ?_
      have hKit : K ∈ items G := by
        rw [hDL, Finset.mem_filter, hD, Finset.mem_filter] at hK
        exact hK.1.1
      exact mul_le_mul_of_nonneg_right (gainF_le_five (mem_items.1 hKit)) (x.weight_nonneg K)
    have : 5 * ∑ K ∈ DL, x.weight K ≤ 5 * ((Light.card : ℚ) * η) := by
      have := hmass.trans hηsum
      linarith
    linarith
  -- los demás tocan `Bad`
  have hBbound : ∑ K ∈ DB, gainF ℚ K * x.weight K ≤ 5 * (Bad.card : ℚ) := by
    have hDBitems : ∀ K ∈ DB, K ∈ PaperIV.FarRounding.items G := by
      intro K hK
      rw [hDB, Finset.mem_filter, hD, Finset.mem_filter] at hK
      rw [← PaperIV.MixedRoundingAdapter.items_eq]
      exact hK.1.1
    have hmeet : ∀ K ∈ DB, ∃ f ∈ Bad, f ∈ PaperIV.FarRounding.pairs K := by
      intro K hK
      rw [hDB, Finset.mem_filter, hD, Finset.mem_filter] at hK
      rcases hcover K hK.1.1 hK.1.2 with hL | hmeet
      · exact absurd hL hK.2
      · exact hmeet
    exact PaperIV.PatternMass.gain_of_discards_le
      (PaperIV.MixedRoundingAdapter.toFarFrac x) Bad hBad DB hDBitems hmeet
  linarith

/-! ## 8. `κ`: la cuenta de §1.1 del encargo, y el precio que tiene -/

/-- **La fracción de copias que `E₀` mata, en el patrón `K₄`.**

`killed ≤ 6·ε_C·t⁴` —seis parejas, `ε_C·t²` aristas malas por pareja, `t²` copias por arista
(la cota **superior**, no la media)— frente a `N ≥ (d₀⁶−6δ)·t⁴`
(`PatternPoolGeometry.patCount_K4_ge`). -/
theorem kappa_of_K4 {epsC d₀ δ t N killed : ℚ} (hepsC : 0 ≤ epsC)
    (hkill : killed ≤ 6 * ((epsC * t ^ 2) * t ^ 2))
    (hD : 0 < d₀ ^ 6 - 6 * δ)
    (hN : (d₀ ^ 6 - 6 * δ) * t ^ 4 ≤ N) :
    killed ≤ (6 * epsC / (d₀ ^ 6 - 6 * δ)) * N := by
  have hfrac : 0 ≤ 6 * epsC / (d₀ ^ 6 - 6 * δ) := by positivity
  have hstep : (6 * epsC / (d₀ ^ 6 - 6 * δ)) * ((d₀ ^ 6 - 6 * δ) * t ^ 4)
      = 6 * epsC * t ^ 4 := by
    field_simp
  calc killed ≤ 6 * ((epsC * t ^ 2) * t ^ 2) := hkill
    _ = (6 * epsC / (d₀ ^ 6 - 6 * δ)) * ((d₀ ^ 6 - 6 * δ) * t ^ 4) := by rw [hstep]; ring
    _ ≤ (6 * epsC / (d₀ ^ 6 - 6 * δ)) * N := mul_le_mul_of_nonneg_left hN hfrac

/-- **El umbral de Chebyshev que hace falta.**  Con `ε_C ≤ ε·D/50` la fracción muerta cabe en
`3ε/25`, que es lo que `value_transfer_budget` pide de `L2`. -/
theorem kappa_le_of_threshold {ε epsC D : ℚ} (hD : 0 < D) (h : epsC ≤ ε * D / 50) :
    6 * epsC / D ≤ 3 * ε / 25 := by
  rw [div_le_iff₀ hD]
  nlinarith [h, hD]

/-- **Y `ε_C = ε·d₀⁶/100` lo cumple**, en cuanto `12δ ≤ d₀⁶`. -/
theorem threshold_of_density {ε d₀ δ : ℚ} (hε : 0 ≤ ε) (h : 12 * δ ≤ d₀ ^ 6) :
    ε * d₀ ^ 6 / 100 ≤ ε * (d₀ ^ 6 - 6 * δ) / 50 := by
  nlinarith [hε, h]

/-- **El precio, escrito donde toca: la condición sobre `δ`.**

`RootedChebyshev.card_badSet_le` con umbral `ε_C` pide `ρ ≤ ε_C³`, y
`checks/second_moment_rho.py` traduce eso a `δ ≤ ε_C³·d¹²/100`.  Con `ε_C = ε·d₀⁶/100` la
condición es **exactamente** `δ ≤ ε³·d³⁰/10⁸`: es la misma cuenta de siempre, no una nueva, y
sigue siendo una condición sobre `δ` —que se elige el último— y no sobre `ε`. -/
theorem delta_suffices_for_spread {ε d δ : ℚ} (h : δ ≤ ε ^ 3 * d ^ 30 / 10 ^ 8) :
    δ ≤ (ε * d ^ 6 / 100) ^ 3 * d ^ 12 / 100 := by
  have hid : (ε * d ^ 6 / 100) ^ 3 * d ^ 12 / 100 = ε ^ 3 * d ^ 30 / 10 ^ 8 := by ring
  rw [hid]
  exact h

end PaperIV.SpreadValueTransfer
