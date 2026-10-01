import PaperIV.WeightedMoments
import PaperIV.WeightedCoin

/-!
# La moneda pesada **indexada por patrón**, y su legalidad

`PaperIV.WeightedCoin.weightedCoin` colorea cada arista con **qué item se la queda**, y
`PaperIV.WeightedCoinCollapse` demuestra que ese índice colapsa: para el color `some K` sólo el
bloque `pairs K` pesa algo, luego la capa tiene a lo sumo un candidato
(`expect_count_le_single`) y no admite nibble.

Este módulo construye el índice correcto, el de Yuster (`arXiv:math/0305350`): **el color de una
arista es el patrón del grafo reducido al que sirve**, con probabilidad `ψ′(H)/d(i,j)`, y `none`
es «sin color».  Muchas copias comparten patrón, que es exactamente lo que faltaba.

## La moneda

Los datos son tres, y son los de la prueba publicada:

* `serving e` — los patrones `H` del grafo reducido que **sirven** al recurso `e`, es decir las
  copias del patrón que usan el par `(i,j)` en el que vive `e`;
* `psi H` — el peso fraccional `ψ′(H)` transferido al grafo reducido;
* `dens e` — la densidad `d(i,j)` del par en el que vive `e`.

```
q e (some H) = si H ∈ serving e entonces ψ′(H)/d(e), si no 0
q e none     = 1 − ∑_{H ∈ serving e} ψ′(H)/d(e)
```

## De dónde sale la legalidad, y por qué es una hipótesis

Con el índice por item la legalidad era **gratis**: era literalmente `FracPacking.capacity`.
Con el índice por patrón **ya no lo es**.  La no negatividad de `q e none` es exactamente

```
∑_{H ∈ serving e} ψ′(H)  ≤  d(i,j),                                        (†)
```

la capacidad **transferida al grafo reducido**, y (†) no es un teorema de este módulo: es lo
que produce el lema de regularidad al pasar de `x` sobre `G` a `ψ′` sobre `R`.  Aquí (†) es la
hipótesis `hcap`, explícita y con nombre, tal como pedía el encargo: *«si esa transferencia te
resulta el cuello de botella, dilo y para ahí»*.  Véase
`docs/CAPACITY_TRANSFER_BOTTLENECK.md` para el diagnóstico.

Todo lo que sigue —legalidad, momentos, truncado, calendario— es incondicional **dado** (†), y
en particular **no menciona la densidad de `G`**.

## Que el índice no colapsa, demostrado

* `blockWeight_pattern_ge` — si todos los recursos del bloque los sirve `H` y `ψ′(H) ≥ η`,
  el peso del bloque es `≥ η^|S|`, **para cualquier bloque**, no sólo para uno;
* `expect_count_ge` — luego la media del conteo de la capa de color `some H` es `≥ |T|·η^m`:
  **crece linealmente con la familia**, frente al `≤ 1` de
  `WeightedCoinCollapse.expect_count_le_single`.

Ésa es, cuantificada, la diferencia entre los dos índices.
-/

namespace PaperIV.PatternCoin

open Finset
open PaperIV.EighthMoment
open PaperIV.OwnerCoins
open PaperIV.OwnerCoinMoments
open PaperIV.WeightedMoments

variable {ρ Pat : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype Pat] [DecidableEq Pat]

/-! ## 1. La moneda por patrón -/

/-- **La moneda pesada por patrón.**  El color de un recurso es a qué patrón del grafo
reducido sirve; `none` es «sin color», que es donde va la masa que `ψ′` no usa. -/
noncomputable def patternCoin (psi : Pat → ℚ) (dens : ρ → ℚ) (serving : ρ → Finset Pat)
    (e : ρ) : Option Pat → ℚ := fun c =>
  match c with
  | some H => if H ∈ serving e then psi H / dens e else 0
  | none => 1 - ∑ H ∈ serving e, psi H / dens e

/-- La masa que los patrones ponen sobre un recurso. -/
noncomputable def patternLoad (psi : Pat → ℚ) (dens : ρ → ℚ) (serving : ρ → Finset Pat)
    (e : ρ) : ℚ := ∑ H ∈ serving e, psi H / dens e

variable {psi : Pat → ℚ} {dens : ρ → ℚ} {serving : ρ → Finset Pat}

omit [Fintype ρ] [DecidableEq ρ] [Fintype Pat] [DecidableEq Pat] in
theorem patternLoad_nonneg (hpsi : ∀ H, 0 ≤ psi H) (hdens : ∀ e, 0 < dens e) (e : ρ) :
    0 ≤ patternLoad psi dens serving e :=
  Finset.sum_nonneg fun H _ => div_nonneg (hpsi H) (hdens e).le

omit [Fintype ρ] [DecidableEq ρ] [Fintype Pat] [DecidableEq Pat] in
/-- **La capacidad transferida al grafo reducido es exactamente la legalidad de la moneda.**

`hcap` es (†): `∑_{H ∈ serving e} ψ′(H) ≤ d(e)`.  No se demuestra aquí; es lo que entrega la
regularidad. -/
theorem patternLoad_le_one (hdens : ∀ e, 0 < dens e)
    (hcap : ∀ e, ∑ H ∈ serving e, psi H ≤ dens e) (e : ρ) :
    patternLoad psi dens serving e ≤ 1 := by
  have hsum : patternLoad psi dens serving e = (∑ H ∈ serving e, psi H) / dens e := by
    rw [patternLoad, Finset.sum_div]
  rw [hsum, div_le_one (hdens e)]
  exact hcap e

omit [Fintype ρ] [DecidableEq ρ] [Fintype Pat] in
theorem patternCoin_nonneg (hpsi : ∀ H, 0 ≤ psi H) (hdens : ∀ e, 0 < dens e)
    (hcap : ∀ e, ∑ H ∈ serving e, psi H ≤ dens e) (e : ρ) (c : Option Pat) :
    0 ≤ patternCoin psi dens serving e c := by
  cases c with
  | none =>
      have h := patternLoad_le_one (psi := psi) hdens hcap e
      have : (0 : ℚ) ≤ 1 - patternLoad psi dens serving e := by linarith
      simpa [patternCoin, patternLoad] using this
  | some H =>
      by_cases h : H ∈ serving e
      · simpa [patternCoin, h] using div_nonneg (hpsi H) (hdens e).le
      · simp [patternCoin, h]

omit [Fintype ρ] [DecidableEq ρ] in
theorem patternCoin_sum (e : ρ) :
    ∑ c : Option Pat, patternCoin psi dens serving e c = 1 := by
  classical
  have hsub : ∑ H ∈ serving e, patternCoin psi dens serving e (some H)
      = ∑ H : Pat, patternCoin psi dens serving e (some H) :=
    Finset.sum_subset (Finset.subset_univ _)
      (by intro H _ hH; simp [patternCoin, hH])
  have hval : ∑ H ∈ serving e, patternCoin psi dens serving e (some H)
      = patternLoad psi dens serving e := by
    rw [patternLoad]
    exact Finset.sum_congr rfl fun H hH => by simp [patternCoin, hH]
  rw [Fintype.sum_option, hsub.symm.trans hval]
  show (1 - patternLoad psi dens serving e) + patternLoad psi dens serving e = 1
  ring

/-- **El espacio de monedas por patrón.**  Una elección independiente por recurso, con la
probabilidad de cada color proporcional al peso del patrón en el grafo reducido.

Es `OwnerCoins.coinSpace` instanciado con `patternCoin`; la infraestructura no cambia, y el
aparato de segundo momento que lo consume es `WeightedMoments.variance_le_gen`, que no supone
nada sobre el índice de color. -/
noncomputable def patternCoins (hpsi : ∀ H, 0 ≤ psi H) (hdens : ∀ e, 0 < dens e)
    (hcap : ∀ e, ∑ H ∈ serving e, psi H ≤ dens e) :
    FinProb (ρ → Option Pat) :=
  coinSpace (patternCoin psi dens serving)
    (patternCoin_nonneg hpsi hdens hcap) patternCoin_sum

/-! ## 2. El peso de un bloque: el índice **no** colapsa -/

omit [Fintype ρ] [DecidableEq ρ] [Fintype Pat] in
theorem patternCoin_some_of_mem {e : ρ} {H : Pat} (h : H ∈ serving e) :
    patternCoin psi dens serving e (some H) = psi H / dens e := by
  simp [patternCoin, h]

omit [Fintype ρ] [DecidableEq ρ] [Fintype Pat] in
/-- El peso de un bloque servido enteramente por `H`. -/
theorem blockWeight_pattern_eq {H : Pat} {S : Finset ρ} (hS : ∀ f ∈ S, H ∈ serving f) :
    blockWeight (patternCoin psi dens serving) (some H) S = ∏ f ∈ S, psi H / dens f := by
  rw [blockWeight]
  exact Finset.prod_congr rfl fun f hf => patternCoin_some_of_mem (hS f hf)

omit [Fintype ρ] [DecidableEq ρ] [Fintype Pat] in
/-- **El índice por patrón no colapsa.**  Si todos los recursos del bloque los sirve `H` y la
probabilidad por recurso `ψ′(H)/d(f)` no baja de `η`, el peso del bloque es al menos `η^|S|`,
**sea cual sea el bloque**.

Compárese con `WeightedCoinCollapse.blockWeight_some_eq_zero`, donde basta un recurso fuera de
`pairs K` para anular el bloque entero. -/
theorem blockWeight_pattern_ge_ratio {H : Pat} {S : Finset ρ} {η : ℚ} (hη : 0 ≤ η)
    (hS : ∀ f ∈ S, H ∈ serving f) (hratio : ∀ f ∈ S, η ≤ psi H / dens f) :
    η ^ S.card ≤ blockWeight (patternCoin psi dens serving) (some H) S := by
  rw [blockWeight_pattern_eq hS, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun f _ => hη) hratio

omit [Fintype ρ] [DecidableEq ρ] [Fintype Pat] in
/-- La forma que se usa cuando las densidades están normalizadas (`d ≤ 1`): basta que el patrón
sobreviva al truncado, `η ≤ ψ′(H)`. -/
theorem blockWeight_pattern_ge {H : Pat} {S : Finset ρ} {η : ℚ} (hη : 0 ≤ η)
    (hS : ∀ f ∈ S, H ∈ serving f) (hpsiH : η ≤ psi H)
    (hdens : ∀ e, 0 < dens e) (hdens1 : ∀ f ∈ S, dens f ≤ 1) :
    η ^ S.card ≤ blockWeight (patternCoin psi dens serving) (some H) S := by
  refine blockWeight_pattern_ge_ratio hη hS (fun f hf => ?_)
  have hd := hdens f
  have h1 : psi H ≤ psi H / dens f := by
    rw [le_div_iff₀ hd]
    nlinarith [hdens1 f hf, hη.trans hpsiH]
  linarith

omit [Fintype ρ] [DecidableEq ρ] [Fintype Pat] in
/-- La cota superior gemela, que es la que consume `variance_le_gen`. -/
theorem blockWeight_pattern_le {H : Pat} {S : Finset ρ} {β : ℚ}
    (hS : ∀ f ∈ S, H ∈ serving f) (hpsi : ∀ H, 0 ≤ psi H) (hdens : ∀ e, 0 < dens e)
    (hβ : ∀ f ∈ S, psi H / dens f ≤ β) :
    blockWeight (patternCoin psi dens serving) (some H) S ≤ β ^ S.card := by
  rw [blockWeight_pattern_eq hS, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun f _ => div_nonneg (hpsi H) (hdens f).le) hβ

variable {ι : Type*}

/-- **La media del conteo crece con la familia.**

Frente a `WeightedCoinCollapse.expect_count_le_single`, que acota la capa del color `some K`
por `x.weight K ^ |pairs K|` —**un** candidato—, aquí la capa del color `some H` tiene media al
menos `|T|·η^m`: tantos candidatos como copias comparten el patrón.  Eso es lo que hace posible
el nibble. -/
theorem expect_count_ge (hpsi : ∀ H, 0 ≤ psi H) (hdens : ∀ e, 0 < dens e)
    (hcap : ∀ e, ∑ H ∈ serving e, psi H ≤ dens e)
    {H : Pat} {η : ℚ} (hη : 0 ≤ η) {m : ℕ}
    (S : ι → Finset ρ) (T : Finset ι)
    (hcard : ∀ i ∈ T, (S i).card = m)
    (hserved : ∀ i ∈ T, ∀ f ∈ S i, H ∈ serving f)
    (hratio : ∀ i ∈ T, ∀ f ∈ S i, η ≤ psi H / dens f) :
    (T.card : ℚ) * η ^ m
      ≤ (patternCoins hpsi hdens hcap).expect (blockCount S (some H) T) := by
  classical
  rw [patternCoins, expect_count_gen (patternCoin psi dens serving)
    (patternCoin_nonneg hpsi hdens hcap) patternCoin_sum (some H) S T]
  have hterm : ∀ i ∈ T, η ^ m
      ≤ blockWeight (patternCoin psi dens serving) (some H) (S i) := by
    intro i hi
    have h := blockWeight_pattern_ge_ratio (psi := psi) (dens := dens) (serving := serving)
      hη (hserved i hi) (hratio i hi)
    rwa [hcard i hi] at h
  calc (T.card : ℚ) * η ^ m = ∑ _i ∈ T, η ^ m := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum hterm

end PaperIV.PatternCoin
