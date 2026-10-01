import PaperIV.PatternCounting
import PaperIV.NibbleHypotheses

/-!
# La geometría del pool del patrón: lo que el calendario pesado todavía pide

`PoolLayerGen.ownerLowerBoundOnEdges_of_schedule_gen` consume seis cotas. Cuatro
—`Lmass`, `Ldeg`, `M`, `Bb`— las produce `PatternScheduleOwner` para la moneda por patrón. Las
dos que faltaban son las del **pool**:

```lean
hdegU  : ∀ σ g,     deg   (Pool σ).carrier g   ≤ d' σ
hcodeg : ∀ σ g f, f ≠ g → codeg (Pool σ).carrier g f ≤ C σ
```

Este módulo separa las dos mitades del problema, que tienen naturaleza distinta y conviene no
mezclar:

* **Las cotas superiores (`hdegU`, `hcodeg`) no necesitan regularidad.**  `deg` y `codeg` son
  cardinales de filtros del carrier, luego son **monótonos** en el carrier: cualquier
  sub-pool hereda las cotas del pool del que se recorta.  El pool del patrón es un sub-pool del
  canónico, y para el canónico las cotas ya están demostradas en `PaperIV.PoolCounting`.
  §1 da la monotonía y la herencia.

* **La cota inferior sí la necesita**, y es el lema de conteo.  §2 la demuestra:
  `patCount_ge_of_dense` convierte `PatternCounting.counting_of_regular` —que es una cota de
  **error**, en valor absoluto— en la cota inferior que hace falta: si todas las densidades de
  las parejas del patrón son `≥ d₀` y ninguna pareja es excepcional, el número de copias
  transversales es al menos

  ```
  (d₀^{|F|} − |F|·δ) · ∏ᵢ |Vᵢ|
  ```

  Para `K₄` (`|F| = 6`) eso es `(d₀⁶ − 6δ)·t⁴`, que es exactamente el `M = t⁴` de la
  parametrización del calendario, y es **no vacío en cuanto `δ < d₀⁶/6`**.

Ésa es toda la regularidad que la línea del coloreo pesado necesita: nada sobre la densidad de
`G`, sólo que el patrón superviviente al truncado tenga sus seis parejas densas y buenas.
-/

namespace PaperIV.PatternPoolGeometry

open Finset
open PaperIV.NibbleHypotheses
open PaperIV.PatternCounting
open PaperIV.RegularityFormat

/-! ## 1. Las cotas superiores son monótonas: un sub-pool las hereda -/

variable {W : Type*} [DecidableEq W]

/-- **`deg` es monótono en el carrier.** -/
theorem deg_mono {H H' : Finset (Finset W)} (h : H' ⊆ H) (v : W) :
    deg H' v ≤ deg H v :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- **`codeg` es monótono en el carrier.** -/
theorem codeg_mono {H H' : Finset (Finset W)} (h : H' ⊆ H) (x z : W) :
    codeg H' x z ≤ codeg H x z :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- **La herencia, en la forma que consume el calendario.**  Si el pool del patrón se recorta
del pool canónico, hereda sus dos cotas superiores sin ninguna hipótesis nueva.

Es la razón por la que `hdegU` y `hcodeg` **no** son el cuello de botella: el truncado por
patrón sólo puede quitar candidatos. -/
theorem degU_codeg_of_subset {H H' : Finset (Finset W)} (h : H' ⊆ H) {d' C : ℕ}
    (hdegU : ∀ v : W, deg H v ≤ d')
    (hcodeg : ∀ x z : W, x ≠ z → codeg H x z ≤ C) :
    (∀ v : W, deg H' v ≤ d') ∧ (∀ x z : W, x ≠ z → codeg H' x z ≤ C) :=
  ⟨fun v => le_trans (deg_mono h v) (hdegU v),
   fun x z hxz => le_trans (codeg_mono h x z) (hcodeg x z hxz)⟩

/-! ## 2. El lema de conteo, en la forma que hace falta: cota **inferior** -/

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
variable {H : SimpleGraph β} [DecidableRel H.Adj]

/-- **El lema de conteo como cota inferior.**

`counting_of_regular` acota el **error** en valor absoluto. Lo que el calendario necesita es la
mitad inferior, y con las densidades acotadas por debajo:

> si cada pareja del patrón tiene densidad `≥ d₀` y no es excepcional, hay al menos
> `(d₀^{|F|} − |F|·δ)·∏ᵢ|Vᵢ|` copias transversales.

El producto de densidades se acota por debajo por `d₀^{|F|}` con `Finset.prod_le_prod`; el
error, por `counting_of_regular`. No se usa nada más. -/
theorem patCount_ge_of_dense {δ d₀ : ℚ} (hδ : 0 ≤ δ) (hd₀ : 0 ≤ d₀)
    (R : EqualRegularity H δ) (V : ι → Finset β) (F : Finset (ι × ι))
    (hV : ∀ i, V i ∈ R.parts)
    (hne : ∀ e ∈ F, e.1 ≠ e.2) (hsym : ∀ e ∈ F, (e.2, e.1) ∉ F)
    (hVne : ∀ e ∈ F, V e.1 ≠ V e.2)
    (hgood : ∀ e ∈ F, (V e.1, V e.2) ∉ R.bad)
    (hdens : ∀ e ∈ F, d₀ ≤ H.edgeDensity (V e.1) (V e.2)) :
    (d₀ ^ F.card - (F.card : ℚ) * δ) * ∏ i, ((V i).card : ℚ)
      ≤ patCount H V F := by
  classical
  have hcount := counting_of_regular hδ R V F hV hne hsym hVne hgood
  -- el producto de densidades no baja de `d₀ ^ |F|`
  have hprod : d₀ ^ F.card ≤ ∏ e ∈ F, H.edgeDensity (V e.1) (V e.2) := by
    have h := Finset.prod_le_prod (s := F) (f := fun _ : ι × ι => d₀)
      (g := fun e => H.edgeDensity (V e.1) (V e.2))
      (fun e _ => hd₀) (fun e he => hdens e he)
    rwa [Finset.prod_const] at h
  -- el volumen es no negativo
  have hvol : (0 : ℚ) ≤ ∏ i, ((V i).card : ℚ) :=
    Finset.prod_nonneg fun i _ => by positivity
  -- la mitad inferior del valor absoluto
  have hlow : (∏ e ∈ F, H.edgeDensity (V e.1) (V e.2)) * ∏ i, ((V i).card : ℚ)
      - (F.card : ℚ) * δ * ∏ i, ((V i).card : ℚ)
      ≤ patCount H V F := by
    have := (abs_le.1 hcount).1
    linarith
  have hmul : d₀ ^ F.card * ∏ i, ((V i).card : ℚ)
      ≤ (∏ e ∈ F, H.edgeDensity (V e.1) (V e.2)) * ∏ i, ((V i).card : ℚ) :=
    mul_le_mul_of_nonneg_right hprod hvol
  calc (d₀ ^ F.card - (F.card : ℚ) * δ) * ∏ i, ((V i).card : ℚ)
      = d₀ ^ F.card * ∏ i, ((V i).card : ℚ)
        - (F.card : ℚ) * δ * ∏ i, ((V i).card : ℚ) := by ring
    _ ≤ (∏ e ∈ F, H.edgeDensity (V e.1) (V e.2)) * ∏ i, ((V i).card : ℚ)
        - (F.card : ℚ) * δ * ∏ i, ((V i).card : ℚ) := by linarith
    _ ≤ patCount H V F := hlow

/-- **El volumen, en términos del tamaño común de las partes.**  Todas las partes de una
partición equitativa tienen `R.size` elementos, luego `∏ᵢ |Vᵢ| = R.size ^ |ι|`. -/
theorem prod_card_eq_size_pow {δ : ℚ} (R : EqualRegularity H δ) (V : ι → Finset β)
    (hV : ∀ i, V i ∈ R.parts) :
    ∏ i, ((V i).card : ℚ) = (R.size : ℚ) ^ (Fintype.card ι) := by
  classical
  rw [Finset.prod_congr rfl (fun i _ => by rw [R.card_part _ (hV i)]), Finset.prod_const]
  rw [Finset.card_univ]

/-- **La instancia `K₄`.**  Seis parejas, cuatro partes: al menos `(d₀⁶ − 6δ)·t⁴` copias
transversales, con `t = R.size`.

El régimen es **no vacío en cuanto `δ < d₀⁶/6`**, y ninguna hipótesis habla de la densidad de
`H`: sólo de que las seis parejas del patrón sean densas y buenas, que es exactamente lo que el
truncado por patrón garantiza de los patrones supervivientes. -/
theorem patCount_K4_ge {δ d₀ : ℚ} (hδ : 0 ≤ δ) (hd₀ : 0 ≤ d₀)
    (R : EqualRegularity H δ) (V : Fin 4 → Finset β)
    (hV : ∀ i, V i ∈ R.parts)
    (hVne : ∀ e ∈ patK4, V e.1 ≠ V e.2)
    (hgood : ∀ e ∈ patK4, (V e.1, V e.2) ∉ R.bad)
    (hdens : ∀ e ∈ patK4, d₀ ≤ H.edgeDensity (V e.1) (V e.2)) :
    (d₀ ^ 6 - 6 * δ) * (R.size : ℚ) ^ 4 ≤ patCount H V patK4 := by
  have hbase := patCount_ge_of_dense hδ hd₀ R V patK4 hV patK4_ne patK4_sym hVne hgood hdens
  rw [prod_card_eq_size_pow R V hV] at hbase
  have hcard : (patK4.card : ℚ) = 6 := by rw [card_patK4]; norm_num
  have hcard' : patK4.card = 6 := card_patK4
  rw [hcard, hcard'] at hbase
  simpa using hbase

/-- **La instancia `K₃`.**  Tres parejas, tres partes: al menos `(d₀³ − 3δ)·t³`. -/
theorem patCount_K3_ge {δ d₀ : ℚ} (hδ : 0 ≤ δ) (hd₀ : 0 ≤ d₀)
    (R : EqualRegularity H δ) (V : Fin 3 → Finset β)
    (hV : ∀ i, V i ∈ R.parts)
    (hVne : ∀ e ∈ patK3, V e.1 ≠ V e.2)
    (hgood : ∀ e ∈ patK3, (V e.1, V e.2) ∉ R.bad)
    (hdens : ∀ e ∈ patK3, d₀ ≤ H.edgeDensity (V e.1) (V e.2)) :
    (d₀ ^ 3 - 3 * δ) * (R.size : ℚ) ^ 3 ≤ patCount H V patK3 := by
  have hbase := patCount_ge_of_dense hδ hd₀ R V patK3 hV patK3_ne patK3_sym hVne hgood hdens
  rw [prod_card_eq_size_pow R V hV] at hbase
  have hcard : (patK3.card : ℚ) = 3 := by rw [card_patK3]; norm_num
  have hcard' : patK3.card = 3 := card_patK3
  rw [hcard, hcard'] at hbase
  simpa using hbase

/-- **El régimen del conteo no es vacío.**  Con `δ < d₀⁶/6` la cota inferior de `K₄` es
estrictamente positiva, luego hay copias. -/
theorem patCount_K4_pos_regime {δ d₀ : ℚ} (hsmall : 6 * δ < d₀ ^ 6) :
    0 < d₀ ^ 6 - 6 * δ := by linarith

/-! ## 2bis. La **otra mitad** del mismo lema: la cota superior -/

/-- **El lema de conteo como cota superior.**

`counting_of_regular` acota el error en valor absoluto, y hasta ahora sólo se usaba la mitad
inferior (`patCount_ge_of_dense`). La superior sale igual de barata y es la que hace falta para
la condición de reparto del packing esparcido (`SpreadPacking`):

> con todas las densidades del patrón acotadas por arriba por `d₁`, hay a lo sumo
> `(d₁^{|F|} + |F|·δ)·∏ᵢ|Vᵢ|` copias transversales.

Con `d₁ = 1` —que no supone nada, las densidades son probabilidades— queda
`(1 + |F|·δ)·∏ᵢ|Vᵢ|`, y ésa es la forma útil: **el número de copias no pasa del volumen por
`1 + |F|δ`**, sin hipótesis de densidad ninguna. -/
theorem patCount_le_of_dense {δ d₁ : ℚ} (hδ : 0 ≤ δ)
    (R : EqualRegularity H δ) (V : ι → Finset β) (F : Finset (ι × ι))
    (hV : ∀ i, V i ∈ R.parts)
    (hne : ∀ e ∈ F, e.1 ≠ e.2) (hsym : ∀ e ∈ F, (e.2, e.1) ∉ F)
    (hVne : ∀ e ∈ F, V e.1 ≠ V e.2)
    (hgood : ∀ e ∈ F, (V e.1, V e.2) ∉ R.bad)
    (hd₁ : 0 ≤ d₁)
    (hdens : ∀ e ∈ F, H.edgeDensity (V e.1) (V e.2) ≤ d₁) :
    patCount H V F
      ≤ (d₁ ^ F.card + (F.card : ℚ) * δ) * ∏ i, ((V i).card : ℚ) := by
  classical
  have hcount := counting_of_regular hδ R V F hV hne hsym hVne hgood
  have hprod : (∏ e ∈ F, H.edgeDensity (V e.1) (V e.2)) ≤ d₁ ^ F.card := by
    have h := Finset.prod_le_prod (s := F)
      (f := fun e : ι × ι => H.edgeDensity (V e.1) (V e.2))
      (g := fun _ : ι × ι => d₁)
      (fun e _ => H.edgeDensity_nonneg _ _) (fun e he => hdens e he)
    rwa [Finset.prod_const] at h
  have hvol : (0 : ℚ) ≤ ∏ i, ((V i).card : ℚ) :=
    Finset.prod_nonneg fun i _ => by positivity
  have hup : patCount H V F
      ≤ (∏ e ∈ F, H.edgeDensity (V e.1) (V e.2)) * ∏ i, ((V i).card : ℚ)
        + (F.card : ℚ) * δ * ∏ i, ((V i).card : ℚ) := by
    have := (abs_le.1 hcount).2
    linarith
  have hmul : (∏ e ∈ F, H.edgeDensity (V e.1) (V e.2)) * ∏ i, ((V i).card : ℚ)
      ≤ d₁ ^ F.card * ∏ i, ((V i).card : ℚ) :=
    mul_le_mul_of_nonneg_right hprod hvol
  calc patCount H V F
      ≤ (∏ e ∈ F, H.edgeDensity (V e.1) (V e.2)) * ∏ i, ((V i).card : ℚ)
        + (F.card : ℚ) * δ * ∏ i, ((V i).card : ℚ) := hup
    _ ≤ d₁ ^ F.card * ∏ i, ((V i).card : ℚ)
        + (F.card : ℚ) * δ * ∏ i, ((V i).card : ℚ) := by linarith
    _ = (d₁ ^ F.card + (F.card : ℚ) * δ) * ∏ i, ((V i).card : ℚ) := by ring

/-- **La instancia `K₄`, por arriba.**  Sin ninguna hipótesis de densidad: las densidades son
probabilidades, luego `d₁ = 1` sirve y quedan a lo sumo `(1 + 6δ)·t⁴` copias. -/
theorem patCount_K4_le {δ : ℚ} (hδ : 0 ≤ δ)
    (R : EqualRegularity H δ) (V : Fin 4 → Finset β)
    (hV : ∀ i, V i ∈ R.parts)
    (hVne : ∀ e ∈ patK4, V e.1 ≠ V e.2)
    (hgood : ∀ e ∈ patK4, (V e.1, V e.2) ∉ R.bad) :
    patCount H V patK4 ≤ (1 + 6 * δ) * (R.size : ℚ) ^ 4 := by
  have hbase := patCount_le_of_dense hδ R V patK4 hV patK4_ne patK4_sym hVne hgood
    (by norm_num) (fun e _ => H.edgeDensity_le_one _ _)
  rw [prod_card_eq_size_pow R V hV] at hbase
  have hcard : (patK4.card : ℚ) = 6 := by rw [card_patK4]; norm_num
  have hcard' : patK4.card = 6 := card_patK4
  rw [hcard, hcard'] at hbase
  simpa using hbase


end PaperIV.PatternPoolGeometry
