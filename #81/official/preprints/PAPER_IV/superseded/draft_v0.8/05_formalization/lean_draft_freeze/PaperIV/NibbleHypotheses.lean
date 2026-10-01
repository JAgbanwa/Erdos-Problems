import PaperIV.NibblePort
import PaperIV.WeightedCodegree

/-!
# Las hipótesis del nibble sobre `H_σ` (RC01 §17.1)

Último ítem abierto de RP01.  `NearPerfectNibbleAt` —el teorema de Paper III— pide seis cosas
sobre el hipergrafo; `NibblePort.k4Supports_uniform` cerró la primera y el peso constante hace
trivial la segunda.  Aquí se cierran las **cuatro restantes**, que son las que dependen de los
conteos de §16.

## El peso, y por qué eso lo vuelve aritmética

En §17.1 el peso es **constante**: `w T = 1/((1+2u)·D_σ)` para toda hiperarista.  Con peso
constante la carga de un vértice es su grado por el peso, y el codegree ponderado es el
codegree por el peso (`load_eq`, `codegree_eq`).  Las cuatro hipótesis restantes se convierten
así en cuatro desigualdades entre **números de copias**, que es exactamente lo que entregan
§16.3, §16.4 y (17.3):

| hipótesis del nibble | se obtiene de |
|---|---|
| carga `≤ 1` | `deg ≤ (1+u)D` (§16.3) — `load_le_one` |
| carga `≥ 1−γ` fuera de `Exc` | `deg ≥ (1−3u)D` (§16.3) — `load_ge`, con `γ ≥ 5u` |
| `\|Exc\| ≤ η\|W\|` | §16.4, `ResourceSizes.exceptional_le` |
| codegree ponderado `≤ γ` | `codeg ≤ t^{r−3}` (17.3) — `WeightedCodegree.card_two_resources_le` |

## La holgura `1−5u`

`load_ge` usa `(1−3u)/(1+2u) ≥ 1−5u`, que es (17.2).  La diferencia es exactamente `10u²/(1+2u)`,
así que la desigualdad es estricta para `u > 0`: el margen entre `1−3u` y `1−5u` paga el
denominador con sobra.  (`GlobalBudget.load_lower` es la misma cuenta sobre `ℚ`; aquí hace falta
sobre `ℝ`, que es el cuerpo del nibble.)

## El orden de los parámetros

`NearPerfectNibbleAt` **produce** `γ` y `η`; no los recibe.  Por eso `nibble_applies` los
existencializa antes de cuantificar sobre `H`, `u` y `t`: `u` se elige después de `γ` (hace
falta `5u ≤ γ`) y `t` después de ambos.  Ése es justamente el orden de (17.4), y la razón de
que no haya circularidad.
-/

namespace PaperIV.NibbleHypotheses

open Finset
open PaperIV.NibblePort

/-! ## 1. Grado, codegrado y peso constante -/

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- El grado de un vértice en el hipergrafo: cuántas hiperaristas lo contienen. -/
def deg (H : Finset (Finset W)) (v : W) : ℕ := (H.filter (fun T => v ∈ T)).card

/-- El codegrado de dos vértices. -/
def codeg (H : Finset (Finset W)) (x z : W) : ℕ :=
  (H.filter (fun T => x ∈ T ∧ z ∈ T)).card

/-- **Con peso constante, la carga es el grado por el peso.** -/
theorem load_eq (H : Finset (Finset W)) (v : W) (c : ℝ) :
    ∑ _T ∈ H.filter (fun T => v ∈ T), c = (deg H v : ℝ) * c := by
  rw [Finset.sum_const, nsmul_eq_mul, deg]

/-- **Con peso constante, el codegree ponderado es el codegrado por el peso.** -/
theorem codegree_eq (H : Finset (Finset W)) (x z : W) (c : ℝ) :
    ∑ _T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), c = (codeg H x z : ℝ) * c := by
  rw [Finset.sum_const, nsmul_eq_mul, codeg]

/-- La masa total con peso constante. -/
theorem total_eq (H : Finset (Finset W)) (c : ℝ) :
    ∑ _T ∈ H, c = (H.card : ℝ) * c := by
  rw [Finset.sum_const, nsmul_eq_mul]

/-! ## 2. La aritmética de las dos cotas de carga -/

/-- **(17.2) sobre `ℝ`.**  `GlobalBudget.load_lower` es la misma cuenta sobre `ℚ`; el nibble
vive en `ℝ`.  La diferencia es `10u²/(1+2u)`. -/
theorem load_lower_real {u : ℝ} (hu : 0 ≤ u) : 1 - 5 * u ≤ (1 - 3 * u) / (1 + 2 * u) := by
  have hpos : (0 : ℝ) < 1 + 2 * u := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith [sq_nonneg u]

/-- **La carga no pasa de `1`.**  De `deg ≤ (1+u)D` con peso `1/((1+2u)D)`: sobra el `u`
extra del denominador. -/
theorem load_le_one {D u c : ℝ} (hD : 0 < D) (hu : 0 ≤ u)
    (hc : c = 1 / ((1 + 2 * u) * D)) {N : ℕ} (hN : (N : ℝ) ≤ (1 + u) * D) :
    (N : ℝ) * c ≤ 1 := by
  have h2 : (0 : ℝ) < 1 + 2 * u := by linarith
  have hpos : (0 : ℝ) < (1 + 2 * u) * D := mul_pos h2 hD
  rw [hc, mul_one_div, div_le_one hpos]
  nlinarith [hN, hD, hu]

/-- **La carga es `≥ 1−5u` fuera del excepcional.**  De `deg ≥ (1−3u)D` y (17.2). -/
theorem load_ge {D u c : ℝ} (hD : 0 < D) (hu : 0 ≤ u)
    (hc : c = 1 / ((1 + 2 * u) * D)) {N : ℕ} (hN : (1 - 3 * u) * D ≤ (N : ℝ)) :
    1 - 5 * u ≤ (N : ℝ) * c := by
  have h2 : (0 : ℝ) < 1 + 2 * u := by linarith
  have hpos : (0 : ℝ) < (1 + 2 * u) * D := mul_pos h2 hD
  rw [hc, mul_one_div, le_div_iff₀ hpos]
  nlinarith [hN, hD, hu, sq_nonneg u, mul_nonneg (mul_nonneg hu hu) (le_of_lt hD)]

/-- **El codegree ponderado.**  Es la forma en que (17.3) entra como hipótesis del nibble:
`codeg ≤ γ·(1+2u)D` equivale a `codeg·w ≤ γ`. -/
theorem codeg_weight_le {D u c γ : ℝ} (hD : 0 < D) (hu : 0 ≤ u)
    (hc : c = 1 / ((1 + 2 * u) * D)) {N : ℕ} (hN : (N : ℝ) ≤ γ * ((1 + 2 * u) * D)) :
    (N : ℝ) * c ≤ γ := by
  have h2 : (0 : ℝ) < 1 + 2 * u := by linarith
  have hpos : (0 : ℝ) < (1 + 2 * u) * D := mul_pos h2 hD
  rw [hc, mul_one_div, div_le_iff₀ hpos]
  exact hN

/-! ## 3. El ensamblaje: el nibble se aplica a `H_σ` -/

/-- **§17.1, cerrado.**  Las cuatro hipótesis restantes del nibble sobre `H_σ`, reducidas a
conteos de copias.

Léase así: fijados `r` y `β`, el nibble entrega `γ` y `η`; **después** se eligen `u` (con
`5u ≤ γ`) y el hipergrafo.  Las cuatro premisas son literalmente las salidas de §16.3 (las dos
de grado), §16.4 (el excepcional) y (17.3) (el codegrado).

La conclusión es la del teorema casi-perfecto: un matching que es a la vez casi-perfecto en
`W` y casi-óptimo para la masa `|H|/((1+2u)D)`. -/
theorem nibble_applies (hnib : NearPerfectNibbleAt) {r : ℕ} (hr : 2 ≤ r)
    {β : ℝ} (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ (W : Type) [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (Exc : Finset W)
        (D u : ℝ),
        Hypergraph.IsUniform H r → 0 < D → 0 ≤ u → 5 * u ≤ γ →
        (∀ v : W, (deg H v : ℝ) ≤ (1 + u) * D) →
        (∀ v : W, v ∉ Exc → (1 - 3 * u) * D ≤ (deg H v : ℝ)) →
        (Exc.card : ℝ) ≤ η * (Fintype.card W : ℝ) →
        (∀ x z : W, x ≠ z → (codeg H x z : ℝ) ≤ γ * ((1 + 2 * u) * D)) →
        ∃ M : Finset (Finset W), Hypergraph.IsMatching H M ∧
          (1 - β) * ((Fintype.card W : ℝ) / r) ≤ (M.card : ℝ) ∧
          (1 - β) * ((H.card : ℝ) / ((1 + 2 * u) * D)) ≤ (M.card : ℝ) := by
  obtain ⟨γ, hγ, η, hη, hmain⟩ := hnib r hr β hβ
  refine ⟨γ, hγ, η, hη, ?_⟩
  intro W _ _ H Exc D u huni hD hu huγ hdeg hdeglow hExc hcod
  set c : ℝ := 1 / ((1 + 2 * u) * D) with hc
  have h2 : (0 : ℝ) < 1 + 2 * u := by linarith
  have hpos : (0 : ℝ) < (1 + 2 * u) * D := mul_pos h2 hD
  have hc0 : (0 : ℝ) ≤ c := by rw [hc]; positivity
  obtain ⟨M, hM, hM1, hM2⟩ :=
    hmain H (fun _ => c) Exc huni (fun _ => hc0)
      (fun v => by rw [load_eq H v c]; exact load_le_one hD hu hc (hdeg v))
      (fun v hv => by
        rw [load_eq H v c]
        exact le_trans (by linarith) (load_ge hD hu hc (hdeglow v hv)))
      hExc
      (fun x z hxz => by
        rw [codegree_eq H x z c]
        exact codeg_weight_le hD hu hc (hcod x z hxz))
  refine ⟨M, hM, hM1, ?_⟩
  rw [total_eq H c, hc, mul_one_div] at hM2
  exact hM2

/-- **(17.3) en la forma que pide `nibble_applies`.**  Con `D = α^{ℓ−1}·t^{r−2}` y el conteo
`codeg ≤ t^{r−3}` de `WeightedCodegree.card_two_resources_le`, la premisa de codegrado se
cumple en cuanto `t` es grande: `1/(a₀⁵t) ≤ γ`.

Es `WeightedCodegree.codegree_le` —que vive en `ℚ`— trasladado a `ℝ`, que es el cuerpo del
nibble, y despejado en la forma `codeg ≤ γ·(1+2u)·D`.  El exponente `r` entra como `r = j+3`,
así que no hay restas naturales. -/
theorem codeg_condition_of_sizes {α a₀ t u γ : ℝ} {k j N : ℕ}
    (hu : 0 ≤ u) (ht : 0 < t) (ha₀ : 0 < a₀) (hαa : a₀ ≤ α) (hα1 : α ≤ 1) (hk : k ≤ 5)
    (hγ : 1 / (a₀ ^ 5 * t) ≤ γ) (hN : (N : ℝ) ≤ t ^ j) :
    (N : ℝ) ≤ γ * ((1 + 2 * u) * (α ^ k * t ^ (j + 1))) := by
  have hα0 : (0 : ℝ) < α := lt_of_lt_of_le ha₀ hαa
  have hstep : a₀ ^ 5 ≤ α ^ k := by
    calc a₀ ^ 5 ≤ α ^ 5 := pow_le_pow_left₀ (le_of_lt ha₀) hαa 5
      _ ≤ α ^ k := pow_le_pow_of_le_one (le_of_lt hα0) hα1 hk
  have ha0' : a₀ ≠ 0 := ne_of_gt ha₀
  have ht' : t ≠ 0 := ne_of_gt ht
  have htj1 : (0 : ℝ) < t ^ (j + 1) := by positivity
  have hγ0 : (0 : ℝ) < γ := lt_of_lt_of_le (by positivity) hγ
  have hX : (0 : ℝ) ≤ α ^ k * t ^ (j + 1) := by positivity
  calc (N : ℝ) ≤ t ^ j := hN
    _ = (1 / (a₀ ^ 5 * t)) * (a₀ ^ 5 * t ^ (j + 1)) := by
        rw [pow_succ]; field_simp; ring
    _ ≤ γ * (a₀ ^ 5 * t ^ (j + 1)) := mul_le_mul_of_nonneg_right hγ (by positivity)
    _ ≤ γ * (α ^ k * t ^ (j + 1)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hstep (le_of_lt htj1)) (le_of_lt hγ0)
    _ ≤ γ * ((1 + 2 * u) * (α ^ k * t ^ (j + 1))) := by
        have hgX : (0 : ℝ) ≤ γ * (α ^ k * t ^ (j + 1)) := mul_nonneg (le_of_lt hγ0) hX
        nlinarith [mul_nonneg hgX hu]

end PaperIV.NibbleHypotheses
