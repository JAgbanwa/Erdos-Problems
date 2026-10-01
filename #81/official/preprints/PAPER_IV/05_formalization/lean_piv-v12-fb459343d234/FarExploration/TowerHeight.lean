import PaperIV.NearH1Calibration
import PaperIV.RC01Final

/-!
# Pregunta 2: cuantificar `Nfar`

`PaperIV.RC01Final.rc01_uniformRoundingTarget ε` fija su umbral como

```
N = max (max k₀ ⌈B/δ⌉) (max ⌈(12+10D)/ζ⌉ (max ⌈scaleBound⌉ ⌈massBound⌉)) + 1
```

con `δ = deltaOf s`, `s = min (ε/4500) (1/10)`, `k₀ = ⌈1500/ε⌉₊ + 1` y
`B = SzemerediRegularity.bound (δ/8) k₀`.  Todos los ingredientes salvo `B` son
polinómicos o exponenciales en `1/ε`; `B` es la torre.

Este módulo calcula, **para la única instancia que el ensamblaje necesita**
(`ξ = η₀/2 = 5·10⁻¹⁷`, véase `FarExploration.ThresholdCalculus`), los parámetros de
regularidad correspondientes y acota `B` por abajo por una torre de exponenciales:

* `deltaFar_eq` — el parámetro de regularidad exacto, `δ = 1/(2208·9²¹·10³⁹⁹)`;
* `k0Far_eq` — el tamaño mínimo de la partición, `3·10¹⁹ + 1`;
* `heightFar_ge` — la altura de la iteración de regularidad es `≥ 10²¹¹⁷`;
* `tower_le_bound` — `B` domina la torre de doses de esa altura.

Conclusión: `Nfar` **es escribible** (todas las constantes de la cadena son explícitas),
pero su valor es al menos una torre de exponenciales de altura `10²¹¹⁷`.
-/

namespace FarExploration.TowerHeight

open SzemerediRegularity

/-! ## 1. Los parámetros de la única instancia -/

/-- La holgura cuadrática del ensamblaje, `η₀ = 10⁻¹⁶`. -/
def etaFar : ℚ := PaperIV.NearH1Calibration.eta

/-- El único valor de `ξ` que el ensamblaje pide al contrato de redondeo. -/
def xiFar : ℚ := etaFar / 2

theorem xiFar_eq : xiFar = 1 / (2 * 10 ^ 16) := by
  norm_num [xiFar, etaFar, PaperIV.NearH1Calibration.eta]

/-- La escala del esquema de `RC01Final`, `s = min (ξ/4500) (1/10)`. -/
def sFar : ℚ := min (xiFar / 4500) (1 / 10)

theorem sFar_eq : sFar = 1 / (9 * 10 ^ 19) := by
  rw [sFar, xiFar_eq]
  norm_num

/-- El parámetro de regularidad de esa instancia, `δ = s²¹/2208`. -/
def deltaFar : ℚ := PaperIV.RC01Final.deltaOf sFar

theorem deltaFar_eq : deltaFar = 1 / (2208 * (9 * 10 ^ 19) ^ 21) := by
  rw [deltaFar, PaperIV.RC01Final.deltaOf, sFar_eq, div_pow, one_pow, div_div, mul_comm]

theorem deltaFar_pos : 0 < deltaFar := by
  rw [deltaFar_eq]; positivity

/-- El número mínimo de clases de la partición, `k₀ = ⌈1500/ξ⌉₊ + 1`. -/
def k0Far : ℕ := ⌈(1500 / xiFar : ℚ)⌉₊ + 1

theorem k0Far_eq : k0Far = 3 * 10 ^ 19 + 1 := by
  have h : (1500 / xiFar : ℚ) = 3 * 10 ^ 19 := by rw [xiFar_eq]; norm_num
  rw [k0Far, h]
  norm_num

/-! ## 2. La altura de la iteración de regularidad -/

/-- La altura de la iteración en `SzemerediRegularity.bound (δ/8) k₀`. -/
noncomputable def heightFar : ℕ := ⌊(4 : ℝ) / (((deltaFar / 8 : ℚ) : ℝ)) ^ 5⌋₊

set_option exponentiation.threshold 5000 in
set_option maxRecDepth 100000 in
theorem heightFar_ge : 10 ^ 2117 ≤ heightFar := by
  have hQ : ((10 ^ 2117 : ℕ) : ℚ) ≤ 4 / (deltaFar / 8) ^ 5 := by
    rw [deltaFar_eq]
    push_cast
    norm_num
  have hcast : ((4 / (deltaFar / 8) ^ 5 : ℚ) : ℝ)
      = (4 : ℝ) / (((deltaFar / 8 : ℚ) : ℝ)) ^ 5 := by push_cast; ring
  have hR : ((10 ^ 2117 : ℕ) : ℝ) ≤ (4 : ℝ) / (((deltaFar / 8 : ℚ) : ℝ)) ^ 5 := by
    rw [← hcast]
    exact_mod_cast hQ
  exact Nat.le_floor hR

/-! ## 3. La torre -/

/-- La torre de doses: `tower m 0 = m`, `tower m (h+1) = tower (2^m) h`. -/
def tower : ℕ → ℕ → ℕ
  | m, 0 => m
  | m, (h + 1) => tower (2 ^ m) h

theorem tower_mono {m m' : ℕ} (h : ℕ) (hm : m ≤ m') : tower m h ≤ tower m' h := by
  induction h generalizing m m' with
  | zero => exact hm
  | succ h ih =>
      exact ih (Nat.pow_le_pow_right (by norm_num) hm)

theorem tower_le_iterate (h : ℕ) : ∀ m : ℕ, 1 ≤ m → tower m h ≤ stepBound^[h] m := by
  induction h with
  | zero => intro m _; simp [tower]
  | succ h ih =>
      intro m hm
      have hstep : 2 ^ m ≤ stepBound m := by
        have h4 : 2 ^ m ≤ 4 ^ m := Nat.pow_le_pow_left (by norm_num) m
        have : 4 ^ m ≤ m * 4 ^ m := Nat.le_mul_of_pos_left _ hm
        exact le_trans h4 (by simpa [stepBound] using this)
      have hpos : 1 ≤ stepBound m := le_trans (Nat.one_le_two_pow) hstep
      calc tower m (h + 1) = tower (2 ^ m) h := rfl
        _ ≤ tower (stepBound m) h := tower_mono h hstep
        _ ≤ stepBound^[h] (stepBound m) := ih _ hpos
        _ = stepBound^[h + 1] m := (Function.iterate_succ_apply _ _ _).symm

/-- **La cota de regularidad de la instancia domina una torre de doses de altura
`heightFar`.** -/
theorem tower_le_bound (l : ℕ) :
    tower 7 heightFar ≤ SzemerediRegularity.bound (((deltaFar / 8 : ℚ) : ℝ)) l := by
  set eps : ℝ := ((deltaFar / 8 : ℚ) : ℝ) with hEps
  have hinit : 7 ≤ initialBound eps l := seven_le_initialBound _ _
  have h1 : tower 7 heightFar ≤ tower (initialBound eps l) heightFar :=
    tower_mono heightFar hinit
  have h2 : tower (initialBound eps l) heightFar
      ≤ stepBound^[heightFar] (initialBound eps l) :=
    tower_le_iterate heightFar _ (le_trans (by norm_num) hinit)
  have h3 : stepBound^[heightFar] (initialBound eps l)
      ≤ (stepBound^[heightFar] (initialBound eps l)) *
          16 ^ (stepBound^[heightFar] (initialBound eps l)) :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have hbound : SzemerediRegularity.bound eps l
      = (stepBound^[heightFar] (initialBound eps l)) *
          16 ^ (stepBound^[heightFar] (initialBound eps l)) := by
    rw [SzemerediRegularity.bound, heightFar, hEps]
  rw [hbound]
  exact le_trans h1 (le_trans h2 h3)

/-- **Resumen cuantitativo.**  La cota de regularidad de la única instancia que el
ensamblaje necesita domina la torre de doses de altura `10²¹¹⁷`. -/
theorem bound_ge_tower_of_height (l : ℕ) :
    ∃ h : ℕ, 10 ^ 2117 ≤ h ∧
      tower 7 h ≤ SzemerediRegularity.bound (((deltaFar / 8 : ℚ) : ℝ)) l :=
  ⟨heightFar, heightFar_ge, tower_le_bound l⟩

end FarExploration.TowerHeight
