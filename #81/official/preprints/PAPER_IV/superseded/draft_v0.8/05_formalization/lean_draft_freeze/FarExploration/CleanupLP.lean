import Mathlib

/-!
# La limpieza de codegree como programa lineal: el modelo abstracto

`FarExploration.CodegreeCleanup.CodegreeCleanupAt` pide, dado un empaquetamiento fraccional
`x` de un grafo `G`, otro empaquetamiento `y` con

1. **codegrado ponderado** `≤ gam` sobre cada par de aristas distintas,
2. **masa triangular** `≥ Cst`,
3. **pérdida de valor** `≤ xi·n²`.

Las tres condiciones son lineales en los pesos de `y`, y las restricciones de capacidad del
empaquetamiento también.  Es decir: la limpieza es **factibilidad de un programa lineal**
sobre `ℚ` cuyas variables son los pesos de los items.

Este módulo escribe ese LP en la forma más general posible: un **sistema de items** sobre un
conjunto finito de *recursos* `R` es una familia finita de soportes de rango `3` ó `6`
(exactamente los rangos de `K₃` y `K₄` en la familia conjunta de `PaperIV`).  Todo lo que la
limpieza usa del grafo —capacidades por recurso, rangos, ganancias `2`/`5`, codegrado por par de
recursos, masa de los items de rango `3`— queda registrado; lo único que se olvida es que los
soportes sean **cliques de un grafo**.

Los módulos siguientes usan este modelo:

* `FarExploration.CleanupDuality` — el dual del LP y la alternativa de Farkas;
* `FarExploration.CleanupObstruction` — un sistema de items explícito sobre `Sym2 (Fin n)` que
  refuta la versión abstracta del enunciado, con certificado dual;
* `FarExploration.CleanupBridge` — que la versión abstracta **implica** la concreta, de modo que
  la refutación de la abstracta es exactamente la medida de lo que hace falta usar del grafo;
* `FarExploration.CleanupVerdict` — el veredicto.
-/

namespace FarExploration.CleanupLP

open Finset

variable {R : Type*} [Fintype R] [DecidableEq R]

/-! ## 1. Sistemas de items -/

/-- **Un sistema de items** sobre un conjunto finito de recursos: una familia de soportes, cada
uno de rango `3` (tipo `K₃`) ó `6` (tipo `K₄`). -/
structure ItemSystem (R : Type*) [Fintype R] [DecidableEq R] where
  /-- Los soportes de los items. -/
  supports : Finset (Finset R)
  /-- Cada soporte tiene rango `3` ó `6`. -/
  rank_mem : ∀ S ∈ supports, S.card = 3 ∨ S.card = 6

/-- La ganancia de un soporte: `2` para el rango `3`, `5` para el rango `6`. -/
def gainOfSupport (S : Finset R) : ℚ := if S.card = 3 then 2 else 5

omit [Fintype R] [DecidableEq R] in
lemma gainOfSupport_nonneg (S : Finset R) : 0 ≤ gainOfSupport S := by
  unfold gainOfSupport; split <;> norm_num

omit [Fintype R] [DecidableEq R] in
/-- Cota de la ganancia por el rango: `gain S ≤ (5/6)·|S|` para los dos rangos admisibles. -/
lemma gainOfSupport_le_card {S : Finset R} (h : S.card = 3 ∨ S.card = 6) :
    gainOfSupport S ≤ (5 / 6 : ℚ) * (S.card : ℚ) := by
  rcases h with h | h <;> · unfold gainOfSupport; rw [h]; norm_num

/-- **Una solución fraccional del LP de empaquetamiento** sobre un sistema de items: pesos no
negativos cuya carga sobre cada recurso no excede `1`. -/
structure Frac (H : ItemSystem R) where
  /-- El peso de cada soporte. -/
  w : Finset R → ℚ
  /-- Los pesos son no negativos. -/
  nonneg : ∀ S, 0 ≤ w S
  /-- La carga de cada recurso no excede `1`. -/
  capacity : ∀ r : R, ∑ S ∈ H.supports.filter (fun S => r ∈ S), w S ≤ 1

namespace Frac

variable {H : ItemSystem R}

/-- El valor de una solución fraccional. -/
def value (x : Frac H) : ℚ := ∑ S ∈ H.supports, gainOfSupport S * x.w S

/-- La masa de rango `3` (la «masa triangular» del modelo concreto). -/
def mass (x : Frac H) : ℚ := ∑ S ∈ H.supports.filter (fun S => S.card = 3), x.w S

/-- El **codegrado ponderado** de un par de recursos. -/
def codeg (x : Frac H) (r s : R) : ℚ :=
  ∑ S ∈ H.supports.filter (fun S => r ∈ S ∧ s ∈ S), x.w S

lemma value_nonneg (x : Frac H) : 0 ≤ x.value :=
  Finset.sum_nonneg fun S _ => mul_nonneg (gainOfSupport_nonneg S) (x.nonneg S)

lemma mass_nonneg (x : Frac H) : 0 ≤ x.mass :=
  Finset.sum_nonneg fun S _ => x.nonneg S

lemma codeg_nonneg (x : Frac H) (r s : R) : 0 ≤ x.codeg r s :=
  Finset.sum_nonneg fun S _ => x.nonneg S

/-- **El codegrado nunca pasa de `1`**: es una subsuma de la carga del recurso `r`. -/
lemma codeg_le_one (x : Frac H) (r s : R) : x.codeg r s ≤ 1 := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (x.capacity r)
  · intro S hS
    simp only [Finset.mem_filter] at hS ⊢
    exact ⟨hS.1, hS.2.1⟩
  · intro S _ _
    exact x.nonneg S

/-! ### Escalado -/

/-- Escalar una solución fraccional por `t ∈ [0,1]`. -/
def scale (x : Frac H) (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Frac H where
  w := fun S => t * x.w S
  nonneg := fun S => mul_nonneg ht0 (x.nonneg S)
  capacity := fun r => by
    rw [← Finset.mul_sum]
    calc t * ∑ S ∈ H.supports.filter (fun S => r ∈ S), x.w S
        ≤ t * 1 := by
          exact mul_le_mul_of_nonneg_left (x.capacity r) ht0
      _ = t := mul_one t
      _ ≤ 1 := ht1

@[simp] lemma scale_w (x : Frac H) (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (S : Finset R) :
    (x.scale t ht0 ht1).w S = t * x.w S := rfl

lemma value_scale (x : Frac H) (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (x.scale t ht0 ht1).value = t * x.value := by
  unfold value
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => by simp [scale]; ring

lemma mass_scale (x : Frac H) (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (x.scale t ht0 ht1).mass = t * x.mass := by
  unfold mass
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => rfl

lemma codeg_scale (x : Frac H) (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (r s : R) :
    (x.scale t ht0 ht1).codeg r s = t * x.codeg r s := by
  unfold codeg
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => rfl

/-! ### La cota universal de valor -/

/-- Doble conteo: la suma de rangos ponderados es la suma de las cargas. -/
lemma sum_card_mul_w (x : Frac H) :
    ∑ S ∈ H.supports, (S.card : ℚ) * x.w S
      = ∑ r : R, ∑ S ∈ H.supports.filter (fun S => r ∈ S), x.w S := by
  classical
  have h1 : ∀ r : R, ∑ S ∈ H.supports.filter (fun S => r ∈ S), x.w S
      = ∑ S ∈ H.supports, (if r ∈ S then x.w S else 0) := by
    intro r; rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl fun r _ => h1 r, Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

/-- **Cota universal del valor**: `value ≤ (5/6)·|R|`.  Es la única cota que el LP da sin mirar
la estructura del sistema de items, y es la que hace funcionar el escalado. -/
theorem value_le_card (x : Frac H) : x.value ≤ (5 / 6 : ℚ) * (Fintype.card R : ℚ) := by
  classical
  have hstep : x.value ≤ (5 / 6 : ℚ) * ∑ S ∈ H.supports, (S.card : ℚ) * x.w S := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun S hS => ?_
    have := gainOfSupport_le_card (H.rank_mem S hS)
    have hw := x.nonneg S
    nlinarith [this, hw]
  have hload : ∑ S ∈ H.supports, (S.card : ℚ) * x.w S ≤ (Fintype.card R : ℚ) := by
    rw [sum_card_mul_w]
    calc ∑ r : R, ∑ S ∈ H.supports.filter (fun S => r ∈ S), x.w S
        ≤ ∑ _r : R, (1 : ℚ) := Finset.sum_le_sum fun r _ => x.capacity r
      _ = (Fintype.card R : ℚ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
  calc x.value ≤ (5 / 6 : ℚ) * ∑ S ∈ H.supports, (S.card : ℚ) * x.w S := hstep
    _ ≤ (5 / 6 : ℚ) * (Fintype.card R : ℚ) := by
        exact mul_le_mul_of_nonneg_left hload (by norm_num)

end Frac

/-! ### Sistemas rígidos

Un sistema de items es **rígido** si cada recurso pertenece a lo sumo a un item.  Entonces la
restricción de codegrado sobre dos recursos de un mismo item dice literalmente que el peso de ese
item es `≤ gam`, y el valor total de cualquier solución admisible queda aplastado.  Es la
configuración que hace grandes a los precios duales. -/

/-- **Sistema rígido**: cada recurso pertenece a lo sumo a un item. -/
def ItemSystem.Rigid (H : ItemSystem R) : Prop :=
  ∀ S ∈ H.supports, ∀ T ∈ H.supports, ∀ r : R, r ∈ S → r ∈ T → S = T

namespace Frac

variable {H : ItemSystem R}

/-- En un sistema rígido el codegrado de dos recursos de un item es el peso del item. -/
lemma codeg_eq_w_of_rigid (hR : H.Rigid) (y : Frac H) {S : Finset R} (hS : S ∈ H.supports)
    {r s : R} (hr : r ∈ S) (hs : s ∈ S) : y.codeg r s = y.w S := by
  classical
  have hfilter : H.supports.filter (fun T => r ∈ T ∧ s ∈ T) = {S} := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hT, hrT, -⟩
      exact (hR T hT S hS r hrT hr)
    · rintro rfl
      exact ⟨hS, hr, hs⟩
  rw [codeg, hfilter, Finset.sum_singleton]

/-- En un sistema rígido, cada peso está acotado por el umbral de codegrado. -/
lemma w_le_of_rigid (hR : H.Rigid) (y : Frac H) (gam : ℝ)
    (hcod : ∀ r s : R, r ≠ s → ((y.codeg r s : ℚ) : ℝ) ≤ gam)
    {S : Finset R} (hS : S ∈ H.supports) (hcard : 2 ≤ S.card) :
    ((y.w S : ℚ) : ℝ) ≤ gam := by
  classical
  obtain ⟨r, hr, s, hs, hrs⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
  have := hcod r s hrs
  rwa [codeg_eq_w_of_rigid hR y hS hr hs] at this

/-- **La cota de valor en un sistema rígido de rango `3`.** -/
lemma value_le_of_rigid_three (hR : H.Rigid) (hthree : ∀ S ∈ H.supports, S.card = 3)
    (y : Frac H) (gam : ℝ)
    (hcod : ∀ r s : R, r ≠ s → ((y.codeg r s : ℚ) : ℝ) ≤ gam) :
    ((y.value : ℚ) : ℝ) ≤ 2 * gam * (H.supports.card : ℝ) := by
  classical
  rw [value, Rat.cast_sum]
  have hterm : ∀ S ∈ H.supports, ((gainOfSupport S * y.w S : ℚ) : ℝ) ≤ 2 * gam := by
    intro S hS
    have hw := w_le_of_rigid hR y gam hcod hS (by rw [hthree S hS]; norm_num)
    rw [gainOfSupport, if_pos (hthree S hS)]
    push_cast
    linarith
  calc ∑ S ∈ H.supports, ((gainOfSupport S * y.w S : ℚ) : ℝ)
      ≤ ∑ _S ∈ H.supports, (2 * gam) := Finset.sum_le_sum hterm
    _ = 2 * gam * (H.supports.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

end Frac

/-- **El empaquetamiento de peso `1`** de un sistema rígido. -/
def ItemSystem.rigidFrac (H : ItemSystem R) (hR : H.Rigid) : Frac H where
  w := fun S => if S ∈ H.supports then 1 else 0
  nonneg := by
    intro S
    by_cases hS : S ∈ H.supports <;> simp [hS]
  capacity := by
    intro r
    classical
    have hle : (H.supports.filter (fun S => r ∈ S)).card ≤ 1 := by
      refine Finset.card_le_one.2 ?_
      intro S hS T hT
      simp only [Finset.mem_filter] at hS hT
      exact hR S hS.1 T hT.1 r hS.2 hT.2
    have hsum : ∑ S ∈ H.supports.filter (fun S => r ∈ S),
        (if S ∈ H.supports then (1 : ℚ) else 0)
        = ((H.supports.filter (fun S => r ∈ S)).card : ℚ) := by
      rw [Finset.sum_congr rfl (fun S hS => if_pos (Finset.mem_filter.1 hS).1),
        Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsum]
    exact_mod_cast hle

@[simp] lemma ItemSystem.rigidFrac_w (H : ItemSystem R) (hR : H.Rigid) (S : Finset R) :
    (H.rigidFrac hR).w S = if S ∈ H.supports then 1 else 0 := rfl

lemma ItemSystem.rigidFrac_value (H : ItemSystem R) (hR : H.Rigid)
    (hthree : ∀ S ∈ H.supports, S.card = 3) :
    (H.rigidFrac hR).value = 2 * (H.supports.card : ℚ) := by
  classical
  rw [Frac.value]
  have hterm : ∀ S ∈ H.supports, gainOfSupport S * (H.rigidFrac hR).w S = 2 := by
    intro S hS
    rw [gainOfSupport, if_pos (hthree S hS), ItemSystem.rigidFrac_w, if_pos hS, mul_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  ring

lemma ItemSystem.rigidFrac_mass (H : ItemSystem R) (hR : H.Rigid)
    (hthree : ∀ S ∈ H.supports, S.card = 3) :
    (H.rigidFrac hR).mass = (H.supports.card : ℚ) := by
  classical
  rw [Frac.mass, Finset.filter_true_of_mem hthree]
  have hterm : ∀ S ∈ H.supports, (H.rigidFrac hR).w S = 1 := by
    intro S hS
    rw [ItemSystem.rigidFrac_w, if_pos hS]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]

/-! ## 2. El enunciado abstracto

La versión del enunciado de limpieza que sólo usa el LP.  Los recursos son los del modelo
concreto —los pares de vértices, `Sym2 (Fin n)`— y los parámetros son los mismos; lo único
que se ha borrado es que los soportes provengan de cliques de un grafo. -/

/-- **`AbstractCleanupAt gam Cst m xi`** — la limpieza de codegree para un sistema de items
cualquiera sobre `Sym2 (Fin n)`.  Idéntica a `CodegreeCleanupAt` salvo que la familia de
soportes no tiene por qué ser la de las cliques de un grafo. -/
def AbstractCleanupAt (gam Cst : ℝ) (m xi : ℚ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (H : ItemSystem (Sym2 (Fin n))) (x : Frac H),
    (m : ℝ) * (n : ℝ) ^ 2 - 1 ≤ ((x.mass : ℚ) : ℝ) →
    ∃ y : Frac H,
      (∀ r s : Sym2 (Fin n), r ≠ s → ((y.codeg r s : ℚ) : ℝ) ≤ gam) ∧
      Cst ≤ ((y.mass : ℚ) : ℝ) ∧
      x.value - y.value ≤ xi * (n : ℚ) ^ 2

/-! ## 3. El lado positivo: escalar

Escalar `x` por un factor `t ≤ gam` produce siempre un `y` admisible: el codegrado de `x` nunca
pasa de `1`, luego el de `t·x` no pasa de `t`.  El precio es una pérdida de valor de
`(1-t)·value x`, que la cota universal acota por `(1-t)·(5/6)·n²`.  Es **todo** lo que la
dualidad lineal da, y es exactamente lo que el módulo de obstrucción demuestra que no se puede
mejorar. -/

lemma card_sym2_fin_le (n : ℕ) : (Fintype.card (Sym2 (Fin n)) : ℚ) ≤ (n : ℚ) ^ 2 := by
  have hsurj : Function.Surjective (fun p : Fin n × Fin n => s(p.1, p.2)) := by
    intro e
    induction e using Sym2.ind with
    | _ a b => exact ⟨(a, b), rfl⟩
  have hcard : Fintype.card (Sym2 (Fin n)) ≤ Fintype.card (Fin n × Fin n) :=
    Fintype.card_le_of_surjective _ hsurj
  have : (Fintype.card (Sym2 (Fin n)) : ℚ) ≤ (Fintype.card (Fin n × Fin n) : ℚ) := by
    exact_mod_cast hcard
  simpa [Fintype.card_prod, sq] using this

/-- **La limpieza abstracta vale en el régimen de holgura.**  Si la pérdida admitida `xi` cubre
`(1-t)·(5/6)` para algún racional `t ≤ gam`, el escalado `t·x` sirve, y el umbral `N` es
explícito: `N = ⌈(Cst/t + 1)/m⌉₊`. -/
theorem abstractCleanupAt_of_scale (gam Cst : ℝ) (m xi t : ℚ)
    (ht0 : 0 < t) (ht1 : t ≤ 1) (htgam : (t : ℝ) ≤ gam) (hm : 0 < m)
    (hxi : (1 - t) * 5 ≤ 6 * xi) :
    AbstractCleanupAt gam Cst m xi := by
  classical
  refine ⟨max 1 ⌈(Cst / (t : ℝ) + 1) / (m : ℝ)⌉₊, ?_⟩
  intro n hn H x hmass
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnceil : ⌈(Cst / (t : ℝ) + 1) / (m : ℝ)⌉₊ ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have ht0R : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  refine ⟨x.scale t ht0.le ht1, ?_, ?_, ?_⟩
  · -- codegrado
    intro r s _
    rw [Frac.codeg_scale]
    have h1 : x.codeg r s ≤ 1 := x.codeg_le_one r s
    have h2 : (t : ℝ) * ((x.codeg r s : ℚ) : ℝ) ≤ (t : ℝ) * 1 := by
      have : ((x.codeg r s : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h1
      exact mul_le_mul_of_nonneg_left this ht0R.le
    push_cast
    calc (t : ℝ) * ((x.codeg r s : ℚ) : ℝ) ≤ (t : ℝ) * 1 := h2
      _ = (t : ℝ) := mul_one _
      _ ≤ gam := htgam
  · -- masa
    rw [Frac.mass_scale]
    have hthresh : (Cst / (t : ℝ) + 1) / (m : ℝ) ≤ (n : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      exact_mod_cast hnceil
    have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hstep : Cst / (t : ℝ) + 1 ≤ (m : ℝ) * (n : ℝ) ^ 2 := by
      rw [div_le_iff₀ hmR] at hthresh
      nlinarith
    have hmassR : Cst / (t : ℝ) ≤ ((x.mass : ℚ) : ℝ) := by linarith
    have := mul_le_mul_of_nonneg_left hmassR ht0R.le
    rw [mul_div_cancel₀ _ (ne_of_gt ht0R)] at this
    push_cast
    exact this
  · -- pérdida de valor
    rw [Frac.value_scale]
    have hvalue : x.value ≤ (5 / 6 : ℚ) * (n : ℚ) ^ 2 := by
      refine le_trans (Frac.value_le_card x) ?_
      have := card_sym2_fin_le n
      nlinarith [this]
    have hv0 : 0 ≤ x.value := x.value_nonneg
    nlinarith [hvalue, hv0, hxi, ht0.le, ht1]

end FarExploration.CleanupLP
