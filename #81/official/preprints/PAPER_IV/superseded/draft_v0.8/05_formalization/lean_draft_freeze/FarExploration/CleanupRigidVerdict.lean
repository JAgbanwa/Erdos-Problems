import FarExploration.RigidThreshold
import FarExploration.RuzsaSzemeredi

/-!
# Veredicto: la rigidez **no** la excluye la masa cuadrática

Este módulo junta las dos piezas anteriores —la cota inferior del umbral para familias rígidas
(`FarExploration.RigidThreshold`) y el grafo rígido de Ruzsa–Szemerédi
(`FarExploration.RuzsaSzemeredi`)— y saca la consecuencia cuantitativa.

## Lo que se demuestra

1. **Hay grafos rígidos de masa casi cuadrática** (`rs_rigid_mass_ge`).  Sobre `n = 6M+3`
   vértices, a partir de un conjunto `s ⊆ [0,M)` sin progresiones aritméticas de tres términos,
   el grafo `rsGraph` tiene **todas sus aristas en un único triángulo** y sin embargo su masa
   triangular es `(2M+1)·|s|`, es decir `≈ n²·|s|/(18M)`.  Con la cota de Behrend,
   `|s| ≥ M·e^{-4√(log M)}`, la masa es `n^{2-o(1)}`.

   Esto **refuta la hipótesis de trabajo** de que un grafo rígido sea una unión de triángulos
   disjuntos y tenga masa lineal.  La unión de triángulos disjuntos es sólo el caso más pobre.

2. **El umbral de la limpieza es superpolinómico en `1/eps`** (`threshold_superpolynomial`).
   Para los parámetros de la aplicación `m = eps/30`, `xi = eps/4` y `gam ≤ 1/2`, todo umbral
   válido `N₀` cumple `N₀ > (1/eps)^k` en cuanto `log(1/(7·eps)) ≥ 32k+4`.  En particular el
   umbral **no** puede ser del orden de `1/xi`, ni de ningún polinomio en `1/eps`: la esperanza
   de bajar de torre a `≈ 2·10^16` es imposible tal cual.  La forma cerrada es
   `N₀ > exp(t²/16)` con `t = log(1/(7·eps))` (`threshold_gt_exp`).

## Lo que **no** se demuestra, dicho explícitamente

* No se refuta `CodegreeCleanupAt`.  La familia rígida de arriba deja de cumplir la hipótesis de
  masa en cuanto `n` crece, porque la densidad de un conjunto sin progresiones tiende a cero
  (teorema `(6,3)` de Ruzsa–Szemerédi, **no** formalizado aquí).  Lo que se demuestra es una
  cota inferior del umbral, no la falsedad del enunciado.
* No se demuestra ninguna cota superior del umbral.  El hueco entre esta cota inferior
  —superpolinómica— y la torre actual sigue abierto.
* Todos los enunciados de este módulo son cotas **inferiores** del umbral y valen en el régimen
  de la aplicación (`m = eps/30`, `xi = eps/4`, `gam ≤ 1/2`, `eps` arbitrariamente pequeño).
-/

namespace FarExploration.CleanupRigidVerdict

open Finset MixedRounding FarExploration.CleanupLP FarExploration.CleanupBridge
open FarExploration.CleanupThreshold FarExploration.RigidThreshold
open FarExploration.RuzsaSzemeredi

/-! ## 1. De un conjunto de naturales sin progresiones a un subconjunto de `ZMod (2M+1)` -/

instance instNeZeroTwoMulAddOne (M : ℕ) : NeZero (2 * M + 1) := ⟨by omega⟩

/-- La imagen en `ZMod (2M+1)` de un conjunto de naturales. -/
def zA (M : ℕ) (s : Finset ℕ) : Finset (ZMod (2 * M + 1)) :=
  Finset.image (fun k : ℕ => (k : ZMod (2 * M + 1))) s

lemma natCast_inj_of_lt {M a b : ℕ} (ha : a < 2 * M + 1) (hb : b < 2 * M + 1)
    (h : (a : ZMod (2 * M + 1)) = (b : ZMod (2 * M + 1))) : a = b := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at this

lemma mem_zA {M : ℕ} {s : Finset ℕ} {z : ZMod (2 * M + 1)} :
    z ∈ zA M s ↔ ∃ k ∈ s, (k : ZMod (2 * M + 1)) = z := by
  simp [zA]

lemma card_zA {M : ℕ} {s : Finset ℕ} (hs : s ⊆ Finset.range M) : (zA M s).card = s.card := by
  classical
  refine Finset.card_image_of_injOn ?_
  intro a ha b hb h
  have ha' : a < 2 * M + 1 := by
    have := Finset.mem_range.1 (hs ha); omega
  have hb' : b < 2 * M + 1 := by
    have := Finset.mem_range.1 (hs hb); omega
  exact natCast_inj_of_lt ha' hb' h

/-- La imagen de un conjunto sin progresiones de tres términos sigue sin tenerlas: la
condición `s ⊆ [0,M)` con módulo `2M+1` impide cualquier vuelta. -/
lemma threeAPFree_zA {M : ℕ} {s : Finset ℕ} (hs : s ⊆ Finset.range M)
    (hs3 : ThreeAPFree (s : Set ℕ)) :
    ThreeAPFree (↑(zA M s) : Set (ZMod (2 * M + 1))) := by
  classical
  intro a ha b hb c hc habc
  obtain ⟨a', ha', rfl⟩ := mem_zA.1 (by simpa using ha)
  obtain ⟨b', hb', rfl⟩ := mem_zA.1 (by simpa using hb)
  obtain ⟨c', hc', rfl⟩ := mem_zA.1 (by simpa using hc)
  have haM : a' < M := Finset.mem_range.1 (hs ha')
  have hbM : b' < M := Finset.mem_range.1 (hs hb')
  have hcM : c' < M := Finset.mem_range.1 (hs hc')
  have hcast : ((a' + c' : ℕ) : ZMod (2 * M + 1)) = ((b' + b' : ℕ) : ZMod (2 * M + 1)) := by
    push_cast
    exact habc
  have hnat : a' + c' = b' + b' :=
    natCast_inj_of_lt (by omega) (by omega) hcast
  have hab : a' = b' := hs3 (by simpa using ha') (by simpa using hb') (by simpa using hc') hnat
  rw [hab]

/-- Sobre la imagen, la duplicación `a ↦ a + a` es inyectiva: el módulo `2M+1` es impar. -/
lemma dbl_zA {M : ℕ} {s : Finset ℕ} (hs : s ⊆ Finset.range M) :
    ∀ a ∈ zA M s, ∀ b ∈ zA M s, a + a = b + b → a = b := by
  classical
  intro a ha b hb hab
  obtain ⟨a', ha', rfl⟩ := mem_zA.1 ha
  obtain ⟨b', hb', rfl⟩ := mem_zA.1 hb
  have haM : a' < M := Finset.mem_range.1 (hs ha')
  have hbM : b' < M := Finset.mem_range.1 (hs hb')
  have hcast : ((a' + a' : ℕ) : ZMod (2 * M + 1)) = ((b' + b' : ℕ) : ZMod (2 * M + 1)) := by
    push_cast
    exact hab
  have hnat : a' + a' = b' + b' := natCast_inj_of_lt (by omega) (by omega) hcast
  have : a' = b' := by omega
  rw [this]

/-! ## 2. El grafo rígido de masa casi cuadrática -/

/-- **Un grafo rígido con `(2M+1)·|s|` triángulos.**  Todas sus aristas están en un único
triángulo y, sin embargo, su masa triangular es `(2M+1)·|s|`; con `n = 6M+3` vértices eso es
del orden de `n²·(|s|/M)/18`. -/
theorem rs_rigid_mass_ge (M : ℕ) (s : Finset ℕ) (hs : s ⊆ Finset.range M)
    (hs3 : ThreeAPFree (s : Set ℕ)) :
    (graphSystem (rsGraph (zA M s))).Rigid ∧
    (∀ S ∈ (graphSystem (rsGraph (zA M s))).supports, S.card = 3) ∧
    (((2 * M + 1) * s.card : ℕ) : ℝ)
      ≤ ((graphSystem (rsGraph (zA M s))).supports.card : ℝ) := by
  refine ⟨graphSystem_rigid (threeAPFree_zA hs hs3) (dbl_zA hs), graphSystem_three _, ?_⟩
  have h := card_supports_ge (A := zA M s) (dbl_zA hs)
  rw [card_zA hs] at h
  exact_mod_cast h

/-! ## 3. La cota inferior del umbral -/

/-- **Cota inferior del umbral por la familia de Ruzsa–Szemerédi.**  Si `N₀` es un umbral válido
para la limpieza y `s ⊆ [0,M)` no tiene progresiones aritméticas de tres términos, con
`T = (2M+1)·|s|` triángulos rígidos sobre `n = 3(2M+1)` vértices, entonces `n < N₀` en cuanto la
masa alcanza la hipótesis cuadrática y la pérdida forzada supera la admitida. -/
theorem rs_threshold_gt (gam Cst : ℝ) (m xi : ℚ) (hgam : gam ≤ 1) (N₀ M : ℕ)
    (s : Finset ℕ) (hs : s ⊆ Finset.range M) (hs3 : ThreeAPFree (s : Set ℕ))
    (hN : CleanupAtWith gam Cst m xi N₀)
    (hmass : (m : ℝ) * ((3 * (2 * M + 1) : ℕ) : ℝ) ^ 2 - 1 ≤ (((2 * M + 1) * s.card : ℕ) : ℝ))
    (hloss : (xi : ℝ) * ((3 * (2 * M + 1) : ℕ) : ℝ) ^ 2
      < 2 * (1 - gam) * (((2 * M + 1) * s.card : ℕ) : ℝ)) :
    3 * (2 * M + 1) < N₀ := by
  obtain ⟨hrigid, hthree, hcard⟩ := rs_rigid_mass_ge M s hs hs3
  exact rigid_threshold_gt (rsGraph (zA M s)) gam Cst m xi hgam N₀ hN hrigid hthree
    (((2 * M + 1) * s.card : ℕ) : ℝ) hcard hmass hloss

/-! ## 4. Los parámetros de la aplicación, y la cota de Behrend -/

/-- **Cota inferior del umbral en los parámetros de la aplicación.**  Con `m = eps/30`,
`xi = eps/4` y `gam ≤ 1/2`, si el número de Roth de `M` supera `7·eps·M`, entonces todo umbral
válido supera `3(2M+1) = 6M+3`. -/
theorem application_threshold_gt (eps : ℚ) (heps : 0 < eps) (gam Cst : ℝ) (hgam : gam ≤ 1 / 2)
    (N₀ M : ℕ) (hM : 1 ≤ M) (hN : CleanupAtWith gam Cst (eps / 30) (eps / 4) N₀)
    (hdens : 7 * (eps : ℝ) * (M : ℝ) ≤ (rothNumberNat M : ℝ)) :
    3 * (2 * M + 1) < N₀ := by
  obtain ⟨s, hs, hcard, hs3⟩ := rothNumberNat_spec M
  have hx1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hcardR : (s.card : ℝ) = (rothNumberNat M : ℝ) := by exact_mod_cast hcard
  have hT : (((2 * M + 1) * s.card : ℕ) : ℝ) = (2 * (M : ℝ) + 1) * (rothNumberNat M : ℝ) := by
    push_cast [hcardR]
    ring
  have hn : (((3 * (2 * M + 1) : ℕ)) : ℝ) = 3 * (2 * (M : ℝ) + 1) := by push_cast; ring
  refine rs_threshold_gt gam Cst (eps / 30) (eps / 4) (by linarith) N₀ M s hs hs3 hN ?_ ?_
  · rw [hT, hn]
    have hm : ((eps / 30 : ℚ) : ℝ) = (eps : ℝ) / 30 := by push_cast; ring
    rw [hm]
    nlinarith [hdens, hx1, hepsR, mul_pos hepsR (by linarith : (0:ℝ) < 2 * (M:ℝ) + 1)]
  · rw [hT, hn]
    have hxi : ((eps / 4 : ℚ) : ℝ) = (eps : ℝ) / 4 := by push_cast; ring
    rw [hxi]
    have hgam1 : (1 : ℝ) ≤ 2 * (1 - gam) := by linarith
    have hR0 : (0 : ℝ) ≤ (rothNumberNat M : ℝ) := Nat.cast_nonneg _
    have hstep : (eps : ℝ) / 4 * (3 * (2 * (M : ℝ) + 1)) ^ 2
        < (2 * (M : ℝ) + 1) * (rothNumberNat M : ℝ) := by
      nlinarith [hdens, hx1, hepsR, mul_pos hepsR (by linarith : (0:ℝ) < 2 * (M:ℝ) + 1)]
    nlinarith [hstep, hgam1, mul_nonneg (by linarith : (0:ℝ) ≤ 2 * (M:ℝ) + 1) hR0]

/-- **La misma cota, ya con Behrend.**  Si `7·eps ≤ exp(-4√(log M))` entonces todo umbral válido
supera `6M+3`.  La condición dice que la densidad que Behrend garantiza para los conjuntos sin
progresiones todavía alcanza el nivel `eps`. -/
theorem application_threshold_gt_behrend (eps : ℚ) (heps : 0 < eps) (gam Cst : ℝ)
    (hgam : gam ≤ 1 / 2) (N₀ M : ℕ) (hM : 1 ≤ M)
    (hN : CleanupAtWith gam Cst (eps / 30) (eps / 4) N₀)
    (hdens : 7 * (eps : ℝ) ≤ Real.exp (-4 * Real.sqrt (Real.log M))) :
    3 * (2 * M + 1) < N₀ := by
  refine application_threshold_gt eps heps gam Cst hgam N₀ M hM hN ?_
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hbeh : (M : ℝ) * Real.exp (-4 * Real.sqrt (Real.log M)) ≤ (rothNumberNat M : ℝ) :=
    Behrend.roth_lower_bound
  nlinarith [hdens, hM0, hbeh]

/-- **La forma cerrada de la cota.**  Si `7·eps ≤ e^{-t}` con `t ≥ 4`, todo umbral válido de la
limpieza supera `exp(t²/16)`.  Con `t = log(1/(7·eps))` esto es `exp(log²(1/(7eps))/16)`:
cuasipolinómico en `1/eps`, muy por encima de cualquier `C/eps`. -/
theorem threshold_gt_exp (eps : ℚ) (heps : 0 < eps) (gam Cst : ℝ) (hgam : gam ≤ 1 / 2) (N₀ : ℕ)
    (hN : CleanupAtWith gam Cst (eps / 30) (eps / 4) N₀) (t : ℝ) (ht : 4 ≤ t)
    (hteps : 7 * (eps : ℝ) ≤ Real.exp (-t)) :
    Real.exp (t ^ 2 / 16) < (N₀ : ℝ) := by
  set E : ℝ := Real.exp (t ^ 2 / 16) with hE
  have hE1 : (1 : ℝ) ≤ E := Real.one_le_exp (by positivity)
  have hE0 : (0 : ℝ) ≤ E := by linarith
  set M : ℕ := ⌊E⌋₊ with hMdef
  have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast hE1)
  have hMle : (M : ℝ) ≤ E := Nat.floor_le hE0
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hlogM : Real.log M ≤ t ^ 2 / 16 := by
    rw [Real.log_le_iff_le_exp hMpos]
    exact hMle
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hsqrt : Real.sqrt (Real.log M) ≤ t / 4 := by
    have h1 : Real.sqrt (Real.log M) ≤ Real.sqrt (t ^ 2 / 16) := Real.sqrt_le_sqrt hlogM
    have h2 : Real.sqrt (t ^ 2 / 16) = t / 4 := by
      rw [show t ^ 2 / 16 = (t / 4) ^ 2 by ring, Real.sqrt_sq (by linarith)]
    linarith [h1, h2.le, h2.ge]
  have hdens : 7 * (eps : ℝ) ≤ Real.exp (-4 * Real.sqrt (Real.log M)) := by
    refine le_trans hteps ?_
    exact Real.exp_le_exp.2 (by linarith)
  have hmain := application_threshold_gt_behrend eps heps gam Cst hgam N₀ M hM1 hN hdens
  have hlt : E < (M : ℝ) + 1 := Nat.lt_floor_add_one E
  have hcast : ((3 * (2 * M + 1) : ℕ) : ℝ) < (N₀ : ℝ) := by exact_mod_cast hmain
  have hle : (M : ℝ) + 1 ≤ ((3 * (2 * M + 1) : ℕ) : ℝ) := by push_cast; linarith
  linarith

/-- **El umbral no es polinómico en `1/eps`.**  Para cada exponente `k`, si `eps` es
suficientemente pequeño —`log(1/(7·eps)) ≥ 32k+4`— todo umbral válido de la limpieza supera
`(1/eps)^k`.  En particular la esperanza de un umbral del orden de `1/xi` es imposible. -/
theorem threshold_superpolynomial (k : ℕ) (eps : ℚ) (heps : 0 < eps) (gam Cst : ℝ)
    (hgam : gam ≤ 1 / 2) (N₀ : ℕ) (hN : CleanupAtWith gam Cst (eps / 30) (eps / 4) N₀)
    (hk : (32 * k + 4 : ℝ) ≤ Real.log (1 / (7 * (eps : ℝ)))) :
    (1 / (eps : ℝ)) ^ k < (N₀ : ℝ) := by
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hpos : (0 : ℝ) < 1 / (7 * (eps : ℝ)) := by positivity
  set t : ℝ := Real.log (1 / (7 * (eps : ℝ))) with htdef
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have ht4 : 4 ≤ t := by linarith
  have hexp : Real.exp t = 1 / (7 * (eps : ℝ)) := Real.exp_log hpos
  have hteps : 7 * (eps : ℝ) ≤ Real.exp (-t) := by
    have hval : Real.exp (-t) = 7 * (eps : ℝ) := by
      rw [Real.exp_neg, hexp, one_div, inv_inv]
    exact hval.ge
  have hmain := threshold_gt_exp eps heps gam Cst hgam N₀ hN t ht4 hteps
  have h1e : 1 / (eps : ℝ) = 7 * Real.exp t := by
    rw [hexp]
    field_simp
  have h7 : (7 : ℝ) ≤ Real.exp 2 := by
    have h := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [h, Real.exp_pos 1]
  have hpow : (1 / (eps : ℝ)) ^ k ≤ Real.exp (2 * (k : ℝ) + (k : ℝ) * t) := by
    have hA : (7 : ℝ) ^ k ≤ Real.exp (2 * (k : ℝ)) := by
      calc (7 : ℝ) ^ k ≤ (Real.exp 2) ^ k := by gcongr
        _ = Real.exp ((k : ℝ) * 2) := by rw [← Real.exp_nat_mul]
        _ = Real.exp (2 * (k : ℝ)) := by rw [mul_comm]
    have hB : (Real.exp t) ^ k = Real.exp ((k : ℝ) * t) := by
      rw [← Real.exp_nat_mul]
    have hsplit : Real.exp (2 * (k : ℝ) + (k : ℝ) * t)
        = Real.exp (2 * (k : ℝ)) * Real.exp ((k : ℝ) * t) := Real.exp_add _ _
    rw [h1e, mul_pow, hB, hsplit]
    exact mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
  have hquad : 2 * (k : ℝ) + (k : ℝ) * t ≤ t ^ 2 / 16 := by
    nlinarith [hk, ht4, hk0]
  calc (1 / (eps : ℝ)) ^ k ≤ Real.exp (2 * (k : ℝ) + (k : ℝ) * t) := hpow
    _ ≤ Real.exp (t ^ 2 / 16) := Real.exp_le_exp.2 hquad
    _ < (N₀ : ℝ) := hmain


/-- **La cifra concreta.**  Si `eps ≤ 1/(7·e³⁴) ≈ 2.3·10⁻¹⁶` —el orden de magnitud que la rama
lejana necesita— entonces todo umbral válido de la limpieza supera `e⁷² ≈ 1.9·10³¹`.  Es decir:
el umbral `≈ 1/xi ≈ 2·10¹⁶` que se esperaba no es alcanzable; la cota inferior lo supera en
quince órdenes de magnitud. -/
theorem threshold_gt_exp_seventy_two (eps : ℚ) (heps : 0 < eps) (gam Cst : ℝ) (hgam : gam ≤ 1 / 2)
    (N₀ : ℕ) (hN : CleanupAtWith gam Cst (eps / 30) (eps / 4) N₀)
    (hsmall : (eps : ℝ) ≤ 1 / (7 * Real.exp 34)) :
    Real.exp 72 < (N₀ : ℝ) := by
  have hteps : 7 * (eps : ℝ) ≤ Real.exp (-(34 : ℝ)) := by
    have hpos : (0 : ℝ) < Real.exp 34 := Real.exp_pos _
    rw [Real.exp_neg, inv_eq_one_div]
    calc 7 * (eps : ℝ) ≤ 7 * (1 / (7 * Real.exp 34)) :=
          mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _ = 1 / Real.exp 34 := by field_simp
  have hmain := threshold_gt_exp eps heps gam Cst hgam N₀ hN 34 (by norm_num) hteps
  have hmono : Real.exp 72 ≤ Real.exp ((34 : ℝ) ^ 2 / 16) := Real.exp_le_exp.2 (by norm_num)
  linarith


/-! ## 5. Qué tendría que demostrar cualquier argumento de dispersión -/

/-- **La limpieza implica una cota efectiva de tipo `(6,3)`.**

Si `N₀` es un umbral válido para la limpieza, entonces **todo** grafo rígido de items
triangulares —cada arista en un único triángulo— sobre `n ≥ N₀` vértices tiene pocos triángulos:
o bien su número de triángulos `T` no alcanza la masa `m·n²`, o bien `2(1-gam)·T ≤ xi·n²`.

Es decir: `T ≤ max(m, xi/(2(1-gam)))·n²` para todo `n ≥ N₀`.  Con los parámetros de la
aplicación eso es `T ≤ (eps/4)·n²` para `n ≥ N₀`, que es exactamente una versión **efectiva**
del teorema `(6,3)` de Ruzsa–Szemerédi con cota `N₀(eps)`.

Esto localiza el obstáculo: cualquier demostración de `CodegreeCleanupAt` —por dispersión,
promediado o lo que sea— produce automáticamente una cota efectiva para el problema `(6,3)`, con
el mismo umbral.  Las únicas cotas conocidas para ese problema pasan por el lema de eliminación
de triángulos (y por tanto por regularidad, con umbral de tipo torre), y por debajo están las
construcciones de Behrend, que ya obligan a `N₀` superpolinómico (arriba).  No es que el
argumento de dispersión falle por descuido: no puede evitar el conteo. -/
theorem rigid_card_le_of_cleanup (gam Cst : ℝ) (m xi : ℚ) (hgam : gam ≤ 1) (N₀ n : ℕ)
    (hN : CleanupAtWith gam Cst m xi N₀) (hn : N₀ ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hrigid : (graphSystem G).Rigid)
    (hthree : ∀ S ∈ (graphSystem G).supports, S.card = 3) :
    ((graphSystem G).supports.card : ℝ) < (m : ℝ) * (n : ℝ) ^ 2 ∨
      2 * (1 - gam) * ((graphSystem G).supports.card : ℝ) ≤ (xi : ℝ) * (n : ℝ) ^ 2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hmass, hloss⟩ := hcon
  have := rigid_threshold_gt G gam Cst m xi hgam N₀ hN hrigid hthree
    ((graphSystem G).supports.card : ℝ) (le_refl _) (by linarith) hloss
  omega


end FarExploration.CleanupRigidVerdict
