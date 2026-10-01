import PaperIV.H1LedgerArithmetic

/-!
# H1: las constantes mejoradas, con el denominador correcto

`H1LedgerArithmetic` formaliza la cadena con las constantes **tal como están escritas** en
`docs/RUTA_CANDIDATA_UNIFICADA_H1_SOURCE_20260912.md`. Este módulo formaliza la versión
**mejorada**, que sale de un solo cambio: no redondear la cota de `q`.

## Corrección respecto de la primera versión de este módulo

La primera versión tenía dos defectos, señalados por el equipo principal y ambos ciertos:

* usaba `Q²` donde el denominador real de (L2) es `q(q−1)`;
* sólo formalizaba la contribución en `A`, nunca la de `f`.

Aquí se corrigen los dos. El denominador se maneja como `R = q(q−1)/a²`, acotado por abajo con
`q ≥ Q·a` y `a ≥ 1024`, y se demuestran **las dos** contribuciones.

Además, la constante de `f` baja de `7/250` a `29/1000`. Con `q(q−1)` el coeficiente exacto es
`0,027827`, que cabe en `7/250 = 0,028` con sólo **0,6 %** de margen — exactamente el vicio que
esta revisión venía criticando en §5.4. `29/1000` deja un 4,0 %, y el efecto sobre la cota final
es prácticamente el mismo.

## El cambio y su efecto

§5.4 usa `q, q−1 ≥ 3a/2`, mientras que (L8) da

```
q ≥ (127/64 − 1/693)·a = 87947a/44352 ≈ 1,98293·a
```

Conservando la cota literal, (L10) pasa de `g ≤ (7/40)A + (1/25)f` a
`g ≤ (11/100)A + (29/1000)f`, y la cota final de

```
L ≤ base − (19/365)·m − (253/500)·A   a   L ≤ base − (117/1825)·m − (12687/20000)·A
```

Los descuentos suben un **23,2 %** y un **25,4 %**, y el margen frente a lo que hace falta —`1/20`
y `1/2`— pasa de 4,11 % y 1,20 % a **28,2 %** y **26,9 %**.

## Lo que este módulo NO establece

La propagación de ese margen a la hipótesis (H) y de ahí al `ε` de §5 está **calculada en
aritmética exacta pero no formalizada aquí**. No debe citarse como PASS.
-/

namespace PaperIV.H1ImprovedConstants

/-! ## 1. El denominador correcto -/

/-- **`q(q−1)/a² ≥ 393/100`.**

De `q ≥ Q·a` con `Q = 87947/44352` y `a ≥ 1024`: `q(q−1) ≥ Q²a² − Qa`, luego
`q(q−1)/a² ≥ Q² − Q/1024 = 3,930077… ≥ 3,93`.

Es el paso que la primera versión de este módulo se saltaba al escribir `Q²`. -/
theorem denominator_lower {a q : ℚ} (ha : (1024 : ℚ) ≤ a)
    (hq : (87947 : ℚ) / 44352 * a ≤ q) :
    (393 : ℚ) / 100 * a ^ 2 ≤ q * (q - 1) := by
  have ha0 : (0 : ℚ) < a := by linarith
  have hq0 : (0 : ℚ) < q := by nlinarith
  nlinarith [sq_nonneg (q - (87947 : ℚ) / 44352 * a), sq_nonneg a]

/-! ## 2. Las dos contribuciones -/

/-- **El coeficiente de `A` en (L10), con `R = q(q−1)/a²`.**

Normalizado por `a`: `P = p/a ≤ 101/100`, `Q = q/a ≥ 87947/44352`, `Dn = D/a ≤ 1/3`,
`T = t/a ≤ 1/256`, `S = s/a ≤ 1/48`, `(A+2f)/a² ≤ 11/2000`. El valor exacto es `0,101585`. -/
theorem contribution_A {Q R Dn T S P : ℚ}
    (hP : P ≤ (101 : ℚ) / 100) (hP0 : 0 ≤ P)
    (hQ : (87947 : ℚ) / 44352 ≤ Q)
    (hR : (393 : ℚ) / 100 ≤ R)
    (hD : Dn ≤ (1 : ℚ) / 3) (hD0 : 0 ≤ Dn)
    (hT : T ≤ (1 : ℚ) / 256) (hT0 : 0 ≤ T)
    (hS : S ≤ (1 : ℚ) / 48) (hS0 : 0 ≤ S) :
    S / Q + P * (Dn + 4 * T) / R + ((11 : ℚ) / 2000) / R ≤ (11 : ℚ) / 100 := by
  have hQ0 : (0 : ℚ) < Q := by linarith
  have hR0 : (0 : ℚ) < R := by linarith
  have h1 : S / Q ≤ ((1 : ℚ) / 48) / ((87947 : ℚ) / 44352) := by gcongr
  have hnum : P * (Dn + 4 * T) ≤ ((101 : ℚ) / 100) * ((1 : ℚ) / 3 + 4 * ((1 : ℚ) / 256)) := by
    have hsum : Dn + 4 * T ≤ (1 : ℚ) / 3 + 4 * ((1 : ℚ) / 256) := by linarith
    have hsum0 : (0 : ℚ) ≤ Dn + 4 * T := by linarith
    calc P * (Dn + 4 * T) ≤ ((101 : ℚ) / 100) * (Dn + 4 * T) :=
          mul_le_mul_of_nonneg_right hP hsum0
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)
  have h2 : P * (Dn + 4 * T) / R
      ≤ (((101 : ℚ) / 100) * ((1 : ℚ) / 3 + 4 * ((1 : ℚ) / 256))) / ((393 : ℚ) / 100) := by
    gcongr
  have h3 : ((11 : ℚ) / 2000) / R ≤ ((11 : ℚ) / 2000) / ((393 : ℚ) / 100) := by gcongr
  have hfin : ((1 : ℚ) / 48) / ((87947 : ℚ) / 44352)
      + (((101 : ℚ) / 100) * ((1 : ℚ) / 3 + 4 * ((1 : ℚ) / 256))) / ((393 : ℚ) / 100)
      + ((11 : ℚ) / 2000) / ((393 : ℚ) / 100) ≤ (11 : ℚ) / 100 := by norm_num
  linarith

/-- **El coeficiente de `f` en (L10)**, que la primera versión no formalizaba.

El valor exacto es `0,027827`. Cabe en `7/250 = 0,028` con sólo `0,6 %` de margen, así que se
enuncia con `29/1000 = 0,029`, que deja un `4,0 %`. -/
theorem contribution_f {Q R T S P : ℚ}
    (hP : P ≤ (101 : ℚ) / 100) (hP0 : 0 ≤ P)
    (hQ : (87947 : ℚ) / 44352 ≤ Q)
    (hR : (393 : ℚ) / 100 ≤ R)
    (hT : T ≤ (1 : ℚ) / 256) (hT0 : 0 ≤ T)
    (hS : S ≤ (1 : ℚ) / 48) (hS0 : 0 ≤ S) :
    2 * S / Q + 4 * P * T / R + 2 * ((11 : ℚ) / 2000) / R ≤ (29 : ℚ) / 1000 := by
  have hQ0 : (0 : ℚ) < Q := by linarith
  have hR0 : (0 : ℚ) < R := by linarith
  have h1 : 2 * S / Q ≤ (2 * ((1 : ℚ) / 48)) / ((87947 : ℚ) / 44352) := by gcongr
  have hnum : 4 * P * T ≤ 4 * ((101 : ℚ) / 100) * ((1 : ℚ) / 256) := by
    have h4P : 4 * P ≤ 4 * ((101 : ℚ) / 100) := by linarith
    calc 4 * P * T ≤ (4 * ((101 : ℚ) / 100)) * T :=
          mul_le_mul_of_nonneg_right h4P hT0
      _ ≤ _ := by nlinarith
  have h2 : 4 * P * T / R ≤ (4 * ((101 : ℚ) / 100) * ((1 : ℚ) / 256)) / ((393 : ℚ) / 100) := by
    gcongr
  have h3 : 2 * ((11 : ℚ) / 2000) / R ≤ (2 * ((11 : ℚ) / 2000)) / ((393 : ℚ) / 100) := by gcongr
  have hfin : (2 * ((1 : ℚ) / 48)) / ((87947 : ℚ) / 44352)
      + (4 * ((101 : ℚ) / 100) * ((1 : ℚ) / 256)) / ((393 : ℚ) / 100)
      + (2 * ((11 : ℚ) / 2000)) / ((393 : ℚ) / 100) ≤ (29 : ℚ) / 1000 := by norm_num
  linarith

/-- **The two coefficient estimates turn normalized (L2) into the corrected
(L10).**  This is the small but necessary adapter between the geometric
second-phase estimate and `ledger_le_improved`; without it the latter would
still receive the improved (L10) as an unrelated hypothesis. -/
theorem l10_of_normalized_l2 {Q R Dn T S P A f g : ℚ}
    (hP : P ≤ (101 : ℚ) / 100) (hP0 : 0 ≤ P)
    (hQ : (87947 : ℚ) / 44352 ≤ Q)
    (hR : (393 : ℚ) / 100 ≤ R)
    (hD : Dn ≤ (1 : ℚ) / 3) (hD0 : 0 ≤ Dn)
    (hT : T ≤ (1 : ℚ) / 256) (hT0 : 0 ≤ T)
    (hS : S ≤ (1 : ℚ) / 48) (hS0 : 0 ≤ S)
    (hA : 0 ≤ A) (hf : 0 ≤ f)
    (hL2 : g ≤
      (S / Q + P * (Dn + 4 * T) / R + ((11 : ℚ) / 2000) / R) * A
      + (2 * S / Q + 4 * P * T / R + 2 * ((11 : ℚ) / 2000) / R) * f) :
    g ≤ (11 : ℚ) / 100 * A + (29 : ℚ) / 1000 * f := by
  have hca := contribution_A hP hP0 hQ hR hD hD0 hT hT0 hS hS0
  have hcf := contribution_f hP hP0 hQ hR hT hT0 hS hS0
  nlinarith

/-- The exact raw RD09-L2 expression is bounded by the normalized expression
used by `l10_of_normalized_l2`.  This is the missing algebraic adapter: the
quadratic term is linearized only with the explicit small-mass hypothesis,
and no estimate on `g` is postulated. -/
theorem raw_l2_le_normalized {a q p D t s A f g : ℚ}
    (ha : 0 < a) (hq : 1 < q)
    (hp : 2 ≤ p) (hD : 0 ≤ D) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hA : 0 ≤ A) (hf : 0 ≤ f)
    (hmass : A + 2 * f ≤ (11 : ℚ) / 2000 * a ^ 2)
    (hL2 : g ≤ s / q * (A + 2 * f) +
      ((p - 2) * ((D + 4 * t) * A + 4 * t * f) + (A + 2 * f) ^ 2) /
        (q * (q - 1))) :
    g ≤
      ((s / a) / (q / a) + (p / a) * (D / a + 4 * (t / a)) /
          (q * (q - 1) / a ^ 2) + ((11 : ℚ) / 2000) /
          (q * (q - 1) / a ^ 2)) * A +
      (2 * (s / a) / (q / a) + 4 * (p / a) * (t / a) /
          (q * (q - 1) / a ^ 2) + 2 * ((11 : ℚ) / 2000) /
          (q * (q - 1) / a ^ 2)) * f := by
  have hq0 : 0 < q := by linarith
  have hq10 : 0 < q - 1 := by linarith
  have hden : 0 < q * (q - 1) := mul_pos hq0 hq10
  have hS : 0 ≤ A + 2 * f := by positivity
  let M : ℚ := (D + 4 * t) * A + 4 * t * f
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpM : (p - 2) * M ≤ p * M := by nlinarith
  have hsq : (A + 2 * f) ^ 2 ≤
      ((11 : ℚ) / 2000 * a ^ 2) * (A + 2 * f) := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hmass hS
  have hraw :
      s / q * (A + 2 * f) +
          ((p - 2) * M + (A + 2 * f) ^ 2) / (q * (q - 1)) ≤
        s / q * (A + 2 * f) +
          (p * M + ((11 : ℚ) / 2000 * a ^ 2) * (A + 2 * f)) /
            (q * (q - 1)) := by
    gcongr
  have hid :
      s / q * (A + 2 * f) +
          (p * M + ((11 : ℚ) / 2000 * a ^ 2) * (A + 2 * f)) /
            (q * (q - 1)) =
        ((s / a) / (q / a) + (p / a) * (D / a + 4 * (t / a)) /
            (q * (q - 1) / a ^ 2) + ((11 : ℚ) / 2000) /
            (q * (q - 1) / a ^ 2)) * A +
        (2 * (s / a) / (q / a) + 4 * (p / a) * (t / a) /
            (q * (q - 1) / a ^ 2) + 2 * ((11 : ℚ) / 2000) /
            (q * (q - 1) / a ^ 2)) * f := by
    dsimp [M]
    field_simp
    ring
  rw [← hid]
  exact hL2.trans hraw

/-- Raw RD09-L2, together with the literal near-regime parameter bounds,
implies the improved L10 estimate.  This theorem composes the exact
normalization adapter with the previously verified coefficient calculation. -/
theorem l10_of_raw_rd09L2 {a q p D t s A f g : ℚ}
    (ha : (1024 : ℚ) ≤ a)
    (hq : (87947 : ℚ) / 44352 * a ≤ q)
    (hp2 : 2 ≤ p)
    (hP : p / a ≤ (101 : ℚ) / 100)
    (hD : D / a ≤ (1 : ℚ) / 3)
    (hT : t / a ≤ (1 : ℚ) / 256)
    (hS : s / a ≤ (1 : ℚ) / 48)
    (hD0 : 0 ≤ D) (ht0 : 0 ≤ t) (hs0 : 0 ≤ s)
    (hA : 0 ≤ A) (hf : 0 ≤ f)
    (hmass : A + 2 * f ≤ (11 : ℚ) / 2000 * a ^ 2)
    (hL2 : g ≤ s / q * (A + 2 * f) +
      ((p - 2) * ((D + 4 * t) * A + 4 * t * f) + (A + 2 * f) ^ 2) /
        (q * (q - 1))) :
    g ≤ (11 : ℚ) / 100 * A + (29 : ℚ) / 1000 * f := by
  have ha0 : 0 < a := by linarith
  have hq0 : 1 < q := by
    have : (1024 : ℚ) * ((87947 : ℚ) / 44352) ≤ q := by nlinarith
    norm_num at this ⊢
    linarith
  have hQ : (87947 : ℚ) / 44352 ≤ q / a :=
    (le_div_iff₀ ha0).2 hq
  have hden := denominator_lower ha hq
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha0
  have hR : (393 : ℚ) / 100 ≤ q * (q - 1) / a ^ 2 :=
    (le_div_iff₀ ha2).2 hden
  have hnorm := raw_l2_le_normalized ha0 hq0 hp2 hD0 ht0 hs0 hA hf hmass hL2
  exact l10_of_normalized_l2
    hP (by positivity) hQ hR hD (by positivity) hT (by positivity)
    hS (by positivity) hA hf hnorm

/-! ## 3. La cadena con las constantes seguras -/

/-- **La cota final mejorada.**  Misma (L3) y misma (L9); sólo cambia (L10), con las constantes
que `contribution_A` y `contribution_f` establecen. -/
theorem ledger_le_improved {base m A f g L : ℚ}
    (hA : 0 ≤ A) (hf : 0 ≤ f)
    (hL3 : L = base + m - A - 2 * f + 2 * g)
    (hL9 : (40 : ℚ) / 73 * m - (3 : ℚ) / 40 * A ≤ f)
    (hL10 : g ≤ (11 : ℚ) / 100 * A + (29 : ℚ) / 1000 * f) :
    L ≤ base - (117 : ℚ) / 1825 * m - (12687 : ℚ) / 20000 * A := by
  subst hL3
  linarith

/-- **La mejorada implica la escrita**, luego es sustituible sin tocar nada aguas abajo. -/
theorem improved_le_source {base m A L : ℚ} (hm : 0 ≤ m) (hA : 0 ≤ A)
    (h : L ≤ base - (117 : ℚ) / 1825 * m - (12687 : ℚ) / 20000 * A) :
    L ≤ base - (19 : ℚ) / 365 * m - (253 : ℚ) / 500 * A := by
  linarith

/-- **Y la forma débil, con margen.** -/
theorem improved_le_weak {base m A L : ℚ} (hm : 0 ≤ m) (hA : 0 ≤ A)
    (h : L ≤ base - (117 : ℚ) / 1825 * m - (12687 : ℚ) / 20000 * A) :
    L ≤ base - m / 20 - A / 2 := by
  linarith

/-- **El margen que queda**, escrito: más del 28 % en `m` y más del 26 % en `A`, frente al
4,11 % y 1,20 % de las constantes de la fuente. -/
theorem improved_margins :
    (1 : ℚ) / 20 * (1 + (28 : ℚ) / 100) ≤ (117 : ℚ) / 1825 ∧
      (1 : ℚ) / 2 * (1 + (26 : ℚ) / 100) ≤ (12687 : ℚ) / 20000 := by
  constructor <;> norm_num

end PaperIV.H1ImprovedConstants
