import PaperIV.SplitCompleteSharpValue
import PaperIV.SplitUniformIncidence
import PaperIV.TargetEnvelope

/-!
# Casos de igualdad dentro de la familia completo-split

`SplitCompleteSharpLower.critical_baseline_eq_targetSize` dice que **un** completo-split concreto
—el de núcleo `(n+1)/3`— alcanza `targetSize n`. Este módulo responde la pregunta siguiente:
**¿cuáles lo alcanzan?**

La respuesta es completa y sale de una identidad exacta. Escribiendo

```text
f(n, k) = k · (n − k) − C(k, 2)
```

para el valor óptimo del completo-split con núcleo de tamaño `k` sobre `n` vértices, se tiene

```text
6 · f(n, k) + (n − 3k) · (n − 3k + 1) = n · (n + 1).
```

El segundo sumando es un producto de **enteros consecutivos**, luego nunca es negativo: de ahí
`f(n,k) ≤ n(n+1)/6` para todo `k`. Y como `targetSize n` es el suelo de `n(n+1)/6`, la igualdad
obliga a que ese producto sea a lo sumo `5`, lo que deja exactamente cuatro valores posibles de
`n − 3k`, a saber `-2, -1, 0, 1`.

## La clasificación

```text
f(n, k) = targetSize n   ⟺   k = (n+1)/3   ∨   3k = n + 2
```

La segunda alternativa sólo tiene solución cuando `n ≡ 1 (mod 3)`, y en ese caso `(n+2)/3` es
exactamente `(n+1)/3 + 1`. Dicho en palabras:

* si `n ≢ 1 (mod 3)`, el núcleo óptimo es **único**;
* si `n ≡ 1 (mod 3)`, hay **exactamente dos** núcleos óptimos, y son consecutivos.

El caso con dos es real, no un artefacto de la escritura: para `n = 7` los núcleos `2` y `3` dan
ambos `9`, y para `n = 10` los núcleos `3` y `4` dan ambos `18`.

## Qué **no** dice esto

Clasifica los extremizadores **dentro de la familia completo-split**. No afirma que todo cordal
extremal sea un completo-split: esa es una pregunta distinta, sigue abierta, y necesitaría un
teorema de rigidez que aquí no está. Leer este resultado como «clasificación de todos los casos de
igualdad» sería una sobreafirmación.
-/

namespace PaperIV.SplitCompleteRigidity

open PaperIV.SplitUniformIncidence

/-- El valor óptimo del completo-split con núcleo de tamaño `k` sobre `n` vértices. -/
def baseline (n k : ℕ) : ℕ := k * (n - k) - k.choose 2

/-! ## 1. La identidad exacta -/

/-- **La identidad que gobierna todo.**  El defecto respecto de `n(n+1)` es el producto de dos
enteros consecutivos centrado en `n − 3k`. -/
theorem six_mul_baseline_add_sq (n k : ℕ) (hk : k ≤ n)
    (hle : k.choose 2 ≤ k * (n - k)) :
    6 * (baseline n k : ℤ) + ((n : ℤ) - 3 * k) * ((n : ℤ) - 3 * k + 1)
      = (n : ℤ) * ((n : ℤ) + 1) := by
  have hb : baseline n k + k.choose 2 = k * (n - k) := Nat.sub_add_cancel hle
  have hbZ : (baseline n k : ℤ) + (k.choose 2 : ℤ) = (k : ℤ) * ((n : ℤ) - (k : ℤ)) := by
    have h := congrArg (fun m : ℕ => (m : ℤ)) hb
    push_cast [Nat.cast_sub hk] at h
    linarith
  have hc : (2 : ℤ) * (k.choose 2 : ℤ) = (k : ℤ) * ((k : ℤ) - 1) := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp
    · have h := congrArg (fun m : ℕ => (m : ℤ)) (mul_pred_eq_two_mul_choose_two k)
      push_cast [Nat.cast_sub hkpos] at h
      linarith
  nlinarith [hbZ, hc]

/-! ## 2. La cota superior -/

/-- Producto de dos enteros consecutivos: nunca negativo. -/
private theorem consecutive_nonneg (m : ℤ) : 0 ≤ m * (m + 1) := by
  rcases lt_trichotomy m 0 with h | h | h
  · have h1 : m + 1 ≤ 0 := by omega
    nlinarith
  · simp [h]
  · positivity

/-- **El completo-split nunca supera `targetSize n`.** -/
theorem baseline_le_targetSize (n k : ℕ) (hk : k ≤ n) :
    baseline n k ≤ PaperIV.targetSize n := by
  rcases Nat.lt_or_ge (k * (n - k)) (k.choose 2) with hgt | hle
  · have h0 : baseline n k = 0 := Nat.sub_eq_zero_of_le (le_of_lt hgt)
    omega
  · have hid := six_mul_baseline_add_sq n k hk hle
    have hnn := consecutive_nonneg ((n : ℤ) - 3 * k)
    have h6 : (6 : ℤ) * (baseline n k : ℤ) ≤ (n : ℤ) * ((n : ℤ) + 1) := by linarith
    have h6' : 6 * baseline n k ≤ n * (n + 1) := by exact_mod_cast h6
    unfold PaperIV.targetSize
    omega

/-! ## 3. La clasificación -/

/-- Si el producto de dos enteros consecutivos no llega a `6`, el centro está en `{-2,-1,0,1}`. -/
private theorem consecutive_le_five {m : ℤ} (h : m * (m + 1) ≤ 5) :
    m = -2 ∨ m = -1 ∨ m = 0 ∨ m = 1 := by
  by_contra hc
  push_neg at hc
  obtain ⟨h2, h1, h0, hp⟩ := hc
  rcases lt_trichotomy m 0 with hlt | heq | hgt
  · have : m ≤ -3 := by omega
    nlinarith
  · exact h0 heq
  · have : 2 ≤ m := by omega
    nlinarith

/-- **Los núcleos que alcanzan el máximo, exactamente.**

`k = (n+1)/3` siempre sirve; `3k = n + 2` es la segunda solución, que sólo existe cuando
`n ≡ 1 (mod 3)` y entonces vale `(n+1)/3 + 1`. -/
theorem baseline_eq_targetSize_iff (n k : ℕ) (hn : 2 ≤ n) (hk : k ≤ n) :
    baseline n k = PaperIV.targetSize n ↔ k = (n + 1) / 3 ∨ 3 * k = n + 2 := by
  have htarget : 6 * PaperIV.targetSize n ≤ n * (n + 1) ∧
      n * (n + 1) < 6 * PaperIV.targetSize n + 6 := by
    unfold PaperIV.targetSize; omega
  constructor
  · intro heq
    have hpos : 0 < PaperIV.targetSize n := by
      have h6 : 6 ≤ n * (n + 1) := by nlinarith
      unfold PaperIV.targetSize; omega
    have hle : k.choose 2 ≤ k * (n - k) := by
      by_contra hgt
      push_neg at hgt
      have : baseline n k = 0 := Nat.sub_eq_zero_of_le (le_of_lt hgt)
      omega
    have hid := six_mul_baseline_add_sq n k hk hle
    -- el producto es exactamente el resto, luego no llega a 6
    have hbt : (baseline n k : ℤ) = (PaperIV.targetSize n : ℤ) := by exact_mod_cast heq
    have hupZ : (n : ℤ) * ((n : ℤ) + 1) < 6 * (PaperIV.targetSize n : ℤ) + 6 := by
      exact_mod_cast htarget.2
    have hfive : ((n : ℤ) - 3 * k) * ((n : ℤ) - 3 * k + 1) ≤ 5 := by
      rw [hbt] at hid; linarith
    rcases consecutive_le_five hfive with h | h | h | h
    · right; omega          -- `n - 3k = -2`, es decir `3k = n + 2`
    · left; omega           -- `3k = n + 1`
    · left; omega           -- `3k = n`
    · left; omega           -- `3k = n - 1`, sólo con `n ≡ 1 (mod 3)`
  · intro hk'
    -- en los cuatro casos el producto vale 0 o 2, y con la cota superior eso fuerza la igualdad
    have hle : k.choose 2 ≤ k * (n - k) := by
      have hch : 2 * k.choose 2 = k * (k - 1) := (mul_pred_eq_two_mul_choose_two k).symm
      have hkn : 3 * k ≤ 2 * n + 1 := by rcases hk' with h | h <;> omega
      have h1 : k - 1 ≤ 2 * (n - k) := by omega
      have h2 : k * (k - 1) ≤ k * (2 * (n - k)) := Nat.mul_le_mul (le_refl k) h1
      have h3 : k * (2 * (n - k)) = 2 * (k * (n - k)) := by ring
      omega
    have hid := six_mul_baseline_add_sq n k hk hle
    have hprod : ((n : ℤ) - 3 * k) * ((n : ℤ) - 3 * k + 1) ≤ 2 := by
      rcases hk' with h | h
      · have : (n : ℤ) - 3 * k = 0 ∨ (n : ℤ) - 3 * k = -1 ∨ (n : ℤ) - 3 * k = 1 := by omega
        rcases this with h' | h' | h' <;> rw [h'] <;> norm_num
      · have : (n : ℤ) - 3 * k = -2 := by omega
        rw [this]; norm_num
    have hlowZ : (6 : ℤ) * (PaperIV.targetSize n : ℤ) ≤ (n : ℤ) * ((n : ℤ) + 1) := by
      exact_mod_cast htarget.1
    have hupZ : (n : ℤ) * ((n : ℤ) + 1) < 6 * (PaperIV.targetSize n : ℤ) + 6 := by
      exact_mod_cast htarget.2
    have hge : (PaperIV.targetSize n : ℤ) ≤ (baseline n k : ℤ) := by linarith
    have hge' : PaperIV.targetSize n ≤ baseline n k := by exact_mod_cast hge
    exact le_antisymm (baseline_le_targetSize n k hk) hge'

/-- **Unicidad salvo el caso `n ≡ 1 (mod 3)`.**  Si `n` no es `1` módulo `3`, el núcleo óptimo es
único; si lo es, los óptimos son exactamente dos y consecutivos. -/
theorem optimal_cores (n : ℕ) (hn : 2 ≤ n) :
    (n % 3 ≠ 1 → ∀ k ≤ n, (baseline n k = PaperIV.targetSize n ↔ k = (n + 1) / 3)) ∧
    (n % 3 = 1 → ∀ k ≤ n, (baseline n k = PaperIV.targetSize n ↔
      k = (n + 1) / 3 ∨ k = (n + 1) / 3 + 1)) := by
  refine ⟨fun h3 k hk => ?_, fun h3 k hk => ?_⟩ <;>
    rw [baseline_eq_targetSize_iff n k hn hk] <;>
    constructor <;> intro h <;> omega

end PaperIV.SplitCompleteRigidity
