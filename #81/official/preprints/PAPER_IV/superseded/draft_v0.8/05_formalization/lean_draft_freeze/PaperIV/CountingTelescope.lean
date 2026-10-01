import PaperIV.RootedCountingBridge

/-!
# El telescopado y la constante `(4ℓ − 1)`

Tercera pieza de **GAP-RP01**.  Cierra toda la aritmética del paso (7), dejando como única
obligación externa la **estimación de un paso** de regularidad.

## Las dos piezas

* `telescoping_bound` — si reemplazar una pareja a la vez cuesta `ε` por paso, un patrón de
  `m` parejas cuesta `m·ε`.  Es la estructura entera de la prueba del lema de conteo:
  **reduce el conteo de un patrón a `m` aplicaciones de la estimación de una pareja**.

* `second_moment_constant` — la aritmética de GAP-RP01 (7), **verificada**:
  con `N₁ ≤ ℓ·δ·t^(s+2)` (el patrón tiene `ℓ` parejas),
  `N₂ ≤ (2ℓ−1)·δ·t^(2s+2)` (el duplicado tiene `2ℓ−1`) y `|A| ≤ t^s`,
  ```
  N₂ + 2·|A|·N₁  ≤  (4ℓ − 1)·δ·t^(2s+2).
  ```
  Con `ℓ = 6` (el caso `K₄`) eso es **`23`**, exactamente la constante que GAP-RP01 usa.
  Con `ℓ = 3` (el caso `K₃`) es `11`.

**La constante `23` de su paso (7) no es un ajuste:** es `4·6 − 1`, y se deduce de la
reducción `RootedCounting.second_moment_of_counts` combinada con el telescopado.  Eso
confirma que la descomposición formalizada aquí es la suya.

## Dónde queda la rama

```
segundo momento enraizado            ← RootedCounting.second_moment_of_counts   DEMOSTRADO
  = conteo de patrón + conteo del duplicado
                                     ← RootedCountingBridge.sum_fiber_card(_sq)  DEMOSTRADO
  telescopado: m parejas → m pasos   ← telescoping_bound                        DEMOSTRADO
  constante (4ℓ−1)                   ← second_moment_constant                   DEMOSTRADO
  ─────────────────────────────────────────────────────────────────────────────
  estimación de UN paso de regularidad                                          PENDIENTE
```

La obligación pendiente es una sola y es la estándar: al sustituir la adyacencia de una
pareja `ε`-regular por su densidad, el error es `≤ ε` veces el producto de los tamaños.
Mathlib tiene la infraestructura (`SimpleGraph.IsUniform`, `edgeDensity`, y el patrón de
`badVertices` / `triangle_split_helper` de Dillies–Mehta) pero **no** el enunciado bilateral
para patrón general.
-/

namespace PaperIV.CountingTelescope

open Finset

/-! ## 1. Telescopado -/

/-- **Telescopado.**  Si cada paso mueve el valor a lo sumo `ε`, `m` pasos lo mueven a lo
sumo `m·ε`.  Es la estructura del lema de conteo: sustituir una pareja a la vez. -/
theorem telescoping_bound (f : ℕ → ℚ) (ε : ℚ) (hε : 0 ≤ ε) :
    ∀ m : ℕ, (∀ k, k < m → |f k - f (k + 1)| ≤ ε) → |f 0 - f m| ≤ (m : ℚ) * ε := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ p ih =>
      intro hstep
      have hp : |f 0 - f p| ≤ (p : ℚ) * ε :=
        ih fun k hk => hstep k (Nat.lt_succ_of_lt hk)
      have hlast : |f p - f (p + 1)| ≤ ε := hstep p (Nat.lt_succ_self p)
      obtain ⟨hp1, hp2⟩ := abs_le.1 hp
      obtain ⟨hl1, hl2⟩ := abs_le.1 hlast
      have hcast : ((p + 1 : ℕ) : ℚ) * ε = (p : ℚ) * ε + ε := by push_cast; ring
      rw [hcast]
      exact abs_le.2 ⟨by linarith, by linarith⟩

/-! ## 2. La constante de GAP-RP01 (7) -/

/-- **La constante `(4ℓ − 1)`, verificada.**  El patrón tiene `ℓ` parejas y el duplicado
sobre la raíz tiene `2ℓ − 1`; con `|A| ≤ t^s` la reducción
`RootedCounting.second_moment_of_counts` da el coeficiente `4ℓ − 1`.

Con `ℓ = 6` (caso `K₄`) es **23**, la constante de GAP-RP01.  Con `ℓ = 3` (caso `K₃`) es 11. -/
theorem second_moment_constant (l s : ℕ) (t d A N₁ N₂ : ℚ)
    (ht : 0 ≤ t) (hd : 0 ≤ d)
    (hN₁ : N₁ ≤ (l : ℚ) * d * t ^ (s + 2))
    (hN₁0 : 0 ≤ N₁)
    (hN₂ : N₂ ≤ (2 * (l : ℚ) - 1) * d * t ^ (2 * s + 2))
    (hA : |A| ≤ t ^ s) :
    N₂ + 2 * |A| * N₁ ≤ (4 * (l : ℚ) - 1) * d * t ^ (2 * s + 2) := by
  have hts : (0 : ℚ) ≤ t ^ s := by positivity
  have hprod : |A| * N₁ ≤ t ^ s * ((l : ℚ) * d * t ^ (s + 2)) := by
    calc |A| * N₁ ≤ t ^ s * N₁ := mul_le_mul_of_nonneg_right hA hN₁0
      _ ≤ t ^ s * ((l : ℚ) * d * t ^ (s + 2)) :=
          mul_le_mul_of_nonneg_left hN₁ hts
  have hpow : t ^ s * t ^ (s + 2) = t ^ (2 * s + 2) := by
    rw [← pow_add]; ring_nf
  have hkey : t ^ s * ((l : ℚ) * d * t ^ (s + 2)) = (l : ℚ) * d * t ^ (2 * s + 2) := by
    rw [← hpow]; ring
  rw [hkey] at hprod
  linarith

/-- El caso `K₄`: `ℓ = 6` da la constante **23**. -/
theorem constant_K4 : (4 : ℚ) * 6 - 1 = 23 := by norm_num

/-- El caso `K₃`: `ℓ = 3` da la constante **11**. -/
theorem constant_K3 : (4 : ℚ) * 3 - 1 = 11 := by norm_num

end PaperIV.CountingTelescope
