import PaperIV.TriangleSwap
import PaperIV.Corollary73Assembly

/-!
# El adaptador que `RC01CleanedGate` declaraba pendiente, quitado

`PaperIV.RC01CleanedGate.lowTriangle_branch_of_cleanedSpread` cierra la rama de masa triangular
baja, pero a cambio de

```
hPk : (1 - β) * (restrictToK4 x′).value ≤ Pk.gain
```

es decir: que **el brazo puro de `K₄` entregue un packing**. Su docstring lo llama «el único
adaptador genuino que sigue faltando» (`docs/RC01_REMAINING_ADAPTER.md`), y con razón: ese brazo
sólo tiene `MixedRounding.round_arm_four`, que vuelve a pedir las tres estimaciones previas al
gate —carga casi perfecta fuera de un excepcional, excepcional pequeño y codegrado—.

**No hace falta.**  `PaperIV.TriangleSwap.lowTriangle_dichotomy` cierra esa rama sin el brazo de
`K₄` y sin ninguna de las tres, porque parte el problema por `ν(G)` —el máximo de triángulos
aristo-disjuntos del **grafo**, no la masa del empaquetamiento—:

* si `ν < C`, dualidad débil contra las `3ν` aristas de una familia maximal da `y.value ≤ 15C`
  para **todo** `y`, y el packing **vacío** cierra;
* si `ν ≥ C`, se sustituye `y` por `y″` con `triMass y″ ≥ C` perdiendo `13C` — y entonces el gate
  **sí** se aplica a `y″`, porque su hipótesis era exactamente masa triangular suficiente.

Las dos ramas evitan `round_arm_four`. Lo que quedaba era un hueco de ruta, no de verdad: el gate
no necesitaba que le trajeran un packing del brazo `K₄`, necesitaba un empaquetamiento con masa
triangular, y eso se fabrica.

## Qué se le pide al gate aquí

Sólo su conclusión, como hipótesis `hgate`, igual que en `Corollary73Assembly.dense_of_spread`:
dado un empaquetamiento con masa triangular `≥ C`, devuelve un packing con pérdida `≤ ζn²`. Así
el puente compone con `RC01CleanedGate.exists_packing_loss_le_of_cleanedSpread` sin repetir sus
doce hipótesis de umbrales.
-/

namespace PaperIV.CleanedLowTriangleBridge

open MixedRounding
open PaperIV.TriangleCover
open PaperIV.TriangleSwap

/-! ## 1. En `ℚ`, que es donde vive la dicotomía -/

/-- **La rama de masa triangular baja, sin adaptador.**

No hay hipótesis sobre `y`: la dicotomía es sobre el grafo. Y no aparece `restrictToK4` por
ningún lado. -/
theorem lowTriangle_branch_free {n : ℕ} {Gn : SimpleGraph (Fin n)} [DecidableRel Gn.Adj]
    (y : FracPacking Gn) (C : ℕ) {ε ζ : ℚ}
    (hgate : ∀ z : FracPacking Gn, (C : ℚ) ≤ PaperIV.LowTriangleReduction.triMass z →
      ∃ Pk : Packing Gn, z.value - (Pk.gain : ℚ) ≤ ζ * (n : ℚ) ^ 2)
    (hempty : 15 * (C : ℚ) ≤ ε * (n : ℚ) ^ 2)
    (hswap : 13 * (C : ℚ) + ζ * (n : ℚ) ^ 2 ≤ ε * (n : ℚ) ^ 2) :
    ∃ Pk : Packing Gn, y.value - (Pk.gain : ℚ) ≤ ε * (n : ℚ) ^ 2 := by
  rcases lowTriangle_dichotomy Gn C with hsmall | hbig
  · -- `ν < C`: el valor ya es `O(1)`, el packing vacío basta
    refine ⟨emptyPacking Gn, ?_⟩
    rw [emptyPacking_gain]
    have h := hsmall y
    push_cast
    linarith
  · -- `ν ≥ C`: se sustituye y se entra al gate
    obtain ⟨y', hmass, hloss⟩ := hbig y
    obtain ⟨Pk, hPk⟩ := hgate y' hmass
    exact ⟨Pk, by linarith⟩

/-! ## 2. En `ℝ`, que es donde vive el gate con holgura -/

/-- **La misma rama, en la interfaz del gate.**

`RC01CleanedGate.exists_packing_loss_le_of_cleanedSpread` habla en `ℝ` y con
`JointTwoQuotaPhysical.triangleMass`; `Corollary73Assembly.triMass_cast` dice que es la misma
cantidad que `triMass`, así que el puente pasa sin pérdida. -/
theorem lowTriangle_branch_free_real {n : ℕ} {Gn : SimpleGraph (Fin n)} [DecidableRel Gn.Adj]
    (y : FracPacking Gn) (C : ℕ) {ε ζ : ℝ}
    (hgate : ∀ z : FracPacking Gn,
      (C : ℝ) ≤ PaperIV.JointTwoQuotaPhysical.triangleMass z →
      ∃ Pk : Packing Gn, ((z.value : ℚ) : ℝ) - (Pk.gain : ℝ) ≤ ζ * (n : ℝ) ^ 2)
    (hempty : 15 * (C : ℝ) ≤ ε * (n : ℝ) ^ 2)
    (hswap : 13 * (C : ℝ) + ζ * (n : ℝ) ^ 2 ≤ ε * (n : ℝ) ^ 2) :
    ∃ Pk : Packing Gn, ((y.value : ℚ) : ℝ) - (Pk.gain : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
  rcases lowTriangle_dichotomy Gn C with hsmall | hbig
  · refine ⟨emptyPacking Gn, ?_⟩
    have hg : ((emptyPacking Gn).gain : ℝ) = 0 := by
      rw [emptyPacking_gain]; norm_num
    rw [hg]
    have h : ((y.value : ℚ) : ℝ) ≤ 15 * (C : ℝ) := by
      have := hsmall y
      have hcast : ((y.value : ℚ) : ℝ) ≤ ((15 * (C : ℚ) : ℚ) : ℝ) := by exact_mod_cast this
      push_cast at hcast
      linarith
    linarith
  · obtain ⟨y', hmass, hloss⟩ := hbig y
    have hmassR : (C : ℝ) ≤ PaperIV.JointTwoQuotaPhysical.triangleMass y' := by
      rw [← PaperIV.Corollary73Assembly.triMass_cast y']
      exact_mod_cast hmass
    obtain ⟨Pk, hPk⟩ := hgate y' hmassR
    have hlossR : ((y.value : ℚ) : ℝ) - ((y'.value : ℚ) : ℝ) ≤ 13 * (C : ℝ) := by
      have hcast : ((y.value - y'.value : ℚ) : ℝ) ≤ ((13 * (C : ℚ) : ℚ) : ℝ) := by
        exact_mod_cast hloss
      push_cast at hcast
      linarith
    exact ⟨Pk, by linarith⟩

end PaperIV.CleanedLowTriangleBridge
