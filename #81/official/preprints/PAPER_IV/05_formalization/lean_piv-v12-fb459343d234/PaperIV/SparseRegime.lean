import PaperIV.UniformDual
import MixedRounding.Defs

/-!
# El régimen disperso es gratis, y con eso queda delimitado el crux

`MixedRounding.UniformRoundingTarget ε` cuantifica sobre **todos** los grafos. La cadena
construida —regularidad, capas de propietario, poda, nibble— sólo entrega su conclusión para
grafos que cumplen las hipótesis de conteo, y `RootedK4Hdeg.hdeg_of_dense` las exige con

```
hN : |nonEdgePairs G| ≤ (1 − α₀)·n²     con  1 − α₀ ≲ θ(1 − d₀)/5,
```

es decir `G` **casi completa** (el testigo de régimen usa `α₀ = 1 − 10⁻⁶`).

Este módulo cierra el extremo opuesto y con ello deja el hueco acotado por los dos lados.

## Lo que se demuestra

Si `G` es suficientemente dispersa, el empaquetamiento **vacío** ya sirve:

```
x.value ≤ (5/6)·e(G) ≤ ε·n²     cuando   e(G) ≤ (6/5)·ε·n²
```

`uniformRounding_of_sparse`. No hay nada que redondear: la cota superior del LP es ya menor que
el presupuesto.

## El crux, delimitado

Quedan entonces **tres** regímenes y sólo uno abierto:

| régimen | condición | estado |
|---|---|---|
| disperso | `e(G) ≤ (6/5)·ε·n²` | **cerrado aquí**, con `P = ∅` |
| casi completo | `\|nonEdges\| ≤ (1−α₀)·n²` | cerrado por la cadena (condicional a sus hipótesis) |
| **intermedio** | ni lo uno ni lo otro | **ABIERTO** |

`sparse_or_dense_covers` hace explícito que los dos extremos no se solapan ni cubren: entre
`(12/5)·ε` y `1 − 2(1−α₀)` de densidad de aristas no hay argumento.

## Por qué el intermedio no es cosmético

Un grafo de densidad intermedia puede tener una fracción constante de sus aristas en pares de
densidad baja de la partición de regularidad. Esas aristas están en pocos `K₄`, así que la cota
inferior de grado falla en ellas, y son demasiadas para meterlas en el excepcional, que sólo
admite `θ·n²`.

Para esas aristas la cadena no dice nada, **y su valor en el LP no es necesariamente pequeño**:
una arista en un par de densidad baja puede seguir estando en muchos triángulos. Ése es el
contenido que falta.
-/

namespace PaperIV.SparseRegime

open Finset
open PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. El régimen disperso -/

/-- **Gratis.**  Si el número de aristas no pasa de `(6/5)·ε·n²`, el empaquetamiento vacío ya
cumple el contrato: la cota superior universal del LP es menor que el presupuesto. -/
theorem value_le_of_sparse {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ε : ℚ} (hsparse : (G.edgeFinset.card : ℚ) ≤ (6 / 5 : ℚ) * ε * (n : ℚ) ^ 2)
    (x : FracPacking G ℚ) :
    x.value ≤ ε * (n : ℚ) ^ 2 := by
  calc x.value ≤ (5 / 6 : ℚ) * (G.edgeFinset.card : ℚ) :=
        PaperIV.UniformDual.value_le_five_sixths x
    _ ≤ (5 / 6 : ℚ) * ((6 / 5 : ℚ) * ε * (n : ℚ) ^ 2) :=
        mul_le_mul_of_nonneg_left hsparse (by norm_num)
    _ = ε * (n : ℚ) ^ 2 := by ring

/-- El empaquetamiento vacío. -/
def emptyPacking (G : SimpleGraph V) [DecidableRel G.Adj] : Packing G where
  pieces := ∅
  isItem := by intro K hK; exact absurd hK (Finset.notMem_empty K)
  edgeDisjoint := by intro K hK; exact absurd hK (Finset.notMem_empty K)

theorem emptyPacking_gain (G : SimpleGraph V) [DecidableRel G.Adj] :
    (emptyPacking G).gain = 0 := by
  rw [Packing.gain, emptyPacking]
  simp

/-- **El régimen disperso cumple el contrato, con `P = ∅`.**  Nada que redondear. -/
theorem uniformRounding_of_sparse {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ε : ℚ} (hsparse : (G.edgeFinset.card : ℚ) ≤ (6 / 5 : ℚ) * ε * (n : ℚ) ^ 2)
    (x : FracPacking G ℚ) :
    ∃ P : Packing G, x.value - (P.gain : ℚ) ≤ ε * (n : ℚ) ^ 2 := by
  refine ⟨emptyPacking G, ?_⟩
  rw [emptyPacking_gain]
  simpa using value_le_of_sparse hsparse x

/-! ## 2. El hueco, hecho explícito -/

/-- **Los dos extremos no se tocan.**  Si `ε` es pequeño y `α₀` cercano a `1`, hay grafos que
no son ni dispersos ni casi completos: basta que el número de aristas esté estrictamente entre
las dos cotas.

El enunciado es deliberadamente trivial como aritmética; su función es que el hueco quede
**escrito** y no se pueda usar la cadena creyendo que cubre todo grafo. -/
theorem middle_regime_nonempty {n : ℕ} {ε α₀ : ℚ} {m : ℚ}
    (hlow : (6 / 5 : ℚ) * ε * (n : ℚ) ^ 2 < m)
    (hhigh : m < (n : ℚ) ^ 2 / 2 - (1 - α₀) * (n : ℚ) ^ 2) :
    (6 / 5 : ℚ) * ε * (n : ℚ) ^ 2 < m ∧
      m + (1 - α₀) * (n : ℚ) ^ 2 < (n : ℚ) ^ 2 / 2 :=
  ⟨hlow, by linarith⟩

end PaperIV.SparseRegime
