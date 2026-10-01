import PaperIV.SparseRegime
import PaperIV.LowTriangleReduction

/-!
# La reducción de regímenes: la ruta principal sólo tiene que cubrir uno

`MixedRounding.UniformRoundingTarget ε` cuantifica sobre **todo** grafo y **todo** empaquetamiento
fraccional. Dos de los tres regímenes ya están cerrados por separado y nadie los había
conectado:

* **disperso** — si `e(G) ≤ (6/5)·ε·n²`, la cota dual sola cierra el contrato y basta el
  empaquetamiento vacío (`SparseRegime.uniformRounding_of_sparse`);
* **pocos triángulos** — si `mass₃ x ≤ C`, tirar los triángulos cuesta exactamente `2·mass₃`
  y el problema se reduce al brazo puro de `K₄` (`LowTriangleReduction`).

Este módulo hace explícito lo que eso significa para el trabajo que queda:

> **la ruta de regularidad sólo tiene que cubrir el régimen denso con triángulos.**

Es una reducción trivial en lógica y **no trivial en tipos**: `SparseRegime` vive sobre
`PaperIV.FarRounding.FracPacking G ℚ` y el objetivo sobre `MixedRounding.FracPacking G`, así
que hay que pasar por `MixedRoundingAdapter` en las dos direcciones. Ahí es donde se cuelan los
errores, y por eso conviene escribirlo una vez y no en cada uso.
-/

namespace PaperIV.RoundingTrichotomy

open MixedRounding

/-! ## 1. El régimen disperso, en los tipos del objetivo -/

/-- **El régimen disperso, transportado.**  `SparseRegime.uniformRounding_of_sparse` en los
tipos que `UniformRoundingTarget` usa de verdad. -/
theorem sparse_target {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ε : ℚ}
    (hsparse : (G.edgeFinset.card : ℚ) ≤ (6 / 5 : ℚ) * ε * (n : ℚ) ^ 2)
    (x : FracPacking G) :
    ∃ P : Packing G, x.value - (P.gain : ℚ) ≤ ε * (n : ℚ) ^ 2 := by
  obtain ⟨P, hP⟩ := PaperIV.SparseRegime.uniformRounding_of_sparse hsparse
    (PaperIV.MixedRoundingAdapter.toFarFrac x)
  refine ⟨PaperIV.MixedRoundingAdapter.ofFarPacking P, ?_⟩
  rw [PaperIV.MixedRoundingAdapter.value_toFarFrac] at hP
  rwa [PaperIV.MixedRoundingAdapter.gain_ofFarPacking]

/-! ## 2. La reducción -/

/-- **Sólo falta el régimen denso con triángulos.**

Si el objetivo se cumple

* cuando la masa de triángulos es pequeña (`hlow`), y
* cuando el grafo es denso **y** hay masa de triángulos (`hdense`),

entonces se cumple para todo `G` y todo `x`: el tercer caso —disperso— lo cierra la cota dual
sin hipótesis.

Es la forma precisa de «la ruta de regularidad sólo tiene que cubrir un régimen», y deja por
escrito qué hipótesis puede dar por buenas quien la construya. -/
theorem target_of_regimes {n : ℕ} {ε C : ℚ}
    (hlow : ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : FracPacking G),
      PaperIV.LowTriangleReduction.triMass x ≤ C →
      ∃ P : Packing G, x.value - (P.gain : ℚ) ≤ ε * (n : ℚ) ^ 2)
    (hdense : ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : FracPacking G),
      (6 / 5 : ℚ) * ε * (n : ℚ) ^ 2 < (G.edgeFinset.card : ℚ) →
      C < PaperIV.LowTriangleReduction.triMass x →
      ∃ P : Packing G, x.value - (P.gain : ℚ) ≤ ε * (n : ℚ) ^ 2) :
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : FracPacking G),
      ∃ P : Packing G, x.value - (P.gain : ℚ) ≤ ε * (n : ℚ) ^ 2 := by
  intro G _ x
  by_cases hs : (G.edgeFinset.card : ℚ) ≤ (6 / 5 : ℚ) * ε * (n : ℚ) ^ 2
  · exact sparse_target hs x
  · by_cases ht : PaperIV.LowTriangleReduction.triMass x ≤ C
    · exact hlow G x ht
    · exact hdense G x (not_le.1 hs) (not_le.1 ht)

/-- La misma reducción, envuelta en `UniformRoundingTarget`: basta cubrir los dos regímenes
para todo `n` a partir de un `N`. -/
theorem uniformRoundingTarget_of_regimes {ε C : ℚ} (N : ℕ)
    (hlow : ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (x : FracPacking G), PaperIV.LowTriangleReduction.triMass x ≤ C →
      ∃ P : Packing G, x.value - (P.gain : ℚ) ≤ ε * (n : ℚ) ^ 2)
    (hdense : ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (x : FracPacking G),
      (6 / 5 : ℚ) * ε * (n : ℚ) ^ 2 < (G.edgeFinset.card : ℚ) →
      C < PaperIV.LowTriangleReduction.triMass x →
      ∃ P : Packing G, x.value - (P.gain : ℚ) ≤ ε * (n : ℚ) ^ 2) :
    UniformRoundingTarget ε := by
  refine ⟨N, ?_⟩
  intro n hn G _ x
  exact target_of_regimes (hlow n hn) (hdense n hn) G x

end PaperIV.RoundingTrichotomy
