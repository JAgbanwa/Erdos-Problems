import PaperIV.HybridDichotomy
import PaperIV.NearRootWindow
import PaperIV.NearEdgeDensity

set_option maxHeartbeats 1000000

/-!
# La dicotomía far/near en forma cuantitativa

`PaperIV.HybridDichotomy.chordal_far_or_nearStructure` devuelve, en la rama
cercana, el paquete estructural completo `NearStructureWitness`.  Ese paquete es
*datos*: hay que leerlo para saber qué dice de la geometría del grafo.  Este
módulo hace esa lectura una sola vez y la publica como enunciados métricos, sin
tocar la dicotomía original (que se usa como caja negra):

* `chordal_far_or_criticalRoot` — todo grafo cordal suficientemente grande con
  óptimo racional certificado, o bien tiene la holgura cuadrática que consume la
  rama RC01, o bien contiene **una clique de tamaño `n/3` con error relativo
  menor que el 1 %** y está a distancia de edición `≤ eps·n²` de un grafo
  completo-split cuyo **núcleo también tiene tamaño `n/3`**, con error relativo
  `3·10^{-5}`, y ambos tamaños coinciden salvo `n/100`;
* `chordal_far_or_cliqueNum_ge` — la consecuencia más corta: fuera del régimen
  lejano, el número de clique de un grafo cordal grande es al menos `0.3267·n`;
* `chordal_far_or_edge_density` — fuera del régimen lejano, el grafo tiene
  exactamente `5n²/18` aristas salvo `n²/10^4`: densidad `5/9`.

Ambos son adiciones: no se modifica ni se debilita ningún enunciado previo, y la
independencia far/near se conserva porque toda la información nueva sale del
testigo cercano.
-/

namespace PaperIV.NearCriticalDichotomy

open PaperIV.FarRounding PaperIV.RC01FarAssembly
open PaperIV.NearH1StructureWitness
open PaperIV.GraphFamilyDistance

/-- **Dicotomía cuantitativa far/near.**  O hay holgura cuadrática certificada,
o el grafo es, a menos de `eps·n²` ediciones, un grafo completo-split cuyo
núcleo y cuya raíz tienen tamaño crítico `n/3`. -/
theorem chordal_far_or_criticalRoot :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
        ((G.edgeFinset.card : ℚ) - w <
            (n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2) ∨
          ∃ R C : Finset (Fin n),
            G.IsClique (R : Set (Fin n)) ∧
            |3 * (R.card : ℚ) - (n : ℚ)| ≤ (n : ℚ) / 50 ∧
            C.Nonempty ∧
            (PaperIV.EditMetric.editDist G.edgeFinset
                (graphEdgeSupport
                  (PaperIV.SplitUniformIncidence.splitGraph C
                    (Finset.univ \ C))) : ℚ) ≤
              PaperIV.NearH1Calibration.eps * (n : ℚ) ^ 2 ∧
            |3 * (C.card : ℚ) - (n : ℚ)| ≤ (n : ℚ) / 10000 ∧
            |(R.card : ℚ) - (C.card : ℚ)| ≤ (n : ℚ) / 100 := by
  classical
  obtain ⟨N, hN⟩ := PaperIV.HybridDichotomy.chordal_far_or_nearStructure
  refine ⟨max N (4 * 10 ^ 12), ?_⟩
  intro n hn G _ hG w hw
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnBig : 4 * 10 ^ 12 ≤ n := le_trans (le_max_right _ _) hn
  have hnQ : 4 * (10 : ℚ) ^ 12 ≤ (Fintype.card (Fin n) : ℚ) := by
    have : (4 * 10 ^ 12 : ℕ) ≤ (n : ℕ) := hnBig
    have := (Nat.cast_le (α := ℚ)).2 this
    simpa only [Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using this
  rcases hN n hnN G hG w hw with hslack | hnearW
  · exact Or.inl hslack
  · obtain ⟨W⟩ := hnearW
    refine Or.inr ⟨W.regularized.root, W.core, W.regularized.isClique, ?_, W.core_nonempty,
      ?_, ?_, ?_⟩
    · simpa only [Fintype.card_fin] using
        PaperIV.NearRootWindow.regularizedRoot_card_near_third W.regularized
    · simpa only [Fintype.card_fin] using W.core_edit_le
    · simpa only [Fintype.card_fin] using PaperIV.NearRootWindow.core_card_near_third W hnQ
    · simpa only [Fintype.card_fin] using PaperIV.NearRootWindow.root_sub_core_le W hnQ

/-- **Número de clique en el régimen cercano.**  Fuera de la rama lejana, un
grafo cordal suficientemente grande tiene número de clique al menos
`3267·n/10000`.  Es la lectura más corta de la ventana de la raíz. -/
theorem chordal_far_or_cliqueNum_ge :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
        ((G.edgeFinset.card : ℚ) - w <
            (n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2) ∨
          3267 * n ≤ 10000 * G.cliqueNum := by
  classical
  obtain ⟨N, hN⟩ := PaperIV.HybridDichotomy.chordal_far_or_nearStructure
  refine ⟨N, ?_⟩
  intro n hn G _ hG w hw
  rcases hN n hn G hG w hw with hslack | hnearW
  · exact Or.inl hslack
  · obtain ⟨W⟩ := hnearW
    refine Or.inr ?_
    have hwin := (PaperIV.NearRootWindow.regularizedRoot_card_window W.regularized).1
    have hcard : W.regularized.root.card ≤ G.cliqueNum :=
      SimpleGraph.IsClique.card_le_cliqueNum (tc := W.regularized.isClique)
    simp only [Fintype.card_fin] at hwin
    omega

/-- **Densidad de aristas fuera del régimen lejano.**  O hay holgura cuadrática
certificada, o el grafo cordal tiene `5n²/18` aristas salvo `n²/10^4`. -/
theorem chordal_far_or_edge_density :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
        ((G.edgeFinset.card : ℚ) - w <
            (n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2) ∨
          |(G.edgeFinset.card : ℚ) - 5 * (n : ℚ) ^ 2 / 18| ≤ (n : ℚ) ^ 2 / 10000 := by
  classical
  obtain ⟨N, hN⟩ := PaperIV.HybridDichotomy.chordal_far_or_nearStructure
  refine ⟨max N (4 * 10 ^ 12), ?_⟩
  intro n hn G _ hG w hw
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnBig : 4 * 10 ^ 12 ≤ n := le_trans (le_max_right _ _) hn
  have hnQ : 4 * (10 : ℚ) ^ 12 ≤ (Fintype.card (Fin n) : ℚ) := by
    have h := (Nat.cast_le (α := ℚ)).2 hnBig
    simpa only [Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  rcases hN n hnN G hG w hw with hslack | hnearW
  · exact Or.inl hslack
  · obtain ⟨W⟩ := hnearW
    refine Or.inr ?_
    simpa only [Fintype.card_fin] using
      PaperIV.NearEdgeDensity.card_edgeFinset_near_five_eighteenths W hnQ

end PaperIV.NearCriticalDichotomy
