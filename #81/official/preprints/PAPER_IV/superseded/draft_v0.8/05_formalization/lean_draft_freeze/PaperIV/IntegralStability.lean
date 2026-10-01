import PaperIV.HybridDichotomy
import PaperIV.NearRegimePackingInterface
import PaperIV.SplitBaselineTarget
import PaperIV.SplitEditIdentity
import PaperIV.FarSlackQuantitative

/-!
# BP-01 — estabilidad integral lineal en el déficit

El contrato pide constantes `γ > 0` y `N` tales que, para todo cordal `G` de orden `n ≥ N`
y todo `0 ≤ δ ≤ γ n²`,

```text
c₄(G) ≥ M(n) − δ   ⟹   ∃ R clique,  d_E(G, S_R) ≤ 20 · δ
```

conservando además las cuentas `m/20 + A/2 ≤ δ`, con `m = e(G − R)` y `A` el número de
enlaces ausentes entre `R` y `V ∖ R`.

## Cómo se formaliza «c₄(G) ≥ M(n) − δ»

`c₄(G)` es el mínimo tamaño de una partición en cliques de orden a lo sumo cuatro.  La
hipótesis se escribe, sin elegir minimizador, como

```text
∀ Q : CliquePartition G, Q.OrderAtMost 4 → (M(n) : ℚ) − δ ≤ Q.size ,
```

que es exactamente «ninguna partición admisible baja de `M(n) − δ`».  Es la forma que el
argumento consume, y es la que hace falta: el resto del contrato es una cota superior
producida por una partición concreta.

## Las dos ramas, y dónde estaba el problema

La dicotomía `PaperIV.HybridDichotomy.chordal_far_or_nearStructure` reparte según haya o no
holgura cuadrática `η n²`, con `η = NearH1Calibration.eta`.

* **Rama cercana.**  El testigo estructural entrega una raíz `R` que es clique de `G`, un
  packing físico `K₃`/`K₄` del grafo original y sus cuentas RD09, cuyas familias literales
  son precisamente `outsideEdges G R` (masa `m`) y `missingSpokeEdges G R` (masa `A`).  El
  descuento del ledger, `PhysicalAccounts.count_le_paid`, da una partición admisible de
  tamaño `≤ splitBaseline − m/20 − A/2 ≤ M(n) − m/20 − A/2`.  Enfrentada a la hipótesis,
  sale `m/20 + A/2 ≤ δ`, y de ahí `m + A ≤ 20 δ` porque `A ≥ 0`.  La identidad
  `SplitEditIdentity.editDist_split_eq` convierte `m + A` en `d_E(G, S_R)` **exactamente**,
  usando que `R` es clique.
* **Rama lejana.**  Aquí estaba el punto difícil.  `farRegime_cliquePartition` concluye
  `Q.size ≤ targetSize n`, que no contradice nada.  El margen se recupera en
  `PaperIV.FarSlackQuantitative`, que rehace la rama sin el redondeo final y conserva
  `Q.size < n²/6 − η n²/2`.  Como `n²/6 ≤ M(n)` para `n ≥ 5`, la hipótesis fuerza
  `δ > η n²/2`, incompatible con `δ ≤ γ n²` en cuanto `γ < η/2`.

## La constante

Con `γ = η/4` la rama lejana queda excluida con margen estricto, y el factor del contrato
es **exactamente 20**, sin pérdida: la desigualdad `m + A ≤ 20 (m/20 + A/2)` es holgada en
`9 A`.  Es decir, las dos constantes del contrato se alcanzan; lo que hay que pagar es la
pequeñez de `γ`, que hereda `η = 10⁻¹⁶` del calibrado del árbol.  El margen se pierde
únicamente ahí: `γ` no puede superar `η/2` mientras la rama lejana se cierre con la holgura
`η n²/2` que produce el redondeo mixto.
-/

namespace PaperIV.IntegralStability

open PaperIV.FarRounding
open PaperIV.NearH1StructureWitness
open PaperIV.SplitUniformIncidence
open PaperIV.GraphFamilyDistance

/-- La constante `γ` de BP-01: la mitad del margen cuadrático que conserva la rama lejana. -/
def gamma : ℚ := PaperIV.NearH1Calibration.eta / 4

theorem gamma_pos : 0 < gamma := by
  norm_num [gamma, PaperIV.NearH1Calibration.eta]

theorem eta_pos : 0 < PaperIV.NearH1Calibration.eta := by
  norm_num [PaperIV.NearH1Calibration.eta]

/-- **BP-01.**  Estabilidad integral con pérdida **lineal** en el déficit, conservando las
cuentas físicas.

Hipótesis, todas visibles:

* `N ≤ n`: umbral fijado antes que `n` (y antes que `G` y `δ`);
* `IsChordal G`;
* `0 ≤ δ ≤ gamma * n²`: el déficit es cuadráticamente pequeño;
* `hmin`: ninguna partición en cliques de orden `≤ 4` de `G` baja de `M(n) − δ`.

Conclusión: existe una clique `R` de `G`, con `2 ≤ |R|` y `|R| ≤ |V ∖ R|`, tal que

* `m/20 + A/2 ≤ δ`, con `m = |outsideEdges G R|` el número de aristas de `G` con los dos
  extremos fuera de `R`, y `A = missingIncidences G R` el número de enlaces ausentes entre
  `R` y `V ∖ R`;
* `d_E(G, S_R) ≤ 20 δ`, donde `S_R` es el completo-split de núcleo `R`. -/
theorem chordal_linear_stability :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G → ∀ δ : ℚ, 0 ≤ δ → δ ≤ gamma * (n : ℚ) ^ 2 →
        (∀ Q : CliquePartition G, Q.OrderAtMost 4 →
            (PaperIV.targetSize n : ℚ) - δ ≤ (Q.size : ℚ)) →
          ∃ R : Finset (Fin n), G.IsClique (R : Set (Fin n)) ∧
            2 ≤ R.card ∧ R.card ≤ (Finset.univ \ R).card ∧
            ((PaperIV.RootVocab.outsideEdges G R).card : ℚ) / 20
                + (PaperIV.RootVocab.missingIncidences G R : ℚ) / 2 ≤ δ ∧
            (PaperIV.EditMetric.editDist G.edgeFinset
                (graphEdgeSupport (splitGraph R (Finset.univ \ R))) : ℚ) ≤ 20 * δ := by
  classical
  obtain ⟨Nnear, hnear⟩ := PaperIV.HybridDichotomy.chordal_near_extremal_stability
  obtain ⟨Nfar, hfar⟩ :=
    PaperIV.FarSlackQuantitative.farRegime_cliquePartition_slack
      PaperIV.NearH1Calibration.eta eta_pos
  refine ⟨max (max Nnear Nfar) 5, ?_⟩
  intro n hn G _ hG δ hδ0 hδ hmin
  have hn5 : 5 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnnear : Nnear ≤ n :=
    le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hnfar : Nfar ≤ n :=
    le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  obtain ⟨w, hw⟩ := PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum G
  by_cases hslack : (G.edgeFinset.card : ℚ) - w <
      (n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2
  · -- Rama lejana: imposible, porque conserva margen cuadrático.
    exfalso
    obtain ⟨Q, hQ4, hQlt⟩ := hfar n hnfar G hG w hw hslack
    have h1 := hmin Q hQ4
    have h2 := PaperIV.FarSlackQuantitative.sq_div_six_le_targetSize hn5
    have hn5Q : (5 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn5
    have hsq : (0 : ℚ) < (n : ℚ) ^ 2 := by nlinarith
    have hγ : gamma = PaperIV.NearH1Calibration.eta / 4 := rfl
    rw [hγ] at hδ
    nlinarith [eta_pos]
  · -- Rama cercana: el testigo estructural da la raíz y las cuentas.
    obtain ⟨W⟩ := hnear n hnnear G hG w hw hslack
    set R : Finset (Fin n) := W.regularized.root with hRdef
    have hRclique : G.IsClique (R : Set (Fin n)) := W.regularized.isClique
    have hRtwo : 2 ≤ R.card := by
      have h := W.regularized.card_ge
      rw [hRdef]
      omega
    have hRout : R.card ≤ (Finset.univ \ R).card := W.regularized.root_le_outside
    obtain ⟨Q, hQ4, hQsize⟩ :=
      PaperIV.NearRegimePacking.exists_cliquePartition_card_completion W.isPacking
    -- la línea de base física nunca supera el objetivo
    have hbase : (W.accounts.baseCount : ℚ) =
        PaperIV.splitBaseline (n : ℚ) W.accounts.split := by
      have h := W.accounts.base_eq
      rw [W.accounts_order] at h
      simpa using h
    have hbaseZ : ((W.accounts.baseCount : ℤ)) ≤ (PaperIV.targetSize n : ℤ) :=
      PaperIV.SplitBaselineTarget.splitBaseline_le_targetSize (by exact_mod_cast hbase)
    have hbaseQ : (W.accounts.baseCount : ℚ) ≤ (PaperIV.targetSize n : ℚ) := by
      exact_mod_cast hbaseZ
    -- el descuento del ledger
    have hpaid := W.accounts.count_le_paid
    rw [← W.accounts.base_eq] at hpaid
    have hQmin := hmin Q hQ4
    rw [hQsize] at hQmin
    have hacct : (W.accounts.missingEdges.card : ℚ) / 20
        + (W.accounts.rootLossEdges.card : ℚ) / 2 ≤ δ := by linarith
    -- identificación de las dos masas con las familias literales de la raíz
    have hm : W.accounts.missingEdges.card = (PaperIV.RootVocab.outsideEdges G R).card := by
      rw [W.accounts_missing]
    have hA : W.accounts.rootLossEdges.card = PaperIV.RootVocab.missingIncidences G R := by
      rw [W.accounts_rootLoss, PaperIV.RD09SplitEditAccount.card_missingSpokeEdges]
    rw [hm, hA] at hacct
    refine ⟨R, hRclique, hRtwo, hRout, hacct, ?_⟩
    rw [PaperIV.SplitEditIdentity.editDist_split_eq G hRclique]
    have hAnn : (0 : ℚ) ≤ (PaperIV.RootVocab.missingIncidences G R : ℚ) := by positivity
    push_cast
    linarith

end PaperIV.IntegralStability
