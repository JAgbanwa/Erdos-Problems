import PaperIV.NearH1Calibration
import PaperIV.RC01FarAssembly

/-!
# Pregunta 3: ¿hace falta la uniformidad en `ξ`?

El ensamblaje final `PaperIV.RC01FarAssembly.chordalTargetAt_of_nearRegimeAt` consume la
rama lejana a través de la cadena

```
rc01_uniformRoundingTarget (η/2)  →  UniformRoundingAt (η/2)  →  UniformTransferAt (η/2)
                                  →  FarRoundingAt η          →  farRegime_cliquePartition η
```

y ninguno de esos pasos toca el umbral: los cuatro reexportan literalmente el `T` de su
hipótesis.  Este módulo lo deja escrito como **cálculo de umbrales**, sin existenciales:

* `MixedRoundingFrom Nx ξ` — el redondeo mixto a partir del umbral explícito `Nx`;
* `NearRegimeFrom Nn η` — la rama cercana a partir del umbral explícito `Nn`;
* `ChordalTargetFrom N` — la conclusión a partir del umbral explícito `N`;
* `chordalTargetFrom_max` — **`N = max Nx Nn`**, sin inflación ninguna.

Consecuencia (`chordalTargetAt_of_single_rounding`): el ensamblaje usa **una sola instancia**
del contrato de redondeo, la del valor `ξ = η/2`.  La uniformidad en `ξ` de
`MixedRounding.UniformRoundingTarget` no se usa en ninguna parte de la rama lejana.

Esto responde la pregunta 3 en su parte lógica: basta el caso `ξ = η₀/2`.  Lo que **no**
se sigue es que el umbral se vuelva escribible: véase `FarExploration.TowerHeight`, donde
se calcula el parámetro de regularidad de esa única instancia y se comprueba que ya es de
tipo torre.
-/

namespace FarExploration.ThresholdCalculus

open PaperIV.FarRounding
open PaperIV.RC01FarAssembly

/-- El contrato de redondeo mixto **con umbral explícito**: la forma sin existencial de
`MixedRounding.UniformRoundingTarget ξ`. -/
def MixedRoundingFrom (Nx : ℕ) (xi : ℚ) : Prop :=
  ∀ n : ℕ, Nx ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : MixedRounding.FracPacking G), ∃ P : MixedRounding.Packing G,
      x.value - (P.gain : ℚ) ≤ xi * (n : ℚ) ^ 2

/-- La rama cercana **con umbral explícito**: la forma sin existencial de `NearRegimeAt η`. -/
def NearRegimeFrom (Nn : ℕ) (eta : ℚ) : Prop :=
  ∀ n : ℕ, Nn ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
      ¬ ((G.edgeFinset.card : ℚ) - w < (n : ℚ) ^ 2 / 6 - eta * (n : ℚ) ^ 2) →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n

/-- La conclusión **con umbral explícito**: la forma sin existencial de `ChordalTargetAt`. -/
def ChordalTargetFrom (N : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n

/-- La rama lejana con umbral explícito: del redondeo mixto a partir de `Nx` con holgura
`η/2` sale la partición de clique objetivo a partir del **mismo** `Nx`. -/
theorem farRegimeFrom (eta : ℚ) (heta : 0 ≤ eta) {Nx : ℕ}
    (hround : MixedRoundingFrom Nx (eta / 2)) :
    ∀ n : ℕ, Nx ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
        (G.edgeFinset.card : ℚ) - w < (n : ℚ) ^ 2 / 6 - eta * (n : ℚ) ^ 2 →
          ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n := by
  intro n hn G _ _ w hw hfar
  obtain ⟨x, -, hx, -⟩ := id hw
  obtain ⟨P, hP⟩ := hround n hn G (PaperIV.MixedRoundingAdapter.ofFarFrac x)
  rw [PaperIV.MixedRoundingAdapter.value_ofFarFrac, hx] at hP
  set Q₀ : PaperIV.FarRounding.Packing G := PaperIV.MixedRoundingAdapter.toFarPacking P with hQ₀
  have hgain : (Q₀.gain : ℚ) = (P.gain : ℚ) := by
    rw [hQ₀, PaperIV.MixedRoundingAdapter.gain_toFarPacking]
  obtain ⟨Q, hQ4, hQsize⟩ := exists_cliquePartition_of_packing Q₀
  refine ⟨Q, hQ4, ?_⟩
  have hsize : (Q.size : ℚ) + (Q₀.gain : ℚ) = (G.edgeFinset.card : ℚ) := by
    exact_mod_cast hQsize
  have hlt : (Q.size : ℚ) < (n : ℚ) ^ 2 / 6 - eta * (n : ℚ) ^ 2 / 2 := by
    have hrw : (Q.size : ℚ) = ((G.edgeFinset.card : ℚ) - w) + (w - (P.gain : ℚ)) := by
      rw [← hgain]; linarith
    rw [hrw]; linarith
  have hn0 : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
  have hn2 : (n : ℚ) ^ 2 ≤ (n : ℚ) * ((n : ℚ) + 1) := by nlinarith
  have hetan : 0 ≤ eta * (n : ℚ) ^ 2 / 2 := by positivity
  have h6 : 6 * Q.size ≤ n * (n + 1) := by
    have hcast : ((6 * Q.size : ℕ) : ℚ) ≤ ((n * (n + 1) : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast hcast
  rw [targetSize, Nat.le_div_iff_mul_le (by norm_num)]
  omega

/-- **El umbral final es exactamente `max Nx Nn`.**  No hay inflación en ninguno de los
cuatro pasos que separan el contrato de redondeo de la conclusión. -/
theorem chordalTargetFrom_max (eta : ℚ) (heta : 0 ≤ eta) {Nx Nn : ℕ}
    (hround : MixedRoundingFrom Nx (eta / 2)) (hnear : NearRegimeFrom Nn eta) :
    ChordalTargetFrom (max Nx Nn) := by
  intro n hn G _ hG w hw
  by_cases hslack : (G.edgeFinset.card : ℚ) - w < (n : ℚ) ^ 2 / 6 - eta * (n : ℚ) ^ 2
  · exact farRegimeFrom eta heta hround n (le_trans (Nat.le_max_left _ _) hn) G hG w hw hslack
  · exact hnear n (le_trans (Nat.le_max_right _ _) hn) G hG w hw hslack

/-- **Una sola instancia del contrato basta.**  El ensamblaje no usa la uniformidad en `ξ`
de `MixedRounding.UniformRoundingTarget`: le basta el caso `ξ = η/2`. -/
theorem chordalTargetAt_of_single_rounding (eta : ℚ) (heta : 0 ≤ eta)
    (hround : MixedRounding.UniformRoundingTarget (eta / 2))
    (hnear : NearRegimeAt eta) : ChordalTargetAt := by
  obtain ⟨Nx, hx⟩ := hround
  obtain ⟨Nn, hn⟩ := hnear
  exact ⟨max Nx Nn, chordalTargetFrom_max eta heta (fun n h G _ x => hx n h G x) hn⟩

/-- La forma calibrada: con `η = 10⁻¹⁶` y la rama cercana desde `10¹⁴`, el umbral final es
`max Nx (10¹⁴)`, donde `Nx` es el umbral de la **única** instancia `ξ = 5·10⁻¹⁷` del
contrato de redondeo. -/
theorem chordalTargetFrom_calibrated {Nx : ℕ}
    (hround : MixedRoundingFrom Nx (PaperIV.NearH1Calibration.eta / 2))
    (hnear : NearRegimeFrom (10 ^ 14) PaperIV.NearH1Calibration.eta) :
    ChordalTargetFrom (max Nx (10 ^ 14)) :=
  chordalTargetFrom_max PaperIV.NearH1Calibration.eta (by norm_num [PaperIV.NearH1Calibration.eta])
    hround hnear

end FarExploration.ThresholdCalculus
