import PaperIV.RC01MarkedRounding
import PaperIV.RC01TriangleSchedule

/-!
# Pregunta 1: ¿dónde se usa exactamente la regularidad?

La rama lejana necesita `MixedRounding.UniformRoundingTarget ε`.  La demostración actual
(`PaperIV.RC01Final`) pasa por una partición de regularidad, perfiles marcados y limpieza.
Este módulo **localiza** el uso: separa la parte que no depende de regularidad de la parte
que sí, y demuestra que la segunda se reduce a un único enunciado.

La puerta física ya disponible, `PaperIV.RC01MarkedRounding.exists_packing_loss_le_of_slackMarkedQuota`,
redondea un empaquetamiento fraccional con pérdida `ζn²` siempre que

1. su **codegree ponderado** esté acotado por una constante `γ` que depende sólo de `ζ`, y
2. su **masa triangular** supere una constante `C` que depende sólo de `ζ`.

Nada de eso usa regularidad: la puerta es el nibble de rango acotado más Beck–Fiala.  Lo que
falla para un `x` arbitrario es (1): un empaquetamiento fraccional cualquiera puede concentrar
toda su masa en pocos items por par de vértices, y entonces su codegree ponderado vale `1`,
no `γ`.

`CodegreeCleanupAt` es exactamente el enunciado que arregla eso, y
`uniformRoundingTarget_of_codegreeCleanup` demuestra que **basta**: con esa limpieza, el
contrato de redondeo sale sin regularidad, sin perfiles y sin selección.  Dicho de otro modo,
en toda la rama lejana la regularidad sirve para una sola cosa: fabricar, a partir de `x`, un
empaquetamiento de valor casi igual con codegree ponderado pequeño y masa triangular
retenida.
-/

namespace FarExploration.CodegreeCleanup

open Finset MixedRounding

/-- **La limpieza de codegree.**  A partir de un empaquetamiento fraccional mixto `x` con masa
triangular cuadrática se obtiene otro, `y`, con

* codegree ponderado acotado por `gam` sobre la familia conjunta de soportes,
* masa triangular al menos `Cst`, y
* valor a distancia `≤ xi·n²` del de `x`.

Es la única propiedad que `PaperIV.RC01Final` obtiene de la partición de regularidad; el
resto de la cadena lejana no la usa. -/
def CodegreeCleanupAt (gam Cst : ℝ) (m xi : ℚ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : FracPacking G),
      (m : ℝ) * (n : ℝ) ^ 2 - 1 ≤ PaperIV.JointTwoQuotaPhysical.triangleMass x →
      ∃ y : FracPacking G,
        (∀ e f : Sym2 (Fin n), e ≠ f →
          ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter
              (fun S => e ∈ S ∧ f ∈ S), inducedWeight y S ≤ gam) ∧
        Cst ≤ PaperIV.JointTwoQuotaPhysical.triangleMass y ∧
        x.value - y.value ≤ xi * (n : ℚ) ^ 2

/-- **La limpieza basta: el contrato de redondeo sale sin regularidad.**

Si para cada umbral de codegree `gam` y cada constante de masa `Cst` existe la limpieza
`CodegreeCleanupAt gam Cst (ε/30) (ε/4)`, entonces vale
`MixedRounding.UniformRoundingTarget ε`.  El resto de la demostración es la puerta física
(nibble de rango acotado con holgura, ya deterministizada) y la rama de pocos triángulos. -/
theorem uniformRoundingTarget_of_codegreeCleanup (eps : ℚ) (heps : 0 < eps)
    (hclean : ∀ gam Cst : ℝ, 0 < gam → 0 < Cst →
      CodegreeCleanupAt gam Cst (eps / 30) (eps / 4)) :
    UniformRoundingTarget eps := by
  classical
  set zq : ℚ := min (eps / 4) 1 with hzqdef
  have hzq0 : 0 < zq := lt_min (by linarith) one_pos
  have hzq1 : zq ≤ 1 := min_le_right _ _
  have hzqe : zq ≤ eps / 4 := min_le_left _ _
  have hzR0 : (0 : ℝ) < ((zq : ℚ) : ℝ) := by exact_mod_cast hzq0
  have hzR1 : ((zq : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hzq1
  obtain ⟨gam, hgam, Cst, hCst, D, hD, hgate⟩ :=
    PaperIV.RC01MarkedRounding.exists_packing_loss_le_of_slackMarkedQuota
      ((zq : ℚ) : ℝ) hzR0 hzR1
  obtain ⟨N₀, hclean'⟩ := hclean gam Cst hgam hCst
  refine ⟨max N₀ ⌈(12 + 10 * D) / ((zq : ℚ) : ℝ)⌉₊ + 1, ?_⟩
  intro n hn G _ x
  have hn1 : 1 ≤ n := le_trans (Nat.le_add_left 1 _) hn
  have hnN₀ : N₀ ≤ n := le_trans (le_trans (le_max_left _ _) (Nat.le_add_right _ 1)) hn
  have hnD : ⌈(12 + 10 * D) / ((zq : ℚ) : ℝ)⌉₊ ≤ n :=
    le_trans (le_trans (le_max_right _ _) (Nat.le_add_right _ 1)) hn
  have hnQ : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn1
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  -- la constante aditiva del nibble
  have hsizeD : 12 + 10 * D ≤ ((zq : ℚ) : ℝ) * (n : ℝ) ^ 2 := by
    have h1 : (12 + 10 * D) / ((zq : ℚ) : ℝ) ≤ (n : ℝ) := by
      refine le_trans (Nat.le_ceil ((12 + 10 * D) / ((zq : ℚ) : ℝ))) ?_
      exact_mod_cast hnD
    rw [div_le_iff₀ hzR0] at h1
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  -- el umbral triangular de la rama baja
  set C : ℕ := ⌊eps * (n : ℚ) ^ 2 / 30⌋₊ with hCdef
  have hCle : 30 * (C : ℚ) ≤ eps * (n : ℚ) ^ 2 := by
    have h := Nat.floor_le (a := eps * (n : ℚ) ^ 2 / 30) (by positivity)
    rw [hCdef]; linarith
  have hCge : eps * (n : ℚ) ^ 2 / 30 - 1 ≤ (C : ℚ) := by
    have h := Nat.sub_one_lt_floor (eps * (n : ℚ) ^ 2 / 30)
    rw [hCdef]; linarith [h.le]
  -- la puerta de masa alta, ya sin regularidad
  have hhigh : ∀ z : FracPacking G, ((C : ℕ) : ℝ) ≤
      PaperIV.JointTwoQuotaPhysical.triangleMass z →
      ∃ Pk : Packing G, ((z.value : ℚ) : ℝ) - (Pk.gain : ℝ)
        ≤ (((eps / 2 : ℚ) : ℝ)) * (n : ℝ) ^ 2 := by
    intro z hz
    have hmassin : ((eps / 30 : ℚ) : ℝ) * (n : ℝ) ^ 2 - 1
        ≤ PaperIV.JointTwoQuotaPhysical.triangleMass z := by
      refine le_trans ?_ hz
      have hQ : ((eps / 30 : ℚ)) * (n : ℚ) ^ 2 - 1 ≤ (C : ℚ) := by
        have : (eps / 30 : ℚ) * (n : ℚ) ^ 2 = eps * (n : ℚ) ^ 2 / 30 := by ring
        rw [this]; exact hCge
      have := (Rat.cast_le (K := ℝ)).2 hQ
      push_cast at this ⊢
      linarith
    obtain ⟨y, hcod, hmass, hloss⟩ := hclean' n hnN₀ G z hmassin
    obtain ⟨Pk, hPk⟩ := hgate n hn1 G y hsizeD hcod hmass
    refine ⟨Pk, ?_⟩
    have hlossR : ((z.value : ℚ) : ℝ) - ((y.value : ℚ) : ℝ)
        ≤ (((eps / 4 : ℚ) : ℝ)) * (n : ℝ) ^ 2 := by
      have := (Rat.cast_le (K := ℝ)).2 hloss
      push_cast at this ⊢
      linarith
    have hzqR : ((zq : ℚ) : ℝ) ≤ (((eps / 4 : ℚ) : ℝ)) := by exact_mod_cast hzqe
    have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
    have hgateR : ((y.value : ℚ) : ℝ) - (Pk.gain : ℝ)
        ≤ (((eps / 4 : ℚ) : ℝ)) * (n : ℝ) ^ 2 :=
      le_trans hPk (mul_le_mul_of_nonneg_right hzqR hn2)
    have hsum : (((eps / 4 : ℚ) : ℝ)) * (n : ℝ) ^ 2 + (((eps / 4 : ℚ) : ℝ)) * (n : ℝ) ^ 2
        = (((eps / 2 : ℚ) : ℝ)) * (n : ℝ) ^ 2 := by push_cast; ring
    linarith
  -- la rama de pocos triángulos
  obtain ⟨P, hP⟩ := PaperIV.RC01TriangleSchedule.lowTriangle_branch_free_scheduled
    (ε := ((eps : ℚ) : ℝ)) (ζ := (((eps / 2 : ℚ) : ℝ))) x C hhigh
    (by push_cast; linarith)
    (by
      have : ((30 * (C : ℚ) : ℚ) : ℝ) ≤ ((eps * (n : ℚ) ^ 2 : ℚ) : ℝ) := by exact_mod_cast hCle
      push_cast at this ⊢
      linarith)
  refine ⟨P, ?_⟩
  have : ((x.value - (P.gain : ℚ) : ℚ) : ℝ) ≤ ((eps * (n : ℚ) ^ 2 : ℚ) : ℝ) := by
    push_cast
    push_cast at hP
    linarith
  exact_mod_cast this

end FarExploration.CodegreeCleanup
