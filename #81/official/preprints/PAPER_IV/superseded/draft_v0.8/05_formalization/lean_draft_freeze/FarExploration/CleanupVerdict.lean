import FarExploration.CleanupBridge
import FarExploration.CleanupCertificate

/-!
# Veredicto: la limpieza de codegree **no** se decide por dualidad lineal

Este módulo reúne lo demostrado en `CleanupLP`, `CleanupBridge`, `CleanupDuality`,
`CleanupObstruction` y `CleanupCertificate`, y lo convierte en un enunciado.

## Lo que se ha demostrado

1. **La limpieza es un LP.**  Sus cuatro familias de restricciones —positividad, capacidad,
   codegrado por par de recursos y las dos cotas inferiores— están escritas en
   `CleanupDuality.mat`/`CleanupDuality.rhs`, y la alternativa de Farkas racional del árbol
   (`PaperI.RationalFarkas.farkas`) da la dicotomía exacta
   `CleanupDuality.cleanupFeasible_iff`: o hay limpieza, o hay **certificado dual**.

2. **El LP, por sí solo, es infactible en el régimen que interesa.**  El sistema de items
   `CleanupObstruction.obstructionSystem` vive sobre los recursos reales del problema,
   `Sym2 (Fin n)`, tiene todos sus items de rango `3`, capacidades `1`, y masa cuadrática
   `⌊n/6⌋² ≥ n²/49`; y sin embargo toda solución con codegrado `≤ gam` pierde al menos
   `2(1-gam)⌊n/6⌋²` de valor.  El certificado dual que lo demuestra es explícito
   (`CleanupCertificate.rigidCertificate`): precio `2` sobre un par de recursos de cada item.

3. **Esa infactibilidad es una obstrucción al método, no al enunciado.**  `CleanupBridge`
   demuestra `AbstractCleanupAt → CodegreeCleanupAt`: el LP abstracto es una generalización fiel
   del enunciado concreto, en la que lo único que se ha borrado es que los soportes sean las
   **cliques de un grafo**.  Un argumento que use sólo capacidades, rangos, ganancias, codegrados
   y masa demostraría también el enunciado abstracto, que es falso.  Por tanto `CodegreeCleanupAt`
   **no** se puede obtener por dualidad lineal: hace falta la realizabilidad de los items como
   triángulos y `K₄` del grafo.

4. **La hipótesis de masa triangular no es lo que salva la situación.**  La familia rígida la
   cumple con holgura (masa `≥ n²/49`).  Lo que la excluye es que sus items no son cliques: un
   sistema de `Θ(n²)` triángulos disjuntos dos a dos *sin más triángulos* es lo que el clásico
   teorema `(6,3)` de Ruzsa–Szemerédi prohíbe a escala cuadrática (resultado clásico, no
   formalizado aquí); y ese es un enunciado de conteo, no de dualidad.  Es la razón por la que la
   ruta actual pasa por regularidad.

5. **Lo que sí da la dualidad, con umbral escribible.**  El escalado `y = t·x` con `t ≤ gam`
   siempre es admisible —el codegrado de un empaquetamiento nunca pasa de `1`— y cuesta
   `(1-t)·valor ≤ (1-t)·(5/6)n²`.  De ahí `codegreeCleanupAt_of_scale`: el enunciado concreto es
   cierto, con umbral explícito `N = max 1 ⌈(Cst/t + 1)/m⌉₊`, en todo el régimen
   `5(1-t) ≤ 6·xi`.  Y `abstractCleanup_dichotomy` muestra que, a nivel de LP, ese régimen es el
   correcto salvo constante: por debajo de `49·xi < 2(1-gam)` el LP es infactible.

En resumen: **la decisión es la salida 2**, obstrucción con certificado dual formalizado, pero la
obstrucción es exactamente del *método* —la dualidad lineal— y se localiza en un enunciado
abstracto que difiere del concreto sólo en la realizabilidad de los items.
-/

namespace FarExploration.CleanupVerdict

open FarExploration.CleanupLP FarExploration.CleanupBridge FarExploration.CleanupObstruction

/-! ## 1. El lado positivo, con umbral explícito -/

/-- **Régimen de holgura, enunciado concreto.**  Si la pérdida admitida cubre `(1-t)·(5/6)` para
algún racional `0 < t ≤ 1` con `t ≤ gam`, entonces `CodegreeCleanupAt` vale con el umbral
explícito `N = max 1 ⌈(Cst/t + 1)/m⌉₊`, sin regularidad. -/
theorem codegreeCleanupAt_of_scale (gam Cst : ℝ) (m xi t : ℚ)
    (ht0 : 0 < t) (ht1 : t ≤ 1) (htgam : (t : ℝ) ≤ gam) (hm : 0 < m)
    (hxi : (1 - t) * 5 ≤ 6 * xi) :
    FarExploration.CodegreeCleanup.CodegreeCleanupAt gam Cst m xi :=
  codegreeCleanupAt_of_abstract gam Cst m xi
    (abstractCleanupAt_of_scale gam Cst m xi t ht0 ht1 htgam hm hxi)

/-! ## 2. La dicotomía del LP -/

/-- **La dicotomía, con parámetros racionales.**  Para `0 < gam ≤ 1`, `0 < m ≤ 1/49` y `xi ≥ 0`:
por encima de `5(1-gam) ≤ 6·xi` el LP abstracto es factible (y el concreto también); por debajo
de `49·xi < 2(1-gam)` el LP abstracto es **infactible**. -/
theorem abstractCleanup_dichotomy (gam m xi : ℚ) (Cst : ℝ)
    (hgam0 : 0 < gam) (hgam1 : gam ≤ 1) (hm : 0 < m) (hm49 : m ≤ 1 / 49) (hxi0 : 0 ≤ xi) :
    (5 * (1 - gam) ≤ 6 * xi → AbstractCleanupAt (gam : ℝ) Cst m xi)
    ∧ (49 * xi < 2 * (1 - gam) → ¬ AbstractCleanupAt (gam : ℝ) Cst m xi) := by
  constructor
  · intro hslack
    refine abstractCleanupAt_of_scale (gam : ℝ) Cst m xi gam hgam0 hgam1 (le_refl _) hm ?_
    linarith
  · intro hgap
    refine FarExploration.CleanupObstruction.not_abstractCleanupAt (gam : ℝ) Cst m xi hxi0 ?_ ?_
    · have : (m : ℝ) ≤ ((1 / 49 : ℚ) : ℝ) := by exact_mod_cast hm49
      push_cast at this
      exact this
    · have : ((49 * xi : ℚ) : ℝ) < ((2 * (1 - gam) : ℚ) : ℝ) := by exact_mod_cast hgap
      push_cast at this
      exact this

/-! ## 3. La forma de cualquier obstrucción -/

/-- **Toda obstrucción tiene valor cuadrático.**  Si para una instancia no existe ninguna
solución con codegrado `≤ gam` y pérdida `≤ xi·n²`, entonces el escalado `t·x` tampoco sirve, y
por tanto `xi·n² < (1-t)·valor x`.  Dicho de otro modo: una familia que refute el enunciado debe
tener valor `Ω(n²)` —y, por la cota universal `valor ≤ (5/6)n²`, parámetros con
`6·xi < 5(1-t)`. -/
theorem obstruction_value_bound {n : ℕ} {H : ItemSystem (Sym2 (Fin n))} (x : Frac H)
    (gam : ℝ) (xi t : ℚ) (ht0 : 0 < t) (ht1 : t ≤ 1) (htgam : (t : ℝ) ≤ gam)
    (hno : ¬ ∃ y : Frac H, (∀ r s : Sym2 (Fin n), r ≠ s → ((y.codeg r s : ℚ) : ℝ) ≤ gam)
      ∧ x.value - y.value ≤ xi * (n : ℚ) ^ 2) :
    xi * (n : ℚ) ^ 2 < (1 - t) * x.value := by
  by_contra hcon
  push_neg at hcon
  refine hno ⟨x.scale t ht0.le ht1, ?_, ?_⟩
  · intro r s _
    rw [Frac.codeg_scale]
    have h1 : x.codeg r s ≤ 1 := x.codeg_le_one r s
    have h1R : ((x.codeg r s : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h1
    have ht0R : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht0.le
    push_cast
    nlinarith
  · rw [Frac.value_scale]
    linarith

/-! ## 4. El veredicto -/

/-- **El veredicto.**  En el régimen `49·xi < 2(1-gam)` con `m ≤ 1/49`:

* el enunciado LP abstracto es **falso** (con certificado dual explícito), y
* si fuera cierto implicaría el enunciado concreto.

Es decir: ninguna demostración de `CodegreeCleanupAt` que sólo use el programa lineal —
capacidades, rangos, ganancias, codegrados y masa— puede funcionar; hay que usar que los items
son cliques del grafo. -/
theorem lp_route_insufficient (gam m xi : ℚ) (Cst : ℝ)
    (hm49 : m ≤ 1 / 49) (hxi0 : 0 ≤ xi) (hgap : 49 * xi < 2 * (1 - gam)) :
    ¬ AbstractCleanupAt (gam : ℝ) Cst m xi
    ∧ (AbstractCleanupAt (gam : ℝ) Cst m xi →
        FarExploration.CodegreeCleanup.CodegreeCleanupAt (gam : ℝ) Cst m xi) := by
  refine ⟨?_, codegreeCleanupAt_of_abstract (gam : ℝ) Cst m xi⟩
  refine FarExploration.CleanupObstruction.not_abstractCleanupAt (gam : ℝ) Cst m xi hxi0 ?_ ?_
  · have : (m : ℝ) ≤ ((1 / 49 : ℚ) : ℝ) := by exact_mod_cast hm49
    push_cast at this
    exact this
  · have : ((49 * xi : ℚ) : ℝ) < ((2 * (1 - gam) : ℚ) : ℝ) := by exact_mod_cast hgap
    push_cast at this
    exact this

/-- **En los parámetros de la aplicación.**  `uniformRoundingTarget_of_codegreeCleanup` usa
`m = eps/30` y `xi = eps/4`.  Para esos parámetros el LP abstracto es falso en cuanto
`eps ≤ 30/49` y `49·eps/4 < 2(1-gam)`, que es el régimen de `gam` pequeño y `eps` pequeño en el
que la puerta física trabaja. -/
theorem not_abstractCleanupAt_applicationParameters (eps gam : ℚ) (Cst : ℝ)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 30 / 49) (hgap : 49 * (eps / 4) < 2 * (1 - gam)) :
    ¬ AbstractCleanupAt (gam : ℝ) Cst (eps / 30) (eps / 4) := by
  refine (lp_route_insufficient gam (eps / 30) (eps / 4) Cst ?_ (by linarith) hgap).1
  linarith

end FarExploration.CleanupVerdict
