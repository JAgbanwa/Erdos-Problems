import PaperIV.RoundingTrichotomy
import PaperIV.RC01MarkedRounding

/-!
# El ensamblaje del Corolario 7.3a: qué falta exactamente

Este módulo pone en un solo sitio la cadena entera y deja **con nombre** las obligaciones que
quedan, en vez de repartidas por doce módulos.

## La forma del argumento

`PaperIV.RoundingTrichotomy.uniformRoundingTarget_of_regimes` reduce el objetivo a **dos**
regímenes —el disperso lo cierra la cota dual sin hipótesis—:

```
(pocos triángulos)  →  (denso con triángulos)  →  UniformRoundingTarget ε
```

y el gate con holgura (`RC01MarkedRounding.exists_packing_loss_le_of_slackMarkedQuota`,
verificado aquí) cierra el segundo a cambio de **una** estimación: codegrado pesado `≤ γ`.

## Las dos obligaciones que quedan, y son distintas

**En el régimen denso**, el gate pide codegrado pequeño, y eso es falso para el `x` del
enunciado (un `K₄` de peso `1` lo pone a `1`). Hay que pasar a un packing esparcido `x′`
—construido y demostrado legal en `PaperIV.SpreadRestricted`— y transferirle el valor. Las dos
condiciones son las hipótesis `hcodeg` y `hvalue` de `dense_of_spread` abajo.

**En el régimen de pocos triángulos** la situación es **peor, no mejor**, y conviene no
confundirlas: el gate no se aplica porque pide `C ≤ triangleMass x`, y ahí la masa de triángulos
es por hipótesis pequeña. `PaperIV.LowTriangleReduction` reduce ese régimen al brazo puro de
`K₄`, pero el único redondeo disponible para un brazo es
`MixedRounding.round_arm_four`, que sigue pidiendo **las tres** estimaciones previas al gate
—carga casi perfecta fuera de `Exc`, `|Exc|` pequeño y codegrado—.

Es decir: **el gate con holgura simplificó el régimen principal pero no el degenerado**. Lo
anoto porque es fácil dar por hecho que el corolario quedó reducido a una sola estimación, y no
es así: quedó reducido a una en el régimen que manda y a tres en el que no.

## Una precisión sobre `x′`

`x′` debe repartir masa en **los dos brazos**. La construcción de `SpreadRestricted` es genérica
en el conjunto de patrones, así que lo admite; pero si sólo se instancia con patrones `K₄`,
entonces `triangleMass x′ = 0 < C` y el gate tampoco se aplica a `x′`. Por eso `hmass` aparece
explícita abajo.
-/

namespace PaperIV.Corollary73Assembly

open MixedRounding

/-! ## 1. El puente de masas entre `ℚ` y `ℝ` -/

/-- `triMass` (en `ℚ`, el que usa `LowTriangleReduction`) y `triangleMass` (en `ℝ`, el que usa
el gate) son la misma cantidad. -/
theorem triMass_cast {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (x : FracPacking G) :
    ((PaperIV.LowTriangleReduction.triMass x : ℚ) : ℝ)
      = PaperIV.JointTwoQuotaPhysical.triangleMass x := by
  rw [PaperIV.LowTriangleReduction.triMass, PaperIV.JointTwoQuotaPhysical.triangleMass]
  push_cast
  rfl

/-! ## 2. El régimen denso, desde el gate y un esparcido -/

/-- **El régimen denso, cerrado.**

Dado el gate con holgura y un packing esparcido `x′` con

* codegrado pesado `≤ γ` (`hcodeg`),
* masa de triángulos suficiente (`hmass`),
* y pérdida de valor acotada (`hvalue`),

sale la conclusión del régimen denso. Las tres hipótesis son sobre `x′`, no sobre `x`: ésa es
toda la diferencia, y es la razón de que `SpreadRestricted` exista. -/
theorem dense_of_spread {n : ℕ} (hn : 1 ≤ n) {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    {γ C D : ℝ}
    (hgate : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (y : FracPacking G'),
      12 + 10 * D ≤ ζ * (n : ℝ) ^ 2 →
      (∀ e f : Sym2 (Fin n), e ≠ f →
        ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G').filter
            (fun S => e ∈ S ∧ f ∈ S), inducedWeight y S ≤ γ) →
      C ≤ PaperIV.JointTwoQuotaPhysical.triangleMass y →
      ∃ P : Packing G', (((y.value : ℚ) : ℝ) - (P.gain : ℝ)) ≤ ζ * (n : ℝ) ^ 2)
    (x x' : FracPacking G)
    (hsize : 12 + 10 * D ≤ ζ * (n : ℝ) ^ 2)
    (hcodeg : ∀ e f : Sym2 (Fin n), e ≠ f →
      ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter
          (fun S => e ∈ S ∧ f ∈ S), inducedWeight x' S ≤ γ)
    (hmass : C ≤ PaperIV.JointTwoQuotaPhysical.triangleMass x')
    {Δ : ℝ} (hvalue : ((x.value : ℚ) : ℝ) - ((x'.value : ℚ) : ℝ) ≤ Δ) :
    ∃ P : Packing G, (((x.value : ℚ) : ℝ) - (P.gain : ℝ)) ≤ ζ * (n : ℝ) ^ 2 + Δ := by
  obtain ⟨P, hP⟩ := hgate G x' hsize hcodeg hmass
  exact ⟨P, by linarith⟩

/-! ## 3. Lo que el régimen degenerado pide, y es más -/

/-- **El régimen de pocos triángulos necesita las tres estimaciones.**

`LowTriangleReduction.lowTriangle_target` lo reduce al brazo puro de `K₄`, pero el redondeo de
un brazo (`MixedRounding.round_arm_four`) sigue pidiendo carga casi perfecta fuera de un
excepcional, excepcional pequeño y codegrado — las tres que el gate con holgura había quitado.

Este enunciado no demuestra nada nuevo: hace explícita la forma de esa obligación, para que no
se confunda con la del régimen denso. -/
def LowTriangleObligation (n : ℕ) (C ε : ℚ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : FracPacking G),
    PaperIV.LowTriangleReduction.triMass x ≤ C →
    ∃ P : Packing G, x.value - (P.gain : ℚ) ≤ ε * (n : ℚ) ^ 2

/-- **El régimen denso, en la forma que la trichotomía consume.** -/
def DenseObligation (n : ℕ) (C ε : ℚ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : FracPacking G),
    (6 / 5 : ℚ) * ε * (n : ℚ) ^ 2 < (G.edgeFinset.card : ℚ) →
    C < PaperIV.LowTriangleReduction.triMass x →
    ∃ P : Packing G, x.value - (P.gain : ℚ) ≤ ε * (n : ℚ) ^ 2

/-- **El remate.**  Con las dos obligaciones, el objetivo. El régimen disperso no aparece:
lo cierra la cota dual sin hipótesis. -/
theorem uniformRoundingTarget_of_obligations {ε C : ℚ} (N : ℕ)
    (hlow : ∀ n : ℕ, N ≤ n → LowTriangleObligation n C ε)
    (hdense : ∀ n : ℕ, N ≤ n → DenseObligation n C ε) :
    UniformRoundingTarget ε :=
  PaperIV.RoundingTrichotomy.uniformRoundingTarget_of_regimes N
    (fun n hn G _ x h => hlow n hn G x h)
    (fun n hn G _ x h1 h2 => hdense n hn G x h1 h2)

end PaperIV.Corollary73Assembly
