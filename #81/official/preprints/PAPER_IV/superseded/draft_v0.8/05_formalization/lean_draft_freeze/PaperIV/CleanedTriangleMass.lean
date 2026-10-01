import PaperIV.RC01CleanedGate
import PaperIV.LowTriangleReduction

/-!
# La masa triangular sobrevive a la limpieza

`PaperIV.CleanedLowTriangleBridge` quitaba el adaptador del brazo `K₄`, pero dejaba un paso sin
demostrar: que el empaquetamiento limpio **conserve** masa triangular. Éste es ese paso.

## Por qué sale, y sale de lo mismo que el valor

`RC01CleanedGate.cleanedPacking_value_ge` demuestra

```
(1 - u - v) · ∑_H patternGain H · ψ′(H)  ≤  xClean.value
```

y la clave allí es `hreward : gainF K = patternGain H`, que sale de que `profileFiber` es
**transversal** (`K.card = H.card`). Esa misma transversalidad da algo más fuerte y que nadie
había usado: el filtro `K.card = 3` sobre los items **selecciona exactamente los patrones de
tres partes**. Ni un `K₄` se cuela en un patrón triangular, ni al revés.

Luego la masa triangular es la misma identidad que el valor, con `card = 3` en vez de `gainF`:

```
triMass xClean  =  ∑_{H ∈ Pats, |H| = 3}  #cleanFiber(H) · ψ′(H)/((1+u)·vol H)
```

y con la retención `(1-v)·vol H ≤ #cleanFiber(H)` queda

```
(1 - u - v) · ∑_{|H| = 3} ψ′(H)  ≤  triMass xClean.
```

## Lo que esto cierra

Con ella, `CleanedLowTriangleBridge.lowTriangle_branch_free` compone de verdad: basta que la masa
transferida del **brazo triangular** sea `≥ C/(1-u-v)` para que `xClean` entre al gate, y si no lo
es, la dicotomía de `TriangleSwap` cierra por el otro lado. El punto (5) de `RC01-ADAPT` deja de
ser una disyunción con `round_arm_four` dentro.

## Una nota sobre el lema genérico

`canonicalPacking_cardMass_eq` no menciona ni patrones ni limpieza: dice que si las fibras de un
`canonicalPacking` son homogéneas en cardinal, la masa de los items de cardinal `r` es la suma
sobre las fibras de ese cardinal. Vale igual para el brazo de `K₄` con `r = 4`.
-/

namespace PaperIV.CleanedTriangleMass

open Finset
open MixedRounding
open PaperIV.PatternTransfer
open PaperIV.RC01CanonicalFractional
open PaperIV.RC01CanonicalNormalization
open PaperIV.RC01CleanFiber
open PaperIV.RC01CleanedGate

/-! ## 1. El lema genérico: masa por cardinal en un `canonicalPacking` -/

variable {V Pat : Type*} [Fintype V] [DecidableEq V] [Fintype Pat] [DecidableEq Pat]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **La masa de los items de cardinal `r`, exacta.**

Si cada fibra es homogénea en cardinal (`hsize`), el filtro por cardinal selecciona fibras
enteras: las de tamaño `r` entran completas y las demás no aportan nada. -/
theorem canonicalWeight_cardMass_eq
    (Active : Finset Pat) (fiber : Pat → Finset (Finset V)) (c : Pat → ℚ)
    (hitems : ∀ σ ∈ Active, fiber σ ⊆ items G)
    (r : ℕ) (sz : Pat → ℕ)
    (hsize : ∀ σ ∈ Active, ∀ K ∈ fiber σ, K.card = sz σ) :
    ∑ K ∈ (items G).filter (fun K => K.card = r),
        canonicalWeight Active fiber c K
      = ∑ σ ∈ Active.filter (fun σ => sz σ = r), ((fiber σ).card : ℚ) * c σ := by
  classical
  have key : ∀ σ ∈ Active,
      (∑ K ∈ (items G).filter (fun K => K.card = r), (if K ∈ fiber σ then c σ else 0))
        = if sz σ = r then ((fiber σ).card : ℚ) * c σ else 0 := by
    intro σ hσ
    rw [Finset.sum_ite_mem]
    by_cases hr : sz σ = r
    · rw [if_pos hr]
      have hsub : fiber σ ⊆ (items G).filter (fun K => K.card = r) := by
        intro K hK
        refine Finset.mem_filter.2 ⟨hitems σ hσ hK, ?_⟩
        rw [hsize σ hσ K hK, hr]
      rw [Finset.inter_eq_right.2 hsub, Finset.sum_const, nsmul_eq_mul]
    · rw [if_neg hr]
      have hempty : (items G).filter (fun K => K.card = r) ∩ fiber σ = ∅ := by
        ext K
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.notMem_empty, iff_false,
          not_and]
        rintro ⟨-, hKr⟩ hKf
        exact hr (by rw [← hsize σ hσ K hKf, hKr])
      rw [hempty, Finset.sum_empty]
  calc ∑ K ∈ (items G).filter (fun K => K.card = r),
        canonicalWeight Active fiber c K
      = ∑ K ∈ (items G).filter (fun K => K.card = r),
          ∑ σ ∈ Active, (if K ∈ fiber σ then c σ else 0) := rfl
    _ = ∑ σ ∈ Active, ∑ K ∈ (items G).filter (fun K => K.card = r),
          (if K ∈ fiber σ then c σ else 0) := Finset.sum_comm
    _ = ∑ σ ∈ Active, (if sz σ = r then ((fiber σ).card : ℚ) * c σ else 0) :=
        Finset.sum_congr rfl key
    _ = ∑ σ ∈ Active.filter (fun σ => sz σ = r), ((fiber σ).card : ℚ) * c σ :=
        (Finset.sum_filter _ _).symm

/-- Structure-level wrapper of `canonicalWeight_cardMass_eq`.  Feasibility
proofs only package the displayed weight as a `FracPacking`. -/
theorem canonicalPacking_cardMass_eq
    (Active : Finset Pat) (fiber : Pat → Finset (Finset V)) (c : Pat → ℚ)
    (hc : ∀ σ ∈ Active, 0 ≤ c σ)
    (hitems : ∀ σ ∈ Active, fiber σ ⊆ items G)
    (hload : ∀ e ∈ G.edgeFinset, ∑ σ ∈ Active, (oneCount fiber σ e : ℚ) * c σ ≤ 1)
    (r : ℕ) (sz : Pat → ℕ)
    (hsize : ∀ σ ∈ Active, ∀ K ∈ fiber σ, K.card = sz σ) :
    ∑ K ∈ (items G).filter (fun K => K.card = r),
        (canonicalPacking Active fiber c hc hitems hload).weight K
      = ∑ σ ∈ Active.filter (fun σ => sz σ = r), ((fiber σ).card : ℚ) * c σ := by
  simpa [canonicalPacking] using
    canonicalWeight_cardMass_eq (G := G) Active fiber c hitems r sz hsize

/-! ## 2. La masa triangular del empaquetamiento limpio -/

variable {P : Type*} [Fintype P] [DecidableEq P] [Nonempty V]

/-- **La identidad.**  La masa triangular de `xClean` es la suma sobre los patrones de **tres**
partes, y sobre ninguno más: la transversalidad de `profileFiber` lo impone. -/
theorem cleanedPacking_triMass_eq (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (A : Finset P → Finset P → ℚ)
    (vol : Finset P → ℚ) (u : ℚ) (hu : 0 ≤ u)
    (hvolpos : ∀ H ∈ Pats, 0 < vol H)
    (hvol : ∀ H ∈ Pats, ∀ f : Sym2 V,
      A H (partsOf part f) * densT G part f ≤ vol H) :
    PaperIV.LowTriangleReduction.triMass
        (cleanedPacking x part Pats A vol u hu hvolpos hvol)
      = ∑ H ∈ Pats.filter (fun H => H.card = 3),
          ((cleanFiber G part A u H).card : ℚ)
            * budgetCoefficient (psiT x part) (fun H => (1 + u) * vol H) H := by
  classical
  rw [PaperIV.LowTriangleReduction.triMass]
  change ∑ K ∈ (items G).filter (fun K => K.card = 3),
      canonicalWeight Pats (cleanFiber G part A u)
        (budgetCoefficient (psiT x part) (fun H => (1 + u) * vol H)) K
    = _
  exact canonicalWeight_cardMass_eq (G := G) _ _ _
    (fun H _ => cleanFiber_subset_items (G := G) part A u H) 3 (fun H => H.card)
    (fun H _ K hK =>
      ((mem_profileFiber (G := G)).1
        (cleanFiber_subset (G := G) part A u H hK)).2.2)

/-- **La masa triangular sobrevive.**

La retención es la misma `1 - u - v` que en `cleanedPacking_value_ge`: la limpieza se lleva a lo
más `v` de la fibra y el presupuesto paga `1 + u`. -/
theorem cleanedPacking_triMass_ge (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (A : Finset P → Finset P → ℚ)
    (vol : Finset P → ℚ) (u : ℚ) (hu : 0 ≤ u)
    (hvolpos : ∀ H ∈ Pats, 0 < vol H)
    (hvol : ∀ H ∈ Pats, ∀ f : Sym2 V,
      A H (partsOf part f) * densT G part f ≤ vol H)
    (v : ℚ) (hv : 0 ≤ v)
    (hclean : ∀ H ∈ Pats, (1 - v) * vol H ≤ ((cleanFiber G part A u H).card : ℚ)) :
    (1 - u - v) * (∑ H ∈ Pats.filter (fun H => H.card = 3), psiT x part H)
      ≤ PaperIV.LowTriangleReduction.triMass
          (cleanedPacking x part Pats A vol u hu hvolpos hvol) := by
  classical
  rw [cleanedPacking_triMass_eq x part Pats A vol u hu hvolpos hvol, Finset.mul_sum]
  refine Finset.sum_le_sum fun H hH => ?_
  have hHPats : H ∈ Pats := (Finset.mem_filter.1 hH).1
  have hvp : 0 < vol H := hvolpos H hHPats
  have hpsi : 0 ≤ psiT x part H := psiT_nonneg x part H
  have hu1 : (0 : ℚ) < 1 + u := by linarith
  have hb : (0 : ℚ) < (1 + u) * vol H := by positivity
  have hquot : 0 ≤ psiT x part H / ((1 + u) * vol H) := div_nonneg hpsi hb.le
  have hkey : ((1 - v) * vol H) * (psiT x part H / ((1 + u) * vol H))
      = ((1 - v) / (1 + u)) * psiT x part H := by
    field_simp
  rw [budgetCoefficient]
  calc (1 - u - v) * psiT x part H
      ≤ ((1 - v) / (1 + u)) * psiT x part H := by
        refine mul_le_mul_of_nonneg_right ?_ hpsi
        rw [le_div_iff₀ hu1]
        nlinarith [sq_nonneg u, mul_nonneg hu hv]
    _ = ((1 - v) * vol H) * (psiT x part H / ((1 + u) * vol H)) := hkey.symm
    _ ≤ ((cleanFiber G part A u H).card : ℚ) * (psiT x part H / ((1 + u) * vol H)) :=
        mul_le_mul_of_nonneg_right (hclean H hHPats) hquot

end PaperIV.CleanedTriangleMass
