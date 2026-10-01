import PaperIV.RC01CleanedMixedCodegree
import PaperIV.RC01MarkedRounding
import PaperIV.RC01PatternMassScale

/-!
# RC01: el gate con slack sobre las fibras limpias

Este módulo reúne los apartados A y B en el empaquetamiento fraccional concreto
`cleanedPacking` y lo entrega al nibble con slack.

* `cleanedPacking` es literalmente
  `RC01CleanedSpreadPacking.cleanedSpreadPacking` aplicado a la fibra limpia
  `RC01CleanFiber.cleanFiber`, con presupuesto `(1+u) · vol σ`.  Sus cuatro
  obligaciones (contención, servicio, presupuesto positivo y dispersión física)
  **son teoremas** del apartado A, no hipótesis.
* `cleanedPacking_joint_codegree_le` descarga el codegree real del hipergrafo
  conjunto con la cota racional del apartado B, vía
  `RC01CanonicalSlackBridge.budgetPacking_joint_codegree_le`.
* `cleanedPacking_value_ge` compara su valor con la masa transferida usando
  `RC01CanonicalNormalization.budget_term_value_ge`, sin renormalizar por el
  cardinal de la fibra limpia: la retención sale de `A.4`.
* `exists_packing_loss_le_of_cleanedSpread` aplica
  `RC01MarkedRounding.exists_packing_loss_le_of_slackMarkedQuota`.
* `lowTriangle_branch_of_cleanedSpread` cubre la rama de masa triangular baja
  con `LowTriangleReduction.lowTriangle_target`.

El adaptador que sigue faltando para `MixedRounding.UniformRoundingTarget` está
documentado (sin postularse) en `docs/RC01_REMAINING_ADAPTER.md`.
-/

namespace PaperIV.RC01CleanedGate

open Finset
open MixedRounding
open PaperIV.PatternTransfer
open PaperIV.RC01CleanFiber
open PaperIV.RC01CleanedMixedCodegree
open PaperIV.RC01CleanedSpreadPacking
open PaperIV.RC01CanonicalFractional
open PaperIV.RC01CanonicalNormalization
open PaperIV.RC01CanonicalSlackBridge
open PaperIV.RC01PatternMassScale
open PaperIV.JointTwoQuotaPhysical
open PaperIV.RootedCountingBridge

variable {V P : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype P] [DecidableEq P]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. El empaquetamiento limpio -/

/-- La ganancia común de todas las copias de un patrón reducido. -/
def patternGain (H : Finset P) : ℚ := (H.card.choose 2 : ℚ) - 1

/-- **El empaquetamiento fraccional limpio.**  Es `cleanedSpreadPacking` sobre la
fibra limpia literal, con presupuesto `(1+u) · vol σ`. -/
noncomputable def cleanedPacking (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (A : Finset P → Finset P → ℚ)
    (vol : Finset P → ℚ) (u : ℚ) (hu : 0 ≤ u)
    (hvolpos : ∀ H ∈ Pats, 0 < vol H)
    (hvol : ∀ H ∈ Pats, ∀ f : Sym2 V,
      A H (partsOf part f) * densT G part f ≤ vol H) :
    FracPacking G :=
  cleanedSpreadPacking x part Pats (cleanFiber G part A u)
    (fun H => (1 + u) * vol H)
    (fun H hH => by
      have := hvolpos H hH
      positivity)
    (fun H _ => cleanFiber_subset_items part A u H)
    (fun H _ K hK e he => serving_of_mem_cleanFiber hK he)
    (fun e H hH => by
      have hHPats : H ∈ Pats := (Finset.mem_filter.1 hH).1
      exact cleanFiber_oneCount_mul_densT_le_budget part A vol u hu H
        (hvolpos H hHPats) (hvol H hHPats) e)

/-! ## 2. El codegree del empaquetamiento limpio -/

/-- **(C.1)** El codegree del hipergrafo conjunto queda descargado por la cota
racional del apartado B. -/
theorem cleanedPacking_joint_codegree_le (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (A : Finset P → Finset P → ℚ)
    (vol : Finset P → ℚ) (u : ℚ) (hu : 0 ≤ u)
    (hvolpos : ∀ H ∈ Pats, 0 < vol H)
    (hvol : ∀ H ∈ Pats, ∀ f : Sym2 V,
      A H (partsOf part f) * densT G part f ≤ vol H)
    (t : ℕ) (k3 k4 a2 a5 gamma : ℚ)
    (ht : 1 ≤ t) (ha2 : 0 < a2) (ha5 : 0 < a5)
    (hmass1 : ∀ H ∈ Pats, psiT x part H ≤ 1)
    (hcard : ∀ H ∈ Pats, H.card = 3 ∨ H.card = 4)
    (hpart : ∀ H ∈ Pats, ∀ p ∈ H,
      (univ.filter (fun v => part v = p)).card ≤ t)
    (hk3 : ((Pats.filter (fun H => H.card = 3)).card : ℚ) ≤ k3)
    (hk4 : ((Pats.filter (fun H => ¬ H.card = 3)).card : ℚ) ≤ k4)
    (hb3 : ∀ H ∈ Pats, H.card = 3 → a2 * (t : ℚ) ≤ (1 + u) * vol H)
    (hb4 : ∀ H ∈ Pats, H.card = 4 → a5 * (t : ℚ) ^ 2 ≤ (1 + u) * vol H)
    (hthreshold : k3 * a5 + k4 * a2 ≤ gamma * a2 * a5 * (t : ℚ)) :
    ∀ e f : Sym2 V, e ≠ f →
      ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter
          (fun S => e ∈ S ∧ f ∈ S),
        inducedWeight (cleanedPacking x part Pats A vol u hu hvolpos hvol) S
      ≤ (gamma : ℝ) := by
  have hcodeg : ∀ e f : Sym2 V, e ≠ f →
      ∑ H ∈ Pats, (twoCount (cleanFiber G part A u) H e f : ℚ) *
        budgetCoefficient (psiT x part) (fun H => (1 + u) * vol H) H ≤ gamma := by
    intro e f hef
    exact cleaned_mixed_codegree_le part A vol (psiT x part) u Pats t k3 k4 a2 a5
      gamma ht ha2 ha5 (fun H => psiT_nonneg x part H) hmass1 hcard hpart hk3 hk4
      hb3 hb4 hthreshold e f hef
  exact budgetPacking_joint_codegree_le Pats (cleanFiber G part A u)
    (psiT x part) (fun H => (1 + u) * vol H) (activeServing Pats part)
    (densT G part) (fun H => psiT_nonneg x part H) (fun e => densT_pos part e)
    (activeServing_patternCapacity x part Pats) (activeServing_subset Pats part)
    (fun H hH => by have := hvolpos H hH; positivity)
    (fun H _ => cleanFiber_subset_items part A u H)
    (fun e H hH hcount => activeServing_of_oneCount_pos hH hcount)
    (fun e H hH => by
      have hHPats : H ∈ Pats := (Finset.mem_filter.1 hH).1
      exact cleanFiber_oneCount_mul_densT_le_budget part A vol u hu H
        (hvolpos H hHPats) (hvol H hHPats) e)
    gamma hcodeg

/-- Dimensionally correct variant of `cleanedPacking_joint_codegree_le`.
It permits transferred pattern mass up to a physical pair scale `D`, provided
the reference volumes carry the same scale. -/
theorem cleanedPacking_joint_codegree_le_of_mass_le (x : FracPacking G)
    (part : V → P) (Pats : Finset (Finset P))
    (A : Finset P → Finset P → ℚ) (vol : Finset P → ℚ)
    (u : ℚ) (hu : 0 ≤ u)
    (hvolpos : ∀ H ∈ Pats, 0 < vol H)
    (hvol : ∀ H ∈ Pats, ∀ f : Sym2 V,
      A H (partsOf part f) * densT G part f ≤ vol H)
    (t : ℕ) (D k3 k4 a2 a5 gamma : ℚ)
    (ht : 1 ≤ t) (hD : 0 < D) (ha2 : 0 < a2) (ha5 : 0 < a5)
    (hmassD : ∀ H ∈ Pats, psiT x part H ≤ D)
    (hcard : ∀ H ∈ Pats, H.card = 3 ∨ H.card = 4)
    (hpart : ∀ H ∈ Pats, ∀ p ∈ H,
      (univ.filter (fun v => part v = p)).card ≤ t)
    (hk3 : ((Pats.filter (fun H => H.card = 3)).card : ℚ) ≤ k3)
    (hk4 : ((Pats.filter (fun H => ¬ H.card = 3)).card : ℚ) ≤ k4)
    (hb3 : ∀ H ∈ Pats, H.card = 3 →
      a2 * D * (t : ℚ) ≤ (1 + u) * vol H)
    (hb4 : ∀ H ∈ Pats, H.card = 4 →
      a5 * D * (t : ℚ) ^ 2 ≤ (1 + u) * vol H)
    (hthreshold : k3 * a5 + k4 * a2 ≤ gamma * a2 * a5 * (t : ℚ)) :
    ∀ e f : Sym2 V, e ≠ f →
      ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter
          (fun S => e ∈ S ∧ f ∈ S),
        inducedWeight (cleanedPacking x part Pats A vol u hu hvolpos hvol) S
      ≤ (gamma : ℝ) := by
  have hcodeg : ∀ e f : Sym2 V, e ≠ f →
      ∑ H ∈ Pats, (twoCount (cleanFiber G part A u) H e f : ℚ) *
        budgetCoefficient (psiT x part) (fun H => (1 + u) * vol H) H ≤ gamma := by
    intro e f hef
    exact cleaned_mixed_codegree_le_of_mass_le part A vol (psiT x part) u Pats t D
      k3 k4 a2 a5 gamma ht hD ha2 ha5 (fun H => psiT_nonneg x part H)
      hmassD hcard hpart hk3 hk4 hb3 hb4 hthreshold e f hef
  exact budgetPacking_joint_codegree_le Pats (cleanFiber G part A u)
    (psiT x part) (fun H => (1 + u) * vol H) (activeServing Pats part)
    (densT G part) (fun H => psiT_nonneg x part H) (fun e => densT_pos part e)
    (activeServing_patternCapacity x part Pats) (activeServing_subset Pats part)
    (fun H hH => by have := hvolpos H hH; positivity)
    (fun H _ => cleanFiber_subset_items part A u H)
    (fun e H hH hcount => activeServing_of_oneCount_pos hH hcount)
    (fun e H hH => by
      have hHPats : H ∈ Pats := (Finset.mem_filter.1 hH).1
      exact cleanFiber_oneCount_mul_densT_le_budget part A vol u hu H
        (hvolpos H hHPats) (hvol H hHPats) e)
    gamma hcodeg

/-- Fully physical `D = t²` instance.  It is enough that every retained
pattern serves at least one real pair; capacity and the class-size bound then
derive the mass bound rather than assuming a normalization. -/
theorem cleanedPacking_joint_codegree_le_of_served_patterns (x : FracPacking G)
    (part : V → P) (Pats : Finset (Finset P))
    (A : Finset P → Finset P → ℚ) (vol : Finset P → ℚ)
    (u : ℚ) (hu : 0 ≤ u)
    (hvolpos : ∀ H ∈ Pats, 0 < vol H)
    (hvol : ∀ H ∈ Pats, ∀ f : Sym2 V,
      A H (partsOf part f) * densT G part f ≤ vol H)
    (t : ℕ) (k3 k4 a2 a5 gamma : ℚ)
    (ht : 1 ≤ t) (ha2 : 0 < a2) (ha5 : 0 < a5)
    (hserved : ∀ H ∈ Pats, ∃ e : Sym2 V, H ∈ servingT part e)
    (hcard : ∀ H ∈ Pats, H.card = 3 ∨ H.card = 4)
    (hpart : ∀ H ∈ Pats, ∀ p ∈ H,
      (univ.filter (fun v => part v = p)).card ≤ t)
    (hk3 : ((Pats.filter (fun H => H.card = 3)).card : ℚ) ≤ k3)
    (hk4 : ((Pats.filter (fun H => ¬ H.card = 3)).card : ℚ) ≤ k4)
    (hb3 : ∀ H ∈ Pats, H.card = 3 →
      a2 * (t : ℚ) ^ 2 * (t : ℚ) ≤ (1 + u) * vol H)
    (hb4 : ∀ H ∈ Pats, H.card = 4 →
      a5 * (t : ℚ) ^ 2 * (t : ℚ) ^ 2 ≤ (1 + u) * vol H)
    (hthreshold : k3 * a5 + k4 * a2 ≤ gamma * a2 * a5 * (t : ℚ)) :
    ∀ e f : Sym2 V, e ≠ f →
      ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter
          (fun S => e ∈ S ∧ f ∈ S),
        inducedWeight (cleanedPacking x part Pats A vol u hu hvolpos hvol) S
      ≤ (gamma : ℝ) := by
  have hD : (0 : ℚ) < (t : ℚ) ^ 2 := by
    have htQ : (0 : ℚ) < (t : ℚ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht)
    positivity
  have hmass : ∀ H ∈ Pats, psiT x part H ≤ (t : ℚ) ^ 2 := by
    intro H hH
    obtain ⟨e, he⟩ := hserved H hH
    exact psiT_le_sq_of_mem_serving x part t ht (hpart H hH) he
  exact cleanedPacking_joint_codegree_le_of_mass_le x part Pats A vol u hu hvolpos
    hvol t ((t : ℚ) ^ 2) k3 k4 a2 a5 gamma ht hD ha2 ha5 hmass hcard hpart
    hk3 hk4 hb3 hb4 hthreshold

/-! ## 3. El valor del empaquetamiento limpio -/

/-- **(C.2)** El valor del empaquetamiento limpio domina la masa transferida con
la retención multiplicativa `1 - u - v`.  No hay renormalización por el cardinal
de la fibra limpia: la escala es el volumen de referencia `vol σ`. -/
theorem cleanedPacking_value_ge (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (A : Finset P → Finset P → ℚ)
    (vol : Finset P → ℚ) (u : ℚ) (hu : 0 ≤ u)
    (hvolpos : ∀ H ∈ Pats, 0 < vol H)
    (hvol : ∀ H ∈ Pats, ∀ f : Sym2 V,
      A H (partsOf part f) * densT G part f ≤ vol H)
    (v : ℚ) (hv : 0 ≤ v)
    (hcard : ∀ H ∈ Pats, H.card = 3 ∨ H.card = 4)
    (hclean : ∀ H ∈ Pats, (1 - v) * vol H ≤ ((cleanFiber G part A u H).card : ℚ)) :
    (1 - u - v) * (∑ H ∈ Pats, patternGain H * psiT x part H)
      ≤ (cleanedPacking x part Pats A vol u hu hvolpos hvol).value := by
  have hreward : ∀ H ∈ Pats, ∀ K ∈ cleanFiber G part A u H,
      gainF ℚ K = patternGain H := by
    intro H _ K hK
    obtain ⟨-, -, hcardK⟩ :=
      mem_profileFiber.1 (cleanFiber_subset part A u H hK)
    rw [gainF, patternGain, hcardK]
  have hvalue : (cleanedPacking x part Pats A vol u hu hvolpos hvol).value
      = ∑ H ∈ Pats, ((cleanFiber G part A u H).card : ℚ) *
          (patternGain H *
            budgetCoefficient (psiT x part) (fun H => (1 + u) * vol H) H) := by
    exact budgetPacking_value_eq Pats (cleanFiber G part A u) (psiT x part)
      (fun H => (1 + u) * vol H) patternGain (activeServing Pats part)
      (densT G part) (fun H => psiT_nonneg x part H) (fun e => densT_pos part e)
      (activeServing_patternCapacity x part Pats) (activeServing_subset Pats part)
      (fun H hH => by have := hvolpos H hH; positivity)
      (fun H _ => cleanFiber_subset_items part A u H)
      (fun e H hH hcount => activeServing_of_oneCount_pos hH hcount)
      (fun e H hH => by
        have hHPats : H ∈ Pats := (Finset.mem_filter.1 hH).1
        exact cleanFiber_oneCount_mul_densT_le_budget part A vol u hu H
          (hvolpos H hHPats) (hvol H hHPats) e)
      hreward
  rw [hvalue, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro H hH
  have hgain : 0 ≤ patternGain H := by
    rcases hcard H hH with h | h
    · rw [patternGain, h]; norm_num
    · rw [patternGain, h, show Nat.choose 4 2 = 6 from by decide]; norm_num
  have hterm := budget_term_value_ge (clean := ((cleanFiber G part A u H).card : ℚ))
    (reference := vol H) (mass := psiT x part H) (reward := patternGain H)
    (u := u) (v := v) (hvolpos H hH) (psiT_nonneg x part H) hgain hu hv
    (hclean H hH)
  simpa [budgetCoefficient] using hterm

/-- **(C.2')** La misma comparación, con la retención deducida directamente de
los datos de conteo: cotas sobre las familias de raíces malas, sobre las fibras
de una raíz y sobre el volumen de referencia.  La retención `1-v` no se supone:
es `RC01CleanFiber.cleanFiber_card_ge`. -/
theorem cleanedPacking_value_ge_of_removal_bounds (x : FracPacking G)
    (part : V → P) (Pats : Finset (Finset P))
    (A : Finset P → Finset P → ℚ) (vol : Finset P → ℚ) (u : ℚ)
    (hu : 0 ≤ u) (hvolpos : ∀ H ∈ Pats, 0 < vol H)
    (hvol : ∀ H ∈ Pats, ∀ f : Sym2 V,
      A H (partsOf part f) * densT G part f ≤ vol H)
    {beta M v : ℚ} (hM : 0 ≤ M) (hv : 0 ≤ v)
    (hcard : ∀ H ∈ Pats, H.card = 3 ∨ H.card = 4)
    (hbad : ∀ H ∈ Pats, ∀ pq ∈ H.powersetCard 2,
      ((badRoots G part A u H pq).card : ℚ) ≤ beta)
    (hfib : ∀ H ∈ Pats, ∀ pq : Finset P, ∀ e : Sym2 V,
      ((fiber (profileFiber G part H) (rootEdge part pq) e).card : ℚ) ≤ M)
    (href : ∀ H ∈ Pats, vol H ≤ ((profileFiber G part H).card : ℚ))
    (hloss : ∀ H ∈ Pats, ((H.card.choose 2 : ℕ) : ℚ) * (beta * M) ≤ v * vol H) :
    (1 - u - v) * (∑ H ∈ Pats, patternGain H * psiT x part H)
      ≤ (cleanedPacking x part Pats A vol u hu hvolpos hvol).value :=
  cleanedPacking_value_ge x part Pats A vol u hu hvolpos hvol v hv hcard
    (fun H hH => cleanFiber_card_ge part A u H hM (hbad H hH) (hfib H hH)
      (href H hH) (hloss H hH))

/-! ## 4. El gate con slack -/

/-- **(C.3)** El gate con slack aplicado al empaquetamiento limpio.

Todas las obligaciones físicas del nibble —dispersión y codegree— son teoremas
de los apartados A y B sobre las fibras limpias literales: sólo quedan la
aritmética de umbrales y la cota constante inferior de masa triangular, que es
exactamente la hipótesis del gate. -/
theorem exists_packing_loss_le_of_cleanedSpread (zeta : ℝ) (hzeta : 0 < zeta)
    (hzeta1 : zeta ≤ 1) :
    ∃ gam : ℝ, 0 < gam ∧ ∃ Cst : ℝ, 0 < Cst ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (n : ℕ) [NeZero n] (Gn : SimpleGraph (Fin n)) [DecidableRel Gn.Adj]
        (x : FracPacking Gn) (part : Fin n → P) (Pats : Finset (Finset P))
        (A : Finset P → Finset P → ℚ) (vol : Finset P → ℚ)
        (u : ℚ) (hu : 0 ≤ u)
        (hvolpos : ∀ H ∈ Pats, 0 < vol H)
        (hvol : ∀ H ∈ Pats, ∀ f : Sym2 (Fin n),
          A H (partsOf part f) * densT Gn part f ≤ vol H)
        (t : ℕ) (k3 k4 a2 a5 gamma : ℚ),
        1 ≤ t → 0 < a2 → 0 < a5 →
        (∀ H ∈ Pats, psiT x part H ≤ 1) →
        (∀ H ∈ Pats, H.card = 3 ∨ H.card = 4) →
        (∀ H ∈ Pats, ∀ p ∈ H,
          (univ.filter (fun w => part w = p)).card ≤ t) →
        ((Pats.filter (fun H => H.card = 3)).card : ℚ) ≤ k3 →
        ((Pats.filter (fun H => ¬ H.card = 3)).card : ℚ) ≤ k4 →
        (∀ H ∈ Pats, H.card = 3 → a2 * (t : ℚ) ≤ (1 + u) * vol H) →
        (∀ H ∈ Pats, H.card = 4 → a5 * (t : ℚ) ^ 2 ≤ (1 + u) * vol H) →
        k3 * a5 + k4 * a2 ≤ gamma * a2 * a5 * (t : ℚ) →
        (gamma : ℝ) ≤ gam →
        12 + 10 * D ≤ zeta * (n : ℝ) ^ 2 →
        Cst ≤ triangleMass (cleanedPacking x part Pats A vol u hu hvolpos hvol) →
        ∃ Pk : Packing Gn,
          (((cleanedPacking x part Pats A vol u hu hvolpos hvol).value : ℚ) : ℝ)
            - (Pk.gain : ℝ) ≤ zeta * (n : ℝ) ^ 2 := by
  obtain ⟨gam, hgam, Cst, hCst, D, hD, hgate⟩ :=
    PaperIV.RC01MarkedRounding.exists_packing_loss_le_of_slackMarkedQuota zeta
      hzeta hzeta1
  refine ⟨gam, hgam, Cst, hCst, D, hD, ?_⟩
  intro n _ Gn _ x part Pats A vol u hu hvolpos hvol t k3 k4 a2 a5 gamma ht ha2
    ha5 hmass1 hcard hpart hk3 hk4 hb3 hb4 hthreshold hgamma hsize hmass
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  refine hgate n hn Gn _ hsize ?_ hmass
  intro e f hef
  refine le_trans ?_ hgamma
  exact cleanedPacking_joint_codegree_le x part Pats A vol u hu hvolpos hvol t k3
    k4 a2 a5 gamma ht ha2 ha5 hmass1 hcard hpart hk3 hk4 hb3 hb4 hthreshold e f hef

/-- Physical-scale version of the cleaned slack gate.  The obsolete
normalization `psiT ≤ 1` is replaced by the literal statement that each active
pattern serves a pair; the theorem derives `psiT ≤ t²` internally. -/
theorem exists_packing_loss_le_of_cleanedSpread_physicalScale
    (zeta : ℝ) (hzeta : 0 < zeta) (hzeta1 : zeta ≤ 1) :
    ∃ gam : ℝ, 0 < gam ∧ ∃ Cst : ℝ, 0 < Cst ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (n : ℕ) [NeZero n] (Gn : SimpleGraph (Fin n)) [DecidableRel Gn.Adj]
        (x : FracPacking Gn) (part : Fin n → P) (Pats : Finset (Finset P))
        (A : Finset P → Finset P → ℚ) (vol : Finset P → ℚ)
        (u : ℚ) (hu : 0 ≤ u)
        (hvolpos : ∀ H ∈ Pats, 0 < vol H)
        (hvol : ∀ H ∈ Pats, ∀ f : Sym2 (Fin n),
          A H (partsOf part f) * densT Gn part f ≤ vol H)
        (t : ℕ) (k3 k4 a2 a5 gamma : ℚ),
        1 ≤ t → 0 < a2 → 0 < a5 →
        (∀ H ∈ Pats, ∃ e : Sym2 (Fin n), H ∈ servingT part e) →
        (∀ H ∈ Pats, H.card = 3 ∨ H.card = 4) →
        (∀ H ∈ Pats, ∀ p ∈ H,
          (univ.filter (fun w => part w = p)).card ≤ t) →
        ((Pats.filter (fun H => H.card = 3)).card : ℚ) ≤ k3 →
        ((Pats.filter (fun H => ¬ H.card = 3)).card : ℚ) ≤ k4 →
        (∀ H ∈ Pats, H.card = 3 →
          a2 * (t : ℚ) ^ 2 * (t : ℚ) ≤ (1 + u) * vol H) →
        (∀ H ∈ Pats, H.card = 4 →
          a5 * (t : ℚ) ^ 2 * (t : ℚ) ^ 2 ≤ (1 + u) * vol H) →
        k3 * a5 + k4 * a2 ≤ gamma * a2 * a5 * (t : ℚ) →
        (gamma : ℝ) ≤ gam →
        12 + 10 * D ≤ zeta * (n : ℝ) ^ 2 →
        Cst ≤ triangleMass (cleanedPacking x part Pats A vol u hu hvolpos hvol) →
        ∃ Pk : Packing Gn,
          (((cleanedPacking x part Pats A vol u hu hvolpos hvol).value : ℚ) : ℝ)
            - (Pk.gain : ℝ) ≤ zeta * (n : ℝ) ^ 2 := by
  obtain ⟨gam, hgam, Cst, hCst, D, hD, hgate⟩ :=
    PaperIV.RC01MarkedRounding.exists_packing_loss_le_of_slackMarkedQuota zeta
      hzeta hzeta1
  refine ⟨gam, hgam, Cst, hCst, D, hD, ?_⟩
  intro n _ Gn _ x part Pats A vol u hu hvolpos hvol t k3 k4 a2 a5 gamma ht ha2
    ha5 hserved hcard hpart hk3 hk4 hb3 hb4 hthreshold hgamma hsize hmass
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  refine hgate n hn Gn _ hsize ?_ hmass
  intro e f hef
  refine le_trans ?_ hgamma
  exact cleanedPacking_joint_codegree_le_of_served_patterns x part Pats A vol u hu
    hvolpos hvol t k3 k4 a2 a5 gamma ht ha2 ha5 hserved hcard hpart hk3 hk4 hb3
    hb4 hthreshold e f hef

/-- **(C.3')** La forma con masa: el packing físico entregado por el gate pierde
a lo sumo `zeta · n²` respecto de la **masa transferida** `∑ gain · ψ′`, con la
retención multiplicativa `1 - u - v` deducida de los datos de conteo.  Es el
enunciado que usa la ruta RC01 río abajo: no aparece ni `hspread`, ni `hcodeg`,
ni la existencia de un packing como hipótesis. -/
theorem exists_packing_mass_loss_le_of_cleanedSpread (zeta : ℝ) (hzeta : 0 < zeta)
    (hzeta1 : zeta ≤ 1) :
    ∃ gam : ℝ, 0 < gam ∧ ∃ Cst : ℝ, 0 < Cst ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (n : ℕ) [NeZero n] (Gn : SimpleGraph (Fin n)) [DecidableRel Gn.Adj]
        (x : FracPacking Gn) (part : Fin n → P) (Pats : Finset (Finset P))
        (A : Finset P → Finset P → ℚ) (vol : Finset P → ℚ)
        (u : ℚ) (hu : 0 ≤ u)
        (hvolpos : ∀ H ∈ Pats, 0 < vol H)
        (hvol : ∀ H ∈ Pats, ∀ f : Sym2 (Fin n),
          A H (partsOf part f) * densT Gn part f ≤ vol H)
        (t : ℕ) (k3 k4 a2 a5 gamma beta M v : ℚ),
        1 ≤ t → 0 < a2 → 0 < a5 → 0 ≤ M → 0 ≤ v →
        (∀ H ∈ Pats, psiT x part H ≤ 1) →
        (∀ H ∈ Pats, H.card = 3 ∨ H.card = 4) →
        (∀ H ∈ Pats, ∀ p ∈ H,
          (univ.filter (fun w => part w = p)).card ≤ t) →
        ((Pats.filter (fun H => H.card = 3)).card : ℚ) ≤ k3 →
        ((Pats.filter (fun H => ¬ H.card = 3)).card : ℚ) ≤ k4 →
        (∀ H ∈ Pats, H.card = 3 → a2 * (t : ℚ) ≤ (1 + u) * vol H) →
        (∀ H ∈ Pats, H.card = 4 → a5 * (t : ℚ) ^ 2 ≤ (1 + u) * vol H) →
        k3 * a5 + k4 * a2 ≤ gamma * a2 * a5 * (t : ℚ) →
        (∀ H ∈ Pats, ∀ pq ∈ H.powersetCard 2,
          ((badRoots Gn part A u H pq).card : ℚ) ≤ beta) →
        (∀ H ∈ Pats, ∀ pq : Finset P, ∀ e : Sym2 (Fin n),
          ((fiber (profileFiber Gn part H) (rootEdge part pq) e).card : ℚ) ≤ M) →
        (∀ H ∈ Pats, vol H ≤ ((profileFiber Gn part H).card : ℚ)) →
        (∀ H ∈ Pats, ((H.card.choose 2 : ℕ) : ℚ) * (beta * M) ≤ v * vol H) →
        (gamma : ℝ) ≤ gam →
        12 + 10 * D ≤ zeta * (n : ℝ) ^ 2 →
        Cst ≤ triangleMass (cleanedPacking x part Pats A vol u hu hvolpos hvol) →
        ∃ Pk : Packing Gn,
          (((1 - u - v) * (∑ H ∈ Pats, patternGain H * psiT x part H) : ℚ) : ℝ)
            - (Pk.gain : ℝ) ≤ zeta * (n : ℝ) ^ 2 := by
  obtain ⟨gam, hgam, Cst, hCst, D, hD, hgate⟩ :=
    exists_packing_loss_le_of_cleanedSpread (P := P) zeta hzeta hzeta1
  refine ⟨gam, hgam, Cst, hCst, D, hD, ?_⟩
  intro n _ Gn _ x part Pats A vol u hu hvolpos hvol t k3 k4 a2 a5 gamma beta M v
    ht ha2 ha5 hM hv hmass1 hcard hpart hk3 hk4 hb3 hb4 hthreshold hbad hfib href
    hloss hgamma hsize hmass
  obtain ⟨Pk, hPk⟩ := hgate n Gn x part Pats A vol u hu hvolpos hvol t k3 k4 a2
    a5 gamma ht ha2 ha5 hmass1 hcard hpart hk3 hk4 hb3 hb4 hthreshold hgamma hsize
    hmass
  refine ⟨Pk, ?_⟩
  have hvalue := cleanedPacking_value_ge_of_removal_bounds x part Pats A vol u hu
    hvolpos hvol hM hv hcard hbad hfib href hloss
  have hcast : (((1 - u - v) * (∑ H ∈ Pats, patternGain H * psiT x part H) : ℚ) : ℝ)
      ≤ (((cleanedPacking x part Pats A vol u hu hvolpos hvol).value : ℚ) : ℝ) := by
    exact_mod_cast hvalue
  linarith

/-- End-to-end mass comparison using the physical `t²` scale.  This is the
dimensionally valid replacement for the earlier theorem with `psiT ≤ 1`. -/
theorem exists_packing_mass_loss_le_of_cleanedSpread_physicalScale
    (zeta : ℝ) (hzeta : 0 < zeta) (hzeta1 : zeta ≤ 1) :
    ∃ gam : ℝ, 0 < gam ∧ ∃ Cst : ℝ, 0 < Cst ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (n : ℕ) [NeZero n] (Gn : SimpleGraph (Fin n)) [DecidableRel Gn.Adj]
        (x : FracPacking Gn) (part : Fin n → P) (Pats : Finset (Finset P))
        (A : Finset P → Finset P → ℚ) (vol : Finset P → ℚ)
        (u : ℚ) (hu : 0 ≤ u)
        (hvolpos : ∀ H ∈ Pats, 0 < vol H)
        (hvol : ∀ H ∈ Pats, ∀ f : Sym2 (Fin n),
          A H (partsOf part f) * densT Gn part f ≤ vol H)
        (t : ℕ) (k3 k4 a2 a5 gamma beta M v : ℚ),
        1 ≤ t → 0 < a2 → 0 < a5 → 0 ≤ M → 0 ≤ v →
        (∀ H ∈ Pats, H.card = 3 ∨ H.card = 4) →
        (∀ H ∈ Pats, ∀ p ∈ H,
          (univ.filter (fun w => part w = p)).card ≤ t) →
        ((Pats.filter (fun H => H.card = 3)).card : ℚ) ≤ k3 →
        ((Pats.filter (fun H => ¬ H.card = 3)).card : ℚ) ≤ k4 →
        (∀ H ∈ Pats, H.card = 3 →
          a2 * (t : ℚ) ^ 2 * (t : ℚ) ≤ (1 + u) * vol H) →
        (∀ H ∈ Pats, H.card = 4 →
          a5 * (t : ℚ) ^ 2 * (t : ℚ) ^ 2 ≤ (1 + u) * vol H) →
        k3 * a5 + k4 * a2 ≤ gamma * a2 * a5 * (t : ℚ) →
        (∀ H ∈ Pats, ∀ pq ∈ H.powersetCard 2,
          ((badRoots Gn part A u H pq).card : ℚ) ≤ beta) →
        (∀ H ∈ Pats, ∀ pq : Finset P, ∀ e : Sym2 (Fin n),
          ((fiber (profileFiber Gn part H) (rootEdge part pq) e).card : ℚ) ≤ M) →
        (∀ H ∈ Pats, vol H ≤ ((profileFiber Gn part H).card : ℚ)) →
        (∀ H ∈ Pats, ((H.card.choose 2 : ℕ) : ℚ) * (beta * M) ≤ v * vol H) →
        (gamma : ℝ) ≤ gam →
        12 + 10 * D ≤ zeta * (n : ℝ) ^ 2 →
        Cst ≤ triangleMass (cleanedPacking x part Pats A vol u hu hvolpos hvol) →
        ∃ Pk : Packing Gn,
          (((1 - u - v) * (∑ H ∈ Pats, patternGain H * psiT x part H) : ℚ) : ℝ)
            - (Pk.gain : ℝ) ≤ zeta * (n : ℝ) ^ 2 := by
  obtain ⟨gam, hgam, Cst, hCst, D, hD, hgate⟩ :=
    exists_packing_loss_le_of_cleanedSpread_physicalScale (P := P) zeta hzeta hzeta1
  refine ⟨gam, hgam, Cst, hCst, D, hD, ?_⟩
  intro n _ Gn _ x part Pats A vol u hu hvolpos hvol t k3 k4 a2 a5 gamma beta M v
    ht ha2 ha5 hM hv hcard hpart hk3 hk4 hb3 hb4 hthreshold hbad hfib
    href hloss hgamma hsize hmass
  have hserved : ∀ H ∈ Pats, ∃ e : Sym2 (Fin n), H ∈ servingT part e := by
    intro H hH
    have hposQ : (0 : ℚ) < ((profileFiber Gn part H).card : ℚ) :=
      lt_of_lt_of_le (hvolpos H hH) (href H hH)
    have hpos : 0 < (profileFiber Gn part H).card := by exact_mod_cast hposQ
    obtain ⟨K, hK⟩ := Finset.card_pos.1 hpos
    have hitem : IsItem Gn K := mem_items.1 (mem_profileFiber.1 hK).1
    have hpairs : (pairs K).Nonempty := by
      rw [← Finset.card_pos, card_pairs]
      rcases hitem.2 with h3 | h4
      · simp [h3]
      · rw [h4]
        decide
    obtain ⟨e, he⟩ := hpairs
    exact ⟨e, serving_of_mem_profileFiber hK he⟩
  obtain ⟨Pk, hPk⟩ := hgate n Gn x part Pats A vol u hu hvolpos hvol t k3 k4 a2
    a5 gamma ht ha2 ha5 hserved hcard hpart hk3 hk4 hb3 hb4 hthreshold hgamma
    hsize hmass
  refine ⟨Pk, ?_⟩
  have hvalue := cleanedPacking_value_ge_of_removal_bounds x part Pats A vol u hu
    hvolpos hvol hM hv hcard hbad hfib href hloss
  have hcast : (((1 - u - v) * (∑ H ∈ Pats, patternGain H * psiT x part H) : ℚ) : ℝ)
      ≤ (((cleanedPacking x part Pats A vol u hu hvolpos hvol).value : ℚ) : ℝ) := by
    exact_mod_cast hvalue
  linarith

/-- End-to-end physical-scale comparison with the cleanup retention supplied
directly.  This is the interface used by the graph adapter: the `K₃` and `K₄`
families have different natural fibre scales, so forcing both through one
common pair `(beta, M)` would introduce a spurious factor of `t` in the
triangle branch. -/
theorem exists_packing_mass_loss_le_of_cleanedSpread_physicalScale_of_clean
    (zeta : ℝ) (hzeta : 0 < zeta) (hzeta1 : zeta ≤ 1) :
    ∃ gam : ℝ, 0 < gam ∧ ∃ Cst : ℝ, 0 < Cst ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (n : ℕ) [NeZero n] (Gn : SimpleGraph (Fin n)) [DecidableRel Gn.Adj]
        (x : FracPacking Gn) (part : Fin n → P) (Pats : Finset (Finset P))
        (A : Finset P → Finset P → ℚ) (vol : Finset P → ℚ)
        (u : ℚ) (hu : 0 ≤ u)
        (hvolpos : ∀ H ∈ Pats, 0 < vol H)
        (hvol : ∀ H ∈ Pats, ∀ f : Sym2 (Fin n),
          A H (partsOf part f) * densT Gn part f ≤ vol H)
        (t : ℕ) (k3 k4 a2 a5 gamma v : ℚ),
        1 ≤ t → 0 < a2 → 0 < a5 → 0 ≤ v →
        (∀ H ∈ Pats, H.card = 3 ∨ H.card = 4) →
        (∀ H ∈ Pats, ∀ p ∈ H,
          (univ.filter (fun w => part w = p)).card ≤ t) →
        ((Pats.filter (fun H => H.card = 3)).card : ℚ) ≤ k3 →
        ((Pats.filter (fun H => ¬ H.card = 3)).card : ℚ) ≤ k4 →
        (∀ H ∈ Pats, H.card = 3 →
          a2 * (t : ℚ) ^ 2 * (t : ℚ) ≤ (1 + u) * vol H) →
        (∀ H ∈ Pats, H.card = 4 →
          a5 * (t : ℚ) ^ 2 * (t : ℚ) ^ 2 ≤ (1 + u) * vol H) →
        k3 * a5 + k4 * a2 ≤ gamma * a2 * a5 * (t : ℚ) →
        (∀ H ∈ Pats, vol H ≤ ((profileFiber Gn part H).card : ℚ)) →
        (∀ H ∈ Pats,
          (1 - v) * vol H ≤ ((cleanFiber Gn part A u H).card : ℚ)) →
        (gamma : ℝ) ≤ gam →
        12 + 10 * D ≤ zeta * (n : ℝ) ^ 2 →
        Cst ≤ triangleMass (cleanedPacking x part Pats A vol u hu hvolpos hvol) →
        ∃ Pk : Packing Gn,
          (((1 - u - v) * (∑ H ∈ Pats, patternGain H * psiT x part H) : ℚ) : ℝ)
            - (Pk.gain : ℝ) ≤ zeta * (n : ℝ) ^ 2 := by
  obtain ⟨gam, hgam, Cst, hCst, D, hD, hgate⟩ :=
    exists_packing_loss_le_of_cleanedSpread_physicalScale (P := P) zeta hzeta hzeta1
  refine ⟨gam, hgam, Cst, hCst, D, hD, ?_⟩
  intro n _ Gn _ x part Pats A vol u hu hvolpos hvol t k3 k4 a2 a5 gamma v
    ht ha2 ha5 hv hcard hpart hk3 hk4 hb3 hb4 hthreshold href hclean hgamma hsize hmass
  have hserved : ∀ H ∈ Pats, ∃ e : Sym2 (Fin n), H ∈ servingT part e := by
    intro H hH
    have hposQ : (0 : ℚ) < ((profileFiber Gn part H).card : ℚ) :=
      lt_of_lt_of_le (hvolpos H hH) (href H hH)
    have hpos : 0 < (profileFiber Gn part H).card := by exact_mod_cast hposQ
    obtain ⟨K, hK⟩ := Finset.card_pos.1 hpos
    have hitem : IsItem Gn K := mem_items.1 (mem_profileFiber.1 hK).1
    have hpairs : (pairs K).Nonempty := by
      rw [← Finset.card_pos, card_pairs]
      rcases hitem.2 with h3 | h4
      · simp [h3]
      · rw [h4]
        decide
    obtain ⟨e, he⟩ := hpairs
    exact ⟨e, serving_of_mem_profileFiber hK he⟩
  obtain ⟨Pk, hPk⟩ := hgate n Gn x part Pats A vol u hu hvolpos hvol t k3 k4 a2
    a5 gamma ht ha2 ha5 hserved hcard hpart hk3 hk4 hb3 hb4 hthreshold hgamma
    hsize hmass
  refine ⟨Pk, ?_⟩
  have hvalue := cleanedPacking_value_ge x part Pats A vol u hu hvolpos hvol v hv
    hcard hclean
  have hcast : (((1 - u - v) * (∑ H ∈ Pats, patternGain H * psiT x part H) : ℚ) : ℝ)
      ≤ (((cleanedPacking x part Pats A vol u hu hvolpos hvol).value : ℚ) : ℝ) := by
    exact_mod_cast hvalue
  linarith

/-- **(C.4)** La rama complementaria: cuando la masa triangular del
empaquetamiento limpio es baja, el tapón `LowTriangleReduction.lowTriangle_target`
cierra el presupuesto en cuanto el brazo puro de `K₄` entrega su packing.  Ése es
el único adaptador genuino que sigue faltando; véase
`docs/RC01_REMAINING_ADAPTER.md`. -/
theorem lowTriangle_branch_of_cleanedSpread {n : ℕ} [NeZero n]
    {Gn : SimpleGraph (Fin n)} [DecidableRel Gn.Adj] (x : FracPacking Gn)
    (part : Fin n → P) (Pats : Finset (Finset P))
    (A : Finset P → Finset P → ℚ) (vol : Finset P → ℚ) (u : ℚ)
    (hu : 0 ≤ u) (hvolpos : ∀ H ∈ Pats, 0 < vol H)
    (hvol : ∀ H ∈ Pats, ∀ f : Sym2 (Fin n),
      A H (partsOf part f) * densT Gn part f ≤ vol H)
    {Pk : Packing Gn} {beta Cst eps : ℚ}
    (hbeta : 0 ≤ beta) (hbetaeps : beta ≤ (6 / 5) * eps)
    (hCst : 4 * Cst ≤ eps * (n : ℚ) ^ 2)
    (hlow : PaperIV.LowTriangleReduction.triMass
      (cleanedPacking x part Pats A vol u hu hvolpos hvol) ≤ Cst)
    (hPk : (1 - beta) * (PaperIV.LowTriangleReduction.restrictToK4
        (cleanedPacking x part Pats A vol u hu hvolpos hvol)).value ≤ (Pk.gain : ℚ)) :
    (cleanedPacking x part Pats A vol u hu hvolpos hvol).value - (Pk.gain : ℚ)
      ≤ eps * (n : ℚ) ^ 2 :=
  PaperIV.LowTriangleReduction.lowTriangle_target hbeta hbetaeps hCst hlow hPk

end PaperIV.RC01CleanedGate
