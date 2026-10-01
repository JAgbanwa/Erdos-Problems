import FarExploration.CleanupLP
import PaperI.RationalFarkas

/-!
# El dual del LP de limpieza, y la alternativa de Farkas

La limpieza pedida por `CodegreeCleanupAt` es, para cada instancia, la **factibilidad** de un
programa lineal sobre `ℚ` con cuatro familias de restricciones:

| familia | restricción | multiplicador |
|---|---|---|
| positividad | `w S ≥ 0` | — |
| capacidad | `∑_{S ∋ r} w S ≤ 1` | `price r` |
| codegrado | `∑_{S ⊇ {r,s}} w S ≤ gam` (`r ≠ s`) | `pairPrice r s` |
| masa | `∑_{|S| = 3} w S ≥ Cst` | `massPrice` |
| valor | `∑_S gain S · w S ≥ valLB` | `valuePrice` |

`DualCertificate` es exactamente el certificado dual: precios no negativos por recurso y por
**par** de recursos que dominan, item a item, la combinación `massPrice·[rango 3] +
valuePrice·gain`, y cuyo coste total `∑ price + gam·∑ pairPrice` es menor que lo exigido
`massPrice·Cst + valuePrice·valLB`.

Se demuestran las dos direcciones:

* `not_feasible_of_dualCertificate` — dualidad débil: un certificado impide la limpieza;
* `dualCertificate_of_not_feasible` — completitud, por el Farkas racional de
  `PaperI.RationalFarkas` (eliminación de Fourier–Motzkin);
* `cleanupFeasible_iff` — la alternativa: o hay limpieza, o hay certificado.

`FarExploration.CleanupObstruction` exhibe una familia donde el certificado se realiza.
-/

namespace FarExploration.CleanupDuality

open Finset FarExploration.CleanupLP

variable {R : Type} [Fintype R] [DecidableEq R]

/-! ## 1. El primal -/

/-- **El LP de limpieza en una instancia**: existe una solución fraccional con codegrado `≤ gam`,
masa `≥ Cst` y valor `≥ valLB`. -/
def CleanupFeasible (H : ItemSystem R) (gam Cst valLB : ℚ) : Prop :=
  ∃ y : Frac H, (∀ r s : R, r ≠ s → y.codeg r s ≤ gam) ∧ Cst ≤ y.mass ∧ valLB ≤ y.value

/-! ## 2. El dual -/

/-- **Un certificado dual de imposibilidad de la limpieza.**  `price` son precios por recurso
(las capacidades), `pairPrice` precios por par de recursos (los codegrados), `massPrice` y
`valuePrice` los precios de las dos cotas inferiores. -/
structure DualCertificate (H : ItemSystem R) (gam Cst valLB : ℚ) where
  /-- Precio de la capacidad de cada recurso. -/
  price : R → ℚ
  /-- Precio de la restricción de codegrado de cada par de recursos. -/
  pairPrice : R → R → ℚ
  /-- Precio de la cota inferior de masa. -/
  massPrice : ℚ
  /-- Precio de la cota inferior de valor. -/
  valuePrice : ℚ
  price_nonneg : ∀ r, 0 ≤ price r
  pairPrice_nonneg : ∀ r s, 0 ≤ pairPrice r s
  /-- Sólo se ponen precios a pares de recursos **distintos**. -/
  pairPrice_diag : ∀ r, pairPrice r r = 0
  massPrice_nonneg : 0 ≤ massPrice
  valuePrice_nonneg : 0 ≤ valuePrice
  /-- Los precios dominan, item a item, lo que la limpieza promete. -/
  dominates : ∀ S ∈ H.supports,
    massPrice * (if S.card = 3 then 1 else 0) + valuePrice * gainOfSupport S
      ≤ (∑ r ∈ S, price r) + ∑ r ∈ S, ∑ s ∈ S, pairPrice r s
  /-- …y aun así cuestan menos de lo que la limpieza exige. -/
  strict : (∑ r : R, price r) + gam * ∑ r : R, ∑ s : R, pairPrice r s
      < massPrice * Cst + valuePrice * valLB

/-! ## 3. Dualidad débil -/

section Swaps

variable {H : ItemSystem R}

/-- Intercambio de sumas: los precios por recurso se cobran sobre las cargas. -/
lemma sum_weight_mul_sum_mem (y : Frac H) (f : R → ℚ) :
    ∑ S ∈ H.supports, y.w S * ∑ r ∈ S, f r
      = ∑ r : R, f r * ∑ S ∈ H.supports.filter (fun S => r ∈ S), y.w S := by
  classical
  have hstep : ∀ S ∈ H.supports, y.w S * ∑ r ∈ S, f r
      = ∑ r : R, (if r ∈ S then f r * y.w S else 0) := by
    intro S _
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases h : r ∈ S <;> simp [h]

/-- Intercambio de sumas: los precios por par se cobran sobre los codegrados. -/
lemma sum_weight_mul_sum_pair (y : Frac H) (q : R → R → ℚ) :
    ∑ S ∈ H.supports, y.w S * ∑ r ∈ S, ∑ s ∈ S, q r s
      = ∑ r : R, ∑ s : R, q r s * y.codeg r s := by
  classical
  have hstep : ∀ S ∈ H.supports, y.w S * ∑ r ∈ S, ∑ s ∈ S, q r s
      = ∑ r : R, ∑ s : R, (if r ∈ S ∧ s ∈ S then q r s * y.w S else 0) := by
    intro S _
    have hinner : ∀ r : R, ∑ s : R, (if r ∈ S ∧ s ∈ S then q r s * y.w S else 0)
        = (if r ∈ S then y.w S * ∑ s ∈ S, q r s else 0) := by
      intro r
      by_cases hr : r ∈ S
      · rw [if_pos hr]
        rw [Finset.mul_sum, ← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun s _ => by ring)
        ext s; simp [hr]
      · rw [if_neg hr]
        refine Finset.sum_eq_zero fun s _ => ?_
        rw [if_neg (by tauto)]
    rw [Finset.sum_congr rfl fun r _ => hinner r, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.mul_sum]
  rw [Finset.sum_congr rfl hstep]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Frac.codeg, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases h : r ∈ S ∧ s ∈ S <;> simp [h]

end Swaps

/-- **Dualidad débil.**  Un certificado dual impide la limpieza. -/
theorem not_feasible_of_dualCertificate {H : ItemSystem R} {gam Cst valLB : ℚ}
    (c : DualCertificate H gam Cst valLB) : ¬ CleanupFeasible H gam Cst valLB := by
  classical
  rintro ⟨y, hcod, hmass, hval⟩
  set T : ℚ := ∑ S ∈ H.supports,
      y.w S * ((∑ r ∈ S, c.price r) + ∑ r ∈ S, ∑ s ∈ S, c.pairPrice r s) with hT
  -- cota inferior de `T`
  have hlow : c.massPrice * Cst + c.valuePrice * valLB ≤ T := by
    have h1 : ∑ S ∈ H.supports,
        y.w S * (c.massPrice * (if S.card = 3 then 1 else 0)
          + c.valuePrice * gainOfSupport S) ≤ T := by
      refine Finset.sum_le_sum fun S hS => ?_
      exact mul_le_mul_of_nonneg_left (c.dominates S hS) (y.nonneg S)
    have hm' : c.massPrice * y.mass
        = ∑ S ∈ H.supports, (if S.card = 3 then c.massPrice * y.w S else 0) := by
      rw [Frac.mass, Finset.mul_sum, Finset.sum_filter]
    have hv' : c.valuePrice * y.value
        = ∑ S ∈ H.supports, c.valuePrice * (gainOfSupport S * y.w S) := by
      rw [Frac.value, Finset.mul_sum]
    have h2 : ∑ S ∈ H.supports, y.w S * (c.massPrice * (if S.card = 3 then 1 else 0)
          + c.valuePrice * gainOfSupport S)
        = c.massPrice * y.mass + c.valuePrice * y.value := by
      rw [hm', hv', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun S _ => ?_
      by_cases h : S.card = 3 <;> simp [h] <;> ring
    have h3 : c.massPrice * Cst ≤ c.massPrice * y.mass :=
      mul_le_mul_of_nonneg_left hmass c.massPrice_nonneg
    have h4 : c.valuePrice * valLB ≤ c.valuePrice * y.value :=
      mul_le_mul_of_nonneg_left hval c.valuePrice_nonneg
    rw [h2] at h1
    linarith
  -- cota superior de `T`
  have hhigh : T ≤ (∑ r : R, c.price r) + gam * ∑ r : R, ∑ s : R, c.pairPrice r s := by
    have hsplit : T = (∑ S ∈ H.supports, y.w S * ∑ r ∈ S, c.price r)
        + ∑ S ∈ H.supports, y.w S * ∑ r ∈ S, ∑ s ∈ S, c.pairPrice r s := by
      rw [hT, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun S _ => by ring
    have hA : (∑ S ∈ H.supports, y.w S * ∑ r ∈ S, c.price r) ≤ ∑ r : R, c.price r := by
      rw [sum_weight_mul_sum_mem y c.price]
      refine Finset.sum_le_sum fun r _ => ?_
      have := y.capacity r
      nlinarith [c.price_nonneg r, Finset.sum_nonneg (fun S (_ : S ∈ H.supports.filter
        (fun S => r ∈ S)) => y.nonneg S)]
    have hB : (∑ S ∈ H.supports, y.w S * ∑ r ∈ S, ∑ s ∈ S, c.pairPrice r s)
        ≤ gam * ∑ r : R, ∑ s : R, c.pairPrice r s := by
      rw [sum_weight_mul_sum_pair y c.pairPrice, Finset.mul_sum]
      refine Finset.sum_le_sum fun r _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      by_cases hrs : r = s
      · subst hrs
        rw [c.pairPrice_diag r]
        ring_nf
        simp
      · have := hcod r s hrs
        have hq := c.pairPrice_nonneg r s
        nlinarith
    rw [hsplit]
    linarith
  have := c.strict
  linarith

/-! ## 4. Completitud: la alternativa de Farkas -/

/-- Las filas del LP: positividad, capacidad, codegrado, masa y valor. -/
abbrev Row (R : Type) [Fintype R] [DecidableEq R] :=
  Finset R ⊕ R ⊕ (R × R) ⊕ Bool

section Farkas

variable (H : ItemSystem R) (gam Cst valLB : ℚ)

/-- La matriz del LP. -/
noncomputable def mat : Row R → Finset R → ℚ
  | Sum.inl S₀, S => if S = S₀ then -1 else 0
  | Sum.inr (Sum.inl r), S => if S ∈ H.supports ∧ r ∈ S then 1 else 0
  | Sum.inr (Sum.inr (Sum.inl (r, s))), S =>
      if r ≠ s ∧ S ∈ H.supports ∧ r ∈ S ∧ s ∈ S then 1 else 0
  | Sum.inr (Sum.inr (Sum.inr false)), S => if S ∈ H.supports ∧ S.card = 3 then -1 else 0
  | Sum.inr (Sum.inr (Sum.inr true)), S => if S ∈ H.supports then -gainOfSupport S else 0

/-- El lado derecho del LP. -/
noncomputable def rhs : Row R → ℚ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl (r, s))) => if r ≠ s then gam else 0
  | Sum.inr (Sum.inr (Sum.inr false)) => -Cst
  | Sum.inr (Sum.inr (Sum.inr true)) => -valLB

variable {H gam Cst valLB}

/-- Suma sobre todos los subconjuntos con el indicador de pertenencia al sistema. -/
lemma sum_univ_ite (P : Finset R → Prop) [DecidablePred P] (f : Finset R → ℚ) :
    ∑ S : Finset R, (if S ∈ H.supports ∧ P S then f S else 0)
      = ∑ S ∈ H.supports.filter P, f S := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext S
  simp

/-- Suma sobre todos los subconjuntos, restringida al sistema. -/
lemma sum_univ_ite_mem (f : Finset R → ℚ) :
    ∑ S : Finset R, (if S ∈ H.supports then f S else 0) = ∑ S ∈ H.supports, f S := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext S
  simp

/-- **Completitud del dual.**  Si no hay limpieza, hay certificado. -/
theorem dualCertificate_of_not_feasible (h : ¬ CleanupFeasible H gam Cst valLB) :
    Nonempty (DualCertificate H gam Cst valLB) := by
  classical
  rcases PaperI.RationalFarkas.farkas (mat H) (rhs gam Cst valLB) with ⟨x, hx⟩ | hcert
  · -- la alternativa primal produce una limpieza, contra la hipótesis
    exfalso
    have hnonneg : ∀ S : Finset R, 0 ≤ (if S ∈ H.supports then x S else 0) := by
      intro S
      by_cases hS : S ∈ H.supports
      · rw [if_pos hS]
        have hrow := hx (Sum.inl S)
        have heval : ∑ T : Finset R, mat H (Sum.inl S) T * x T = - x S := by
          rw [Finset.sum_eq_single S]
          · simp [mat]
          · intro T _ hTS
            simp [mat, hTS]
          · intro hS'
            exact absurd (Finset.mem_univ S) hS'
        rw [heval] at hrow
        simp only [rhs] at hrow
        linarith
      · rw [if_neg hS]
    have hfiltereq : ∀ (P : Finset R → Prop) [DecidablePred P],
        ∑ T ∈ H.supports.filter P, (if T ∈ H.supports then x T else 0)
          = ∑ T ∈ H.supports.filter P, x T := by
      intro P _
      refine Finset.sum_congr rfl fun T hT => ?_
      rw [if_pos (Finset.mem_filter.1 hT).1]
    have hcap : ∀ r : R, ∑ S ∈ H.supports.filter (fun S => r ∈ S),
        (if S ∈ H.supports then x S else 0) ≤ 1 := by
      intro r
      have hrow := hx (Sum.inr (Sum.inl r))
      have heval : ∑ T : Finset R, mat H (Sum.inr (Sum.inl r)) T * x T
          = ∑ T ∈ H.supports.filter (fun T => r ∈ T), x T := by
        rw [← sum_univ_ite (H := H) (fun T => r ∈ T) x]
        refine Finset.sum_congr rfl fun T _ => ?_
        by_cases hT : T ∈ H.supports ∧ r ∈ T <;> simp [mat, hT]
      rw [heval] at hrow
      rw [hfiltereq (fun T => r ∈ T)]
      simpa [rhs] using hrow
    refine h ⟨⟨fun S => if S ∈ H.supports then x S else 0, hnonneg, hcap⟩, ?_, ?_, ?_⟩
    · intro r s hrs
      have hrow := hx (Sum.inr (Sum.inr (Sum.inl (r, s))))
      have heval : ∑ T : Finset R, mat H (Sum.inr (Sum.inr (Sum.inl (r, s)))) T * x T
          = ∑ T ∈ H.supports.filter (fun T => r ∈ T ∧ s ∈ T), x T := by
        rw [← sum_univ_ite (H := H) (fun T => r ∈ T ∧ s ∈ T) x]
        refine Finset.sum_congr rfl fun T _ => ?_
        by_cases hT : T ∈ H.supports ∧ r ∈ T ∧ s ∈ T <;> simp [mat, hrs, hT]
      have hrhs : rhs gam Cst valLB (Sum.inr (Sum.inr (Sum.inl (r, s)))) = gam := by
        simp [rhs, hrs]
      rw [heval, hrhs] at hrow
      show ∑ T ∈ H.supports.filter (fun T => r ∈ T ∧ s ∈ T),
          (if T ∈ H.supports then x T else 0) ≤ gam
      rw [hfiltereq (fun T => r ∈ T ∧ s ∈ T)]
      exact hrow
    · have hrow := hx (Sum.inr (Sum.inr (Sum.inr false)))
      have heval : ∑ T : Finset R, mat H (Sum.inr (Sum.inr (Sum.inr false))) T * x T
          = - ∑ T ∈ H.supports.filter (fun T => T.card = 3), x T := by
        rw [← Finset.sum_neg_distrib,
          ← sum_univ_ite (H := H) (fun T => T.card = 3) (fun T => - x T)]
        refine Finset.sum_congr rfl fun T _ => ?_
        by_cases hT : T ∈ H.supports ∧ T.card = 3 <;> simp [mat, hT]
      rw [heval] at hrow
      simp only [rhs] at hrow
      show Cst ≤ ∑ T ∈ H.supports.filter (fun T => T.card = 3),
          (if T ∈ H.supports then x T else 0)
      rw [hfiltereq (fun T => T.card = 3)]
      linarith
    · have hrow := hx (Sum.inr (Sum.inr (Sum.inr true)))
      have heval : ∑ T : Finset R, mat H (Sum.inr (Sum.inr (Sum.inr true))) T * x T
          = - ∑ T ∈ H.supports, gainOfSupport T * x T := by
        rw [← Finset.sum_neg_distrib,
          ← sum_univ_ite_mem (H := H) (fun T => - (gainOfSupport T * x T))]
        refine Finset.sum_congr rfl fun T _ => ?_
        by_cases hT : T ∈ H.supports <;> simp [mat, hT]
      rw [heval] at hrow
      simp only [rhs] at hrow
      have hvaleq : ∑ T ∈ H.supports, gainOfSupport T * (if T ∈ H.supports then x T else 0)
          = ∑ T ∈ H.supports, gainOfSupport T * x T := by
        refine Finset.sum_congr rfl fun T hT => ?_
        rw [if_pos hT]
      show valLB ≤ ∑ T ∈ H.supports, gainOfSupport T * (if T ∈ H.supports then x T else 0)
      rw [hvaleq]
      linarith
  · -- la alternativa dual es el certificado
    obtain ⟨u, hu0, huA, hub⟩ := hcert
    refine ⟨{ price := fun r => u (Sum.inr (Sum.inl r))
              pairPrice := fun r s => if r = s then 0 else u (Sum.inr (Sum.inr (Sum.inl (r, s))))
              massPrice := u (Sum.inr (Sum.inr (Sum.inr false)))
              valuePrice := u (Sum.inr (Sum.inr (Sum.inr true)))
              price_nonneg := fun r => hu0 _
              pairPrice_nonneg := ?_
              pairPrice_diag := ?_
              massPrice_nonneg := hu0 _
              valuePrice_nonneg := hu0 _
              dominates := ?_
              strict := ?_ }⟩
    · intro r s
      by_cases hrs : r = s <;> simp [hrs, hu0]
    · intro r; simp
    · intro S hS
      have hcol := huA S
      -- se desarrolla la columna `S` de la ecuación dual
      have hsplit : ∑ i : Row R, u i * mat H i S
          = (∑ S₀ : Finset R, u (Sum.inl S₀) * mat H (Sum.inl S₀) S)
            + ((∑ r : R, u (Sum.inr (Sum.inl r)) * mat H (Sum.inr (Sum.inl r)) S)
              + ((∑ p : R × R, u (Sum.inr (Sum.inr (Sum.inl p)))
                    * mat H (Sum.inr (Sum.inr (Sum.inl p))) S)
                + ∑ b : Bool, u (Sum.inr (Sum.inr (Sum.inr b)))
                    * mat H (Sum.inr (Sum.inr (Sum.inr b))) S)) := by
        rw [Fintype.sum_sum_type]
        congr 1
        rw [Fintype.sum_sum_type]
        congr 1
        rw [Fintype.sum_sum_type]
      have hnn : ∑ S₀ : Finset R, u (Sum.inl S₀) * mat H (Sum.inl S₀) S
          = - u (Sum.inl S) := by
        rw [Finset.sum_eq_single S]
        · simp [mat]
        · intro T _ hTS
          simp [mat, Ne.symm hTS]
        · intro hS'
          exact absurd (Finset.mem_univ S) hS'
      have hcap : ∑ r : R, u (Sum.inr (Sum.inl r)) * mat H (Sum.inr (Sum.inl r)) S
          = ∑ r ∈ S, u (Sum.inr (Sum.inl r)) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r => r ∈ S)]
        have h1 : ∑ r ∈ Finset.univ.filter (fun r => r ∈ S),
              u (Sum.inr (Sum.inl r)) * mat H (Sum.inr (Sum.inl r)) S
            = ∑ r ∈ S, u (Sum.inr (Sum.inl r)) := by
          have hset : Finset.univ.filter (fun r => r ∈ S) = S := by ext r; simp
          rw [hset]
          refine Finset.sum_congr rfl fun r hr => ?_
          simp [mat, hS, hr]
        have h2 : ∑ r ∈ Finset.univ.filter (fun r => ¬ r ∈ S),
              u (Sum.inr (Sum.inl r)) * mat H (Sum.inr (Sum.inl r)) S = 0 := by
          refine Finset.sum_eq_zero fun r hr => ?_
          have : r ∉ S := (Finset.mem_filter.1 hr).2
          simp [mat, this]
        rw [h1, h2, add_zero]
      have hpair : ∑ p : R × R, u (Sum.inr (Sum.inr (Sum.inl p)))
            * mat H (Sum.inr (Sum.inr (Sum.inl p))) S
          = ∑ r ∈ S, ∑ s ∈ S, (if r = s then 0
              else u (Sum.inr (Sum.inr (Sum.inl (r, s))))) := by
        rw [Fintype.sum_prod_type]
        have hstep : ∀ r : R, ∑ s : R, u (Sum.inr (Sum.inr (Sum.inl (r, s))))
              * mat H (Sum.inr (Sum.inr (Sum.inl (r, s)))) S
            = if r ∈ S then ∑ s ∈ S, (if r = s then 0
                else u (Sum.inr (Sum.inr (Sum.inl (r, s))))) else 0 := by
          intro r
          by_cases hr : r ∈ S
          · rw [if_pos hr, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s => s ∈ S)]
            have hset : Finset.univ.filter (fun s => s ∈ S) = S := by ext s; simp
            have h2 : ∑ s ∈ Finset.univ.filter (fun s => ¬ s ∈ S),
                  u (Sum.inr (Sum.inr (Sum.inl (r, s))))
                    * mat H (Sum.inr (Sum.inr (Sum.inl (r, s)))) S = 0 := by
              refine Finset.sum_eq_zero fun s hs => ?_
              have : s ∉ S := (Finset.mem_filter.1 hs).2
              simp [mat, this]
            rw [hset, h2, add_zero]
            refine Finset.sum_congr rfl fun s hs => ?_
            by_cases hrs : r = s
            · simp [mat, hrs]
            · simp [mat, hrs, hr, hs, hS]
          · rw [if_neg hr]
            refine Finset.sum_eq_zero fun s _ => ?_
            simp [mat, hr]
        rw [Finset.sum_congr rfl fun r _ => hstep r, Finset.sum_ite_mem, Finset.univ_inter]
      have hmv : ∑ b : Bool, u (Sum.inr (Sum.inr (Sum.inr b)))
            * mat H (Sum.inr (Sum.inr (Sum.inr b))) S
          = - (u (Sum.inr (Sum.inr (Sum.inr false))) * (if S.card = 3 then 1 else 0))
            - u (Sum.inr (Sum.inr (Sum.inr true))) * gainOfSupport S := by
        rw [Fintype.sum_bool]
        by_cases h3 : S.card = 3 <;>
          first
            | (simp [mat, hS, h3]; ring)
            | simp [mat, hS, h3]
      rw [hsplit, hnn, hcap, hpair, hmv] at hcol
      have hu : 0 ≤ u (Sum.inl S) := hu0 _
      linarith
    · -- el coste total del certificado
      have hsplit : ∑ i : Row R, u i * rhs gam Cst valLB i
          = (∑ S₀ : Finset R, u (Sum.inl S₀) * rhs gam Cst valLB (Sum.inl S₀ : Row R))
            + ((∑ r : R, u (Sum.inr (Sum.inl r))
                  * rhs gam Cst valLB (Sum.inr (Sum.inl r) : Row R))
              + ((∑ p : R × R, u (Sum.inr (Sum.inr (Sum.inl p)))
                    * rhs gam Cst valLB (Sum.inr (Sum.inr (Sum.inl p)) : Row R))
                + ∑ b : Bool, u (Sum.inr (Sum.inr (Sum.inr b)))
                    * rhs gam Cst valLB (Sum.inr (Sum.inr (Sum.inr b)) : Row R))) := by
        rw [Fintype.sum_sum_type]
        congr 1
        rw [Fintype.sum_sum_type]
        congr 1
        rw [Fintype.sum_sum_type]
      have hnn : ∑ S₀ : Finset R, u (Sum.inl S₀)
          * rhs gam Cst valLB (Sum.inl S₀ : Row R) = 0 := by
        refine Finset.sum_eq_zero fun S₀ _ => ?_
        simp [rhs]
      have hcap : ∑ r : R, u (Sum.inr (Sum.inl r))
            * rhs gam Cst valLB (Sum.inr (Sum.inl r) : Row R)
          = ∑ r : R, u (Sum.inr (Sum.inl r)) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        simp [rhs]
      have hpair : ∑ p : R × R, u (Sum.inr (Sum.inr (Sum.inl p)))
            * rhs gam Cst valLB (Sum.inr (Sum.inr (Sum.inl p)) : Row R)
          = gam * ∑ r : R, ∑ s : R, (if r = s then 0
              else u (Sum.inr (Sum.inr (Sum.inl (r, s))))) := by
        rw [Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        by_cases hrs : r = s <;>
          first
            | (simp [rhs, hrs]; ring)
            | simp [rhs, hrs]
      have hmv : ∑ b : Bool, u (Sum.inr (Sum.inr (Sum.inr b)))
            * rhs gam Cst valLB (Sum.inr (Sum.inr (Sum.inr b)) : Row R)
          = - (u (Sum.inr (Sum.inr (Sum.inr false))) * Cst)
            - u (Sum.inr (Sum.inr (Sum.inr true))) * valLB := by
        rw [Fintype.sum_bool]
        simp [rhs]
        ring
      rw [hsplit, hnn, hcap, hpair, hmv] at hub
      linarith

/-- **La alternativa.**  O hay limpieza, o hay certificado dual; nunca las dos. -/
theorem cleanupFeasible_iff :
    CleanupFeasible H gam Cst valLB ↔ IsEmpty (DualCertificate H gam Cst valLB) := by
  constructor
  · intro hfeas
    refine ⟨fun c => ?_⟩
    exact not_feasible_of_dualCertificate c hfeas
  · intro hempty
    by_contra hfeas
    obtain ⟨c⟩ := dualCertificate_of_not_feasible hfeas
    exact hempty.elim c

end Farkas

end FarExploration.CleanupDuality
