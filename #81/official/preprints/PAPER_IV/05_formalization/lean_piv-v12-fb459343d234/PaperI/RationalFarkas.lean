import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.Positivity

/-!
# Lema de Farkas sobre los racionales, por eliminacion de Fourier--Motzkin

Version **racional** del lema de Farkas. Se demuestra por induccion en el numero de variables,
eliminando la ultima columna y repartiendo las filas segun el signo de su coeficiente; los pesos
de cada fila nueva quedan registrados, de modo que el certificado dual del sistema reducido se
levanta explicitamente al original.

Trabajar sobre `Q` y no sobre `R` es esencial para este desarrollo: el valor optimo que consume el
modelo mixto tiene que ser un numero racional. El resultado de dualidad fuerte en forma
cubrimiento/empaquetamiento es de Paper I, donde se prueba sobre `R` con conos cerrados y
Caratheodory conico; la demostracion de aqui es independiente de aquella.

**Procedencia.**  El *resultado* --dualidad fuerte finita en forma cubrimiento/empaquetamiento--
es de Paper I.  La *demostracion* de este fichero no lo es: Paper I la establece sobre `R`
(`EuclideanSpace`, conos simpliciales cerrados, Caratheodory conico), y el modelo mixto de
Paper IV necesita que el valor optimo sea **racional**.  Por eso aqui se reprueba sobre `Q`
por eliminacion de Fourier--Motzkin.  Se cita Paper I por el resultado; la prueba racional es
material nuevo de Paper IV.
-/


/-!
# A rational Farkas lemma by Fourier--Motzkin elimination

This file proves, from scratch and over the rationals, the alternative

```
(∃ x, A x ≤ b)   or   (∃ y ≥ 0, yᵀ A = 0 ∧ yᵀ b < 0)
```

for a finite system of linear inequalities with rational data.  The proof is
Fourier--Motzkin elimination: one variable is removed by combining every row
with a positive coefficient with every row with a negative coefficient, and the
induction hypothesis is applied to the smaller system.  Both alternatives
transfer: a solution of the smaller system extends by choosing the eliminated
coordinate between the induced bounds, and a Farkas certificate of the smaller
system pulls back because every new row is an explicit nonnegative combination
of old rows.

Working over `ℚ` (rather than over `ℝ` with a separation theorem) is essential
downstream: the mixed packing/covering optimum has to be a *rational* number.
-/

open scoped BigOperators
open Finset

namespace PaperI.RationalFarkas

variable {ι : Type} [Fintype ι] {n : ℕ}

/-- The coefficient of the last variable in row `i`. -/
def colLast (A : ι → Fin (n + 1) → ℚ) (i : ι) : ℚ := A i (Fin.last n)

/-- Row `i` with the last variable removed. -/
def restrict (A : ι → Fin (n + 1) → ℚ) (i : ι) (j : Fin n) : ℚ := A i j.castSucc

/-- Rows whose last coefficient is positive: upper bounds for the last
variable. -/
abbrev Pos (A : ι → Fin (n + 1) → ℚ) := {i : ι // 0 < colLast A i}

/-- Rows whose last coefficient is negative: lower bounds. -/
abbrev Neg (A : ι → Fin (n + 1) → ℚ) := {i : ι // colLast A i < 0}

/-- Rows not involving the last variable. -/
abbrev Zer (A : ι → Fin (n + 1) → ℚ) := {i : ι // colLast A i = 0}

/-- The index type of the Fourier--Motzkin eliminated system. -/
abbrev Elim (A : ι → Fin (n + 1) → ℚ) := (Pos A × Neg A) ⊕ Zer A

/-- The matrix of the eliminated system. -/
def elimA (A : ι → Fin (n + 1) → ℚ) : Elim A → Fin n → ℚ
  | Sum.inl (p, q) => fun j =>
      (-(colLast A q.1)) * restrict A p.1 j + colLast A p.1 * restrict A q.1 j
  | Sum.inr z => restrict A z.1

/-- The right-hand side of the eliminated system. -/
def elimB (A : ι → Fin (n + 1) → ℚ) (b : ι → ℚ) : Elim A → ℚ
  | Sum.inl (p, q) => (-(colLast A q.1)) * b p.1 + colLast A p.1 * b q.1
  | Sum.inr z => b z.1

/-- Each row of the eliminated system is a nonnegative combination of rows of
the original system; `elimWeight` records the coefficients. -/
def elimWeight [DecidableEq ι] (A : ι → Fin (n + 1) → ℚ) : Elim A → ι → ℚ
  | Sum.inl (p, q) => fun i =>
      (if i = (p : ι) then -(colLast A q.1) else 0) +
        (if i = (q : ι) then colLast A p.1 else 0)
  | Sum.inr z => fun i => if i = (z : ι) then 1 else 0

omit [Fintype ι] in
theorem elimWeight_nonneg [DecidableEq ι] (A : ι → Fin (n + 1) → ℚ)
    (i' : Elim A) (i : ι) : 0 ≤ elimWeight A i' i := by
  cases i' with
  | inl pq =>
      obtain ⟨p, q⟩ := pq
      have hp : 0 < colLast A p.1 := p.2
      have hq : colLast A q.1 < 0 := q.2
      have h1 : (0 : ℚ) ≤ if i = (p : ι) then -(colLast A q.1) else 0 := by
        split <;> linarith
      have h2 : (0 : ℚ) ≤ if i = (q : ι) then colLast A p.1 else 0 := by
        split <;> linarith
      simpa [elimWeight] using add_nonneg h1 h2
  | inr z => by_cases h : i = (z : ι) <;> simp [elimWeight, h]

/-- Combining any function along the weights of a row of the eliminated
system. -/
theorem elimWeight_sum_inl [DecidableEq ι] (A : ι → Fin (n + 1) → ℚ)
    (p : Pos A) (q : Neg A) (f : ι → ℚ) :
    ∑ i, elimWeight A (Sum.inl (p, q)) i * f i =
      (-(colLast A q.1)) * f p.1 + colLast A p.1 * f q.1 := by
  classical
  have : ∀ i : ι, elimWeight A (Sum.inl (p, q)) i * f i =
      (if i = (p : ι) then -(colLast A q.1) * f i else 0) +
        (if i = (q : ι) then colLast A p.1 * f i else 0) := by
    intro i
    by_cases h1 : i = (p : ι) <;> by_cases h2 : i = (q : ι) <;>
      simp [elimWeight, h1, h2, add_mul]
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib]
  simp

theorem elimWeight_sum_inr [DecidableEq ι] (A : ι → Fin (n + 1) → ℚ)
    (z : Zer A) (f : ι → ℚ) :
    ∑ i, elimWeight A (Sum.inr z) i * f i = f z.1 := by
  classical
  have : ∀ i : ι, elimWeight A (Sum.inr z) i * f i =
      if i = (z : ι) then f i else 0 := by
    intro i; by_cases h : i = (z : ι) <;> simp [elimWeight, h]
  rw [Finset.sum_congr rfl fun i _ => this i]
  simp

/-- The weights of a row of the eliminated system annihilate the last
column. -/
theorem elimWeight_last [DecidableEq ι] (A : ι → Fin (n + 1) → ℚ)
    (i' : Elim A) : ∑ i, elimWeight A i' i * colLast A i = 0 := by
  cases i' with
  | inl pq =>
      obtain ⟨p, q⟩ := pq
      rw [elimWeight_sum_inl]
      ring
  | inr z =>
      rw [elimWeight_sum_inr]
      exact z.2

/-- The weights of a row of the eliminated system reproduce its coefficients. -/
theorem elimWeight_col [DecidableEq ι] (A : ι → Fin (n + 1) → ℚ)
    (i' : Elim A) (j : Fin n) :
    ∑ i, elimWeight A i' i * A i j.castSucc = elimA A i' j := by
  cases i' with
  | inl pq =>
      obtain ⟨p, q⟩ := pq
      rw [elimWeight_sum_inl]
      rfl
  | inr z =>
      rw [elimWeight_sum_inr]
      rfl

/-- The weights of a row of the eliminated system reproduce its right-hand
side. -/
theorem elimWeight_rhs [DecidableEq ι] (A : ι → Fin (n + 1) → ℚ) (b : ι → ℚ)
    (i' : Elim A) : ∑ i, elimWeight A i' i * b i = elimB A b i' := by
  cases i' with
  | inl pq =>
      obtain ⟨p, q⟩ := pq
      rw [elimWeight_sum_inl]
      rfl
  | inr z =>
      rw [elimWeight_sum_inr]
      rfl

/-- Exchanging the two summations in a weighted combination. -/
theorem sum_swap_weights {α β : Type} [Fintype α] [Fintype β] (u : β → ℚ)
    (w : β → α → ℚ) (f : α → ℚ) :
    ∑ i : α, (∑ i' : β, u i' * w i' i) * f i =
      ∑ i' : β, u i' * ∑ i : α, w i' i * f i := by
  calc ∑ i : α, (∑ i' : β, u i' * w i' i) * f i
      = ∑ i : α, ∑ i' : β, u i' * (w i' i * f i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i' _ => by ring
    _ = ∑ i' : β, ∑ i : α, u i' * (w i' i * f i) := Finset.sum_comm
    _ = ∑ i' : β, u i' * ∑ i : α, w i' i * f i :=
        Finset.sum_congr rfl fun i' _ => (Finset.mul_sum _ _ _).symm

/-- **Farkas' lemma over `ℚ`, variables indexed by `Fin n`.**  Either the
system `A x ≤ b` has a rational solution, or it has a nonnegative rational
certificate of infeasibility. -/
theorem farkas_fin : ∀ (n : ℕ) {ι : Type} [Fintype ι] (A : ι → Fin n → ℚ)
    (b : ι → ℚ),
      (∃ x : Fin n → ℚ, ∀ i, ∑ j, A i j * x j ≤ b i) ∨
      (∃ y : ι → ℚ, (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, y i * A i j = 0) ∧
        ∑ i, y i * b i < 0) := by
  intro n
  induction n with
  | zero =>
      intro ι _ A b
      classical
      by_cases h : ∀ i, 0 ≤ b i
      · exact Or.inl ⟨fun j => j.elim0, fun i => by simpa using h i⟩
      · push_neg at h
        obtain ⟨i0, hi0⟩ := h
        refine Or.inr ⟨fun i => if i = i0 then 1 else 0, ?_, fun j => j.elim0, ?_⟩
        · intro i
          dsimp only
          split <;> norm_num
        · simpa using hi0
  | succ n ih =>
      intro ι _ A b
      classical
      rcases ih (elimA A) (elimB A b) with ⟨x', hx'⟩ | ⟨y', hy0, hyA, hyb⟩
      · -- extend the solution by a value for the last coordinate
        left
        set s : ι → ℚ := fun i => b i - ∑ j, restrict A i j * x' j with hs
        have hkey : ∀ (p : Pos A) (q : Neg A),
            s q.1 / colLast A q.1 ≤ s p.1 / colLast A p.1 := by
          intro p q
          have hp : 0 < colLast A p.1 := p.2
          have hq : colLast A q.1 < 0 := q.2
          have hnq : (0 : ℚ) < -(colLast A q.1) := by linarith
          have hrow := hx' (Sum.inl (p, q))
          have hexp : ∑ j, elimA A (Sum.inl (p, q)) j * x' j =
              (-(colLast A q.1)) * (∑ j, restrict A p.1 j * x' j) +
                colLast A p.1 * (∑ j, restrict A q.1 j * x' j) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun j _ => ?_
            show ((-(colLast A q.1)) * restrict A p.1 j
                + colLast A p.1 * restrict A q.1 j) * x' j = _
            ring
          rw [hexp] at hrow
          have hb : elimB A b (Sum.inl (p, q)) =
              (-(colLast A q.1)) * b p.1 + colLast A p.1 * b q.1 := rfl
          rw [hb] at hrow
          have hcomb : 0 ≤ (-(colLast A q.1)) * s p.1 + colLast A p.1 * s q.1 := by
            simp only [hs]
            nlinarith [hrow]
          have e1 : s q.1 / colLast A q.1 = (-(s q.1)) / (-(colLast A q.1)) := by
            rw [neg_div_neg_eq]
          rw [e1, div_le_div_iff₀ hnq hp]
          nlinarith [hcomb]
        obtain ⟨t, htN, htP⟩ : ∃ t : ℚ,
            (∀ q : Neg A, s q.1 / colLast A q.1 ≤ t) ∧
            (∀ p : Pos A, t ≤ s p.1 / colLast A p.1) := by
          by_cases hN : Nonempty (Neg A)
          · haveI := hN
            refine ⟨Finset.univ.sup' Finset.univ_nonempty
              (fun q : Neg A => s q.1 / colLast A q.1), ?_, ?_⟩
            · intro q
              exact Finset.le_sup' (fun q : Neg A => s q.1 / colLast A q.1)
                (Finset.mem_univ q)
            · intro p
              exact Finset.sup'_le _ _ fun q _ => hkey p q
          · by_cases hP : Nonempty (Pos A)
            · haveI := hP
              refine ⟨Finset.univ.inf' Finset.univ_nonempty
                (fun p : Pos A => s p.1 / colLast A p.1), ?_, ?_⟩
              · intro q; exact absurd ⟨q⟩ hN
              · intro p
                exact Finset.inf'_le (fun p : Pos A => s p.1 / colLast A p.1)
                  (Finset.mem_univ p)
            · exact ⟨0, fun q => absurd ⟨q⟩ hN, fun p => absurd ⟨p⟩ hP⟩
        refine ⟨Fin.snoc x' t, fun i => ?_⟩
        have hsplit : ∑ j, A i j * (Fin.snoc x' t : Fin (n + 1) → ℚ) j =
            (∑ j : Fin n, restrict A i j * x' j) + colLast A i * t := by
          rw [Fin.sum_univ_castSucc]
          simp [restrict, colLast]
        rw [hsplit]
        rcases lt_trichotomy (colLast A i) 0 with hneg | hzero | hpos
        · have hle := htN ⟨i, hneg⟩
          have hmul : t * colLast A i ≤ (s i / colLast A i) * colLast A i :=
            mul_le_mul_of_nonpos_right hle hneg.le
          rw [div_mul_cancel₀ _ (ne_of_lt hneg)] at hmul
          have hfin : colLast A i * t ≤ s i := by linarith [hmul]
          simp only [hs] at hfin
          linarith
        · have hrow := hx' (Sum.inr ⟨i, hzero⟩)
          have hb : elimB A b (Sum.inr ⟨i, hzero⟩) = b i := rfl
          have hA : ∀ j, elimA A (Sum.inr ⟨i, hzero⟩) j = restrict A i j :=
            fun _ => rfl
          rw [hb] at hrow
          have hres : ∑ j, restrict A i j * x' j ≤ b i := by
            calc ∑ j, restrict A i j * x' j
                = ∑ j, elimA A (Sum.inr ⟨i, hzero⟩) j * x' j :=
                  Finset.sum_congr rfl fun j _ => by rw [hA j]
              _ ≤ b i := hrow
          rw [hzero]
          linarith
        · have hle := htP ⟨i, hpos⟩
          rw [le_div_iff₀ hpos] at hle
          have hfin : colLast A i * t ≤ s i := by linarith [hle]
          simp only [hs] at hfin
          linarith
      · -- pull the certificate back
        right
        refine ⟨fun i => ∑ i' : Elim A, y' i' * elimWeight A i' i, ?_, ?_, ?_⟩
        · intro i
          exact Finset.sum_nonneg fun i' _ =>
            mul_nonneg (hy0 i') (elimWeight_nonneg A i' i)
        · intro j
          refine Fin.lastCases ?_ (fun j0 => ?_) j
          · show ∑ i, (∑ i' : Elim A, y' i' * elimWeight A i' i)
                * A i (Fin.last n) = 0
            rw [sum_swap_weights]
            refine Finset.sum_eq_zero fun i' _ => ?_
            have hz := elimWeight_last A i'
            simp only [colLast] at hz
            rw [hz, mul_zero]
          · show ∑ i, (∑ i' : Elim A, y' i' * elimWeight A i' i)
                * A i j0.castSucc = 0
            rw [sum_swap_weights]
            have h2 : ∀ i' : Elim A,
                y' i' * ∑ i, elimWeight A i' i * A i j0.castSucc =
                  y' i' * elimA A i' j0 := by
              intro i'; rw [elimWeight_col A i' j0]
            rw [Finset.sum_congr rfl fun i' _ => h2 i']
            exact hyA j0
        · show ∑ i, (∑ i' : Elim A, y' i' * elimWeight A i' i) * b i < 0
          rw [sum_swap_weights]
          have h2 : ∀ i' : Elim A, y' i' * ∑ i, elimWeight A i' i * b i =
              y' i' * elimB A b i' := by
            intro i'; rw [elimWeight_rhs A b i']
          rw [Finset.sum_congr rfl fun i' _ => h2 i']
          exact hyb

/-- **Farkas' lemma over `ℚ`** with the variables indexed by an arbitrary
finite type. -/
theorem farkas {κ : Type} [Fintype κ] {ι : Type} [Fintype ι] (A : ι → κ → ℚ)
    (b : ι → ℚ) :
    (∃ x : κ → ℚ, ∀ i, ∑ k, A i k * x k ≤ b i) ∨
    (∃ y : ι → ℚ, (∀ i, 0 ≤ y i) ∧ (∀ k, ∑ i, y i * A i k = 0) ∧
      ∑ i, y i * b i < 0) := by
  classical
  obtain ⟨e⟩ := Fintype.truncEquivFin κ
  rcases farkas_fin (Fintype.card κ) (fun i j => A i (e.symm j)) b with
    ⟨x, hx⟩ | ⟨y, hy0, hyA, hyb⟩
  · refine Or.inl ⟨fun k => x (e k), fun i => ?_⟩
    have hi := hx i
    calc ∑ k, A i k * x (e k) = ∑ j, A i (e.symm j) * x j := by
          rw [← Equiv.sum_comp e (fun j => A i (e.symm j) * x j)]
          exact Finset.sum_congr rfl fun k _ => by simp
      _ ≤ b i := hi
  · refine Or.inr ⟨y, hy0, fun k => ?_, hyb⟩
    simpa using hyA (e k)

end PaperI.RationalFarkas

