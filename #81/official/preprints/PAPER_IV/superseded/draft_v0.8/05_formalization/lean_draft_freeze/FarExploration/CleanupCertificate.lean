import FarExploration.CleanupDuality
import FarExploration.CleanupObstruction

/-!
# El certificado dual, explícito, sobre la familia rígida

`FarExploration.CleanupObstruction` demuestra que la familia rígida refuta el enunciado LP.
Aquí se escribe la razón en la forma que pide la dualidad: un **certificado dual** literal, con
precios.

El certificado es el mínimo imaginable:

* precios de capacidad: `0`;
* precio de la cota de masa: `0`;
* precio de la cota de valor: `1`;
* precios de codegrado: `2` sobre **un** par ordenado de recursos de cada item, `0` en el resto.

La condición de dominación se lee item a item: cada item tiene ganancia `2`, y los pares
cobrados dentro de él suman exactamente `2`.  El coste total es `gam · 2 · ⌊n/6⌋²`, que es menor
que el valor exigido en cuanto `xi·n² < 2(1-gam)⌊n/6⌋²`.

Los multiplicadores grandes viven, pues, sobre **pares de recursos dentro de un mismo item**, y
la configuración que los hace grandes es la de items disjuntos dos a dos: un item que no comparte
recursos con ningún otro no admite ninguna redistribución, y su peso queda aplastado contra `gam`.
-/

namespace FarExploration.CleanupCertificate

open Finset FarExploration.CleanupLP FarExploration.CleanupDuality
open FarExploration.CleanupObstruction

variable {n : ℕ}

/-! ## 1. Los dos recursos cobrados de cada item -/

/-- El primer recurso del item `(i,j)`. -/
def edge0 (i j : Fin (n / 6)) : Sym2 (Fin n) := s(vtx 0 i, vtx 1 j)

/-- El segundo recurso del item `(i,j)`. -/
def edge1 (i j : Fin (n / 6)) : Sym2 (Fin n) := s(vtx 2 i, vtx 3 j)

lemma edge0_mem (i j : Fin (n / 6)) : edge0 i j ∈ block i j := mem_block.2 (Or.inl rfl)

lemma edge1_mem (i j : Fin (n / 6)) : edge1 i j ∈ block i j :=
  mem_block.2 (Or.inr (Or.inl rfl))

lemma edge0_ne_edge1 (i j : Fin (n / 6)) : edge0 i j ≠ edge1 i j := by
  intro h
  rw [edge0, edge1, Sym2.eq_iff] at h
  simp only [Fin.ext_iff, vtx_val] at h
  omega

/-- Los pares ordenados de recursos que llevan precio: uno por item. -/
def pricedPairs (n : ℕ) : Finset (Sym2 (Fin n) × Sym2 (Fin n)) :=
  (Finset.univ : Finset (Fin (n / 6) × Fin (n / 6))).image fun ij =>
    (edge0 ij.1 ij.2, edge1 ij.1 ij.2)

lemma mem_pricedPairs {p : Sym2 (Fin n) × Sym2 (Fin n)} :
    p ∈ pricedPairs n ↔ ∃ i j : Fin (n / 6), p = (edge0 i j, edge1 i j) := by
  simp [pricedPairs, Prod.exists, eq_comm]

lemma pricedPairs_injective {i j i' j' : Fin (n / 6)}
    (h : (edge0 i j, edge1 i j) = ((edge0 i' j', edge1 i' j') : Sym2 (Fin n) × Sym2 (Fin n))) :
    (i, j) = (i', j') := by
  have h0 : edge0 i j = edge0 i' j' := congrArg Prod.fst h
  have hmem : edge0 i j ∈ block i' j' := by rw [h0]; exact edge0_mem i' j'
  obtain ⟨hi, hj⟩ := block_index_unique (edge0_mem i j) hmem
  simp [hi, hj]

lemma card_pricedPairs (n : ℕ) : (pricedPairs n).card = (n / 6) * (n / 6) := by
  classical
  rw [pricedPairs, Finset.card_image_of_injective _ (fun ij kl h => pricedPairs_injective h)]
  simp [Finset.card_univ]

/-! ## 2. Los precios -/

/-- Los precios de codegrado: `2` sobre el par distinguido de cada item. -/
def pairPriceOf (n : ℕ) (r s : Sym2 (Fin n)) : ℚ := if (r, s) ∈ pricedPairs n then 2 else 0

lemma pairPriceOf_nonneg (n : ℕ) (r s : Sym2 (Fin n)) : 0 ≤ pairPriceOf n r s := by
  unfold pairPriceOf; split <;> norm_num

lemma pairPriceOf_diag (n : ℕ) (r : Sym2 (Fin n)) : pairPriceOf n r r = 0 := by
  unfold pairPriceOf
  rw [if_neg]
  intro hmem
  obtain ⟨i, j, hij⟩ := mem_pricedPairs.1 hmem
  refine edge0_ne_edge1 i j ?_
  have h1 : r = edge0 i j := congrArg Prod.fst hij
  have h2 : r = edge1 i j := congrArg Prod.snd hij
  rw [← h1, ← h2]

lemma sum_pairPriceOf (n : ℕ) :
    ∑ r : Sym2 (Fin n), ∑ s : Sym2 (Fin n), pairPriceOf n r s
      = 2 * (((n / 6) * (n / 6) : ℕ) : ℚ) := by
  classical
  have hprod : ∑ p : Sym2 (Fin n) × Sym2 (Fin n), pairPriceOf n p.1 p.2
      = ∑ r : Sym2 (Fin n), ∑ s : Sym2 (Fin n), pairPriceOf n r s := by
    rw [Fintype.sum_prod_type]
  have hsum : ∑ p : Sym2 (Fin n) × Sym2 (Fin n), pairPriceOf n p.1 p.2
      = ∑ _p ∈ pricedPairs n, (2 : ℚ) := by
    have hcongr : ∀ p : Sym2 (Fin n) × Sym2 (Fin n),
        pairPriceOf n p.1 p.2 = if p ∈ pricedPairs n then (2 : ℚ) else 0 := by
      intro p
      rw [pairPriceOf]
    rw [Finset.sum_congr rfl fun p _ => hcongr p, Finset.sum_ite_mem, Finset.univ_inter]
  rw [← hprod, hsum, Finset.sum_const, nsmul_eq_mul, card_pricedPairs]
  ring

/-! ## 3. El certificado -/

/-- **El certificado dual de la familia rígida.**  Precios de capacidad y de masa nulos, precio
de valor `1`, y precio `2` sobre el par distinguido de cada item. -/
def rigidCertificate (n : ℕ) (gam Cst valLB : ℚ)
    (hstrict : gam * (2 * (((n / 6) * (n / 6) : ℕ) : ℚ)) < valLB) :
    DualCertificate (obstructionSystem n) gam Cst valLB where
  price := fun _ => 0
  pairPrice := pairPriceOf n
  massPrice := 0
  valuePrice := 1
  price_nonneg := fun _ => le_refl 0
  pairPrice_nonneg := pairPriceOf_nonneg n
  pairPrice_diag := pairPriceOf_diag n
  massPrice_nonneg := le_refl 0
  valuePrice_nonneg := by norm_num
  dominates := by
    intro S hS
    obtain ⟨i, j, rfl⟩ := mem_obstructionSystem.1 hS
    have hgain : gainOfSupport (block i j) = 2 := by
      rw [gainOfSupport, if_pos (card_block i j)]
    have hpriced : pairPriceOf n (edge0 i j) (edge1 i j) = 2 := by
      rw [pairPriceOf, if_pos (mem_pricedPairs.2 ⟨i, j, rfl⟩)]
    have hinner : (2 : ℚ) ≤ ∑ s ∈ block i j, pairPriceOf n (edge0 i j) s := by
      refine le_trans (le_of_eq hpriced.symm) ?_
      exact Finset.single_le_sum (f := fun s => pairPriceOf n (edge0 i j) s)
        (fun s _ => pairPriceOf_nonneg n _ s) (edge1_mem i j)
    have houter : (2 : ℚ) ≤ ∑ r ∈ block i j, ∑ s ∈ block i j, pairPriceOf n r s := by
      refine le_trans hinner ?_
      exact Finset.single_le_sum (f := fun r => ∑ s ∈ block i j, pairPriceOf n r s)
        (fun r _ => Finset.sum_nonneg fun s _ => pairPriceOf_nonneg n r s) (edge0_mem i j)
    rw [hgain]
    simp only [Finset.sum_const_zero, zero_mul, zero_add, one_mul]
    linarith
  strict := by
    rw [sum_pairPriceOf]
    simp only [Finset.sum_const_zero, zero_mul, zero_add, one_mul]
    linarith

/-! ## 4. La infactibilidad, vía dualidad débil -/

/-- **La limpieza es infactible sobre la familia rígida**, y lo certifica el dual. -/
theorem rigid_not_cleanupFeasible (n : ℕ) (gam Cst valLB : ℚ)
    (hstrict : gam * (2 * (((n / 6) * (n / 6) : ℕ) : ℚ)) < valLB) :
    ¬ CleanupFeasible (obstructionSystem n) gam Cst valLB :=
  not_feasible_of_dualCertificate (rigidCertificate n gam Cst valLB hstrict)

end FarExploration.CleanupCertificate
