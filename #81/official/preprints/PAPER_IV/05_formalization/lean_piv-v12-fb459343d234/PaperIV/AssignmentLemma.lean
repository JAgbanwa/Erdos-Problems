import PaperIV.FarRoundingFromAssignment

/-!
# (A) El lema de asignación: forma por *pertenencia*, y separación de las dos pérdidas

`FarRoundingFromAssignment.exists_packing_of_edgeAssignment` pide que los conjuntos
de aristas asignados a bolsas distintas sean disjuntos dos a dos.  Toda construcción
real produce en cambio una **función** `own : Sym2 V → β` («esta arista pertenece a
esta bolsa»), y la disyunción es entonces automática.  Este módulo hace ese cambio
de interfaz y lo demuestra.

Aporta además la **descomposición de la pérdida**, que separa las dos cantidades que
la ruta mide por separado y que hasta ahora iban mezcladas en `AssignmentLossAt`:

  `w − Σ_b gain(P_b)  =  (w − Σ_b val_b)  +  Σ_b (val_b − gain(P_b))`

donde `val_b` es cualquier valor asignado a la bolsa `b` (en la práctica `W*(H_b)`).
El primer sumando es la **pérdida de asignación** —cuánto cuesta repartir las aristas—
y el segundo la **pérdida de redondeo** por bolsa.  Son independientes: la primera es
un problema de reparto, la segunda es exactamente lo que `SplitBagExact.split_bag_exact`
anula cuando la bolsa es split.

## Contenido

* `ownParts`, `ownParts_disjoint` — las fibras de `own` y su disyunción.
* `exists_packing_of_ownership` — ensamblaje a partir de una función de pertenencia.
* `loss_decomposition` — la identidad de arriba.
* `AssignmentLossOwnAt`, `assignmentLossAt_of_own` — la hipótesis en forma de
  pertenencia implica `FarRoundingFromAssignment.AssignmentLossAt`, y por tanto
  (vía `farRoundingAt_of_assignmentLoss`) el redondeo lejano.

## Estado

Nada de esto demuestra `AssignmentLossAt`: sigue siendo la entrada externa.  Lo que
se demuestra es que basta exhibir **una función arista→bolsa** y packings por bolsa,
sin verificar ninguna disyunción.

## Evidencia computacional (`checks/bigsep.py`, `checks/bigsep_scale.py`)

Con separadores **grandes** —el régimen que faltaba medir— la asignación canónica
(arista a la bolsa más cercana a la raíz) es `Θ(n²)`: su pérdida relativa `p/n²` se
mantiene esencialmente constante al crecer el número de bolsas (≈0.07 con `s=5,t=2`;
≈0.13 con `s=8,t=2`; ≈0.019 con `s=t=4`).  **La canónica no sirve.**  Reasignando por
búsqueda local desde ella, la pérdida *entera* pasa a ser `Θ(n)`: `p/n` se queda
en ≈0.8 (`s=5,t=2`, `n=15..55`), ≈1.1 (`s=8,t=2`, `n=14..30`) y ≈0.86 (`s=t=4`,
`n=20..68`), con `p/n²` decayendo monótonamente en las tres familias.  Eso es
justo la forma que `AssignmentLossAt ζ` necesita para todo `ζ > 0`.  No es prueba.
-/

namespace PaperIV.AssignmentLemma

open Finset
open PaperIV.FarRounding
open PaperIV.FarRoundingFromAssignment

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {β : Type*} [DecidableEq β]

/-! ## 1. Pertenencia en vez de disyunción -/

/-- Las aristas que `own` asigna a la bolsa `b`. -/
def ownParts (own : Sym2 V → β) (b : β) : Finset (Sym2 V) :=
  Finset.univ.filter (fun e => own e = b)

/-- Las fibras de una función son disjuntas: la hipótesis de disyunción de
`exists_packing_of_edgeAssignment` es gratuita. -/
theorem ownParts_disjoint (own : Sym2 V → β) {b b' : β} (hbb : b ≠ b') :
    Disjoint (ownParts own b) (ownParts own b') := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro e he he'
  simp only [ownParts, Finset.mem_filter] at he he'
  exact hbb (he.2 ▸ he'.2 ▸ rfl)

/-- **Ensamblaje por pertenencia.**  Dada una función `own` que asigna cada arista a
una bolsa y packings por bolsa soportados en las aristas de su propia bolsa, la unión
es un `Packing` literal de `G` cuya ganancia es la suma exacta. -/
theorem exists_packing_of_ownership
    (Bs : Finset β) (own : Sym2 V → β) (P : β → Packing G)
    (hsupp : ∀ b ∈ Bs, ∀ K ∈ (P b).pieces, ∀ e ∈ pairs K, own e = b) :
    ∃ Q : Packing G, Q.gain = ∑ b ∈ Bs, (P b).gain := by
  classical
  refine exists_packing_of_edgeAssignment Bs (ownParts own)
    (fun b _ b' _ hbb => ownParts_disjoint own hbb) P ?_
  intro b hb K hK e he
  simp only [ownParts, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hsupp b hb K hK e he

/-! ## 2. Las dos pérdidas son independientes -/

/-- **Descomposición de la pérdida.**  La distancia entre el óptimo fraccional global
y la ganancia ensamblada se parte exactamente en pérdida de *asignación* (global
menos suma de valores por bolsa) más pérdida de *redondeo* (valor de la bolsa menos
la ganancia entera que se extrae de ella).  Ninguna hipótesis: es una identidad. -/
theorem loss_decomposition (w : ℚ) (Bs : Finset β) (bagVal : β → ℚ) (P : β → Packing G) :
    w - ∑ b ∈ Bs, ((P b).gain : ℚ)
      = (w - ∑ b ∈ Bs, bagVal b) + ∑ b ∈ Bs, (bagVal b - ((P b).gain : ℚ)) := by
  rw [Finset.sum_sub_distrib]
  ring

/-- Si cada pérdida por separado está acotada, la pérdida total lo está por la suma.
Es el uso previsto de `loss_decomposition`: la asignación aporta `ζ₁ n²` y el redondeo
por bolsa aporta `ζ₂ n²` (cero en las bolsas split, por `SplitBagExact.split_bag_exact`). -/
theorem loss_le_of_parts (w : ℚ) (Bs : Finset β) (bagVal : β → ℚ) (P : β → Packing G)
    {a c : ℚ} (hassign : w - ∑ b ∈ Bs, bagVal b ≤ a)
    (hround : ∑ b ∈ Bs, (bagVal b - ((P b).gain : ℚ)) ≤ c) :
    w - ∑ b ∈ Bs, ((P b).gain : ℚ) ≤ a + c := by
  rw [loss_decomposition w Bs bagVal P]
  linarith

/-! ## 3. La hipótesis en forma de pertenencia -/

/-- `AssignmentLossAt` reformulada con una función arista→bolsa en lugar de una
familia de partes disjuntas.  Es la forma que produce cualquier construcción. -/
def AssignmentLossOwnAt (ζ : ℚ) : Prop :=
  ∃ T : ℕ, ∀ n : ℕ, T ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
      ∃ (Bs : Finset ℕ) (own : Sym2 (Fin n) → ℕ) (P : ℕ → Packing G),
        (∀ b ∈ Bs, ∀ K ∈ (P b).pieces, ∀ e ∈ pairs K, own e = b) ∧
        w - (∑ b ∈ Bs, ((P b).gain : ℚ)) ≤ ζ * (n : ℚ) ^ 2

/-- La forma por pertenencia implica la forma por partes. -/
theorem assignmentLossAt_of_own {ζ : ℚ} (h : AssignmentLossOwnAt ζ) : AssignmentLossAt ζ := by
  classical
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  intro n hn G _ hchord w hw
  obtain ⟨Bs, own, P, hsupp, hloss⟩ := hT n hn G hchord w hw
  refine ⟨Bs, ownParts own, P, fun b _ b' _ hbb => ownParts_disjoint own hbb, ?_, hloss⟩
  intro b hb K hK e he
  simp only [ownParts, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hsupp b hb K hK e he

/-- **La cadena completa.**  Una función de pertenencia con pérdida `η/2 · n²` da el
redondeo lejano `FarRoundingAt η`. -/
theorem farRoundingAt_of_assignmentLossOwn {η : ℚ} (h : AssignmentLossOwnAt (η / 2)) :
    FarRoundingAt η :=
  farRoundingAt_of_assignmentLoss (assignmentLossAt_of_own h)

end PaperIV.AssignmentLemma
