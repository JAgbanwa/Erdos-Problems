import Nibble.BeckFiala
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# HT-01 — reserva de aristas equilibrada en cada vértice

Herramienta técnica: para un grafo finito `F` y una fracción `θ ∈ [0,1]`, existe un conjunto de
aristas `R ⊆ E(F)` cuyo grado en **cada** vértice se desvía del grado fraccional en a lo sumo `2`:

```text
| d_R(v) − θ · d_F(v) | ≤ 2.
```

## De dónde sale

Es `Nibble.BeckFiala.exists_rounding` —ya usado por el nibble de Paper III— aplicado a un caso
muy concreto: la familia de conjuntos es la de las **aristas vistas como pares de vértices**, y el
peso fraccional es la constante `θ`. Como cada arista tiene exactamente dos extremos, la constante
de Beck–Fiala vale `2`.

Lo que había que formalizar, y es lo único con trabajo, es el **adaptador**: pasar de `Sym2 V` a
`Finset V` sin perder información —la correspondencia es inyectiva sobre aristas, porque ninguna
es diagonal— y la identidad entre el grado del grafo y el grado de la familia.

## Qué **no** da

* No elimina `hfree` ni ninguna otra hipótesis de recursos: reparte la pérdida de grado de una
  reserva, no construye un packing factible.
* No garantiza que un packing posterior evite `R`.
* No demuestra ningún gap mixto universal.

Beck–Fiala ya estaba en el nibble; esto es una especialización de apéndice, no otro motor.
-/

open scoped BigOperators

namespace PaperIV.BalancedReserve

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (F : SimpleGraph V) [DecidableRel F.Adj]

/-- Las aristas, vistas como conjuntos de dos vértices. -/
noncomputable def edgeFamily : Finset (Finset V) :=
  F.edgeFinset.image Sym2.toFinset

variable {F}

/-- El adaptador es inyectivo: dos aristas con los mismos extremos son la misma. -/
theorem toFinset_injOn :
    Set.InjOn Sym2.toFinset (F.edgeFinset : Set (Sym2 V)) := by
  intro e _ f _ hef
  refine Sym2.ext fun x => ?_
  rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hef]

/-- Cada miembro de la familia tiene exactamente dos elementos. -/
theorem card_mem_edgeFamily {t : Finset V} (ht : t ∈ edgeFamily F) : t.card ≤ 2 := by
  classical
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 ht
  have hnd : ¬ e.IsDiag :=
    SimpleGraph.not_isDiag_of_mem_edgeSet F (SimpleGraph.mem_edgeFinset.mp he)
  exact le_of_eq (Sym2.card_toFinset_of_not_isDiag e hnd)

/-- **La identidad de grados.**  El grado de un vértice en la familia de aristas es su grado en el
grafo. -/
theorem card_filter_edgeFamily (x : V) :
    ((edgeFamily F).filter fun t => x ∈ t).card = F.degree x := by
  classical
  have himg : (edgeFamily F).filter (fun t => x ∈ t)
      = (F.edgeFinset.filter fun e => x ∈ e).image Sym2.toFinset := by
    ext t
    simp only [edgeFamily, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨e, he, rfl⟩, hx⟩
      exact ⟨e, ⟨he, Sym2.mem_toFinset.1 hx⟩, rfl⟩
    · rintro ⟨e, ⟨heF, hx⟩, rfl⟩
      exact ⟨⟨e, heF, rfl⟩, Sym2.mem_toFinset.2 hx⟩
  rw [himg, Finset.card_image_of_injOn
    (toFinset_injOn.mono (by intro e he; exact (Finset.mem_filter.1 he).1)),
    ← SimpleGraph.incidenceFinset_eq_filter, SimpleGraph.card_incidenceFinset_eq_degree]

/-- **HT-01.  Reserva equilibrada determinista.**

Para cualquier fracción `θ ∈ [0,1]` hay un conjunto de aristas cuyo grado en cada vértice dista a
lo sumo `2` de `θ` veces el grado del grafo. -/
theorem exists_balanced_reserve (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ∃ R ⊆ F.edgeFinset, ∀ x : V,
      |((R.filter fun e => x ∈ e).card : ℝ) - θ * (F.degree x : ℝ)| ≤ 2 := by
  classical
  obtain ⟨S, hSsub, -, -, hdeg⟩ :=
    Nibble.BeckFiala.exists_rounding 2 (edgeFamily F)
      (fun t ht => card_mem_edgeFamily ht) (fun _ => θ)
      (fun _ _ => h0) (fun _ _ => h1)
  refine ⟨F.edgeFinset.filter fun e => Sym2.toFinset e ∈ S, Finset.filter_subset _ _, ?_⟩
  intro x
  -- el grado de la reserva coincide con el grado de `S`
  have hcard : ((F.edgeFinset.filter fun e => Sym2.toFinset e ∈ S).filter
      fun e => x ∈ e).card = (S.filter fun t => x ∈ t).card := by
    have himg : S.filter (fun t => x ∈ t)
        = ((F.edgeFinset.filter fun e => Sym2.toFinset e ∈ S).filter
            fun e => x ∈ e).image Sym2.toFinset := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · intro ⟨htS, hx⟩
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 (hSsub htS)
        exact ⟨e, ⟨⟨he, htS⟩, Sym2.mem_toFinset.1 hx⟩, rfl⟩
      · rintro ⟨e, ⟨⟨he, hS⟩, hx⟩, rfl⟩
        exact ⟨hS, Sym2.mem_toFinset.2 hx⟩
    rw [himg, Finset.card_image_of_injOn
      (toFinset_injOn.mono (by intro e he; exact (Finset.mem_filter.1 (Finset.mem_filter.1 he).1).1))]
  -- y la suma fraccional es `θ` por el grado
  have hsum : ∑ _t ∈ (edgeFamily F).filter (fun t => x ∈ t), θ = θ * (F.degree x : ℝ) := by
    rw [Finset.sum_const, card_filter_edgeFamily, nsmul_eq_mul, mul_comm]
  have h := hdeg x
  rw [hsum] at h
  rw [hcard]
  simpa using h

end PaperIV.BalancedReserve
