import PaperIV.SimultaneousSelection
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Capas cíclicas y soportes disjuntos (RC01 §16.2)

La pieza estructural que hace funcionar la concentración de §16.3: dentro de una capa, los
indicadores de supervivencia son **mutuamente independientes**, porque sus soportes son
disjuntos.

## El contenido

Para `K₄`, las completaciones de una raíz `ab` son pares `(c,d)` de las dos partes restantes.
Identificando ambas con `ℤ/t` y agrupando por el valor `c+d`, hay `t` capas y

> **en una misma capa, dos pares distintos tienen a la vez `c ≠ c'` y `d ≠ d'`.**

Eso es `layer_distinct`, y es todo el contenido matemático: si `c = c'` entonces
`d = s − c = s − c' = d'`, luego los pares coinciden.

De ahí sale `pageEdges_disjoint`: las cinco aristas no raíz `ac, bc, ad, bd, cd` de una
completación son disjuntas de las cinco de la otra.  La fuente añade que *«la distinción entre
las cuatro partes asegura también que los cinco tipos de arista no se identifican
accidentalmente»* — aquí eso son las hipótesis de disyunción de las cuatro partes, que se usan
todas.

## Lo que no está aquí

La independencia probabilística propiamente dicha (que soportes disjuntos ⟹ indicadores
independientes bajo el condicionamiento de la raíz) necesita el espacio de monedas por arista
de §15.4, que no está formalizado.  Lo de aquí es su hipótesis combinatoria.
-/

namespace PaperIV.CyclicLayering

open Finset

/-! ## 1. La capa determina el otro extremo -/

/-- **La propiedad de capa.**  Dos pares distintos con la misma suma difieren en **ambas**
coordenadas.  Es lo único que se necesita de la estructura cíclica. -/
theorem layer_distinct {t : ℕ} {s c d c' d' : ZMod t}
    (h : c + d = s) (h' : c' + d' = s) (hne : (c, d) ≠ (c', d')) :
    c ≠ c' ∧ d ≠ d' := by
  constructor
  · intro hc
    apply hne
    have : d = d' := by
      have := h.trans h'.symm
      rw [hc] at this
      exact add_left_cancel this
    rw [hc, this]
  · intro hd
    apply hne
    have : c = c' := by
      have := h.trans h'.symm
      rw [hd] at this
      exact add_right_cancel this
    rw [hd, this]

/-! ## 2. Los cinco soportes no raíz -/

variable {V : Type*} [DecidableEq V]

/-- Las cinco aristas no raíz de la completación `(c,d)` de la raíz `(a,b)`. -/
def pageEdges (a b c d : V) : Finset (Sym2 V) :=
  {s(a, c), s(b, c), s(a, d), s(b, d), s(c, d)}

/-- **Soportes disjuntos (RC01 §16.2).**  Dos completaciones de la misma raíz que difieren en
ambas coordenadas tienen soportes no raíz disjuntos.

Las cuatro partes deben ser disjuntas dos a dos: es lo que impide que «los cinco tipos de
arista se identifiquen accidentalmente». -/
theorem pageEdges_disjoint {A B C D : Finset V}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    {a b c d c' d' : V} (ha : a ∈ A) (hb : b ∈ B)
    (hc : c ∈ C) (hd : d ∈ D) (hc' : c' ∈ C) (hd' : d' ∈ D)
    (hcc : c ≠ c') (hdd : d ≠ d') :
    Disjoint (pageEdges a b c d) (pageEdges a b c' d') := by
  classical
  have hab : a ≠ b := fun h => (Finset.disjoint_left.1 hAB ha) (h ▸ hb)
  have hac : a ≠ c := fun h => (Finset.disjoint_left.1 hAC ha) (h ▸ hc)
  have had : a ≠ d := fun h => (Finset.disjoint_left.1 hAD ha) (h ▸ hd)
  have hac' : a ≠ c' := fun h => (Finset.disjoint_left.1 hAC ha) (h ▸ hc')
  have had' : a ≠ d' := fun h => (Finset.disjoint_left.1 hAD ha) (h ▸ hd')
  have hbc : b ≠ c := fun h => (Finset.disjoint_left.1 hBC hb) (h ▸ hc)
  have hbd : b ≠ d := fun h => (Finset.disjoint_left.1 hBD hb) (h ▸ hd)
  have hbc' : b ≠ c' := fun h => (Finset.disjoint_left.1 hBC hb) (h ▸ hc')
  have hbd' : b ≠ d' := fun h => (Finset.disjoint_left.1 hBD hb) (h ▸ hd')
  have hcd : c ≠ d := fun h => (Finset.disjoint_left.1 hCD hc) (h ▸ hd)
  have hcd' : c ≠ d' := fun h => (Finset.disjoint_left.1 hCD hc) (h ▸ hd')
  have hc'd : c' ≠ d := fun h => (Finset.disjoint_left.1 hCD hc') (h ▸ hd)
  have hc'd' : c' ≠ d' := fun h => (Finset.disjoint_left.1 hCD hc') (h ▸ hd')
  rw [Finset.disjoint_left]
  intro e he hf
  simp only [pageEdges, Finset.mem_insert, Finset.mem_singleton] at he hf
  rcases he with rfl | rfl | rfl | rfl | rfl <;>
    rcases hf with h | h | h | h | h <;>
    rw [Sym2.eq_iff] at h <;>
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp_all

end PaperIV.CyclicLayering
