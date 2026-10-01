import PaperIV.FarRounding
import MixedRounding.Cleanup

/-!
# Adaptador `MixedRounding` ↔ `PaperIV.FarRounding`

`MixedRounding` es una biblioteca **neutral** (sólo Mathlib) y por eso duplica las definiciones
del modelo mixto que `PaperIV.FarRounding` ya tenía.  Este módulo demuestra que las dos copias
son la misma cosa, para que la duplicación no se convierta en deriva.

Vive en `PaperIV` —no en `MixedRounding`— precisamente para no romper la neutralidad de la
biblioteca: quien importe `MixedRounding` no arrastra `PaperIV`.

## Qué se demuestra

Que `pairs`, `IsItem`, `items` y `gainF` coinciden, y que los empaquetamientos —fraccionales y
físicos— se transportan en ambas direcciones.  Todo es `rfl` o casi: las definiciones se
escribieron para ser iguales, y esto lo certifica la máquina en vez de un comentario.
-/

namespace PaperIV.MixedRoundingAdapter

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. Los ingredientes coinciden -/

theorem pairs_eq (K : Finset V) : MixedRounding.pairs K = PaperIV.FarRounding.pairs K := rfl

theorem isItem_iff (K : Finset V) :
    MixedRounding.IsItem G K ↔ PaperIV.FarRounding.IsItem G K := Iff.rfl

theorem gainF_eq (K : Finset V) :
    MixedRounding.gainF ℚ K = PaperIV.FarRounding.gainF ℚ K := rfl

theorem gainOf_eq (K : Finset V) :
    MixedRounding.gainOf K = PaperIV.FarRounding.gainOf K := rfl

theorem items_eq : MixedRounding.items G = PaperIV.FarRounding.items G := by
  ext K
  rw [MixedRounding.mem_items, PaperIV.FarRounding.mem_items]
  exact isItem_iff K

/-! ## 2. Transporte de empaquetamientos fraccionales -/

/-- Un empaquetamiento fraccional de `MixedRounding` es uno de `PaperIV`. -/
def toFarFrac (x : MixedRounding.FracPacking G) : PaperIV.FarRounding.FracPacking G ℚ where
  weight := x.weight
  weight_nonneg := x.weight_nonneg
  capacity := by
    intro e he
    have h := x.capacity e he
    rwa [items_eq] at h

/-- Y al revés. -/
def ofFarFrac (x : PaperIV.FarRounding.FracPacking G ℚ) : MixedRounding.FracPacking G where
  weight := x.weight
  weight_nonneg := x.weight_nonneg
  capacity := by
    intro e he
    have h := x.capacity e he
    rwa [← items_eq] at h

theorem value_toFarFrac (x : MixedRounding.FracPacking G) :
    (toFarFrac x).value = x.value := by
  rw [PaperIV.FarRounding.FracPacking.value, MixedRounding.FracPacking.value, ← items_eq]
  rfl

theorem value_ofFarFrac (x : PaperIV.FarRounding.FracPacking G ℚ) :
    (ofFarFrac x).value = x.value := by
  rw [MixedRounding.FracPacking.value, PaperIV.FarRounding.FracPacking.value, items_eq]
  rfl

/-! ## 3. Transporte de empaquetamientos físicos -/

def toFarPacking (P : MixedRounding.Packing G) : PaperIV.FarRounding.Packing G where
  pieces := P.pieces
  isItem := fun K hK => (isItem_iff K).1 (P.isItem K hK)
  edgeDisjoint := P.edgeDisjoint

def ofFarPacking (P : PaperIV.FarRounding.Packing G) : MixedRounding.Packing G where
  pieces := P.pieces
  isItem := fun K hK => (isItem_iff K).2 (P.isItem K hK)
  edgeDisjoint := P.edgeDisjoint

theorem gain_toFarPacking (P : MixedRounding.Packing G) :
    (toFarPacking P).gain = P.gain := rfl

theorem gain_ofFarPacking (P : PaperIV.FarRounding.Packing G) :
    (ofFarPacking P).gain = P.gain := rfl

end PaperIV.MixedRoundingAdapter
