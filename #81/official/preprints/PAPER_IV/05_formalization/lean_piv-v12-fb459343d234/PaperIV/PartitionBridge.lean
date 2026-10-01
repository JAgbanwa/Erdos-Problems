import PaperIV.PatternTransfer
import PaperIV.RegularityFormat

/-!
# El puente entre las tres representaciones de la partición

La composición del Corolario 7.3a tropieza, antes que con nada de matemática, con que la
partición aparece de **tres formas distintas** que nadie había conectado:

| módulo | representación |
|---|---|
| `RegularityFormat.EqualRegularity` | `R.parts : Finset (Finset α)` |
| `PatternTransfer` | `part : α → P`, un color por vértice |
| `TransversalCopies` | `V : ι → Finset α`, una familia indexada |

Este módulo da la primera: de `R.parts` a un color por vértice.

## La basura obliga a `Option`

No todo vértice está en una parte: `EqualRegularity.garbage` permite `≤ δn` vértices fuera.
Luego el color natural es

```
partOf R : α → Option (Finset α)
```

con `none` para la basura. Y eso encaja **exactamente** con el mecanismo del coloreo:
`PatternTransfer.servingT` sólo sirve a los pares cuyo perfil tiene **dos** partes distintas,
así que una arista que toca la basura tiene perfil con `none` y **no la sirve ningún patrón**.
Queda sin color, sin consumir excepcional, y su masa se paga en `L4` del presupuesto
(`RegularityLosses.garbage_edges_le`).

No es un apaño: es la misma razón por la que los pares dentro de una parte quedan sin color
(`L5`).

## El lema que lo sostiene

`partOf_eq_some`: si `v ∈ Q` y `Q ∈ R.parts`, entonces `partOf R v = some Q`. Depende de que las
partes sean **disjuntas dos a dos** —si no, el color no estaría bien definido— y es lo único con
contenido aquí.
-/

namespace PaperIV.PartitionBridge

open Finset
open PaperIV.RegularityFormat

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-- **El color de un vértice**: la parte que lo contiene, o `none` si está en la basura. -/
noncomputable def partOf {δ : ℚ} (R : EqualRegularity G δ) (v : α) : Option (Finset α) :=
  if h : ∃ Q ∈ R.parts, v ∈ Q then some h.choose else none

/-- **El color está bien definido.**  Si `v` está en una parte, ése es su color — y aquí es
donde se usa que las partes sean disjuntas dos a dos. -/
theorem partOf_eq_some {δ : ℚ} (R : EqualRegularity G δ) {v : α} {Q : Finset α}
    (hQ : Q ∈ R.parts) (hv : v ∈ Q) : partOf R v = some Q := by
  classical
  have hex : ∃ Q ∈ R.parts, v ∈ Q := ⟨Q, hQ, hv⟩
  rw [partOf, dif_pos hex]
  congr 1
  obtain ⟨hmem, hin⟩ := hex.choose_spec
  by_contra hne
  exact (Finset.disjoint_left.1 (R.pairwise_disjoint _ hmem _ hQ hne)) hin hv

/-- Un vértice de la basura no tiene color. -/
theorem partOf_eq_none {δ : ℚ} (R : EqualRegularity G δ) {v : α}
    (hv : ∀ Q ∈ R.parts, v ∉ Q) : partOf R v = none := by
  classical
  rw [partOf, dif_neg]
  rintro ⟨Q, hQ, hvQ⟩
  exact hv Q hQ hvQ

/-- **Vértices de partes distintas tienen colores distintos.** -/
theorem partOf_ne_of_mem_ne {δ : ℚ} (R : EqualRegularity G δ) {u v : α} {Q Q' : Finset α}
    (hQ : Q ∈ R.parts) (hQ' : Q' ∈ R.parts) (hu : u ∈ Q) (hv : v ∈ Q') (hne : Q ≠ Q') :
    partOf R u ≠ partOf R v := by
  rw [partOf_eq_some R hQ hu, partOf_eq_some R hQ' hv]
  simpa using hne

/-! ## El perfil de una arista -/

/-- **El perfil de una arista que cruza dos partes.**  Es el par de colores, y tiene cardinal
`2` justo cuando la arista cruza dos partes **distintas** — que es la condición que
`PatternTransfer.servingT` pide para colorearla. -/
theorem partsOf_eq_pair {δ : ℚ} (R : EqualRegularity G δ) {u v : α} {Q Q' : Finset α}
    (hQ : Q ∈ R.parts) (hQ' : Q' ∈ R.parts) (hu : u ∈ Q) (hv : v ∈ Q') :
    PaperIV.PatternTransfer.partsOf (partOf R) s(u, v) = {some Q, some Q'} := by
  rw [PaperIV.PatternTransfer.partsOf_mk, partOf_eq_some R hQ hu, partOf_eq_some R hQ' hv]

/-- **Una arista dentro de una parte tiene perfil de cardinal `1`**, luego no la sirve ningún
patrón: es la pérdida `L5` del presupuesto, vista desde el coloreo. -/
theorem partsOf_card_eq_one_of_same_part {δ : ℚ} (R : EqualRegularity G δ)
    {u v : α} {Q : Finset α} (hQ : Q ∈ R.parts) (hu : u ∈ Q) (hv : v ∈ Q) :
    (PaperIV.PatternTransfer.partsOf (partOf R) s(u, v)).card = 1 := by
  classical
  rw [partsOf_eq_pair R hQ hQ hu hv]
  simp

/-- **Una arista que toca la basura tampoco se colorea.**  Su perfil contiene `none`, y ningún
patrón —que es un conjunto de partes reales— lo contiene. -/
theorem none_mem_partsOf_of_garbage {δ : ℚ} (R : EqualRegularity G δ) {u v : α}
    (hu : ∀ Q ∈ R.parts, u ∉ Q) :
    none ∈ PaperIV.PatternTransfer.partsOf (partOf R) s(u, v) := by
  rw [PaperIV.PatternTransfer.partsOf_mk, partOf_eq_none R hu]
  simp

end PaperIV.PartitionBridge
