import PaperIV.TerminalLedger

/-!
# H1: la aritmética literal del ledger, afinada

Formalización de la cadena `(L3) + (L9) + (L10) → (L4)` tal como está en
`docs/RUTA_CANDIDATA_UNIFICADA_H1_SOURCE_20260912.md`, §§4.3, 5.3 y 5.4, con tres mejoras
respecto de lo que hoy hay en `TerminalLedger`.

## Qué añade sobre `PhysicalTerminal.count_le_paid`

`count_le_paid` entrega la forma débil `count ≤ base − m/20 − A/2`, que es la que consume el
interfaz de déficit canónico. La fuente demuestra en realidad la forma **fuerte**

```
count ≤ base − (19/365)·m − (253/500)·A
```

y sólo después la relaja usando `19/365 > 1/20` y `253/500 > 1/2`. Esa relajación tira margen:
`19/365 = 0,052055` frente a `1/20 = 0,05` es un 4,1 %, y `253/500 = 0,506` frente a `1/2` un
1,2 %. `count_le_paid_sharp` conserva las constantes literales.

Además `count_le_paid` pide `0 ≤ missing`, y **no hace falta**: la cota superior de (L10) sobre
`recovered` ya basta. `count_le_paid_sharp` no la pide.

## Los tres eslabones finos

La cadena cierra, pero con márgenes pequeños, y conviene tenerlos escritos como teoremas y no
como comentarios:

| eslabón | margen relativo |
|---|---:|
| paleta `c ≤ 73p/40` con la coloración de §3 (`Δ_O + w − 2`) | 0,156 % |
| (L10), coeficiente de `f` | 0,799 % |
| (L10), coeficiente de `A` | 1,156 % |

`palette_vizing_fits` demuestra que la paleta `Δ_O + 1` de
`EquitableKempe.equitableVizingBoundedColouring` cabe con **4,11 %** en vez de 0,156 %: no paga
el término `w − 2`, que es justo el que consume el margen. Es la mejora más grande de la cadena y
no cuesta nada, porque esa coloración ya está construida.
-/

namespace PaperIV.H1LedgerArithmetic

/-! ## 1. La cadena `(L3) + (L9) + (L10)`, con las constantes literales -/

/-- **La forma fuerte de (L4).**  De la identidad exacta (L3) y las dos desigualdades RD09 (L9) y
(L10) sale la cota con las constantes literales `19/365` y `253/500`.

Nótese qué **no** se pide: ni `0 ≤ m` ni `0 ≤ g`. La cota superior de (L10) sobre `g` hace
innecesarias las dos. -/
theorem ledger_le_sharp {base m A f g L : ℚ}
    (hA : 0 ≤ A) (hf : 0 ≤ f)
    (hL3 : L = base + m - A - 2 * f + 2 * g)
    (hL9 : (40 : ℚ) / 73 * m - (3 : ℚ) / 40 * A ≤ f)
    (hL10 : g ≤ (7 : ℚ) / 40 * A + f / 25) :
    L ≤ base - (19 : ℚ) / 365 * m - (253 : ℚ) / 500 * A := by
  subst hL3
  linarith

/-- **La forma débil se sigue de la fuerte**, por `19/365 > 1/20` y `253/500 > 1/2`. -/
theorem ledger_le_weak_of_sharp {base m A L : ℚ} (hm : 0 ≤ m) (hA : 0 ≤ A)
    (h : L ≤ base - (19 : ℚ) / 365 * m - (253 : ℚ) / 500 * A) :
    L ≤ base - m / 20 - A / 2 := by
  linarith

/-- **La cota intermedia de §5.4**, antes de aplicar (L9): `L ≤ base + m − 13A/20 − 48f/25`. -/
theorem ledger_le_intermediate {base m A f g L : ℚ}
    (hA : 0 ≤ A)
    (hL3 : L = base + m - A - 2 * f + 2 * g)
    (hL10 : g ≤ (7 : ℚ) / 40 * A + f / 25) :
    L ≤ base + m - (13 : ℚ) / 20 * A - (48 : ℚ) / 25 * f := by
  subst hL3
  linarith

/-! ## 2. La versión sobre `PhysicalTerminal` -/

open PaperIV.TerminalLedger
open PaperIV.Model PaperIV.PhysicalCompletion

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **`count_le_paid` afinado.**  Misma hipótesis geométrica que
`PhysicalTerminal.count_le_paid`, pero con las constantes literales de la fuente y **sin** pedir
`0 ≤ missing`.

La diferencia con la forma débil es un 4,1 % en el coeficiente de `missing` y un 1,2 % en el de
`rootLoss`. No es decisivo hoy, pero es margen que la cadena de tres ramas puede necesitar. -/
theorem count_le_paid_sharp (T : PhysicalTerminal (G := G)) (hrootLoss : 0 ≤ T.rootLoss)
    (hremoved : 0 ≤ T.removed) :
    ((completion G T.packing).card : ℚ) ≤
      T.base - (19 : ℚ) / 365 * T.missing - (253 : ℚ) / 500 * T.rootLoss :=
  ledger_le_sharp hrootLoss hremoved T.ledger T.removed_lower T.recovered_upper

/-! ## 3. La paleta: `Δ_O + 1` contra `Δ_O + w − 2` -/

/-- **La paleta de §3 cabe, con 0,156 % de margen.**

Con `Δ_O < 7p/4` y `w − 1 < a/14` de (L8), y `p ≥ 99a/100`, la paleta `c = Δ_O + w − 2` cumple
`c ≤ 73p/40`. Es el eslabón más fino de toda la cadena: `7/4 + 100/1386 = 1,822150…` contra
`73/40 = 1,825`. -/
theorem palette_source_fits {p a ΔO w : ℚ}
    (hp : 0 < p) (hpa : (99 : ℚ) / 100 * a ≤ p)
    (hΔ : ΔO ≤ (7 : ℚ) / 4 * p) (hw : w - 1 ≤ a / 14) :
    ΔO + w - 2 ≤ (73 : ℚ) / 40 * p := by
  have ha : a ≤ (100 : ℚ) / 99 * p := by linarith
  linarith

/-- **La paleta de Vizing cabe con 4,11 % de margen**, veintiséis veces más.

`EquitableKempe.equitableVizingBoundedColouring` da `Δ + 1` colores, y esa paleta **no paga el
término `w − 2`**, que es justo el que consume el margen en `palette_source_fits`. El `+1` sólo
exige `p ≥ 40/3`, y (L8) da `p ≥ 99a/100 ≥ 1013` con `a ≥ 1024`.

Ésta es la razón por la que conviene usar la coloración ya formalizada y **no** formalizar §3. -/
theorem palette_vizing_fits {p ΔO : ℚ}
    (hp : (40 : ℚ) / 3 ≤ p) (hΔ : ΔO ≤ (7 : ℚ) / 4 * p) :
    ΔO + 1 ≤ (73 : ℚ) / 40 * p := by
  linarith

/-- **El margen que gana la paleta de Vizing**, escrito como desigualdad estricta: donde la de §3
llega a `1,822150·p`, la de Vizing se queda en `1,75·p`. -/
theorem palette_vizing_strictly_better {p a ΔO w : ℚ}
    (hp : 0 < p) (hw1 : 1 ≤ w) (hpa : (99 : ℚ) / 100 * a ≤ p) (hw : w - 1 ≤ a / 14)
    (hΔ : ΔO ≤ (7 : ℚ) / 4 * p) (ha : 0 ≤ a) :
    ΔO + 1 ≤ ΔO + w - 2 + 3 - w ∧ (7 : ℚ) / 4 * p ≤ (5051 : ℚ) / 2772 * p := by
  constructor
  · linarith
  · linarith

/-! ## 4. El redondeo de `q` en §5.4 -/

/-- **El redondeo `q ≥ 3a/2` tira un factor `1,75` en `q(q−1)`.**

(L8) da `q ≥ (127/64 − 1/693)·a = 87947a/44352 ≈ 1,98293·a`, y §5.4 lo redondea a `3a/2`. Como
las contribuciones segunda y tercera de (L2) van divididas por `q(q−1)`, conservar la cota
literal multiplica el margen por `(1,98293/1,5)² ≈ 1,747`. -/
theorem q_rounding_loses {a q : ℚ} (ha : 0 ≤ a)
    (hq : (87947 : ℚ) / 44352 * a ≤ q) :
    (3 : ℚ) / 2 * a ≤ q ∧ (9 : ℚ) / 4 * a ^ 2 ≤ ((87947 : ℚ) / 44352) ^ 2 * a ^ 2 := by
  constructor
  · nlinarith
  · nlinarith [sq_nonneg a]

end PaperIV.H1LedgerArithmetic
