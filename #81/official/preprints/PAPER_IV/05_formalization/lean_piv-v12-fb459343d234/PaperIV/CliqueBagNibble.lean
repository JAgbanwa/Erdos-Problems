import PaperIV.AssignmentLemma

/-!
# (B2) Las bolsas clique: cota dual universal, ensamblaje desde `K₄`s, y el nibble a `r = 6`

`SplitBagExact.split_bag_exact` anula la pérdida de redondeo en las bolsas **split**.
Este módulo trata el otro tipo de bolsa, la **clique**, y reduce (B2) a un único
enunciado externo que —a diferencia de lo que yo había recomendado— **no necesita
diseños de Wilson/Hanani**: es el nibble ponderado `r`-genérico, aplicado en `r = 6`
al hipergrafo de los `K₄`.

## Contenido

* `sixthsDual` — el dual de **precio uniforme `5/6`** en toda arista. Es factible para
  el LP mixto porque un `K₃` paga `3·(5/6) = 5/2 ≥ 2` y un `K₄` paga `6·(5/6) = 5 ≥ 5`.
* `sixthsDual_value`, `certified_le_five_sixths` — **cota universal** `W*(G) ≤ (5/6)·e(G)`,
  válida para *todo* grafo, sin cordalidad ni hipótesis alguna.
* `exists_packing_of_k4Family` — una familia de `K₄` disjunta en aristas es un `Packing`
  de ganancia exactamente `5·|M|`.
* `loss_le_of_k4Packing` — **la cota de pérdida por sobrante**: si la familia deja `L`
  aristas sin cubrir, la pérdida es a lo sumo `(5/6)·L`.
* `CliqueBagNibbleAt`, `clique_bag_loss_of_nibble` — la hipótesis externa y el teorema.

## Por qué `5/6` es el precio correcto

Fraccionalmente un `K₄` rinde `5` sobre `6` aristas (`5/6` por arista) y un `K₃` rinde
`2` sobre `3` (`2/3` por arista): el `K₄` domina, y `5/6` es el menor precio uniforme
factible. La cota es **ajustada en las cliques**: el LP exacto da
`W*(K_m) = (5/6)·C(m,2)` para `m = 4..11` (verificado, `checks/b2_nibble_hyp.py`).
Esto convierte (B2) en un enunciado puramente combinatorio: *cubrir casi todas las
aristas de `K_m` con `K₄`s disjuntos en aristas*.

## El insumo externo, y por qué es más débil de lo que yo había dicho

Tómese el hipergrafo `H` cuyos **vértices** son las `C(m,2)` aristas de `K_m` y cuyas
**hiperaristas** son los `C(m,4)` conjuntos de `6` aristas que forman un `K₄`. Es
`6`-uniforme. Con peso uniforme `w ≡ 1/C(m-2,2)`:

* **carga de cada vértice = exactamente `1`** (una arista está en `C(m-2,2)` copias de
  `K₄`), luego el conjunto excepcional es **vacío**;
* **codegree ponderado máximo = `2/(m-3) → 0`** (dos aristas adyacentes abarcan `3`
  vértices y dejan `m-3` elecciones; dos disjuntas determinan el `K₄`), luego el
  packing fraccional es **disperso**;
* `∑_T w = C(m,4)/C(m-2,2) = C(m,2)/6`.

Las tres son exactamente las hipótesis de `Nibble.fracNibbleWeighted_nearPerfect`
(`PAPER_III/05_formalization/lean_v1.4_freeze/Nibble/FracNibbleRepaired.lean`), que está
**demostrado para todo `r ≥ 2`**, sin `sorry`, y cuya cadena a AX1 audita
`[propext, Classical.choice, Quot.sound]` en el log del freeze. Su conclusión da un
matching entero `M` con `|M| ≥ (1-β)·C(m,2)/6`, es decir un sobrante `≤ β·C(m,2)`.

**`Nibble/K4Obstruction.lean` no obstruye esto.** Ese resultado negativo es sobre el
hipergrafo de **triángulos** (`r = 3`), donde el óptimo fraccional de `K₄` vale `2` y se
alcanza *sólo* con los cuatro pesos iguales a `1/2` — no disperso. Aquí el hipergrafo es
el de los **`K₄`** (`r = 6`) de una clique **grande**, y su óptimo es uniforme con pesos
`1/C(m-2,2) → 0`. Son hipergrafos distintos, y la hipótesis de dispersión que allá falla,
aquí se cumple.

**Consecuencia de fuerza.** El nibble entrega sobrante `o(m²)`, que es exactamente lo que
el régimen **lejano** pide (`FarRoundingAt η` tiene `η` arbitrario). Los diseños
`K₄` (Hanani/Wilson) darían `O(m)`, más fuerte, y sólo hacen falta si se quiere alimentar
el régimen **cercano**.

## Estado

`CliqueBagNibbleAt` **no se demuestra aquí**: el `lakefile.toml` de Paper IV depende sólo
de Mathlib, así que `Nibble/` no puede importarse. Queda como hipótesis externa visible,
con la procedencia y la verificación de sus hipótesis documentadas arriba. Todo lo demás
—la cota dual, el ensamblaje y la cota de pérdida— está demostrado.
-/

namespace PaperIV.CliqueBagNibble

open Finset
open PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. La cota dual universal `W* ≤ (5/6)·e` -/

/-- **El dual de precio uniforme `5/6`.**  Factible porque un `K₃` paga `5/2 ≥ 2` y un
`K₄` paga `5 ≥ 5`.  Ninguna hipótesis sobre `G`. -/
def sixthsDual (G : SimpleGraph V) [DecidableRel G.Adj] : DualCover G ℚ where
  price := fun _ => 5 / 6
  price_nonneg := fun _ => by norm_num
  covers := by
    intro K hK
    have hitem := mem_items.1 hK
    rw [Finset.sum_const]
    have e32 : Nat.choose 3 2 = 3 := by decide
    have e42 : Nat.choose 4 2 = 6 := by decide
    rcases hitem.2 with h3 | h4
    · have hc : (pairs K).card = 3 := by rw [card_pairs, h3, e32]
      rw [hc]
      simp only [gainF, h3, e32, nsmul_eq_mul]
      norm_num
    · have hc : (pairs K).card = 6 := by rw [card_pairs, h4, e42]
      rw [hc]
      simp only [gainF, h4, e42, nsmul_eq_mul]
      norm_num

@[simp] theorem sixthsDual_value :
    (sixthsDual G).value = (5 / 6 : ℚ) * (G.edgeFinset.card : ℚ) := by
  simp only [DualCover.value, sixthsDual, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Cota universal del óptimo fraccional mixto.**  Para *todo* grafo,
`W*(G) ≤ (5/6)·e(G)`.  No usa cordalidad. -/
theorem certified_le_five_sixths {w : ℚ} (hw : CertifiedFractionalOptimum G w) :
    w ≤ (5 / 6 : ℚ) * (G.edgeFinset.card : ℚ) := by
  obtain ⟨x, _, hx, _⟩ := hw
  calc w = x.value := hx.symm
    _ ≤ (sixthsDual G).value := weak_duality x (sixthsDual G)
    _ = (5 / 6 : ℚ) * (G.edgeFinset.card : ℚ) := sixthsDual_value

/-! ## 2. Ensamblaje desde una familia de `K₄` -/

/-- Una familia de `K₄` de `G` disjunta en aristas **es** un `Packing`, de ganancia
exactamente `5·|M|`. -/
theorem exists_packing_of_k4Family (M : Finset (Finset V))
    (hitem : ∀ K ∈ M, IsItem G K) (hcard : ∀ K ∈ M, K.card = 4)
    (hdisj : ∀ K ∈ M, ∀ L ∈ M, K ≠ L → Disjoint (pairs K) (pairs L)) :
    ∃ P : Packing G, P.gain = 5 * M.card := by
  refine ⟨⟨M, hitem, hdisj⟩, ?_⟩
  show ∑ K ∈ M, gainOf K = 5 * M.card
  rw [Finset.sum_congr rfl (fun K hK => gainOf_of_card_eq_four (hcard K hK)),
    Finset.sum_const, smul_eq_mul, mul_comm]

/-! ## 3. La pérdida está gobernada por el sobrante -/

/-- **Cota de pérdida por sobrante.**  Si una familia de `K₄` disjunta en aristas deja
`L` aristas sin cubrir —es decir `6·|M| + L = e(G)`— entonces la pérdida respecto del
óptimo fraccional es a lo sumo `(5/6)·L`.

Es la forma exacta en que el problema de (B2) se vuelve *combinatorio*: todo se reduce a
hacer pequeño el sobrante de un empaquetamiento de `K₄`s. -/
theorem loss_le_of_k4Packing {w : ℚ} (hw : CertifiedFractionalOptimum G w)
    (M : Finset (Finset V)) (L : ℕ)
    (hitem : ∀ K ∈ M, IsItem G K) (hcard : ∀ K ∈ M, K.card = 4)
    (hdisj : ∀ K ∈ M, ∀ L ∈ M, K ≠ L → Disjoint (pairs K) (pairs L))
    (hleave : 6 * M.card + L = G.edgeFinset.card) :
    ∃ P : Packing G, w - (P.gain : ℚ) ≤ (5 / 6 : ℚ) * (L : ℚ) := by
  obtain ⟨P, hP⟩ := exists_packing_of_k4Family M hitem hcard hdisj
  refine ⟨P, ?_⟩
  have hub := certified_le_five_sixths hw
  have hE : (G.edgeFinset.card : ℚ) = 6 * (M.card : ℚ) + (L : ℚ) := by
    rw [← hleave]; push_cast; ring
  have hg : (P.gain : ℚ) = 5 * (M.card : ℚ) := by rw [hP]; push_cast; ring
  rw [hg]
  rw [hE] at hub
  linarith

/-! ## 4. La hipótesis externa y el teorema -/

/-- **El nibble a `r = 6`, especializado a bolsas clique.**  Toda clique suficientemente
grande admite un `Packing` (de hecho una familia de `K₄` disjunta en aristas) cuya
ganancia alcanza una fracción `1-β` de la cota dual `(5/6)·e`.

Es la instancia en `r = 6` de `Nibble.fracNibbleWeighted_nearPerfect`, cuyas tres
hipótesis se verifican exactamente en este hipergrafo (docstring del módulo). No se
demuestra aquí: `Nibble/` no es importable bajo el `lakefile.toml` de Paper IV. -/
def CliqueBagNibbleAt (β : ℚ) : Prop :=
  ∃ m₀ : ℕ, ∀ (m : ℕ), m₀ ≤ m → ∀ (G : SimpleGraph (Fin m)) [DecidableRel G.Adj],
    (∀ a b : Fin m, a ≠ b → G.Adj a b) →
      ∃ P : Packing G,
        (1 - β) * ((5 / 6 : ℚ) * (G.edgeFinset.card : ℚ)) ≤ (P.gain : ℚ)

/-- **(B2).**  Bajo el nibble a `r = 6`, la pérdida de redondeo de una bolsa clique es a
lo sumo `β · (5/6) · e`, es decir `o(m²)` al hacer `β → 0`.  Junto con
`SplitBagExact.split_bag_exact` (pérdida **cero** en bolsas split) esto cubre los dos
tipos de bolsa del árbol de cliques. -/
theorem clique_bag_loss_of_nibble {β : ℚ} (h : CliqueBagNibbleAt β) :
    ∃ m₀ : ℕ, ∀ (m : ℕ), m₀ ≤ m → ∀ (G : SimpleGraph (Fin m)) [DecidableRel G.Adj],
      (∀ a b : Fin m, a ≠ b → G.Adj a b) → ∀ w : ℚ, CertifiedFractionalOptimum G w →
        ∃ P : Packing G,
          w - (P.gain : ℚ) ≤ β * ((5 / 6 : ℚ) * (G.edgeFinset.card : ℚ)) := by
  obtain ⟨m₀, hm₀⟩ := h
  refine ⟨m₀, ?_⟩
  intro m hm G _ hcomplete w hw
  obtain ⟨P, hP⟩ := hm₀ m hm G hcomplete
  refine ⟨P, ?_⟩
  have hub := certified_le_five_sixths hw
  nlinarith [hub, hP]

end PaperIV.CliqueBagNibble
