import PaperIV.E01Ledger

/-!
# Porte del nibble de Paper III: la reducción, y lo que queda

## Qué se porta y qué no, dicho antes que nada

La clausura de imports de `Nibble.FracNibbleRepaired` (Paper III, freeze v1.4) son **83
módulos y 16 844 líneas**. Copiar eso dentro de Paper IV no sería un porte sino un **fork**
de la librería completa — exactamente el agregado histórico que la política del encargo
prohíbe, sólo que duplicado. No se hace aquí.

Lo que se porta es **la reducción**, que es donde vive el contenido propio de Paper IV:
construir el hipergrafo de los `K₄` de un grafo, verificar que es `6`-uniforme, y convertir
un *matching* de ese hipergrafo en un `Packing` literal con la ganancia correcta. Con eso,
la cláusula 4 de `E01Ledger.TwoRegimeRouteAt` deja de ser «una hipótesis sobre packings» y
pasa a ser **el enunciado de Paper III, verbatim, sin nada en medio**.

## Contenido

* `Hypergraph.IsUniform`, `Hypergraph.IsMatching` — las definiciones de
  `Nibble/Basic.lean`, reproducidas literalmente para poder enunciar el nibble.
* `WeightedNibbleAt` — `Nibble.FracNibbleWeightedTheorem` (`Nibble/FracNibbleRepaired.lean`
  línea 40), verbatim. **NO demostrado**, ni en Paper III ni aquí: allí es un `def : Prop` y
  sólo se concluye desde `FracNibbleWeightedHeavyEdge`, que tampoco lo está.
* `NearPerfectNibbleAt` — `Nibble.fracNibbleWeighted_nearPerfect`
  (`Nibble/FracNibbleRepaired.lean` línea 53), verbatim. **Esto sí está demostrado en Paper
  III**, para todo `r ≥ 2`, sin `sorry`, con la cadena a AX1 auditando
  `[propext, Classical.choice, Quot.sound]` en el log del freeze.  Lleva dos hipótesis extra
  que, para el hipergrafo de los `K₄` de una clique completa, son triviales.
* `k4Supports` — el hipergrafo de los `K₄` de `G`: vértices = aristas, hiperaristas = los
  soportes de seis aristas de cada `K₄`.
* `k4Supports_uniform` — **demostrado**: es `6`-uniforme.
* `packing_of_matching` — **demostrado**: todo matching de `k4Supports G` es un `Packing`
  de `G` con ganancia exactamente `5·|M|`. **Éste es el puente que faltaba.**

## Lo que queda para cerrar la cláusula 4

Con `packing_of_matching`, aplicar el nibble a una bolsa requiere sólo verificar sus tres
hipótesis sobre el hipergrafo `k4Supports`:

1. `IsUniform (k4Supports G) 6` — **demostrado aquí**.
2. cargas `≤ 1` y `≥ 1-γ` fuera de un excepcional pequeño;
3. codegrees ponderados `≤ γ`.

Para la clique **completa** (2) y (3) son identidades de conteo verificadas en aritmética
exacta (`checks/b2_nibble_hyp.py`, `m = 4..14`): la carga es **exactamente 1** con peso
uniforme `1/C(m-2,2)`, luego el excepcional es vacío, y el codegree máximo es `2/(m-3) → 0`.
Para bolsas **densas** (`δ > 0`) sólo están **medidas** (`checks/b2_dense.py`), y degradan:
a `δ = 0.20` el excepcional llega al 70 %. `nibble_gives_denseBag` las deja como hipótesis
explícitas y nombradas, que es exactamente el residuo.
-/

namespace PaperIV.NibblePort

open Finset
open PaperIV.FarRounding

/-! ## 1. Las definiciones de hipergrafo de Paper III, reproducidas -/

namespace Hypergraph

variable {W : Type*} [DecidableEq W]

/-- `Nibble.Hypergraph.IsUniform` (`Nibble/Basic.lean:30`), verbatim. -/
def IsUniform (H : Finset (Finset W)) (r : ℕ) : Prop := ∀ e ∈ H, e.card = r

/-- `Nibble.Hypergraph.IsMatching` (`Nibble/Basic.lean:33`), verbatim. -/
structure IsMatching (H M : Finset (Finset W)) : Prop where
  subset : M ⊆ H
  disjoint : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

end Hypergraph

/-- **`Nibble.FracNibbleWeightedTheorem`** (`Nibble/FracNibbleRepaired.lean:40`), verbatim.

**AVISO — corrección.**  Una versión anterior de esta nota decía «está demostrado en Paper
III».  Es falso tal como se lee: en Paper III esto es un `def : Prop` y **no** hay teorema que
lo concluya; lo único que hay es `fracNibbleWeightedTheorem_of_heavyEdge`, condicionado a
`FracNibbleWeightedHeavyEdge`, que tampoco está demostrada.  Lo demostrado allí es la forma
**casi-perfecta**, que lleva dos hipótesis extra y está reproducida abajo como
`NearPerfectNibbleAt`.

Usar `WeightedNibbleAt` es, por tanto, apoyarse en algo que no está demostrado en ninguna
parte del programa.  Para la aplicación de Paper IV **no hace falta**: úsese
`K4UniformNibbleCounts.cliqueBagNibbleAt_of_nearPerfectNibble`. -/
def WeightedNibbleAt : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β → ∃ γ : ℝ, 0 < γ ∧
    ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ),
      Hypergraph.IsUniform H r →
      (∀ T, 0 ≤ w T) →
      (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
      (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
      ∃ M : Finset (Finset W), Hypergraph.IsMatching H M ∧
        (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ)

/-- **`Nibble.fracNibbleWeighted_nearPerfect`** (Paper III, `Nibble/FracNibbleRepaired.lean`
línea 53), verbatim.

**Ésta es la que Paper III demuestra**, sin `sorry`, para todo `r ≥ 2`.  `WeightedNibbleAt`
—arriba— es el enunciado *irrestricto* `Nibble.FracNibbleWeightedTheorem`, que en Paper III
es un `def : Prop` y **sólo se demuestra condicionado** a `FracNibbleWeightedHeavyEdge`
(`fracNibbleWeightedTheorem_of_heavyEdge`).  Así que asumir `WeightedNibbleAt` es asumir algo
que **no está demostrado en ninguna parte del programa**, mientras que asumir
`NearPerfectNibbleAt` es asumir un teorema demostrado y auditado.

Las dos hipótesis extra son: la carga es `≥ 1-γ` fuera de un excepcional `Exc`, y
`|Exc| ≤ η·|W|`.  Para la aplicación de Paper IV —el hipergrafo de los `K₄` de una clique
**completa** con peso uniforme— ambas son triviales: la carga vale exactamente `1` en toda
arista real, y `Exc` es el conjunto de los diagonales de `Sym2`, de tamaño `m` frente a
`|W| ≥ C(m,2)`.  Véase `K4UniformNibbleCounts.cliqueBagNibbleAt_of_nearPerfectNibble`. -/
def NearPerfectNibbleAt : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β → ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ)
      (Exc : Finset W),
      Hypergraph.IsUniform H r →
      (∀ T, 0 ≤ w T) →
      (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
      (∀ v : W, v ∉ Exc → 1 - γ ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
      (Exc.card : ℝ) ≤ η * (Fintype.card W : ℝ) →
      (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
      ∃ M : Finset (Finset W), Hypergraph.IsMatching H M ∧
        (1 - β) * ((Fintype.card W : ℝ) / r) ≤ (M.card : ℝ) ∧
        (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ)

/-- El enunciado irrestricto implica el casi-perfecto: basta olvidar las dos hipótesis extra
(y la conclusión extra se obtiene ignorándola).  Se registra para dejar visible que
`NearPerfectNibbleAt` es **más débil**, luego sustituirlo no es un fortalecimiento
encubierto. -/
theorem nearPerfectNibbleAt_of_weightedNibbleAt (h : WeightedNibbleAt) {r : ℕ} (hr : 2 ≤ r)
    {β : ℝ} (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ),
        Hypergraph.IsUniform H r →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        ∃ M : Finset (Finset W), Hypergraph.IsMatching H M ∧
          (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ) :=
  h r hr β hβ

/-! ## 2. El hipergrafo de los `K₄`, y que es `6`-uniforme -/

section K4

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- El conjunto de vértices que toca un conjunto de aristas. -/
def cliqueOf (S : Finset (Sym2 V)) : Finset V := S.biUnion Sym2.toFinset

/-- Un conjunto de al menos dos vértices se recupera de su soporte de aristas. -/
theorem cliqueOf_pairs {K : Finset V} (h : 2 ≤ K.card) : cliqueOf (pairs K) = K := by
  classical
  ext v
  simp only [cliqueOf, Finset.mem_biUnion]
  constructor
  · rintro ⟨e, he, hve⟩
    induction e using Sym2.ind with
    | _ a b =>
      rw [mk_mem_pairs] at he
      rw [Sym2.mem_toFinset, Sym2.mem_iff] at hve
      rcases hve with rfl | rfl
      · exact he.1
      · exact he.2.1
  · intro hv
    have hne : (K.erase v).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hv]; omega
    obtain ⟨u, hu⟩ := hne
    obtain ⟨huv, huK⟩ := Finset.mem_erase.1 hu
    refine ⟨s(v, u), ?_, ?_⟩
    · rw [mk_mem_pairs]; exact ⟨hv, huK, fun hc => huv hc.symm⟩
    · rw [Sym2.mem_toFinset, Sym2.mem_iff]; exact Or.inl rfl

/-- **El hipergrafo de los `K₄` de `G`.**  Vértices: las aristas de `G`.  Hiperaristas: los
soportes de seis aristas de cada copia de `K₄`. -/
def k4Supports (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset (Sym2 V)) :=
  ((items G).filter (fun K => K.card = 4)).image pairs

theorem mem_k4Supports {S : Finset (Sym2 V)} :
    S ∈ k4Supports G ↔ ∃ K : Finset V, IsItem G K ∧ K.card = 4 ∧ pairs K = S := by
  classical
  simp only [k4Supports, Finset.mem_image, Finset.mem_filter, mem_items]
  constructor
  · rintro ⟨K, ⟨hK, h4⟩, rfl⟩; exact ⟨K, hK, h4, rfl⟩
  · rintro ⟨K, hK, h4, rfl⟩; exact ⟨K, ⟨hK, h4⟩, rfl⟩

/-- **El hipergrafo de los `K₄` es `6`-uniforme.**  Un `K₄` tiene `C(4,2) = 6` aristas. -/
theorem k4Supports_uniform : Hypergraph.IsUniform (k4Supports G) 6 := by
  intro S hS
  obtain ⟨K, _, h4, rfl⟩ := mem_k4Supports.1 hS
  have e42 : Nat.choose 4 2 = 6 := by decide
  rw [card_pairs, h4, e42]

/-- Sobre `k4Supports`, `cliqueOf` es inversa de `pairs`. -/
theorem pairs_cliqueOf {S : Finset (Sym2 V)} (hS : S ∈ k4Supports G) :
    pairs (cliqueOf S) = S := by
  obtain ⟨K, _, h4, rfl⟩ := mem_k4Supports.1 hS
  rw [cliqueOf_pairs (by omega : 2 ≤ K.card)]

/-- **El puente que faltaba.**  Todo matching del hipergrafo de los `K₄` **es** un `Packing`
literal de `G`, de ganancia exactamente `5·|M|`.

Con esto, la conclusión del nibble —un matching de `k4Supports`— se convierte directamente
en la conclusión que pide `DenseBagClosure.DenseBagNibbleAt`. -/
theorem packing_of_matching (M : Finset (Finset (Sym2 V)))
    (hM : Hypergraph.IsMatching (k4Supports G) M) :
    ∃ P : Packing G, P.gain = 5 * M.card := by
  classical
  have hitem : ∀ S ∈ M, IsItem G (cliqueOf S) ∧ (cliqueOf S).card = 4 := by
    intro S hS
    obtain ⟨K, hK, h4, rfl⟩ := mem_k4Supports.1 (hM.subset hS)
    rw [cliqueOf_pairs (by omega : 2 ≤ K.card)]
    exact ⟨hK, h4⟩
  have hinj : ∀ S ∈ M, ∀ S' ∈ M, cliqueOf S = cliqueOf S' → S = S' := by
    intro S hS S' hS' heq
    rw [← pairs_cliqueOf (hM.subset hS), ← pairs_cliqueOf (hM.subset hS'), heq]
  refine ⟨{ pieces := M.image cliqueOf
            isItem := by
              intro K hK
              obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hK
              exact (hitem S hS).1
            edgeDisjoint := by
              intro K hK L hL hKL
              obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hK
              obtain ⟨S', hS', rfl⟩ := Finset.mem_image.1 hL
              rw [pairs_cliqueOf (hM.subset hS), pairs_cliqueOf (hM.subset hS')]
              exact hM.disjoint S hS S' hS' (fun hc => hKL (by rw [hc])) }, ?_⟩
  show ∑ K ∈ M.image cliqueOf, gainOf K = 5 * M.card
  rw [Finset.sum_image hinj]
  rw [Finset.sum_congr rfl (fun S hS => gainOf_of_card_eq_four (hitem S hS).2),
    Finset.sum_const, smul_eq_mul, mul_comm]

end K4

/-! ## 3. La reducción, con el residuo nombrado -/

section Reduction

-- `Type` y no `Type*`: el enunciado de Paper III está cuantificado sobre `Type` (universo 0),
-- y esta reducción hereda esa restricción del original.
variable {V : Type} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **La reducción.**  Dado el nibble genérico y las hipótesis de carga y codegree sobre el
hipergrafo `k4Supports G` con un peso `w`, se obtiene un `Packing` de `G` cuya ganancia
alcanza la fracción `1-β` del valor fraccional `∑ w`.

Todo lo específico de Paper IV —`6`-uniformidad y la conversión matching→`Packing`— ya está
demostrado (`k4Supports_uniform`, `packing_of_matching`).  Lo que queda como hipótesis es
**exactamente** lo que el nibble pide de la instancia: cargas y codegrees.  Para la clique
completa son identidades de conteo (carga exactamente `1`, codegree `2/(m-3)`); para bolsas
densas están medidas, no demostradas. -/
theorem packing_of_nibble (hnib : WeightedNibbleAt) {β : ℝ} (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (w : Finset (Sym2 V) → ℝ),
      (∀ T, 0 ≤ w T) →
      (∀ e : Sym2 V, ∑ T ∈ (k4Supports G).filter (fun T => e ∈ T), w T ≤ 1) →
      (∀ e f : Sym2 V, e ≠ f →
        ∑ T ∈ (k4Supports G).filter (fun T => e ∈ T ∧ f ∈ T), w T ≤ γ) →
      ∃ P : Packing G,
        (1 - β) * (∑ T ∈ k4Supports G, w T) ≤ ((P.gain : ℝ) / 5) := by
  classical
  obtain ⟨γ, hγ, hmain⟩ := hnib 6 (by norm_num) β hβ
  refine ⟨γ, hγ, ?_⟩
  intro w hw0 hload hcod
  obtain ⟨M, hM, hcard⟩ :=
    hmain (W := Sym2 V) (k4Supports G) w k4Supports_uniform hw0 hload hcod
  obtain ⟨P, hP⟩ := packing_of_matching M hM
  refine ⟨P, ?_⟩
  have : ((P.gain : ℝ) / 5) = (M.card : ℝ) := by
    rw [hP]; push_cast; ring
  rw [this]
  exact hcard

end Reduction

end PaperIV.NibblePort
