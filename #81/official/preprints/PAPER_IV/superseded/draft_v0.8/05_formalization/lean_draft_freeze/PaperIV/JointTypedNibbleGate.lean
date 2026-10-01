import PaperIV.MixedNibbleUnion
import PaperIV.NibbleHypotheses

/-!
# La puerta conjunta tipada `K₃/K₄` de RC01

## Qué se cierra aquí, dicho antes que nada

RC01 necesita un *nibble* que produzca, **de una sola vez**, un matching que mezcle soportes
de triángulos y soportes de `K₄` sobre **el mismo conjunto de recursos** (las aristas de `G`),
sin repartir previamente las aristas en dos brazos exclusivos.  El reparto en brazos no es
una comodidad de presentación: como se demuestra en §5, la cota aditiva
`2·|M₃| + 5·|M₄|` que el reparto sugiere es **falsa** en general.

Este módulo:

1. define el hipergrafo conjunto tipado `jointSupports G = k3Supports G ∪ k4Supports G`,
   sobre el conjunto de vértices **único** `Sym2 V` (§1);
2. demuestra la **reducción más fuerte disponible**: todo matching del hipergrafo conjunto es
   un `Packing` literal de `G` con ganancia **exacta** `∑ typedGain`, y en particular
   `≥ 2·|M|` (§2).  Esto subsume `MixedNibbleUnion.exists_mixed_packing_of_matchings`, que se
   recupera como corolario (`joint_of_arms`);
3. demuestra que **el teorema de Paper III, tal como está, no basta**: el hipergrafo conjunto
   no es `r`-uniforme para **ningún** `r` en cuanto los dos tipos están presentes
   (`jointSupports_not_uniform`), y la uniformidad es premisa literal de
   `NibblePort.NearPerfectNibbleAt` (§3);
4. aísla el **enunciado mínimo fortalecido** `TypedNearPerfectNibbleAt`: el mismo teorema con
   la premisa `IsUniform H r` sustituida por `HasRanks H r₃ r₄` y la conclusión casi-perfecta
   escalada por el rango **máximo**.  Es mínimo en un sentido demostrado:
   `nearPerfectNibbleAt_of_typed` lo especializa a la diagonal `r₃ = r₄` y recupera
   *exactamente* el enunciado actual, sin añadir nada más (§4);
5. cierra la puerta conjunta **condicionada sólo a ese enunciado**
   (`joint_typed_gate`): todas las demás premisas —tipado, cargas, codegrados, y la
   conversión matching → `Packing`— quedan demostradas aquí (§4);
6. demuestra las **obstrucciones formales** a los dos atajos que evitarían (4):

   * atajo de cardinalidad / aditividad: `joint_gain_add_card_le` (presupuesto exacto de
     aristas) y `additive_shortcut_fails` (contraejemplo literal en `K₄`, donde el máximo
     conjunto vale `5` mientras la receta aditiva promete `7`);
   * atajo de relleno (*padding*) del tipo `3` hasta el tipo `6`:
     `no_faithful_padding_of_capacity` (un relleno fiel dentro del mismo conjunto de recursos
     exige capacidad `6|F|`, el doble de la real) y `private_padding_forces_exceptional`
     (un relleno con recursos ficticios privados manda **todo** el vivero al conjunto
     excepcional, y `private_pool_size_bound` convierte eso en la cota que lo mata).

## Lo que **no** se afirma

No se demuestra `TypedNearPerfectNibbleAt`, ni se afirma que se siga del enunciado uniforme.
Se demuestra la implicación en la dirección honesta (typed ⟹ uniform) y se demuestra que las
dos rutas conocidas para la recíproca (reparto en brazos, relleno) están obstruidas.
-/

namespace PaperIV.JointTypedNibbleGate

open Finset
open PaperIV.FarRounding
open PaperIV.NibblePort
open PaperIV.NibbleHypotheses

/-! ## 1. El hipergrafo conjunto tipado -/

section Joint

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **El hipergrafo conjunto tipado.**  Un único conjunto de recursos —las aristas de `G`,
o sea `Sym2 V`— y las hiperaristas de **los dos tipos a la vez**: los tres lados de cada `K₃`
y los seis de cada `K₄`.  No hay reparto previo de aristas en brazos exclusivos. -/
def jointSupports (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset (Sym2 V)) :=
  k3Supports G ∪ k4Supports G

theorem mem_jointSupports {S : Finset (Sym2 V)} :
    S ∈ jointSupports G ↔ ∃ K : Finset V, IsItem G K ∧ pairs K = S := by
  classical
  constructor
  · intro hS
    rcases Finset.mem_union.1 hS with h | h
    · obtain ⟨K, hK, _, hKS⟩ := mem_k3Supports.1 h
      exact ⟨K, hK, hKS⟩
    · obtain ⟨K, hK, _, hKS⟩ := mem_k4Supports.1 h
      exact ⟨K, hK, hKS⟩
  · rintro ⟨K, hK, rfl⟩
    rcases hK.2 with h3 | h4
    · exact Finset.mem_union_left _ (mem_k3Supports.2 ⟨K, hK, h3, rfl⟩)
    · exact Finset.mem_union_right _ (mem_k4Supports.2 ⟨K, hK, h4, rfl⟩)

/-- El hipergrafo conjunto es exactamente la imagen por `pairs` de **todos** los items. -/
theorem jointSupports_eq_image : jointSupports G = (items G).image pairs := by
  classical
  ext S
  simp only [mem_jointSupports, Finset.mem_image, mem_items]

theorem k3Supports_subset_joint : k3Supports G ⊆ jointSupports G :=
  Finset.subset_union_left

theorem k4Supports_subset_joint : k4Supports G ⊆ jointSupports G :=
  Finset.subset_union_right

/-- **El hipergrafo conjunto tiene rangos `3` y `6`, no uno solo.** -/
theorem jointSupports_card {S : Finset (Sym2 V)} (hS : S ∈ jointSupports G) :
    S.card = 3 ∨ S.card = 6 := by
  rcases Finset.mem_union.1 hS with h | h
  · exact Or.inl (k3Supports_uniform S h)
  · exact Or.inr (k4Supports_uniform S h)

/-- Sobre el hipergrafo conjunto, `cliqueOf` sigue siendo inversa de `pairs`. -/
theorem pairs_cliqueOf_joint {S : Finset (Sym2 V)} (hS : S ∈ jointSupports G) :
    pairs (cliqueOf S) = S := by
  rcases Finset.mem_union.1 hS with h | h
  · exact pairs_cliqueOf_k3 h
  · exact pairs_cliqueOf h

theorem isItem_cliqueOf_joint {S : Finset (Sym2 V)} (hS : S ∈ jointSupports G) :
    IsItem G (cliqueOf S) := by
  obtain ⟨K, hK, rfl⟩ := mem_jointSupports.1 hS
  have h2 : 2 ≤ K.card := by rcases hK.2 with h | h <;> omega
  rwa [cliqueOf_pairs h2]

/-- **La ganancia tipada de una hiperarista**: `2` para el tipo `3`, `5` para el tipo `6`.
Es la lectura del tipo *en la propia hiperarista*, sin memoria de qué brazo la produjo. -/
def typedGain (S : Finset (Sym2 V)) : ℕ := if S.card = 3 then 2 else 5

theorem typedGain_eq_gainOf {S : Finset (Sym2 V)} (hS : S ∈ jointSupports G) :
    gainOf (cliqueOf S) = typedGain S := by
  obtain ⟨K, hK, rfl⟩ := mem_jointSupports.1 hS
  have h2 : 2 ≤ K.card := by rcases hK.2 with h | h <;> omega
  rw [cliqueOf_pairs h2, typedGain, card_pairs]
  rcases hK.2 with h3 | h4
  · rw [gainOf_of_card_eq_three h3, h3]; norm_num
  · rw [gainOf_of_card_eq_four h4, h4]; decide

omit [Fintype V] [DecidableEq V] in
theorem two_le_typedGain (S : Finset (Sym2 V)) : 2 ≤ typedGain S := by
  rw [typedGain]; split <;> omega

/-- La ganancia tipada es una unidad menos que el tamaño de la hiperarista. -/
theorem typedGain_add_one {S : Finset (Sym2 V)} (hS : S ∈ jointSupports G) :
    typedGain S + 1 = S.card := by
  rcases jointSupports_card hS with h | h <;> rw [typedGain, h] <;> norm_num

end Joint

/-! ## 2. La reducción: todo matching conjunto **es** un packing mixto -/

section Reduction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **La puerta conjunta, lado constructivo.**  Un matching del hipergrafo conjunto tipado se
convierte en un `Packing` literal de `G` de ganancia **exactamente** `∑ typedGain`.

Esto es estrictamente más fuerte que los dos adaptadores por separado
(`packing_of_k3_matching`, `packing_of_matching`) y que su unión cruzada
(`exists_mixed_packing_of_matchings`): aquí no hay dos matchings ni hipótesis de disjunción
cruzada, porque el matching ya vive sobre el conjunto de recursos único. -/
theorem packing_of_joint_matching (M : Finset (Finset (Sym2 V)))
    (hM : Hypergraph.IsMatching (jointSupports G) M) :
    ∃ P : Packing G, P.gain = ∑ S ∈ M, typedGain S := by
  classical
  have hinj : ∀ S ∈ M, ∀ S' ∈ M, cliqueOf S = cliqueOf S' → S = S' := by
    intro S hS S' hS' heq
    rw [← pairs_cliqueOf_joint (hM.subset hS), ← pairs_cliqueOf_joint (hM.subset hS'), heq]
  refine ⟨{ pieces := M.image cliqueOf
            isItem := by
              intro K hK
              obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hK
              exact isItem_cliqueOf_joint (hM.subset hS)
            edgeDisjoint := by
              intro K hK L hL hKL
              obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hK
              obtain ⟨S', hS', rfl⟩ := Finset.mem_image.1 hL
              rw [pairs_cliqueOf_joint (hM.subset hS), pairs_cliqueOf_joint (hM.subset hS')]
              exact hM.disjoint S hS S' hS' (fun hc => hKL (by rw [hc])) }, ?_⟩
  show ∑ K ∈ M.image cliqueOf, gainOf K = ∑ S ∈ M, typedGain S
  rw [Finset.sum_image hinj]
  exact Finset.sum_congr rfl (fun S hS => typedGain_eq_gainOf (hM.subset hS))

/-- La misma ganancia, contada por tipos. -/
theorem packing_of_joint_matching_counted (M : Finset (Finset (Sym2 V)))
    (hM : Hypergraph.IsMatching (jointSupports G) M) :
    ∃ P : Packing G,
      P.gain = 2 * (M.filter (fun S => S.card = 3)).card
             + 5 * (M.filter (fun S => S.card = 6)).card := by
  classical
  obtain ⟨P, hP⟩ := packing_of_joint_matching M hM
  refine ⟨P, ?_⟩
  rw [hP]
  have hsplit : M = M.filter (fun S => S.card = 3) ∪ M.filter (fun S => S.card = 6) := by
    ext S
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hS
      rcases jointSupports_card (hM.subset hS) with h | h
      · exact Or.inl ⟨hS, h⟩
      · exact Or.inr ⟨hS, h⟩
    · rintro (⟨hS, _⟩ | ⟨hS, _⟩) <;> exact hS
  have hdisj : Disjoint (M.filter (fun S => S.card = 3)) (M.filter (fun S => S.card = 6)) := by
    rw [Finset.disjoint_left]
    intro S hS hS'
    have h3 := (Finset.mem_filter.1 hS).2
    have h6 := (Finset.mem_filter.1 hS').2
    omega
  have hval3 : ∀ S ∈ M.filter (fun S => S.card = 3), typedGain S = 2 := by
    intro S hS
    simp [typedGain, (Finset.mem_filter.1 hS).2]
  have hval6 : ∀ S ∈ M.filter (fun S => S.card = 6), typedGain S = 5 := by
    intro S hS
    simp [typedGain, (Finset.mem_filter.1 hS).2]
  calc ∑ S ∈ M, typedGain S
      = ∑ S ∈ M.filter (fun S => S.card = 3) ∪ M.filter (fun S => S.card = 6), typedGain S := by
        rw [← hsplit]
    _ = (∑ S ∈ M.filter (fun S => S.card = 3), typedGain S)
          + ∑ S ∈ M.filter (fun S => S.card = 6), typedGain S := Finset.sum_union hdisj
    _ = 2 * (M.filter (fun S => S.card = 3)).card
          + 5 * (M.filter (fun S => S.card = 6)).card := by
        rw [Finset.sum_congr rfl hval3, Finset.sum_congr rfl hval6,
            Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
            mul_comm _ 2, mul_comm _ 5]

/-- **Cota grosera pero suficiente**: cada pieza aporta al menos `2`. -/
theorem two_mul_card_le_gain_of_joint_matching (M : Finset (Finset (Sym2 V)))
    (hM : Hypergraph.IsMatching (jointSupports G) M) :
    ∃ P : Packing G, 2 * M.card ≤ P.gain := by
  obtain ⟨P, hP⟩ := packing_of_joint_matching M hM
  refine ⟨P, ?_⟩
  rw [hP]
  calc 2 * M.card = ∑ _S ∈ M, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ S ∈ M, typedGain S := Finset.sum_le_sum (fun S _ => two_le_typedGain S)

/-! ### La unión por brazos, recuperada como caso particular -/

/-- Dos matchings de los brazos con disjunción cruzada **son** un matching conjunto. -/
theorem joint_of_arms (M₃ M₄ : Finset (Finset (Sym2 V)))
    (h₃ : Hypergraph.IsMatching (k3Supports G) M₃)
    (h₄ : Hypergraph.IsMatching (k4Supports G) M₄)
    (hcross : ∀ S ∈ M₃, ∀ T ∈ M₄, Disjoint S T) :
    Hypergraph.IsMatching (jointSupports G) (M₃ ∪ M₄) := by
  classical
  refine ⟨?_, ?_⟩
  · intro S hS
    rcases Finset.mem_union.1 hS with h | h
    · exact k3Supports_subset_joint (h₃.subset h)
    · exact k4Supports_subset_joint (h₄.subset h)
  · intro S hS T hT hST
    rcases Finset.mem_union.1 hS with hS' | hS' <;> rcases Finset.mem_union.1 hT with hT' | hT'
    · exact h₃.disjoint S hS' T hT' hST
    · exact hcross S hS' T hT'
    · exact (hcross T hT' S hS').symm
    · exact h₄.disjoint S hS' T hT' hST

/-- Un matching del brazo triangular es un matching conjunto. -/
theorem matching_of_k3_matching {M : Finset (Finset (Sym2 V))}
    (h : Hypergraph.IsMatching (k3Supports G) M) :
    Hypergraph.IsMatching (jointSupports G) M :=
  ⟨fun _ hS => k3Supports_subset_joint (h.subset hS), h.disjoint⟩

/-- Un matching del brazo `K₄` es un matching conjunto. -/
theorem matching_of_k4_matching {M : Finset (Finset (Sym2 V))}
    (h : Hypergraph.IsMatching (k4Supports G) M) :
    Hypergraph.IsMatching (jointSupports G) M :=
  ⟨fun _ hS => k4Supports_subset_joint (h.subset hS), h.disjoint⟩

/-- **Subsunción, demostrada.**  `MixedNibbleUnion.exists_mixed_packing_of_matchings` se
recupera *a través* de la puerta conjunta: los dos brazos con disjunción cruzada son un único
matching conjunto, y la ganancia tipada de ese matching es exactamente `2|M₃| + 5|M₄|`.

Luego pasar al hipergrafo conjunto no pierde nada de lo ya verificado; sólo deja de exigir el
reparto previo de aristas. -/
theorem exists_mixed_packing_of_matchings_via_joint (M₃ M₄ : Finset (Finset (Sym2 V)))
    (h₃ : Hypergraph.IsMatching (k3Supports G) M₃)
    (h₄ : Hypergraph.IsMatching (k4Supports G) M₄)
    (hcross : ∀ S ∈ M₃, ∀ T ∈ M₄, Disjoint S T) :
    ∃ P : Packing G, P.gain = 2 * M₃.card + 5 * M₄.card := by
  classical
  obtain ⟨P, hP⟩ := packing_of_joint_matching (M₃ ∪ M₄) (joint_of_arms M₃ M₄ h₃ h₄ hcross)
  refine ⟨P, ?_⟩
  have hfam : Disjoint M₃ M₄ := by
    rw [Finset.disjoint_left]
    intro S hS hS'
    have e3 := k3Supports_uniform S (h₃.subset hS)
    have e6 := k4Supports_uniform S (h₄.subset hS')
    omega
  have hval3 : ∀ S ∈ M₃, typedGain S = 2 := by
    intro S hS; simp [typedGain, k3Supports_uniform S (h₃.subset hS)]
  have hval4 : ∀ S ∈ M₄, typedGain S = 5 := by
    intro S hS; simp [typedGain, k4Supports_uniform S (h₄.subset hS)]
  rw [hP, Finset.sum_union hfam, Finset.sum_congr rfl hval3, Finset.sum_congr rfl hval4,
    Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_comm _ 2, mul_comm _ 5]

end Reduction

/-! ## 3. Por qué el teorema de Paper III, tal como está, no basta -/

section Insufficiency

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **La obstrucción de fondo.**  En cuanto `G` tiene a la vez un triángulo y un `K₄`, el
hipergrafo conjunto **no es `r`-uniforme para ningún `r`**.  Como `IsUniform H r` es premisa
literal de `NibblePort.NearPerfectNibbleAt`, el teorema de Paper III no se puede instanciar en
`jointSupports G`: no es que la instancia sea difícil, es que no existe. -/
theorem jointSupports_not_uniform (h3 : (k3Supports G).Nonempty) (h4 : (k4Supports G).Nonempty)
    (r : ℕ) : ¬ Hypergraph.IsUniform (jointSupports G) r := by
  intro huni
  obtain ⟨S, hS⟩ := h3
  obtain ⟨T, hT⟩ := h4
  have e3 : S.card = 3 := k3Supports_uniform S hS
  have e6 : T.card = 6 := k4Supports_uniform T hT
  have h1 : r = 3 := by rw [← huni S (k3Supports_subset_joint hS), e3]
  have h2 : r = 6 := by rw [← huni T (k4Supports_subset_joint hT), e6]
  omega

/-- Y los dos tipos están presentes en cuanto hay un `K₄`: sus cuatro caras son triángulos.
(Se enuncia sólo la parte que hace falta: un `K₄` produce un soporte triangular.) -/
theorem k3Supports_nonempty_of_k4 (h4 : (k4Supports G).Nonempty) : (k3Supports G).Nonempty := by
  classical
  obtain ⟨T, hT⟩ := h4
  obtain ⟨K, hK, hK4, rfl⟩ := mem_k4Supports.1 hT
  obtain ⟨v, hv⟩ : K.Nonempty := by rw [← Finset.card_pos, hK4]; omega
  refine ⟨pairs (K.erase v), mem_k3Supports.2 ⟨K.erase v, ⟨?_, ?_⟩, ?_, rfl⟩⟩
  · intro a ha b hb hab
    exact hK.1 a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab
  · left; rw [Finset.card_erase_of_mem hv, hK4]
  · rw [Finset.card_erase_of_mem hv, hK4]

end Insufficiency

/-! ## 4. El enunciado mínimo fortalecido, y la puerta cerrada con él -/

section Typed

/-- **Hipergrafo tipado**: cada hiperarista tiene uno de **dos** tamaños permitidos.  Es la
relajación mínima de `Hypergraph.IsUniform` que admite `jointSupports`. -/
def HasRanks {W : Type*} (H : Finset (Finset W)) (r₃ r₄ : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r₃ ∨ e.card = r₄

theorem hasRanks_of_isUniform {W : Type*} {H : Finset (Finset W)} {r : ℕ}
    (h : Hypergraph.IsUniform H r) : HasRanks H r r :=
  fun e he => Or.inl (h e he)

/-- **La diagonal del tipado es exactamente la uniformidad.**  Junto con
`nearPerfectNibbleAt_of_typed` esto fija el *delta* del fortalecimiento: en `r₃ = r₄` no se
pide absolutamente nada nuevo, y lo único que se añade son las instancias fuera de la
diagonal —que es donde vive `jointSupports`—. -/
theorem hasRanks_self_iff {W : Type*} {H : Finset (Finset W)} {r : ℕ} :
    HasRanks H r r ↔ Hypergraph.IsUniform H r := by
  constructor
  · intro h e he
    rcases h e he with h' | h' <;> exact h'
  · exact hasRanks_of_isUniform

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem jointSupports_hasRanks : HasRanks (jointSupports G) 3 6 :=
  fun _ hS => jointSupports_card hS

end Typed

/-- **El enunciado mínimo fortalecido, instancia por instancia.**

`TypedNibbleBody r₃ r₄ β` es `NibblePort.NearPerfectNibbleAt` en los parámetros `(r, β)`
fijados, con **un solo cambio**: la premisa `IsUniform H r` se sustituye por
`HasRanks H r₃ r₄` (dos rangos permitidos), y la conclusión casi-perfecta se escala por el
rango **máximo** `r₄` —que es lo único que la cuenta de recursos puede sostener, porque una
hiperarista grande consume `r₄` recursos—.  Todo lo demás —pesos, cargas, excepcional,
codegrados y la segunda conclusión de masa— es literalmente el enunciado actual.

Se aísla como `Prop` con parámetros porque la puerta conjunta de RC01 necesita
**exactamente una** de estas instancias: `TypedNibbleBody 3 6 β`.  Ése, y no más, es el
residuo. -/
def TypedNibbleBody (r₃ r₄ : ℕ) (β : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ)
      (Exc : Finset W),
      HasRanks H r₃ r₄ →
      (∀ T, 0 ≤ w T) →
      (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
      (∀ v : W, v ∉ Exc → 1 - γ ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
      (Exc.card : ℝ) ≤ η * (Fintype.card W : ℝ) →
      (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
      ∃ M : Finset (Finset W), Hypergraph.IsMatching H M ∧
        (1 - β) * ((Fintype.card W : ℝ) / r₄) ≤ (M.card : ℝ) ∧
        (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ)

/-- **El enunciado mínimo fortalecido, en forma cuantificada.**  Es el análogo tipado de
`NibblePort.NearPerfectNibbleAt`.

Que esto sea **mínimo** y no un fortalecimiento encubierto se demuestra abajo:
`nearPerfectNibbleAt_of_typed` recupera el enunciado actual **exactamente**, tomando
`r₃ = r₄ = r`; y `hasRanks_self_iff` dice que en la diagonal la premisa es literalmente la
uniformidad.  La diagonal, además, **ya es un teorema** de Paper III: véase
`PaperIV.JointTypedNibbleGateFromPaperIII.typedNibbleBody_diagonal`. -/
def TypedNearPerfectNibbleAt : Prop :=
  ∀ r₃ r₄ : ℕ, 2 ≤ r₃ → r₃ ≤ r₄ → ∀ β : ℝ, 0 < β → TypedNibbleBody r₃ r₄ β

/-- **Minimalidad, lado demostrado.**  En la diagonal `r₃ = r₄` el enunciado tipado *es* el
enunciado actual de Paper III: ni una hipótesis menos, ni una conclusión más.  Luego el
fortalecimiento consiste **exactamente** en admitir instancias con dos rangos. -/
theorem nearPerfectNibbleAt_of_typed (h : TypedNearPerfectNibbleAt) : NearPerfectNibbleAt := by
  intro r hr β hβ
  obtain ⟨γ, hγ, η, hη, hmain⟩ := h r r hr le_rfl β hβ
  exact ⟨γ, hγ, η, hη, fun H w Exc huni hw hload hlow hExc hcod =>
    hmain H w Exc (hasRanks_of_isUniform huni) hw hload hlow hExc hcod⟩

/-! ### El ensamblaje tipado, paralelo literal de `NibbleHypotheses.nibble_applies` -/

/-- **`nibble_applies` en versión tipada.**  Mismas cuatro premisas de conteo (§16.3, §16.4,
(17.3)), misma aritmética de peso constante; sólo cambia la premisa de rango. -/
theorem typed_nibble_applies {r₃ r₄ : ℕ} {β : ℝ} (hnib : TypedNibbleBody r₃ r₄ β) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ (W : Type) [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (Exc : Finset W)
        (D u : ℝ),
        HasRanks H r₃ r₄ → 0 < D → 0 ≤ u → 5 * u ≤ γ →
        (∀ v : W, (deg H v : ℝ) ≤ (1 + u) * D) →
        (∀ v : W, v ∉ Exc → (1 - 3 * u) * D ≤ (deg H v : ℝ)) →
        (Exc.card : ℝ) ≤ η * (Fintype.card W : ℝ) →
        (∀ x z : W, x ≠ z → (codeg H x z : ℝ) ≤ γ * ((1 + 2 * u) * D)) →
        ∃ M : Finset (Finset W), Hypergraph.IsMatching H M ∧
          (1 - β) * ((Fintype.card W : ℝ) / r₄) ≤ (M.card : ℝ) ∧
          (1 - β) * ((H.card : ℝ) / ((1 + 2 * u) * D)) ≤ (M.card : ℝ) := by
  obtain ⟨γ, hγ, η, hη, hmain⟩ := hnib
  refine ⟨γ, hγ, η, hη, ?_⟩
  intro W _ _ H Exc D u hranks hD hu huγ hdeg hdeglow hExc hcod
  set c : ℝ := 1 / ((1 + 2 * u) * D) with hc
  have h2 : (0 : ℝ) < 1 + 2 * u := by linarith
  have hpos : (0 : ℝ) < (1 + 2 * u) * D := mul_pos h2 hD
  have hc0 : (0 : ℝ) ≤ c := by rw [hc]; positivity
  obtain ⟨M, hM, hM1, hM2⟩ :=
    hmain H (fun _ => c) Exc hranks (fun _ => hc0)
      (fun v => by rw [load_eq H v c]; exact load_le_one hD hu hc (hdeg v))
      (fun v hv => by
        rw [load_eq H v c]
        exact le_trans (by linarith) (load_ge hD hu hc (hdeglow v hv)))
      hExc
      (fun x z hxz => by
        rw [codegree_eq H x z c]
        exact codeg_weight_le hD hu hc (hcod x z hxz))
  refine ⟨M, hM, hM1, ?_⟩
  rw [total_eq H c, hc, mul_one_div] at hM2
  exact hM2

/-- **LA PUERTA CONJUNTA TIPADA DE RC01, CERRADA.**

Bajo la **única** instancia `TypedNibbleBody 3 6 β` —nada más queda como hipótesis— RC01
obtiene, de una sola pasada del nibble sobre el hipergrafo conjunto y **sin repartir aristas
en brazos exclusivos**, un `Packing` mixto literal de `G` cuya ganancia domina las dos cotas
del teorema casi-perfecto.

Las premisas son exactamente los conteos de §16.3, §16.4 y (17.3) sobre `jointSupports G`;
el tipado (`jointSupports_hasRanks`) y la conversión matching → `Packing`
(`packing_of_joint_matching`) están demostrados aquí. -/
theorem joint_typed_gate {β : ℝ} (hnib : TypedNibbleBody 3 6 β) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (Exc : Finset (Sym2 V)) (D u : ℝ),
        0 < D → 0 ≤ u → 5 * u ≤ γ →
        (∀ e : Sym2 V, (deg (jointSupports G) e : ℝ) ≤ (1 + u) * D) →
        (∀ e : Sym2 V, e ∉ Exc → (1 - 3 * u) * D ≤ (deg (jointSupports G) e : ℝ)) →
        (Exc.card : ℝ) ≤ η * (Fintype.card (Sym2 V) : ℝ) →
        (∀ e f : Sym2 V, e ≠ f →
          (codeg (jointSupports G) e f : ℝ) ≤ γ * ((1 + 2 * u) * D)) →
        ∃ P : Packing G,
          (1 - β) * ((Fintype.card (Sym2 V) : ℝ) / 6) ≤ ((P.gain : ℝ) / 2) ∧
          (1 - β) * (((jointSupports G).card : ℝ) / ((1 + 2 * u) * D)) ≤ ((P.gain : ℝ) / 2) := by
  obtain ⟨γ, hγ, η, hη, hmain⟩ := typed_nibble_applies hnib
  refine ⟨γ, hγ, η, hη, ?_⟩
  intro V _ _ G _ Exc D u hD hu huγ hdeg hdeglow hExc hcod
  obtain ⟨M, hM, hM1, hM2⟩ :=
    hmain (Sym2 V) (jointSupports G) Exc D u jointSupports_hasRanks hD hu huγ hdeg hdeglow
      hExc hcod
  obtain ⟨P, hP⟩ := two_mul_card_le_gain_of_joint_matching M hM
  have hcard : (M.card : ℝ) ≤ (P.gain : ℝ) / 2 := by
    have : (2 * M.card : ℕ) ≤ (P.gain : ℕ) := hP
    have h' : (2 : ℝ) * (M.card : ℝ) ≤ (P.gain : ℝ) := by exact_mod_cast this
    linarith
  refine ⟨P, le_trans ?_ hcard, le_trans hM2 hcard⟩
  simpa using hM1

/-- La misma puerta, tomando la hipótesis en su forma cuantificada. -/
theorem joint_typed_gate_of_typedNibble (hnib : TypedNearPerfectNibbleAt) {β : ℝ} (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (Exc : Finset (Sym2 V)) (D u : ℝ),
        0 < D → 0 ≤ u → 5 * u ≤ γ →
        (∀ e : Sym2 V, (deg (jointSupports G) e : ℝ) ≤ (1 + u) * D) →
        (∀ e : Sym2 V, e ∉ Exc → (1 - 3 * u) * D ≤ (deg (jointSupports G) e : ℝ)) →
        (Exc.card : ℝ) ≤ η * (Fintype.card (Sym2 V) : ℝ) →
        (∀ e f : Sym2 V, e ≠ f →
          (codeg (jointSupports G) e f : ℝ) ≤ γ * ((1 + 2 * u) * D)) →
        ∃ P : Packing G,
          (1 - β) * ((Fintype.card (Sym2 V) : ℝ) / 6) ≤ ((P.gain : ℝ) / 2) ∧
          (1 - β) * (((jointSupports G).card : ℝ) / ((1 + 2 * u) * D)) ≤ ((P.gain : ℝ) / 2) :=
  joint_typed_gate (hnib 3 6 (by norm_num) (by norm_num) β hβ)

/-! ## 5. Obstrucciones formales a los atajos -/

section Obstructions

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Las hiperaristas del hipergrafo conjunto son conjuntos de aristas **reales** de `G`. -/
theorem jointSupports_subset_edgeFinset {S : Finset (Sym2 V)} (hS : S ∈ jointSupports G) :
    S ⊆ G.edgeFinset := by
  obtain ⟨K, hK, rfl⟩ := mem_jointSupports.1 hS
  exact pairs_subset_edgeFinset hK

/-- **El presupuesto exacto de recursos.**  Las piezas de un matching conjunto son disjuntas y
viven dentro de las aristas de `G`, luego consumen `∑ |S|` aristas. -/
theorem sum_card_le_edges (M : Finset (Finset (Sym2 V)))
    (hM : Hypergraph.IsMatching (jointSupports G) M) :
    ∑ S ∈ M, S.card ≤ G.edgeFinset.card := by
  classical
  have hbi : (M.biUnion id).card = ∑ S ∈ M, S.card :=
    Finset.card_biUnion (fun S hS T hT hST => hM.disjoint S hS T hT hST)
  rw [← hbi]
  refine Finset.card_le_card ?_
  intro e he
  obtain ⟨S, hS, heS⟩ := Finset.mem_biUnion.1 he
  exact jointSupports_subset_edgeFinset (hM.subset hS) heS

/-- **La obstrucción de cardinalidad, en forma exacta.**  Para todo matching conjunto,

`ganancia + número de piezas ≤ número de aristas de G`.

Toda receta que prometa una ganancia mayor —en particular la receta aditiva
`2|M₃| + 5|M₄|` sin control del cruce— contradice esta identidad de presupuesto. -/
theorem joint_gain_add_card_le (M : Finset (Finset (Sym2 V)))
    (hM : Hypergraph.IsMatching (jointSupports G) M) :
    (∑ S ∈ M, typedGain S) + M.card ≤ G.edgeFinset.card := by
  classical
  have hsum : (∑ S ∈ M, typedGain S) + M.card = ∑ S ∈ M, S.card := by
    calc (∑ S ∈ M, typedGain S) + M.card = ∑ S ∈ M, (typedGain S + 1) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      _ = ∑ S ∈ M, S.card :=
          Finset.sum_congr rfl (fun S hS => typedGain_add_one (hM.subset hS))
  rw [hsum]
  exact sum_card_le_edges M hM

end Obstructions

/-! ### El contraejemplo literal: `K₄` -/

section K4Counterexample

open scoped Classical

/-- El grafo completo en cuatro vértices: el testigo mínimo de que los brazos **no** se suman.
-/
abbrev G4 : SimpleGraph (Fin 4) := ⊤

theorem G4_edges_card : (SimpleGraph.edgeFinset G4).card = 6 := by decide

theorem triangle_mem_k3 : pairs ({0, 1, 2} : Finset (Fin 4)) ∈ k3Supports G4 := by
  refine mem_k3Supports.2 ⟨{0, 1, 2}, ⟨?_, ?_⟩, ?_, rfl⟩
  · decide
  · left; decide
  · decide

theorem square_mem_k4 : pairs (Finset.univ : Finset (Fin 4)) ∈ k4Supports G4 := by
  refine mem_k4Supports.2 ⟨Finset.univ, ⟨?_, ?_⟩, ?_, rfl⟩
  · decide
  · right; decide
  · decide

/-- **El atajo aditivo es falso.**  En `K₄` hay un matching triangular de tamaño `1` y un
matching de `K₄` de tamaño `1`; la receta aditiva promete ganancia `2·1 + 5·1 = 7`, pero
**todo** matching del hipergrafo conjunto tiene ganancia `≤ 5`.

La razón es la identidad de presupuesto `joint_gain_add_card_le`: el triángulo y el `K₄`
comparten aristas, y separar las aristas en dos brazos exclusivos sólo puede empeorar la
cuenta.  Por eso la puerta conjunta **no** se puede obtener sumando dos corridas uniformes. -/
theorem additive_shortcut_fails :
    ∃ M₃ M₄ : Finset (Finset (Sym2 (Fin 4))),
      Hypergraph.IsMatching (k3Supports G4) M₃ ∧
      Hypergraph.IsMatching (k4Supports G4) M₄ ∧
      M₃.card = 1 ∧ M₄.card = 1 ∧
      ∀ M : Finset (Finset (Sym2 (Fin 4))),
        Hypergraph.IsMatching (jointSupports G4) M →
        (∑ S ∈ M, typedGain S) < 2 * M₃.card + 5 * M₄.card := by
  classical
  refine ⟨{pairs ({0, 1, 2} : Finset (Fin 4))}, {pairs (Finset.univ : Finset (Fin 4))},
    ⟨by simpa using triangle_mem_k3, ?_⟩, ⟨by simpa using square_mem_k4, ?_⟩,
    Finset.card_singleton _, Finset.card_singleton _, ?_⟩
  · intro S hS T hT hST
    rw [Finset.mem_singleton] at hS hT
    exact absurd (hS.trans hT.symm) hST
  · intro S hS T hT hST
    rw [Finset.mem_singleton] at hS hT
    exact absurd (hS.trans hT.symm) hST
  · intro M hM
    have hbudget := joint_gain_add_card_le M hM
    rw [G4_edges_card] at hbudget
    rcases Finset.eq_empty_or_nonempty M with rfl | ⟨S, hS⟩
    · simp
    · have hpos : 1 ≤ M.card := Finset.card_pos.2 ⟨S, hS⟩
      rw [Finset.card_singleton, Finset.card_singleton]
      omega

end K4Counterexample

/-! ### La obstrucción al relleno (*padding*) -/

section Padding

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **Relleno fiel.**  `pad` agranda cada hiperarista de `F` hasta el rango `r₄` y **conserva
la disjunción**: es exactamente lo que hace falta para que un matching de la familia rellenada
se lea como un matching de la original y recíprocamente. -/
structure FaithfulPadding (F : Finset (Finset W)) (pad : Finset W → Finset W) (r₄ : ℕ) :
    Prop where
  subset : ∀ S ∈ F, S ⊆ pad S
  card : ∀ S ∈ F, (pad S).card = r₄
  faithful : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint S T → Disjoint (pad S) (pad T)

/-- **Obstrucción de capacidad al relleno dentro del mismo conjunto de recursos.**

Si `F` ya es un matching (piezas disjuntas) y admite un relleno fiel a rango `r₄`, entonces el
conjunto de recursos tiene que sostener `r₄·|F|` elementos, no los `r₃·|F|` reales.  Para
`r₃ = 3`, `r₄ = 6` eso es el **doble**: el relleno divide por dos la capacidad del gate, y por
tanto no puede certificar la componente triangular de la puerta conjunta. -/
theorem faithful_padding_capacity {F : Finset (Finset W)} {pad : Finset W → Finset W} {r₄ : ℕ}
    (hpad : FaithfulPadding F pad r₄)
    (hmatch : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint S T) :
    r₄ * F.card ≤ Fintype.card W := by
  classical
  have hdisj : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint (pad S) (pad T) :=
    fun S hS T hT hST => hpad.faithful S hS T hT hST (hmatch S hS T hT hST)
  have hbi : (F.biUnion pad).card = ∑ S ∈ F, (pad S).card := Finset.card_biUnion hdisj
  have hsum : ∑ S ∈ F, (pad S).card = r₄ * F.card := by
    rw [Finset.sum_congr rfl hpad.card, Finset.sum_const, smul_eq_mul, mul_comm]
  have hle : (F.biUnion pad).card ≤ Fintype.card W := Finset.card_le_univ _
  rw [hbi, hsum] at hle
  exact hle

/-- **Corolario: no hay relleno fiel cuando la capacidad se agota.**  Una familia disjunta de
`|F|` triángulos cabe siempre que `3|F| ≤ n`; si además `n < 6|F|`, ningún relleno fiel a
rango `6` existe. -/
theorem no_faithful_padding_of_capacity {F : Finset (Finset W)} {pad : Finset W → Finset W}
    (hmatch : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint S T)
    (hcap : Fintype.card W < 6 * F.card) :
    ¬ FaithfulPadding F pad 6 :=
  fun hpad => absurd (faithful_padding_capacity hpad hmatch) (by omega)

omit [Fintype W] in
/-- **Obstrucción de vivero al relleno con recursos ficticios.**  Si los elementos añadidos
salen de un vivero `P`, el vivero tiene que ser al menos tan grande como las aristas que se
quieren rellenar: `(r₄ − r₃)·|F| ≤ |P|`. -/
theorem padding_pool_lower_bound {F : Finset (Finset W)} {pad : Finset W → Finset W}
    {P : Finset W} {r₃ r₄ : ℕ}
    (hpad : FaithfulPadding F pad r₄)
    (hmatch : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint S T)
    (hrank : ∀ S ∈ F, S.card = r₃)
    (hpool : ∀ S ∈ F, pad S \ S ⊆ P) :
    (r₄ - r₃) * F.card ≤ P.card := by
  classical
  have hdisj : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint (pad S \ S) (pad T \ T) := by
    intro S hS T hT hST
    exact Finset.disjoint_of_subset_left (Finset.sdiff_subset)
      (Finset.disjoint_of_subset_right (Finset.sdiff_subset)
        (hpad.faithful S hS T hT hST (hmatch S hS T hT hST)))
  have hbi : (F.biUnion (fun S => pad S \ S)).card = ∑ S ∈ F, (pad S \ S).card :=
    Finset.card_biUnion hdisj
  have hcards : ∀ S ∈ F, (pad S \ S).card = r₄ - r₃ := by
    intro S hS
    rw [Finset.card_sdiff_of_subset (hpad.subset S hS), hpad.card S hS, hrank S hS]
  have hsub : F.biUnion (fun S => pad S \ S) ⊆ P := by
    intro x hx
    obtain ⟨S, hS, hxS⟩ := Finset.mem_biUnion.1 hx
    exact hpool S hS hxS
  have hle := Finset.card_le_card hsub
  rw [hbi, Finset.sum_congr rfl hcards, Finset.sum_const, smul_eq_mul, mul_comm] at hle
  exact hle

/-! #### El relleno con recursos privados destruye la hipótesis de grado -/

omit [Fintype W] in
/-- **Todo recurso ficticio es excepcional.**  Si un elemento `v` está en a lo sumo una
hiperarista del hipergrafo rellenado —que es lo que ocurre con los rellenos *privados*, los
únicos que conservan la disjunción en los dos sentidos— y la escala de grado real `(1−3u)D`
supera `1`, entonces `v` tiene que pertenecer al conjunto excepcional del nibble.

Es la obstrucción decisiva: el vivero entero cae dentro de `Exc`. -/
theorem private_padding_forces_exceptional {Hpad : Finset (Finset W)} {P Exc : Finset W}
    {D u : ℝ}
    (hpriv : ∀ v ∈ P, deg Hpad v ≤ 1)
    (hscale : 1 < (1 - 3 * u) * D)
    (hdeg : ∀ v : W, v ∉ Exc → (1 - 3 * u) * D ≤ (deg Hpad v : ℝ)) :
    P ⊆ Exc := by
  intro v hv
  by_contra hvE
  have h1 : (1 - 3 * u) * D ≤ (deg Hpad v : ℝ) := hdeg v hvE
  have h2 : (deg Hpad v : ℝ) ≤ 1 := by exact_mod_cast hpriv v hv
  linarith

/-- **Y eso mata la cota del excepcional.**  Con `|Exc| ≤ η·|W|`, `P ⊆ Exc` y un conjunto de
recursos de tamaño `n + |P|` (los reales más el vivero), el tamaño del vivero queda atrapado:
`(1−η)|P| ≤ η·n`.  Para `η < 1/2` esto obliga a `|P| < n`, mientras que un relleno privado de
todas las hiperaristas triangulares exige `|P| = 3·|H₃|`, que es del orden de `n` o mayor. -/
theorem private_pool_size_bound {n p : ℕ} {η : ℝ}
    (h : (p : ℝ) ≤ η * ((n : ℝ) + (p : ℝ))) :
    (1 - η) * (p : ℝ) ≤ η * (n : ℝ) := by
  nlinarith [h]

end Padding

end PaperIV.JointTypedNibbleGate

