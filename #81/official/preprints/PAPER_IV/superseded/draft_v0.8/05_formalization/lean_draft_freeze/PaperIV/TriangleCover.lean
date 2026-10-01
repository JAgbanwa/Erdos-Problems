import MixedRounding.Lift

/-!
# El lado difícil de la dicotomía: pocos triángulos ⟹ el valor es `O(1)`

El régimen degenerado del Corolario 7.3a —`triMass x ≤ C`— parecía el peor, porque el gate con
holgura no se le aplica (pide `C ≤ triangleMass`) y el redondeo de un brazo sigue pidiendo tres
estimaciones. Este módulo lo cierra **sin ninguna de las tres**, y sin nibble.

## El argumento, que es un dual factible

Tómese una familia de triángulos aristo-disjuntos **maximal** `F`, de tamaño `ν`. Entonces:

* por maximalidad, **todo** triángulo de `G` comparte una arista con algún miembro de `F`, o sea
  contiene una de las `3ν` aristas de la cobertura `coverOf F`;
* todo `K₄` contiene un triángulo, luego también contiene una de esas aristas;
* luego la asignación `y_e = 5` sobre la cobertura y `0` fuera es **dual factible**: cada item
  `K` cumple `∑_{e ∈ K} y_e ≥ 5 ≥ gainF K`;
* y dualidad débil da `x.value ≤ 5·|coverOf F| ≤ 15·ν`.

Si `ν ≤ C` eso es `O(1)`, y el **packing vacío** ya satisface el objetivo. No hace falta redondear
nada: en este régimen no hay nada que redondear.

Certificado aparte, `checks/dichotomy_cover_dual.py`: en `K₅` la familia maximal tiene `ν = 2`,
la cota da `30`, y el óptimo real del LP mixto es `25/3`, con gap de integralidad `10/3`. La cota
es holgada, que es justo lo que el régimen pide.

## Dónde **no** hay circularidad

La tentación es pensar que «todo triángulo toca la cobertura» es un resultado de tipo
Haxell–Rödl. No lo es: sale de la definición de maximalidad, y el paso siguiente es capacidad
LP **arista a arista**, no un teorema de empaquetamiento. Nada de esto usa el nibble.

## La disjunción no se usa para la cota

`MaximalTriFamily.disj` está en la estructura porque es lo que hace de `ν` el invariante del
régimen, pero la cota de abajo **no la consume**: cualquier familia maximal de triángulos,
disjunta o no, da el mismo `5·|coverOf F|`. Lo anoto para que nadie busque el uso que no está.
-/

namespace PaperIV.TriangleCover

open Finset
open MixedRounding

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. Una cobertura por aristas, y la dualidad débil que produce -/

/-- Un conjunto de aristas **toca todo item**: cada `K₃` y cada `K₄` de `G` contiene alguna. -/
def CoversItems (G : SimpleGraph V) [DecidableRel G.Adj] (Ecov : Finset (Sym2 V)) : Prop :=
  ∀ K ∈ items G, ∃ e ∈ Ecov, e ∈ pairs K

/-- **La masa total está acotada por el tamaño de la cobertura.**

Es dualidad débil con `y_e = 1` sobre la cobertura: cada item se carga a al menos una arista de
`Ecov`, y cada arista soporta carga `≤ 1` por la capacidad del LP. -/
theorem sum_weight_le_card (x : FracPacking G) {Ecov : Finset (Sym2 V)}
    (hsub : Ecov ⊆ G.edgeFinset) (hcov : CoversItems G Ecov) :
    ∑ K ∈ items G, x.weight K ≤ (Ecov.card : ℚ) := by
  classical
  have step : ∀ K ∈ items G,
      x.weight K ≤ ∑ e ∈ Ecov, (if e ∈ pairs K then x.weight K else 0) := by
    intro K hK
    obtain ⟨e₀, he₀, hmem⟩ := hcov K hK
    have hnn : ∀ e ∈ Ecov, (0 : ℚ) ≤ if e ∈ pairs K then x.weight K else 0 := by
      intro e _
      split_ifs with h
      · exact x.weight_nonneg K
      · exact le_refl 0
    calc x.weight K = (if e₀ ∈ pairs K then x.weight K else 0) := by rw [if_pos hmem]
      _ ≤ ∑ e ∈ Ecov, (if e ∈ pairs K then x.weight K else 0) :=
          Finset.single_le_sum hnn he₀
  calc ∑ K ∈ items G, x.weight K
      ≤ ∑ K ∈ items G, ∑ e ∈ Ecov, (if e ∈ pairs K then x.weight K else 0) :=
        Finset.sum_le_sum step
    _ = ∑ e ∈ Ecov, ∑ K ∈ items G, (if e ∈ pairs K then x.weight K else 0) :=
        Finset.sum_comm
    _ ≤ ∑ e ∈ Ecov, 1 := Finset.sum_le_sum (fun e he => x.capacity e (hsub he))
    _ = (Ecov.card : ℚ) := by simp

/-- **El valor está acotado por `5·|cobertura|`.**  Es la misma dualidad débil con `y_e = 5`:
la ganancia de un item nunca pasa de `5`. -/
theorem value_le_of_cover (x : FracPacking G) {Ecov : Finset (Sym2 V)}
    (hsub : Ecov ⊆ G.edgeFinset) (hcov : CoversItems G Ecov) :
    x.value ≤ 5 * (Ecov.card : ℚ) := by
  classical
  have h1 : x.value ≤ 5 * ∑ K ∈ items G, x.weight K := by
    rw [FracPacking.value, Finset.mul_sum]
    refine Finset.sum_le_sum (fun K hK => ?_)
    exact mul_le_mul_of_nonneg_right (gainF_le_five (mem_items.1 hK)) (x.weight_nonneg K)
  have h2 := sum_weight_le_card x hsub hcov
  linarith

/-! ## 2. La cobertura de una familia de triángulos -/

/-- Las aristas que una familia de items ocupa. -/
def coverOf (F : Finset (Finset V)) : Finset (Sym2 V) := F.biUnion pairs

/-- Una familia de `ν` triángulos ocupa a lo más `3ν` aristas. -/
theorem card_coverOf_le {F : Finset (Finset V)} (h3 : ∀ K ∈ F, K.card = 3) :
    (coverOf F).card ≤ 3 * F.card := by
  classical
  calc (coverOf F).card ≤ ∑ K ∈ F, (pairs K).card := Finset.card_biUnion_le
    _ = ∑ K ∈ F, 3 := Finset.sum_congr rfl (fun K hK => by rw [card_pairs, h3 K hK]; decide)
    _ = 3 * F.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Una familia maximal de triángulos aristo-disjuntos.**

`maximal` es la condición de verdad: si un triángulo es aristo-disjunto de todos los miembros,
ya estaba dentro. De ahí —y sólo de ahí— sale que la cobertura toca todo triángulo. -/
structure MaximalTriFamily (G : SimpleGraph V) [DecidableRel G.Adj] where
  fam : Finset (Finset V)
  isTri : ∀ K ∈ fam, IsItem G K
  card_three : ∀ K ∈ fam, K.card = 3
  disj : ∀ K ∈ fam, ∀ L ∈ fam, K ≠ L → Disjoint (pairs K) (pairs L)
  maximal : ∀ T, IsItem G T → T.card = 3 →
    (∀ K ∈ fam, Disjoint (pairs T) (pairs K)) → T ∈ fam

/-- **Todo triángulo toca la cobertura.**  Es maximalidad, nada más: si no la tocase sería
aristo-disjunto de toda la familia, luego estaría dentro, luego sus aristas estarían en la
cobertura — y un triángulo tiene aristas. -/
theorem meets_cover (F : MaximalTriFamily G) {T : Finset V}
    (hT : IsItem G T) (hT3 : T.card = 3) :
    ∃ e ∈ coverOf F.fam, e ∈ pairs T := by
  classical
  by_contra hcon
  push_neg at hcon
  have hdisj : ∀ K ∈ F.fam, Disjoint (pairs T) (pairs K) := by
    intro K hK
    rw [Finset.disjoint_right]
    intro e heK heT
    exact hcon e (Finset.mem_biUnion.2 ⟨K, hK, heK⟩) heT
  have hmem : T ∈ F.fam := F.maximal T hT hT3 hdisj
  have hne : (pairs T).Nonempty := by
    rw [← Finset.card_pos, card_pairs, hT3]
    decide
  obtain ⟨e, he⟩ := hne
  exact hcon e (Finset.mem_biUnion.2 ⟨T, hmem, he⟩) he

/-! ## 3. De los triángulos a todos los items -/

/-- Un subconjunto de un item hereda ser clique; con tres vértices, es un triángulo. -/
theorem exists_tri_subset {K : Finset V} (hK : IsItem G K) :
    ∃ T ⊆ K, IsItem G T ∧ T.card = 3 := by
  classical
  have h3 : 3 ≤ K.card := by rcases hK.2 with h | h <;> omega
  obtain ⟨T, hTK, hT3⟩ := Finset.exists_subset_card_eq h3
  exact ⟨T, hTK, ⟨fun a ha b hb hab => hK.1 a (hTK ha) b (hTK hb) hab, Or.inl hT3⟩, hT3⟩

/-- Las aristas de un subconjunto son aristas del conjunto. -/
theorem pairs_mono {T K : Finset V} (h : T ⊆ K) : pairs T ⊆ pairs K := by
  intro e he
  rw [mem_pairs] at he ⊢
  exact ⟨fun a ha => h (he.1 a ha), he.2⟩

/-- **La cobertura de una familia maximal toca todo item**, `K₄` incluidos: un `K₄` contiene un
triángulo, y el triángulo toca la cobertura. -/
theorem coversItems_coverOf (F : MaximalTriFamily G) : CoversItems G (coverOf F.fam) := by
  intro K hK
  obtain ⟨T, hTK, hT, hT3⟩ := exists_tri_subset (mem_items.1 hK)
  obtain ⟨e, hecov, heT⟩ := meets_cover F hT hT3
  exact ⟨e, hecov, pairs_mono hTK heT⟩

/-- La cobertura son aristas de verdad de `G`. -/
theorem coverOf_subset_edgeFinset (F : MaximalTriFamily G) :
    coverOf F.fam ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨K, hK, heK⟩ := Finset.mem_biUnion.1 he
  exact pairs_subset_edgeFinset (F.isTri K hK) heK

/-- **El lado difícil de la dicotomía.**  Con una familia maximal de `ν` triángulos
aristo-disjuntos, **todo** empaquetamiento fraccional cumple `x.value ≤ 15ν`.

Sin nibble, sin regularidad, sin excepcional: dualidad débil contra `3ν` aristas. -/
theorem value_le_of_maximal (F : MaximalTriFamily G) (x : FracPacking G) :
    x.value ≤ 15 * (F.fam.card : ℚ) := by
  have h := value_le_of_cover x (coverOf_subset_edgeFinset F) (coversItems_coverOf F)
  have hc : ((coverOf F.fam).card : ℚ) ≤ 3 * (F.fam.card : ℚ) := by
    exact_mod_cast card_coverOf_le F.card_three
  linarith

/-! ## 4. El objetivo, con el packing vacío -/

/-- El empaquetamiento vacío. -/
def emptyPacking (G : SimpleGraph V) [DecidableRel G.Adj] : Packing G where
  pieces := ∅
  isItem := by simp
  edgeDisjoint := by simp

@[simp] theorem emptyPacking_gain : (emptyPacking G).gain = 0 := by
  simp [Packing.gain, emptyPacking]

/-- **El régimen degenerado, cerrado.**  Si la familia maximal tiene a lo más `C` triángulos y
`15C ≤ ε n²`, el packing **vacío** ya alcanza el objetivo del Corolario 7.3a.

No queda ninguna de las tres estimaciones que `round_arm_four` pedía. -/
theorem target_of_small_family {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (F : MaximalTriFamily G) (x : FracPacking G) {C ε : ℚ}
    (hF : (F.fam.card : ℚ) ≤ C) (hCε : 15 * C ≤ ε * (n : ℚ) ^ 2) :
    ∃ P : Packing G, x.value - (P.gain : ℚ) ≤ ε * (n : ℚ) ^ 2 := by
  refine ⟨emptyPacking G, ?_⟩
  rw [emptyPacking_gain]
  have h := value_le_of_maximal F x
  push_cast
  linarith


/-! ## 5. La familia maximal existe, luego la dicotomía no tiene hipótesis -/

/-- Una familia de triángulos aristo-disjuntos. -/
def IsTriFamily (G : SimpleGraph V) [DecidableRel G.Adj] (F : Finset (Finset V)) : Prop :=
  (∀ K ∈ F, IsItem G K) ∧ (∀ K ∈ F, K.card = 3) ∧
    (∀ K ∈ F, ∀ L ∈ F, K ≠ L → Disjoint (pairs K) (pairs L))

/-- **Existe una familia maximal.**  Basta una de **cardinal máximo**: todo es finito, y si un
triángulo fuese aristo-disjunto de todos sus miembros se podría añadir, contradiciendo el
máximo. No hace falta Zorn ni elección más allá de la que Mathlib ya usa. -/
theorem exists_maximalTriFamily (G : SimpleGraph V) [DecidableRel G.Adj] :
    Nonempty (MaximalTriFamily G) := by
  classical
  have hne : ((Finset.univ : Finset (Finset (Finset V))).filter (IsTriFamily G)).Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨by simp, by simp, by simp⟩⟩⟩
  obtain ⟨F, hFmem, hFmax⟩ := Finset.exists_max_image _ Finset.card hne
  obtain ⟨-, hitem, hcard3, hdisj⟩ := Finset.mem_filter.1 hFmem
  refine ⟨⟨F, hitem, hcard3, hdisj, ?_⟩⟩
  intro T hT hT3 hTd
  by_contra hTF
  have hvalid : IsTriFamily G (insert T F) := by
    refine ⟨?_, ?_, ?_⟩
    · intro K hK
      rcases Finset.mem_insert.1 hK with rfl | hK'
      · exact hT
      · exact hitem K hK'
    · intro K hK
      rcases Finset.mem_insert.1 hK with rfl | hK'
      · exact hT3
      · exact hcard3 K hK'
    · intro K hK L hL hKL
      rcases Finset.mem_insert.1 hK with rfl | hK' <;>
        rcases Finset.mem_insert.1 hL with rfl | hL'
      · exact absurd rfl hKL
      · exact hTd L hL'
      · exact (hTd K hK').symm
      · exact hdisj K hK' L hL' hKL
  have hle := hFmax (insert T F) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hvalid⟩)
  rw [Finset.card_insert_of_notMem hTF] at hle
  omega

/-- **La dicotomía, sin ninguna hipótesis.**

Para todo `C`: o `G` tiene `C` triángulos aristo-disjuntos —y entonces vale el lado fácil, que
empaqueta esos triángulos—, o **todo** empaquetamiento fraccional vale a lo más `15C`.

Es el enunciado que el régimen degenerado del Corolario 7.3a necesitaba, y no pide nada. -/
theorem many_disjoint_or_value_le (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℕ) :
    (∃ F : Finset (Finset V), IsTriFamily G F ∧ C ≤ F.card) ∨
      (∀ x : FracPacking G, x.value ≤ 15 * (C : ℚ)) := by
  classical
  obtain ⟨F⟩ := exists_maximalTriFamily G
  by_cases hC : C ≤ F.fam.card
  · exact Or.inl ⟨F.fam, ⟨F.isTri, F.card_three, F.disj⟩, hC⟩
  · refine Or.inr (fun x => ?_)
    have h := value_le_of_maximal F x
    have hcast : (F.fam.card : ℚ) ≤ (C : ℚ) := by
      have : F.fam.card ≤ C := by omega
      exact_mod_cast this
    linarith

end PaperIV.TriangleCover
