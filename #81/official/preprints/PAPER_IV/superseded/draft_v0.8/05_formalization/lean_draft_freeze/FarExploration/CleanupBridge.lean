import FarExploration.CleanupLP
import FarExploration.CodegreeCleanup
import PaperIV.MixedRoundingAdapter

/-!
# El puente: el LP abstracto **contiene** al enunciado concreto

Este módulo demuestra que el modelo LP de `FarExploration.CleanupLP` es una generalización
**fiel** del enunciado `FarExploration.CodegreeCleanup.CodegreeCleanupAt`:

```
AbstractCleanupAt gam Cst m xi  →  CodegreeCleanupAt gam Cst m xi
```

La traducción es una biyección entre empaquetamientos fraccionales de `G` y soluciones
fraccionales del sistema de items `supports G`, que respeta el valor, la masa triangular y el
codegrado ponderado.  Por eso la refutación de `AbstractCleanupAt`
(`FarExploration.CleanupObstruction.not_abstractCleanupAt`) mide exactamente lo que un argumento
tiene que usar del grafo: si un argumento sólo usa las capacidades, los rangos, las ganancias,
el codegrado y la masa —es decir, el LP—, demostraría también el enunciado abstracto, que es
falso.
-/

namespace FarExploration.CleanupBridge

open Finset MixedRounding FarExploration.CleanupLP

section Translation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- La familia conjunta de soportes de `PaperIV` coincide con la de `MixedRounding`. -/
lemma jointSupports_eq_supports :
    PaperIV.JointTypedNibbleGate.jointSupports G = supports G := by
  rw [PaperIV.JointTypedNibbleGate.jointSupports_eq_image, supports,
    PaperIV.MixedRoundingAdapter.items_eq]
  rfl

/-- **El sistema de items de un grafo**: los soportes de sus copias de `K₃` y `K₄`. -/
def graphSystem (G : SimpleGraph V) [DecidableRel G.Adj] : ItemSystem (Sym2 V) where
  supports := supports G
  rank_mem := by
    intro S hS
    obtain ⟨K, hK, rfl⟩ := mem_supports.1 hS
    have e32 : Nat.choose 3 2 = 3 := by decide
    have e42 : Nat.choose 4 2 = 6 := by decide
    rcases hK.2 with h3 | h4
    · exact Or.inl (by rw [card_pairs, h3, e32])
    · exact Or.inr (by rw [card_pairs, h4, e42])

@[simp] lemma graphSystem_supports :
    (graphSystem G).supports = supports G := rfl

/-- Reindexación: sumar sobre soportes filtrados es sumar sobre items filtrados. -/
lemma sum_supports_filter {M : Type*} [AddCommMonoid M] (p : Finset (Sym2 V) → Prop)
    [DecidablePred p] (g : Finset (Sym2 V) → M) :
    ∑ S ∈ (supports G).filter p, g S
      = ∑ K ∈ (items G).filter (fun K => p (pairs K)), g (pairs K) := by
  classical
  rw [supports, Finset.filter_image]
  refine Finset.sum_image ?_
  intro K hK L hL h
  exact pairs_injOn_items (mem_items.1 (Finset.mem_filter.1 hK).1)
    (mem_items.1 (Finset.mem_filter.1 hL).1) h

/-- Sumar sobre todos los soportes es sumar sobre todos los items. -/
lemma sum_supports {M : Type*} [AddCommMonoid M] (g : Finset (Sym2 V) → M) :
    ∑ S ∈ supports G, g S = ∑ K ∈ items G, g (pairs K) := by
  classical
  rw [supports]
  refine Finset.sum_image ?_
  intro K hK L hL h
  exact pairs_injOn_items (mem_items.1 hK) (mem_items.1 hL) h

omit [DecidableRel G.Adj] in
/-- La ganancia abstracta de un soporte es la ganancia del item. -/
lemma gainOfSupport_pairs {K : Finset V} (hK : IsItem G K) :
    gainOfSupport (pairs K) = gainF ℚ K := by
  have e32 : Nat.choose 3 2 = 3 := by decide
  have e42 : Nat.choose 4 2 = 6 := by decide
  rcases hK.2 with h3 | h4
  · rw [gainOfSupport, if_pos (by rw [card_pairs, h3, e32]), gainF, h3, e32]
    norm_num
  · rw [gainOfSupport, if_neg (by rw [card_pairs, h4, e42]; norm_num), gainF, h4, e42]
    norm_num

omit [DecidableRel G.Adj] in
/-- El rango `3` del soporte caracteriza los triángulos. -/
lemma card_pairs_eq_three_iff {K : Finset V} (hK : IsItem G K) :
    (pairs K).card = 3 ↔ K.card = 3 := by
  have e32 : Nat.choose 3 2 = 3 := by decide
  have e42 : Nat.choose 4 2 = 6 := by decide
  rcases hK.2 with h3 | h4
  · rw [card_pairs, h3, e32]
  · rw [card_pairs, h4, e42]
    decide

/-! ## De solución abstracta a empaquetamiento -/

/-- Un peso abstracto sobre `graphSystem G` es un empaquetamiento fraccional de `G`. -/
def toPacking (y : Frac (graphSystem G)) : FracPacking G where
  weight := fun K => if K ∈ items G then y.w (pairs K) else 0
  weight_nonneg := by
    intro K
    by_cases hK : K ∈ items G <;> simp [hK, y.nonneg]
  capacity := by
    intro e _
    classical
    have hrw : ∑ K ∈ items G, (if e ∈ pairs K then (if K ∈ items G then y.w (pairs K) else 0)
        else 0) = ∑ K ∈ (items G).filter (fun K => e ∈ pairs K), y.w (pairs K) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun K hK => ?_
      by_cases he : e ∈ pairs K <;> simp [he, hK]
    rw [hrw, ← sum_supports_filter (fun S => e ∈ S) y.w]
    exact y.capacity e

@[simp] lemma toPacking_weight (y : Frac (graphSystem G)) (K : Finset V) :
    (toPacking y).weight K = if K ∈ items G then y.w (pairs K) else 0 := rfl

lemma toPacking_value (y : Frac (graphSystem G)) : (toPacking y).value = y.value := by
  classical
  rw [FracPacking.value, Frac.value, graphSystem_supports,
    sum_supports (fun S => gainOfSupport S * y.w S)]
  refine Finset.sum_congr rfl fun K hK => ?_
  rw [gainOfSupport_pairs (mem_items.1 hK), toPacking_weight, if_pos hK]

lemma toPacking_massQ (y : Frac (graphSystem G)) :
    ∑ K ∈ (items G).filter (fun K => K.card = 3), (toPacking y).weight K = y.mass := by
  classical
  rw [Frac.mass, graphSystem_supports, sum_supports_filter (fun S => S.card = 3) y.w]
  refine Finset.sum_congr ?_ ?_
  · exact Finset.filter_congr fun K hK => (card_pairs_eq_three_iff (mem_items.1 hK)).symm
  · intro K hK
    rw [toPacking_weight, if_pos (Finset.mem_filter.1 hK).1]

lemma toPacking_mass (y : Frac (graphSystem G)) :
    PaperIV.JointTwoQuotaPhysical.triangleMass (toPacking y) = ((y.mass : ℚ) : ℝ) := by
  classical
  rw [PaperIV.JointTwoQuotaPhysical.triangleMass, ← toPacking_massQ y, Rat.cast_sum]

lemma toPacking_codegQ (y : Frac (graphSystem G)) (e f : Sym2 V) :
    ∑ K ∈ (items G).filter (fun K => e ∈ pairs K ∧ f ∈ pairs K), (toPacking y).weight K
      = y.codeg e f := by
  classical
  rw [Frac.codeg, graphSystem_supports,
    sum_supports_filter (fun S => e ∈ S ∧ f ∈ S) y.w]
  refine Finset.sum_congr rfl fun K hK => ?_
  rw [toPacking_weight, if_pos (Finset.mem_filter.1 hK).1]

lemma toPacking_codeg (y : Frac (graphSystem G)) (e f : Sym2 V) :
    ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter
        (fun S => e ∈ S ∧ f ∈ S), inducedWeight (toPacking y) S
      = ((y.codeg e f : ℚ) : ℝ) := by
  classical
  rw [jointSupports_eq_supports (G := G),
    sum_supports_filter (M := ℝ) (fun S => e ∈ S ∧ f ∈ S)
      (fun S => inducedWeight (toPacking y) S),
    ← toPacking_codegQ y e f, Rat.cast_sum]
  refine Finset.sum_congr rfl fun K hK => ?_
  exact inducedWeight_pairs (toPacking y) (mem_items.1 (Finset.mem_filter.1 hK).1)

/-! ## De empaquetamiento a solución abstracta -/

/-- Un empaquetamiento fraccional de `G` es un peso abstracto sobre `graphSystem G`. -/
def ofPacking (x : FracPacking G) : Frac (graphSystem G) where
  w := fun S => if S ∈ supports G then x.weight (cliqueOf S) else 0
  nonneg := by
    intro S
    by_cases hS : S ∈ supports G <;> simp [hS, x.weight_nonneg]
  capacity := by
    intro e
    classical
    have hrw : ∑ S ∈ (graphSystem G).supports.filter (fun S => e ∈ S),
          (if S ∈ supports G then x.weight (cliqueOf S) else 0)
        = ∑ K ∈ (items G).filter (fun K => e ∈ pairs K), x.weight K := by
      rw [graphSystem_supports,
        sum_supports_filter (fun S => e ∈ S) (fun S => if S ∈ supports G then
          x.weight (cliqueOf S) else 0)]
      refine Finset.sum_congr rfl fun K hK => ?_
      have hK' : K ∈ items G := (Finset.mem_filter.1 hK).1
      have hmem : pairs K ∈ supports G := Finset.mem_image.2 ⟨K, hK', rfl⟩
      rw [if_pos hmem, cliqueOf_pairs (two_le_card_of_isItem (mem_items.1 hK'))]
    rw [hrw]
    by_cases he : e ∈ G.edgeFinset
    · have hcap := x.capacity e he
      rw [Finset.sum_filter]
      exact le_trans (le_of_eq (Finset.sum_congr rfl fun K _ => rfl)) hcap
    · have hempty : (items G).filter (fun K => e ∈ pairs K) = ∅ := by
        refine Finset.filter_false_of_mem fun K hK hmem => he ?_
        exact pairs_subset_edgeFinset (mem_items.1 hK) hmem
      rw [hempty, Finset.sum_empty]
      norm_num

@[simp] lemma ofPacking_w (x : FracPacking G) (S : Finset (Sym2 V)) :
    (ofPacking x).w S = if S ∈ supports G then x.weight (cliqueOf S) else 0 := rfl

lemma ofPacking_value (x : FracPacking G) : (ofPacking x).value = x.value := by
  classical
  rw [Frac.value, FracPacking.value, graphSystem_supports,
    sum_supports (fun S => gainOfSupport S * (ofPacking x).w S)]
  refine Finset.sum_congr rfl fun K hK => ?_
  have hmem : pairs K ∈ supports G := Finset.mem_image.2 ⟨K, hK, rfl⟩
  rw [gainOfSupport_pairs (mem_items.1 hK), ofPacking_w, if_pos hmem,
    cliqueOf_pairs (two_le_card_of_isItem (mem_items.1 hK))]

lemma ofPacking_massQ (x : FracPacking G) :
    (ofPacking x).mass = ∑ K ∈ (items G).filter (fun K => K.card = 3), x.weight K := by
  classical
  rw [Frac.mass, graphSystem_supports,
    sum_supports_filter (fun S => S.card = 3) (fun S => (ofPacking x).w S)]
  refine Finset.sum_congr ?_ ?_
  · exact Finset.filter_congr fun K hK => card_pairs_eq_three_iff (mem_items.1 hK)
  · intro K hK
    have hK' : K ∈ items G := (Finset.mem_filter.1 hK).1
    have hmem : pairs K ∈ supports G := Finset.mem_image.2 ⟨K, hK', rfl⟩
    rw [ofPacking_w, if_pos hmem, cliqueOf_pairs (two_le_card_of_isItem (mem_items.1 hK'))]

lemma ofPacking_codeg (x : FracPacking G) (e f : Sym2 V) :
    ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter
        (fun S => e ∈ S ∧ f ∈ S), inducedWeight x S
      = (((ofPacking x).codeg e f : ℚ) : ℝ) := by
  classical
  rw [Frac.codeg, graphSystem_supports, jointSupports_eq_supports (G := G), Rat.cast_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hS' : S ∈ supports G := (Finset.mem_filter.1 hS).1
  rw [ofPacking_w, if_pos hS', inducedWeight, if_pos hS']

lemma ofPacking_mass (x : FracPacking G) :
    ((((ofPacking x).mass : ℚ)) : ℝ) = PaperIV.JointTwoQuotaPhysical.triangleMass x := by
  classical
  rw [ofPacking_massQ, PaperIV.JointTwoQuotaPhysical.triangleMass, Rat.cast_sum]

end Translation

/-! ## El puente -/

/-- **El LP abstracto implica el enunciado concreto.**  Todo lo que la limpieza pide de `G` está
ya escrito en el sistema de items: capacidades, rangos, ganancias, codegrado y masa. -/
theorem codegreeCleanupAt_of_abstract (gam Cst : ℝ) (m xi : ℚ)
    (h : AbstractCleanupAt gam Cst m xi) :
    FarExploration.CodegreeCleanup.CodegreeCleanupAt gam Cst m xi := by
  classical
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro n hn G _ x hmass
  have hmass' : (m : ℝ) * (n : ℝ) ^ 2 - 1 ≤ (((ofPacking x).mass : ℚ) : ℝ) := by
    rw [ofPacking_mass]; exact hmass
  obtain ⟨y, hcod, hy_mass, hy_val⟩ := hN n hn (graphSystem G) (ofPacking x) hmass'
  refine ⟨toPacking y, ?_, ?_, ?_⟩
  · intro e f hef
    rw [toPacking_codeg]
    exact hcod e f hef
  · rw [toPacking_mass]; exact hy_mass
  · rw [toPacking_value, ← ofPacking_value x]; exact hy_val

end FarExploration.CleanupBridge
