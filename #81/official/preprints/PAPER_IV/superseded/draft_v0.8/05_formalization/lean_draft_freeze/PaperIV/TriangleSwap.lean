import PaperIV.TriangleCover
import PaperIV.LowTriangleReduction

/-!
# El otro lado de la dicotomía: muchos triángulos ⟹ se puede sustituir `x`

`PaperIV.TriangleCover.many_disjoint_or_value_le` parte el régimen degenerado en dos. El lado de
«pocos triángulos» ya está cerrado allí. Éste es el otro, y conviene decir de entrada **por qué
no cierra de la manera obvia**:

> si `G` tiene `C` triángulos aristo-disjuntos, empaquetarlos da `P.gain = 2C` — y eso **no**
> acota `x.value − P.gain`, porque `x.value` puede ser del orden de `n²`.

Lo que el lado fácil da no es un packing: es el permiso para **sustituir `x`**.

## La sustitución

Con `F` una familia de `C` triángulos aristo-disjuntos y `Ecov = coverOf F` sus `3C` aristas:

```
x″(K)  =  1              si K ∈ F
       =  0              si K toca Ecov y no está en F
       =  x(K)           si K no toca Ecov
```

* **es legal** (`swap_capacity`): sobre una arista de `Ecov` sólo carga el único miembro de `F`
  que la contiene —aquí, y sólo aquí, se usa la disjunción—; fuera de `Ecov` la carga es una
  subsuma de la de `x`;
* **tiene masa triangular `≥ C`** (`card_le_triMass_swap`), que es justo lo que el gate con
  holgura pide y `x` no daba;
* y **cuesta a lo más `13C`** (`value_swap_ge`): se pierden `≤ 15C` por dualidad débil contra
  `Ecov` —el mismo lema del lado difícil— y se ganan `2C` con los triángulos.

Así que el régimen degenerado no necesita `round_arm_four` ni sus tres estimaciones por ningún
lado: o el valor ya es `O(1)`, o se sustituye por `13C` y se entra al gate.
-/

namespace PaperIV.TriangleSwap

open Finset
open MixedRounding
open PaperIV.TriangleCover

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. Dualidad débil sobre un subconjunto de items -/

/-- Las aristas de una familia de triángulos son aristas de `G`. -/
theorem coverOf_subset_edgeFinset' {F : Finset (Finset V)} (hF : IsTriFamily G F) :
    coverOf F ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨K, hK, heK⟩ := Finset.mem_biUnion.1 he
  exact pairs_subset_edgeFinset (hF.1 K hK) heK

/-- **La masa de los items que tocan una cobertura está acotada por su tamaño.**

Es `TriangleCover.sum_weight_le_card` sobre un subconjunto: la única diferencia es que la
capacidad se aplica a la suma sobre **todos** los items, que es mayor. -/
theorem sum_weight_meeting_le (x : FracPacking G) {Ecov : Finset (Sym2 V)}
    (hsub : Ecov ⊆ G.edgeFinset) {S : Finset (Finset V)} (hS : S ⊆ items G)
    (hmeet : ∀ K ∈ S, ∃ e ∈ Ecov, e ∈ pairs K) :
    ∑ K ∈ S, x.weight K ≤ (Ecov.card : ℚ) := by
  classical
  have hnn : ∀ (K : Finset V), ∀ e ∈ Ecov, (0 : ℚ) ≤ if e ∈ pairs K then x.weight K else 0 := by
    intro K e _
    split_ifs with h
    · exact x.weight_nonneg K
    · exact le_refl 0
  have step : ∀ K ∈ S, x.weight K ≤ ∑ e ∈ Ecov, (if e ∈ pairs K then x.weight K else 0) := by
    intro K hK
    obtain ⟨e₀, he₀, hmem⟩ := hmeet K hK
    calc x.weight K = (if e₀ ∈ pairs K then x.weight K else 0) := by rw [if_pos hmem]
      _ ≤ ∑ e ∈ Ecov, (if e ∈ pairs K then x.weight K else 0) :=
          Finset.single_le_sum (hnn K) he₀
  calc ∑ K ∈ S, x.weight K
      ≤ ∑ K ∈ S, ∑ e ∈ Ecov, (if e ∈ pairs K then x.weight K else 0) :=
        Finset.sum_le_sum step
    _ = ∑ e ∈ Ecov, ∑ K ∈ S, (if e ∈ pairs K then x.weight K else 0) := Finset.sum_comm
    _ ≤ ∑ e ∈ Ecov, ∑ K ∈ items G, (if e ∈ pairs K then x.weight K else 0) := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        refine Finset.sum_le_sum_of_subset_of_nonneg hS (fun K _ _ => ?_)
        split_ifs with h
        · exact x.weight_nonneg K
        · exact le_refl 0
    _ ≤ ∑ e ∈ Ecov, 1 := Finset.sum_le_sum (fun e he => x.capacity e (hsub he))
    _ = (Ecov.card : ℚ) := by simp

/-- Un subconjunto de una familia de triángulos aristo-disjuntos lo sigue siendo. -/
theorem isTriFamily_subset {F F₀ : Finset (Finset V)} (hF : IsTriFamily G F) (h : F₀ ⊆ F) :
    IsTriFamily G F₀ :=
  ⟨fun K hK => hF.1 K (h hK), fun K hK => hF.2.1 K (h hK),
    fun K hK L hL hKL => hF.2.2 K (h hK) L (h hL) hKL⟩

/-! ## 2. La sustitución -/

/-- Los items que tocan la cobertura de `F`. -/
noncomputable def meeting (G : SimpleGraph V) [DecidableRel G.Adj] (F : Finset (Finset V)) :
    Finset (Finset V) :=
  (items G).filter (fun K => (pairs K ∩ coverOf F).Nonempty)

/-- **El peso sustituido.**  Uno sobre los triángulos de `F`, cero sobre lo demás que toca su
cobertura, y `x` intacto fuera. -/
noncomputable def swapWeight (x : FracPacking G) (F : Finset (Finset V)) (K : Finset V) : ℚ :=
  if (pairs K ∩ coverOf F).Nonempty then (if K ∈ F then 1 else 0) else x.weight K

theorem swapWeight_nonneg (x : FracPacking G) (F : Finset (Finset V)) (K : Finset V) :
    0 ≤ swapWeight x F K := by
  simp only [swapWeight]
  split_ifs
  · norm_num
  · norm_num
  · exact x.weight_nonneg K

/-- **La sustitución es legal.**

Sobre una arista de la cobertura carga exactamente los miembros de `F` que la contienen, y por
**aristo-disjunción** hay a lo más uno. Fuera de la cobertura ningún miembro de `F` aparece, y lo
que queda es una subsuma de la carga de `x`. -/
theorem swap_capacity (x : FracPacking G) {F : Finset (Finset V)} (hF : IsTriFamily G F)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    ∑ K ∈ items G, (if e ∈ pairs K then swapWeight x F K else 0) ≤ 1 := by
  classical
  by_cases hcov : e ∈ coverOf F
  · have hterm : ∀ K ∈ items G,
        (if e ∈ pairs K then swapWeight x F K else 0)
          = (if (e ∈ pairs K ∧ K ∈ F) then (1 : ℚ) else 0) := by
      intro K _
      by_cases hK : e ∈ pairs K
      · have hne : (pairs K ∩ coverOf F).Nonempty := ⟨e, Finset.mem_inter.2 ⟨hK, hcov⟩⟩
        simp only [swapWeight, if_pos hK, if_pos hne]
        by_cases hKF : K ∈ F
        · rw [if_pos hKF, if_pos ⟨hK, hKF⟩]
        · rw [if_neg hKF, if_neg (fun h : e ∈ pairs K ∧ K ∈ F => hKF h.2)]
      · rw [if_neg hK, if_neg (fun h : e ∈ pairs K ∧ K ∈ F => hK h.1)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
    have hone : ((items G).filter (fun K => e ∈ pairs K ∧ K ∈ F)).card ≤ 1 := by
      refine Finset.card_le_one.2 (fun a ha b hb => ?_)
      obtain ⟨-, hae, haF⟩ := Finset.mem_filter.1 ha
      obtain ⟨-, hbe, hbF⟩ := Finset.mem_filter.1 hb
      by_contra hab
      exact (Finset.disjoint_left.1 (hF.2.2 a haF b hbF hab)) hae hbe
    exact_mod_cast hone
  · have hterm : ∀ K ∈ items G,
        (if e ∈ pairs K then swapWeight x F K else 0)
          ≤ (if e ∈ pairs K then x.weight K else 0) := by
      intro K _
      by_cases hK : e ∈ pairs K
      · rw [if_pos hK, if_pos hK]
        simp only [swapWeight]
        split_ifs with h1 h2
        · exact absurd (Finset.mem_biUnion.2 ⟨K, h2, hK⟩) hcov
        · exact x.weight_nonneg K
        · exact le_refl _
      · rw [if_neg hK, if_neg hK]
    exact le_trans (Finset.sum_le_sum hterm) (x.capacity e he)

/-- **`x″`**, el empaquetamiento sustituido. -/
noncomputable def swapPacking (x : FracPacking G) {F : Finset (Finset V)}
    (hF : IsTriFamily G F) : FracPacking G where
  weight := swapWeight x F
  weight_nonneg := swapWeight_nonneg x F
  capacity := swap_capacity x hF

/-! ## 3. Lo que `x″` tiene: masa triangular -/

/-- Los triángulos de `F` tocan su propia cobertura. -/
theorem subset_meeting {F : Finset (Finset V)} (hF : IsTriFamily G F) : F ⊆ meeting G F := by
  classical
  intro T hT
  refine Finset.mem_filter.2 ⟨mem_items.2 (hF.1 T hT), ?_⟩
  have hne : (pairs T).Nonempty := by
    rw [← Finset.card_pos, card_pairs, hF.2.1 T hT]
    decide
  obtain ⟨e, he⟩ := hne
  exact ⟨e, Finset.mem_inter.2 ⟨he, Finset.mem_biUnion.2 ⟨T, hT, he⟩⟩⟩

/-- Sobre un triángulo de `F`, el peso sustituido vale `1`. -/
theorem swapWeight_eq_one {x : FracPacking G} {F : Finset (Finset V)} (hF : IsTriFamily G F)
    {T : Finset V} (hT : T ∈ F) : swapWeight x F T = 1 := by
  classical
  have hmem := subset_meeting hF hT
  simp only [swapWeight, if_pos (Finset.mem_filter.1 hmem).2, if_pos hT]

/-- **`x″` tiene masa triangular al menos `|F|`.**  Es lo que el gate con holgura pedía y `x` no
daba: los `|F|` triángulos entran con peso uno. -/
theorem card_le_triMass_swap (x : FracPacking G) {F : Finset (Finset V)}
    (hF : IsTriFamily G F) :
    (F.card : ℚ) ≤ PaperIV.LowTriangleReduction.triMass (swapPacking x hF) := by
  classical
  have hsub : F ⊆ (items G).filter (fun K => K.card = 3) := by
    intro T hT
    exact Finset.mem_filter.2 ⟨mem_items.2 (hF.1 T hT), hF.2.1 T hT⟩
  calc (F.card : ℚ) = ∑ T ∈ F, (1 : ℚ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = ∑ T ∈ F, swapWeight x F T :=
        Finset.sum_congr rfl (fun T hT => (swapWeight_eq_one hF hT).symm)
    _ ≤ ∑ K ∈ (items G).filter (fun K => K.card = 3), swapWeight x F K :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun K _ _ => swapWeight_nonneg x F K)

/-! ## 4. Lo que `x″` cuesta: `13|F|` -/

/-- Sobre `meeting`, el valor sustituido es exactamente `2|F|`: sólo los triángulos de `F`
contribuyen, y cada uno gana `2`. -/
theorem value_on_meeting (x : FracPacking G) {F : Finset (Finset V)} (hF : IsTriFamily G F) :
    ∑ K ∈ meeting G F, gainF ℚ K * swapWeight x F K = 2 * (F.card : ℚ) := by
  classical
  have h1 : ∀ K ∈ meeting G F,
      gainF ℚ K * swapWeight x F K = if K ∈ F then gainF ℚ K else 0 := by
    intro K hK
    have hP := (Finset.mem_filter.1 hK).2
    simp only [swapWeight, if_pos hP]
    split_ifs
    · ring
    · ring
  rw [Finset.sum_congr rfl h1, Finset.sum_ite_mem,
    Finset.inter_eq_right.2 (subset_meeting hF)]
  have h2 : ∀ T ∈ F, gainF ℚ T = 2 := by
    intro T hT
    rw [gainF, hF.2.1 T hT]
    norm_num
  rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]
  ring

/-- Sobre `meeting`, el valor original pierde a lo más `15|F|`: dualidad débil contra las `3|F|`
aristas de la cobertura. -/
theorem value_on_meeting_le (x : FracPacking G) {F : Finset (Finset V)} (hF : IsTriFamily G F) :
    ∑ K ∈ meeting G F, gainF ℚ K * x.weight K ≤ 15 * (F.card : ℚ) := by
  classical
  have hmS : meeting G F ⊆ items G := Finset.filter_subset _ _
  have hmeet : ∀ K ∈ meeting G F, ∃ e ∈ coverOf F, e ∈ pairs K := by
    intro K hK
    obtain ⟨e, he⟩ := (Finset.mem_filter.1 hK).2
    exact ⟨e, (Finset.mem_inter.1 he).2, (Finset.mem_inter.1 he).1⟩
  have h1 : ∑ K ∈ meeting G F, gainF ℚ K * x.weight K
      ≤ 5 * ∑ K ∈ meeting G F, x.weight K := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun K hK => ?_)
    exact mul_le_mul_of_nonneg_right (gainF_le_five (mem_items.1 (hmS hK))) (x.weight_nonneg K)
  have h2 := sum_weight_meeting_le x (coverOf_subset_edgeFinset' hF) hmS hmeet
  have h3 : ((coverOf F).card : ℚ) ≤ 3 * (F.card : ℚ) := by
    exact_mod_cast card_coverOf_le hF.2.1
  linarith

/-- **La sustitución cuesta a lo más `13|F|`.**

Fuera de `meeting` los dos empaquetamientos coinciden, así que toda la diferencia está dentro:
se pierden `≤ 15|F|` y se ganan `2|F|`. -/
theorem value_swap_ge (x : FracPacking G) {F : Finset (Finset V)} (hF : IsTriFamily G F) :
    x.value - 13 * (F.card : ℚ) ≤ (swapPacking x hF).value := by
  classical
  have hsplit : ∀ y : FracPacking G, y.value
      = ∑ K ∈ meeting G F, gainF ℚ K * y.weight K
        + ∑ K ∈ (items G).filter (fun K => ¬ (pairs K ∩ coverOf F).Nonempty),
            gainF ℚ K * y.weight K := by
    intro y
    rw [FracPacking.value, meeting]
    exact (Finset.sum_filter_add_sum_filter_not (items G)
      (fun K => (pairs K ∩ coverOf F).Nonempty) _).symm
  have houtside : ∀ K ∈ (items G).filter (fun K => ¬ (pairs K ∩ coverOf F).Nonempty),
      gainF ℚ K * swapWeight x F K = gainF ℚ K * x.weight K := by
    intro K hK
    have hP := (Finset.mem_filter.1 hK).2
    simp only [swapWeight, if_neg hP]
  have h1 := hsplit x
  have h2 := hsplit (swapPacking x hF)
  have h3 : (swapPacking x hF).weight = swapWeight x F := rfl
  rw [h3] at h2
  rw [Finset.sum_congr rfl houtside] at h2
  have h4 := value_on_meeting x hF
  have h5 := value_on_meeting_le x hF
  rw [h4] at h2
  linarith

/-! ## 5. El régimen degenerado, entero -/

/-- **El régimen degenerado del Corolario 7.3a, sin `round_arm_four`.**

Para todo `C`: o bien **todo** empaquetamiento fraccional vale a lo más `15C` —y el packing
vacío cierra—, o bien existe una familia de `C` triángulos aristo-disjuntos y entonces todo `x`
se sustituye por un `x″` legal con masa triangular `≥ C` perdiendo a lo más `13C`.

Las dos ramas son `O(1)`: ninguna de las tres estimaciones previas al gate aparece. -/
theorem lowTriangle_dichotomy (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℕ) :
    (∀ x : FracPacking G, x.value ≤ 15 * (C : ℚ)) ∨
      (∀ x : FracPacking G, ∃ x' : FracPacking G,
        (C : ℚ) ≤ PaperIV.LowTriangleReduction.triMass x' ∧
        x.value - x'.value ≤ 13 * (C : ℚ)) := by
  classical
  rcases many_disjoint_or_value_le G C with ⟨F, hF, hCF⟩ | hval
  · -- quedándose con **exactamente** `C`: la familia hallada puede ser mayor, y entonces
    -- `13|F|` no estaría acotado por `13C`.
    obtain ⟨F₀, hF₀F, hF₀card⟩ := Finset.exists_subset_card_eq hCF
    have hF₀ : IsTriFamily G F₀ := isTriFamily_subset hF hF₀F
    refine Or.inr (fun x => ⟨swapPacking x hF₀, ?_, ?_⟩)
    · refine le_trans ?_ (card_le_triMass_swap x hF₀)
      rw [hF₀card]
    · have h := value_swap_ge x hF₀
      rw [hF₀card] at h
      linarith
  · exact Or.inl hval

end PaperIV.TriangleSwap
