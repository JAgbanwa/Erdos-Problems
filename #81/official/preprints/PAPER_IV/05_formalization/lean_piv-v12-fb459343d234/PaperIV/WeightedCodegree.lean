import PaperIV.ResourceSizes

/-!
# El codegree ponderado (RC01, ecuación (17.3))

Última hipótesis del nibble que faltaba controlar en §17.1.

## El argumento

> Dos recursos distintos son dos aristas reales del grafo; su unión tiene al menos tres
> vértices.  Una clique transversal `K_r` que contiene ambos tiene a lo sumo `r−3` vértices aún
> por escoger, uno en cada parte restante.  Por tanto hay a lo sumo `t^{r−3}` completaciones.

Formalizado en dos piezas:

* `card_pinned_le` — **la cota de fijación**: si `|W|` coordenadas de una asignación
  transversal están fijadas, quedan a lo sumo `∏_{i ∉ W} |V_i|` asignaciones.  Es la forma
  general, y no necesita ni grafo ni cliques;
* `card_three_pinned` — con partes de tamaño `t` y **tres** coordenadas fijadas, a lo sumo
  `t^{r−3}`.  La cota es **ajustada**: se alcanza para `r = 4`;
* `codegree_le` — la aritmética de (17.3):

```
t^{r−3} / ((1+2u)·α^{ℓ−1}·t^{r−2})  ≤  1/(a₀⁵·t).
```

La desigualdad usa `α^{ℓ−1} ≥ a₀⁵`, que vale porque `ℓ−1 ≤ 5` y `a₀ ≤ α ≤ 1`: con `α ≤ 1` un
exponente menor da un valor mayor, y luego se baja de `α` a `a₀`.  Cubre a la vez `r = 3`
(`ℓ−1 = 2`) y `r = 4` (`ℓ−1 = 5`).

## El enlace con la estructura concreta

`card_two_resources_le` cierra la otra mitad: las copias transversales que contienen dos
recursos distintos son a lo sumo `t^{r−3}`.  La hipótesis de contención es la débil —que `φ`
**alcance** los cuatro vértices—; que eso fije las coordenadas es `index_unique`, y ahí es
donde se usa que las partes sean disjuntas.  Que la unión de dos pares distintos tenga tres
elementos es `three_le_card_union`.

La fuente observa además que *«filtrar cliques y asignar propietarios sólo disminuye ese
número»*: eso es monotonía del cardinal bajo subconjunto (`Finset.card_le_card`), que ya se usa
dentro de la prueba.
-/

namespace PaperIV.WeightedCodegree

open Finset

/-! ## 1. La cota de fijación -/

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]

/-- **Fijar coordenadas.**  Si `|W|` coordenadas de una asignación transversal están fijadas,
quedan a lo sumo `∏_{i ∉ W} |V_i|` asignaciones. -/
theorem card_pinned_le (V : ι → Finset α) (W : Finset ι) (c : ι → α) :
    ((Fintype.piFinset V).filter (fun φ => ∀ i ∈ W, φ i = c i)).card
      ≤ ∏ i ∈ univ \ W, (V i).card := by
  classical
  have hsub : (Fintype.piFinset V).filter (fun φ => ∀ i ∈ W, φ i = c i)
      ⊆ Fintype.piFinset (fun i => if i ∈ W then ({c i} : Finset α) else V i) := by
    intro φ hφ
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hφ
    rw [Fintype.mem_piFinset]
    intro i
    by_cases hi : i ∈ W
    · rw [if_pos hi, Finset.mem_singleton]
      exact hφ.2 i hi
    · rw [if_neg hi]
      exact hφ.1 i
  have hcard : (Fintype.piFinset (fun i => if i ∈ W then ({c i} : Finset α) else V i)).card
      = ∏ i : ι, (if i ∈ W then ({c i} : Finset α) else V i).card :=
    Fintype.card_piFinset _
  have hsplit : (∏ i : ι, (if i ∈ W then ({c i} : Finset α) else V i).card)
      = ∏ i ∈ univ \ W, (V i).card := by
    rw [← Finset.prod_sdiff (Finset.subset_univ W)]
    have h1 : (∏ i ∈ univ \ W, (if i ∈ W then ({c i} : Finset α) else V i).card)
        = ∏ i ∈ univ \ W, (V i).card := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      rw [if_neg (Finset.mem_sdiff.1 hi).2]
    have h2 : (∏ i ∈ W, (if i ∈ W then ({c i} : Finset α) else V i).card) = 1 := by
      refine Finset.prod_eq_one ?_
      intro i hi
      rw [if_pos hi, Finset.card_singleton]
    rw [h1, h2, mul_one]
  calc ((Fintype.piFinset V).filter (fun φ => ∀ i ∈ W, φ i = c i)).card
      ≤ (Fintype.piFinset (fun i => if i ∈ W then ({c i} : Finset α) else V i)).card :=
        Finset.card_le_card hsub
    _ = _ := by rw [hcard, hsplit]

/-- **Tres coordenadas fijadas.**  Con partes de tamaño `t`, quedan a lo sumo `t^{r−3}`
asignaciones.  Es la cota de (17.3), y es **ajustada**. -/
theorem card_three_pinned (V : ι → Finset α) (i₁ i₂ i₃ : ι)
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃) (c : ι → α) (t : ℕ)
    (hV : ∀ i, (V i).card = t) (ht : 1 ≤ t) :
    ((Fintype.piFinset V).filter
        (fun φ => φ i₁ = c i₁ ∧ φ i₂ = c i₂ ∧ φ i₃ = c i₃)).card
      ≤ t ^ (Fintype.card ι - 3) := by
  classical
  set W : Finset ι := {i₁, i₂, i₃} with hW
  have hWcard : W.card = 3 := by
    rw [hW, Finset.card_insert_of_notMem (by simp [h12, h13]),
      Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
  have hfil : (Fintype.piFinset V).filter
      (fun φ => φ i₁ = c i₁ ∧ φ i₂ = c i₂ ∧ φ i₃ = c i₃)
      = (Fintype.piFinset V).filter (fun φ => ∀ i ∈ W, φ i = c i) := by
    refine Finset.filter_congr ?_
    intro φ _
    rw [hW]
    constructor
    · rintro ⟨e1, e2, e3⟩ i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact e1
      · exact e2
      · exact e3
    · intro h
      exact ⟨h i₁ (by simp), h i₂ (by simp), h i₃ (by simp)⟩
  rw [hfil]
  refine le_trans (card_pinned_le V W c) ?_
  have hprod : (∏ i ∈ univ \ W, (V i).card) = t ^ (univ \ W).card := by
    rw [Finset.prod_congr rfl (fun i _ => hV i), Finset.prod_const]
  rw [hprod]
  refine Nat.pow_le_pow_right ht ?_
  rw [Finset.card_univ_diff, hWcard]

/-! ## 2. La aritmética de (17.3) -/

/-- **(17.3).**  Con `a₀ ≤ α ≤ 1` y `ℓ−1 ≤ 5`, el codegree ponderado no pasa de `1/(a₀⁵t)`.

El exponente `r` entra como `r = j + 3`, así que `t^{r−3}/t^{r−2} = 1/t` sin restas
naturales. -/
theorem codegree_le (u α a₀ t : ℚ) (k j : ℕ) (hu : 0 ≤ u) (ht : 0 < t)
    (ha₀ : 0 < a₀) (hαa : a₀ ≤ α) (hα1 : α ≤ 1) (hk : k ≤ 5) :
    t ^ j / ((1 + 2 * u) * (α ^ k * t ^ (j + 1))) ≤ 1 / (a₀ ^ 5 * t) := by
  have hα0 : 0 < α := lt_of_lt_of_le ha₀ hαa
  -- `α^k ≥ a₀^5`
  have hstep : a₀ ^ 5 ≤ α ^ k := by
    calc a₀ ^ 5 ≤ α ^ 5 := pow_le_pow_left₀ (le_of_lt ha₀) hαa 5
      _ ≤ α ^ k := pow_le_pow_of_le_one (le_of_lt hα0) hα1 hk
  have ha5 : (0 : ℚ) < a₀ ^ 5 := by positivity
  have htj : (0 : ℚ) < t ^ j := by positivity
  have hden : (0 : ℚ) < (1 + 2 * u) * (α ^ k * t ^ (j + 1)) := by
    have : (0 : ℚ) < 1 + 2 * u := by linarith
    positivity
  have hpow : t ^ (j + 1) = t ^ j * t := pow_succ t j
  rw [div_le_div_iff₀ hden (by positivity), hpow]
  have hpos : (0 : ℚ) < t ^ j * t := mul_pos htj ht
  have hA : (0 : ℚ) ≤ α ^ k * (t ^ j * t) := by positivity
  calc t ^ j * (a₀ ^ 5 * t) = a₀ ^ 5 * (t ^ j * t) := by ring
    _ ≤ α ^ k * (t ^ j * t) := mul_le_mul_of_nonneg_right hstep (le_of_lt hpos)
    _ ≤ (1 + 2 * u) * (α ^ k * (t ^ j * t)) := by nlinarith [hu, hA]
    _ = 1 * ((1 + 2 * u) * (α ^ k * (t ^ j * t))) := by ring

/-! ## 3. La forma estructural: dos recursos fijan tres coordenadas -/

/-- **Las partes disjuntas determinan el índice.**  Un vértice vive en una sola parte, así que
saber que `φ` lo alcanza ya dice *en qué coordenada* lo alcanza. -/
theorem index_unique {V : ι → Finset α} (hdisj : (Set.univ : Set ι).PairwiseDisjoint V)
    {a : α} {i j : ι} (hi : a ∈ V i) (hj : a ∈ V j) : i = j := by
  by_contra hij
  exact (Finset.disjoint_left.1 (hdisj (Set.mem_univ i) (Set.mem_univ j) hij) hi) hj

/-- **Dos aristas distintas cubren al menos tres índices.**  Dos pares distintos se cortan en a
lo sumo un elemento, así que su unión tiene al menos tres. -/
theorem three_le_card_union {W₁ W₂ : Finset ι} (h₁ : W₁.card = 2) (h₂ : W₂.card = 2)
    (hne : W₁ ≠ W₂) : 3 ≤ (W₁ ∪ W₂).card := by
  have hinter : (W₁ ∩ W₂).card ≤ 1 := by
    by_contra hc
    push_neg at hc
    have e1 : W₁ ∩ W₂ = W₁ :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have e2 : W₁ ∩ W₂ = W₂ :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hne (e1 ▸ e2)
  have h := Finset.card_union_add_card_inter W₁ W₂
  omega

/-- **Una arista fija dos coordenadas.**  Con partes disjuntas de tamaño `t`, las
asignaciones transversales que alcanzan los dos extremos de una arista entre
partes distintas son a lo sumo `t^(r-2)`.  Éste es el grado de recurso que
necesita el conteo de dependencias de RC01. -/
theorem card_one_resource_le (V : ι → Finset α)
    (hdisj : (Set.univ : Set ι).PairwiseDisjoint V) (t : ℕ)
    (hV : ∀ i, (V i).card = t) (ht : 1 ≤ t)
    {a b : α} {i j : ι} (ha : a ∈ V i) (hb : b ∈ V j) (hij : i ≠ j) :
    ((Fintype.piFinset V).filter
        (fun φ => (∃ q, φ q = a) ∧ (∃ q, φ q = b))).card
      ≤ t ^ (Fintype.card ι - 2) := by
  classical
  set S := (Fintype.piFinset V).filter
      (fun φ => (∃ q, φ q = a) ∧ (∃ q, φ q = b)) with hS
  have hkey : ∀ φ ∈ S, φ i = a ∧ φ j = b := by
    intro φ hφ
    rw [hS, Finset.mem_filter, Fintype.mem_piFinset] at hφ
    obtain ⟨hmem, ⟨p, hp⟩, ⟨q, hq⟩⟩ := hφ
    have ei : φ i = a := by
      have hav : a ∈ V p := by rw [← hp]; exact hmem p
      rw [← index_unique hdisj hav ha]
      exact hp
    have ej : φ j = b := by
      have hbv : b ∈ V q := by rw [← hq]; exact hmem q
      rw [← index_unique hdisj hbv hb]
      exact hq
    exact ⟨ei, ej⟩
  rcases S.eq_empty_or_nonempty with hemp | ⟨φ₀, hφ₀⟩
  · rw [hemp]
    simp
  set W : Finset ι := {i, j} with hW
  have hWcard : W.card = 2 := by
    rw [hW, Finset.card_insert_of_notMem (by simp [hij]), Finset.card_singleton]
  have hsub : S ⊆
      (Fintype.piFinset V).filter (fun φ => ∀ q ∈ W, φ q = φ₀ q) := by
    intro φ hφ
    obtain ⟨ei, ej⟩ := hkey φ hφ
    obtain ⟨fi, fj⟩ := hkey φ₀ hφ₀
    have hmem : φ ∈ Fintype.piFinset V := by
      rw [hS, Finset.mem_filter] at hφ
      exact hφ.1
    refine Finset.mem_filter.2 ⟨hmem, ?_⟩
    intro q hq
    rw [hW] at hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · rw [ei, fi]
    · rw [ej, fj]
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (card_pinned_le V W φ₀) ?_
  have hprod : (∏ q ∈ univ \ W, (V q).card) = t ^ (univ \ W).card := by
    rw [Finset.prod_congr rfl (fun q _ => hV q), Finset.prod_const]
  rw [hprod, Finset.card_univ_diff, hWcard]

/-- `card_pinned_le` con partes iguales y **al menos** tres coordenadas fijadas. -/
theorem card_pinned_pow_le (V : ι → Finset α) (W : Finset ι) (c : ι → α) (t : ℕ)
    (hV : ∀ i, (V i).card = t) (ht : 1 ≤ t) (hW : 3 ≤ W.card) :
    ((Fintype.piFinset V).filter (fun φ => ∀ i ∈ W, φ i = c i)).card
      ≤ t ^ (Fintype.card ι - 3) := by
  refine le_trans (card_pinned_le V W c) ?_
  have hprod : (∏ i ∈ univ \ W, (V i).card) = t ^ (univ \ W).card := by
    rw [Finset.prod_congr rfl (fun i _ => hV i), Finset.prod_const]
  rw [hprod]
  refine Nat.pow_le_pow_right ht ?_
  rw [Finset.card_univ_diff]
  omega

/-- **(17.3), forma estructural.**  Las copias transversales que contienen **dos recursos
distintos** —dos aristas reales `{a₁,b₁} ≠ {a₂,b₂}`, dadas por sus índices— son a lo sumo
`t^{r−3}`.

La hipótesis de contención es la débil, *«`φ` alcanza los cuatro vértices»*: por
`index_unique` eso ya fuerza **en qué** coordenada los alcanza, y ahí es donde entra que las
partes sean disjuntas.  El paso a `card_pinned_pow_le` no necesita construir la función de
fijación: si el conjunto es vacío la cota es trivial, y si no, cualquiera de sus elementos
sirve de testigo. -/
theorem card_two_resources_le (V : ι → Finset α)
    (hdisj : (Set.univ : Set ι).PairwiseDisjoint V) (t : ℕ)
    (hV : ∀ i, (V i).card = t) (ht : 1 ≤ t)
    {a₁ b₁ a₂ b₂ : α} {i₁ j₁ i₂ j₂ : ι}
    (ha₁ : a₁ ∈ V i₁) (hb₁ : b₁ ∈ V j₁) (ha₂ : a₂ ∈ V i₂) (hb₂ : b₂ ∈ V j₂)
    (hij₁ : i₁ ≠ j₁) (hij₂ : i₂ ≠ j₂)
    (hne : ({i₁, j₁} : Finset ι) ≠ ({i₂, j₂} : Finset ι)) :
    ((Fintype.piFinset V).filter (fun φ =>
        (∃ i, φ i = a₁) ∧ (∃ i, φ i = b₁) ∧ (∃ i, φ i = a₂) ∧ (∃ i, φ i = b₂))).card
      ≤ t ^ (Fintype.card ι - 3) := by
  classical
  set S := (Fintype.piFinset V).filter (fun φ =>
      (∃ i, φ i = a₁) ∧ (∃ i, φ i = b₁) ∧ (∃ i, φ i = a₂) ∧ (∃ i, φ i = b₂)) with hS
  -- las cuatro coordenadas quedan fijadas para todo elemento de `S`
  have hkey : ∀ φ ∈ S, φ i₁ = a₁ ∧ φ j₁ = b₁ ∧ φ i₂ = a₂ ∧ φ j₂ = b₂ := by
    intro φ hφ
    rw [hS, Finset.mem_filter, Fintype.mem_piFinset] at hφ
    obtain ⟨hmem, ⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩, ⟨s, hs⟩⟩ := hφ
    have e1 : φ i₁ = a₁ := by
      have hav : a₁ ∈ V p := by rw [← hp]; exact hmem p
      rw [← index_unique hdisj hav ha₁]; exact hp
    have e2 : φ j₁ = b₁ := by
      have hav : b₁ ∈ V q := by rw [← hq]; exact hmem q
      rw [← index_unique hdisj hav hb₁]; exact hq
    have e3 : φ i₂ = a₂ := by
      have hav : a₂ ∈ V r := by rw [← hr]; exact hmem r
      rw [← index_unique hdisj hav ha₂]; exact hr
    have e4 : φ j₂ = b₂ := by
      have hav : b₂ ∈ V s := by rw [← hs]; exact hmem s
      rw [← index_unique hdisj hav hb₂]; exact hs
    exact ⟨e1, e2, e3, e4⟩
  rcases S.eq_empty_or_nonempty with hemp | ⟨φ₀, hφ₀⟩
  · rw [hemp]; simp
  set W : Finset ι := ({i₁, j₁} : Finset ι) ∪ ({i₂, j₂} : Finset ι) with hW
  have hsub : S ⊆ (Fintype.piFinset V).filter (fun φ => ∀ i ∈ W, φ i = φ₀ i) := by
    intro φ hφ
    obtain ⟨e1, e2, e3, e4⟩ := hkey φ hφ
    obtain ⟨f1, f2, f3, f4⟩ := hkey φ₀ hφ₀
    have hmem : φ ∈ Fintype.piFinset V := by
      rw [hS, Finset.mem_filter] at hφ; exact hφ.1
    refine Finset.mem_filter.2 ⟨hmem, ?_⟩
    intro i hi
    rw [hW] at hi
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with (rfl | rfl) | (rfl | rfl)
    · rw [e1, f1]
    · rw [e2, f2]
    · rw [e3, f3]
    · rw [e4, f4]
  refine le_trans (Finset.card_le_card hsub) ?_
  refine card_pinned_pow_le V W φ₀ t hV ht ?_
  rw [hW]
  refine three_le_card_union ?_ ?_ hne
  · rw [Finset.card_insert_of_notMem (by simp [hij₁]), Finset.card_singleton]
  · rw [Finset.card_insert_of_notMem (by simp [hij₂]), Finset.card_singleton]

end PaperIV.WeightedCodegree
