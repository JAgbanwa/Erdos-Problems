import PaperIV.DoubledPattern

/-!
# El lema de conteo de patrón general (RC01 §13.2, ec. (13.3))

Bloque «Conteos» del contrato de RC01, en su forma general: un patrón arbitrario `F` sobre
partes `V : ι → Finset α`, no sólo `K₃`, `K₄` y sus doblados.

## El enunciado

Con las parejas de `F` en el formato (3.2) de `OneStepEstimate.DiscrepAt`,

```
| hom_partes(F, G)  −  (∏_{e ∈ F} d_e) · ∏_i |V_i| |  ≤  |F| · ε · ∏_i |V_i|.
```

## La demostración, y en qué se aparta de la fuente

RC01 §13.2 propone extender (3.2) de indicadores a productos `f(x)g(y)` con `f,g ∈ [0,1]`
mediante un argumento de *capas* (escribir `f` como combinación no negativa de indicadores de
conjuntos anidados).  **Aquí no hace falta.**

La razón es que, si se telescopea sustituyendo **una pareja por vez**, en el paso que sustituye
`(i₀,j₀)` los factores ya sustituidos son **constantes** (densidades) y los que aún no lo están
son **indicadores**.  Fijadas las demás coordenadas, el producto se parte exactamente en

```
C(ψ) · 1[a ∈ A_ψ] · 1[b ∈ B_ψ] · 1[a ~ b]
```

con `C(ψ) ∈ {0,1}` y `A_ψ ⊆ V_{i₀}`, `B_ψ ⊆ V_{j₀}` **conjuntos**, no funciones en `[0,1]`.
Así que (3.2) se aplica tal cual, sin extensión ninguna.  Es la misma estructura que ya tenían
`TelescopeK3` y `TelescopeK4`, ahora hecha una sola vez y para patrón arbitrario.

## Cobertura, y la constante exacta

Cubre los cuatro patrones que consume el segundo momento enraizado de RC01 §13.3, incluido
—lo que faltaba— el **doblado de `K₄`** (`doubledK4`, seis variables y once parejas), sin
telescopado propio.

La constante es `|F|`.  Los telescopados especializados que ya había dan `|F| − 1`
(`counting_lemma_K3`: 2 de 3; `counting_lemma_K4`: 5 de 6; `counting_lemma_book`: 4 de 5)
porque explotan que la **última** pareja no cuesta nada: cuando ya se han sustituido todas las
demás, sus dos extremos recorren las partes enteras y `∑_{a,b} 1[a∼b] = d·|V_i||V_j|` es la
definición de densidad.  Aquí no se explota, así que el lema general **no** los subsume con su
constante, sólo con una unidad más.  Para RP01 da igual —la constante se absorbe en `ε`—, pero
conviene no afirmar de más.
-/

namespace PaperIV.PatternCounting

open Finset
open PaperIV.OneStepEstimate

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-! ## 1. Indicadores, conteo de patrón, y sustitución de dos coordenadas -/

/-- Indicador racional de adyacencia. -/
def adjInd (G : SimpleGraph α) [DecidableRel G.Adj] (x y : α) : ℚ :=
  if G.Adj x y then 1 else 0

theorem adjInd_nonneg (x y : α) : 0 ≤ adjInd G x y := by
  unfold adjInd; split <;> norm_num

theorem adjInd_le_one (x y : α) : adjInd G x y ≤ 1 := by
  unfold adjInd; split <;> norm_num

/-- **El conteo de homomorfismos transversales** del patrón `F` sobre las partes `V`.  Cuando
todos los factores son indicadores, es literalmente el número de asignaciones `φ` que colocan
cada variable en su parte y realizan todas las parejas del patrón. -/
def patCount (G : SimpleGraph α) [DecidableRel G.Adj] (V : ι → Finset α)
    (F : Finset (ι × ι)) : ℚ :=
  ∑ φ ∈ Fintype.piFinset V, ∏ e ∈ F, adjInd G (φ e.1) (φ e.2)

/-- Colocar `a` y `b` en las coordenadas `i₀` y `j₀`. -/
def setTwo (i₀ j₀ : ι) (ψ : ι → α) (a b : α) : ι → α :=
  fun i => if i = i₀ then a else if i = j₀ then b else ψ i

/-- Las partes con `i₀` y `j₀` congeladas en un punto. -/
def freeze (V : ι → Finset α) (i₀ j₀ : ι) (a₀ : α) : ι → Finset α :=
  fun i => if i = i₀ ∨ i = j₀ then {a₀} else V i

theorem setTwo_left {i₀ j₀ : ι} (ψ : ι → α) (a b : α) : setTwo i₀ j₀ ψ a b i₀ = a := by
  simp [setTwo]

theorem setTwo_right {i₀ j₀ : ι} (hij : i₀ ≠ j₀) (ψ : ι → α) (a b : α) :
    setTwo i₀ j₀ ψ a b j₀ = b := by
  simp [setTwo, Ne.symm hij]

theorem setTwo_other {i₀ j₀ : ι} {i : ι} (h1 : i ≠ i₀) (h2 : i ≠ j₀) (ψ : ι → α) (a b : α) :
    setTwo i₀ j₀ ψ a b i = ψ i := by
  simp [setTwo, h1, h2]

/-! ## 2. Fibrar la suma por las dos coordenadas -/

/-- **La fibración.**  Sumar sobre todas las asignaciones equivale a fijar primero las demás
coordenadas y luego recorrer las dos distinguidas. -/
theorem sum_piFinset_split (V : ι → Finset α) {i₀ j₀ : ι} (hij : i₀ ≠ j₀) (a₀ : α)
    (h : (ι → α) → ℚ) :
    ∑ φ ∈ Fintype.piFinset V, h φ
      = ∑ ψ ∈ Fintype.piFinset (freeze V i₀ j₀ a₀),
          ∑ a ∈ V i₀, ∑ b ∈ V j₀, h (setTwo i₀ j₀ ψ a b) := by
  classical
  have hrhs : ∑ q ∈ (Fintype.piFinset (freeze V i₀ j₀ a₀)) ×ˢ (V i₀ ×ˢ V j₀),
        h (setTwo i₀ j₀ q.1 q.2.1 q.2.2)
      = ∑ ψ ∈ Fintype.piFinset (freeze V i₀ j₀ a₀), ∑ a ∈ V i₀, ∑ b ∈ V j₀,
          h (setTwo i₀ j₀ ψ a b) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl ?_
    intro ψ _
    rw [Finset.sum_product]
  rw [← hrhs]
  refine Finset.sum_nbij'
    (fun φ => ((fun i => if i = i₀ ∨ i = j₀ then a₀ else φ i), φ i₀, φ j₀))
    (fun q => setTwo i₀ j₀ q.1 q.2.1 q.2.2) ?_ ?_ ?_ ?_ ?_
  · -- va al producto
    intro φ hφ
    rw [Fintype.mem_piFinset] at hφ
    refine Finset.mem_product.2 ⟨?_, Finset.mem_product.2 ⟨hφ i₀, hφ j₀⟩⟩
    rw [Fintype.mem_piFinset]
    intro i
    by_cases hi : i = i₀ ∨ i = j₀
    · simp [freeze, hi]
    · simp [freeze, hi]; exact hφ i
  · -- vuelve al pi-finset
    intro q hq
    rw [Finset.mem_product, Finset.mem_product] at hq
    have hψ := hq.1
    have ha := hq.2.1
    have hb := hq.2.2
    rw [Fintype.mem_piFinset] at hψ ⊢
    intro i
    dsimp only
    by_cases h1 : i = i₀
    · subst h1; rw [setTwo_left]; exact ha
    · by_cases h2 : i = j₀
      · subst h2; rw [setTwo_right hij]; exact hb
      · rw [setTwo_other h1 h2]
        have := hψ i
        simpa [freeze, h1, h2] using this
  · -- inversa por la izquierda
    intro φ _
    funext i
    dsimp only
    by_cases h1 : i = i₀
    · subst h1; rw [setTwo_left]
    · by_cases h2 : i = j₀
      · subst h2; rw [setTwo_right hij]
      · rw [setTwo_other h1 h2]
        simp [h1, h2]
  · -- inversa por la derecha
    intro q hq
    rw [Finset.mem_product, Finset.mem_product] at hq
    have hψ := hq.1
    rw [Fintype.mem_piFinset] at hψ
    dsimp only
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i
      dsimp only
      by_cases hi : i = i₀ ∨ i = j₀
      · have := hψ i
        rw [show freeze V i₀ j₀ a₀ i = ({a₀} : Finset α) by simp [freeze, hi]] at this
        rw [Finset.mem_singleton] at this
        simp [hi, this]
      · push_neg at hi
        simp [hi.1, hi.2, setTwo_other hi.1 hi.2]
    · simpa using setTwo_left (i₀ := i₀) (j₀ := j₀) q.1 q.2.1 q.2.2
    · simpa using setTwo_right (i₀ := i₀) (j₀ := j₀) hij q.1 q.2.1 q.2.2
  · -- los valores coinciden
    intro φ _
    dsimp only
    congr 1
    funext i
    by_cases h1 : i = i₀
    · subst h1; rw [setTwo_left]
    · by_cases h2 : i = j₀
      · subst h2; rw [setTwo_right hij]
      · rw [setTwo_other h1 h2]; simp [h1, h2]

/-! ## 3. El producto de indicadores se parte en tres -/

/-- Las parejas del patrón que tocan la variable `i`. -/
def touch (i : ι) (F : Finset (ι × ι)) : Finset (ι × ι) :=
  F.filter (fun e => e.1 = i ∨ e.2 = i)

/-- Las que no la tocan. -/
def avoid (i : ι) (F : Finset (ι × ι)) : Finset (ι × ι) :=
  F.filter (fun e => ¬ (e.1 = i ∨ e.2 = i))

/-- Una pareja que toca `i₀` no toca `j₀`, si el patrón no tiene la pareja `(i₀,j₀)` ni su
simétrica.  Es la única hipótesis estructural que hace falta. -/
theorem ne_j_of_mem_touch {i₀ j₀ : ι} (hij : i₀ ≠ j₀) {F : Finset (ι × ι)}
    (hnot : (i₀, j₀) ∉ F) (hnot' : (j₀, i₀) ∉ F) {e : ι × ι} (he : e ∈ touch i₀ F) :
    e.1 ≠ j₀ ∧ e.2 ≠ j₀ := by
  rw [touch, Finset.mem_filter] at he
  obtain ⟨heF, hcase⟩ := he
  constructor
  · intro h1
    have h1i : e.1 ≠ i₀ := by rw [h1]; exact fun h => hij h.symm
    have h2 : e.2 = i₀ := hcase.resolve_left h1i
    exact hnot' (by rw [show e = (j₀, i₀) from Prod.ext h1 h2] at heF; exact heF)
  · intro h2
    have h2i : e.2 ≠ i₀ := by rw [h2]; exact fun h => hij h.symm
    have h1 : e.1 = i₀ := hcase.resolve_right h2i
    exact hnot (by rw [show e = (i₀, j₀) from Prod.ext h1 h2] at heF; exact heF)

/-- **La partición del producto.**  Fijadas las demás coordenadas, el producto de indicadores
se parte en un factor que sólo depende de `a`, uno que sólo depende de `b`, y una constante. -/
theorem prod_setTwo_split {i₀ j₀ : ι} (hij : i₀ ≠ j₀) (F : Finset (ι × ι))
    (hnot : (i₀, j₀) ∉ F) (hnot' : (j₀, i₀) ∉ F) (ψ : ι → α) (a b : α) :
    (∏ e ∈ F, adjInd G (setTwo i₀ j₀ ψ a b e.1) (setTwo i₀ j₀ ψ a b e.2))
      = (∏ e ∈ touch i₀ F,
            adjInd G (Function.update ψ i₀ a e.1) (Function.update ψ i₀ a e.2))
        * ((∏ e ∈ touch j₀ (avoid i₀ F),
              adjInd G (Function.update ψ j₀ b e.1) (Function.update ψ j₀ b e.2))
           * (∏ e ∈ avoid j₀ (avoid i₀ F), adjInd G (ψ e.1) (ψ e.2))) := by
  classical
  have hsplit1 :
      (∏ e ∈ F, adjInd G (setTwo i₀ j₀ ψ a b e.1) (setTwo i₀ j₀ ψ a b e.2))
        = (∏ e ∈ touch i₀ F, adjInd G (setTwo i₀ j₀ ψ a b e.1) (setTwo i₀ j₀ ψ a b e.2))
          * ∏ e ∈ avoid i₀ F, adjInd G (setTwo i₀ j₀ ψ a b e.1) (setTwo i₀ j₀ ψ a b e.2) :=
    (Finset.prod_filter_mul_prod_filter_not F (fun e => e.1 = i₀ ∨ e.2 = i₀) _).symm
  have hsplit2 :
      (∏ e ∈ avoid i₀ F, adjInd G (setTwo i₀ j₀ ψ a b e.1) (setTwo i₀ j₀ ψ a b e.2))
        = (∏ e ∈ touch j₀ (avoid i₀ F),
              adjInd G (setTwo i₀ j₀ ψ a b e.1) (setTwo i₀ j₀ ψ a b e.2))
          * ∏ e ∈ avoid j₀ (avoid i₀ F),
              adjInd G (setTwo i₀ j₀ ψ a b e.1) (setTwo i₀ j₀ ψ a b e.2) :=
    (Finset.prod_filter_mul_prod_filter_not (avoid i₀ F) (fun e => e.1 = j₀ ∨ e.2 = j₀) _).symm
  -- en las que tocan `i₀`, la sustitución de dos coordenadas es la de una
  have h1 : (∏ e ∈ touch i₀ F, adjInd G (setTwo i₀ j₀ ψ a b e.1) (setTwo i₀ j₀ ψ a b e.2))
      = ∏ e ∈ touch i₀ F,
          adjInd G (Function.update ψ i₀ a e.1) (Function.update ψ i₀ a e.2) := by
    refine Finset.prod_congr rfl ?_
    intro e he
    obtain ⟨hne1, hne2⟩ := ne_j_of_mem_touch hij hnot hnot' he
    have hc1 : setTwo i₀ j₀ ψ a b e.1 = Function.update ψ i₀ a e.1 := by
      by_cases h : e.1 = i₀
      · rw [h, setTwo_left, Function.update_self]
      · rw [setTwo_other h hne1, Function.update_of_ne h]
    have hc2 : setTwo i₀ j₀ ψ a b e.2 = Function.update ψ i₀ a e.2 := by
      by_cases h : e.2 = i₀
      · rw [h, setTwo_left, Function.update_self]
      · rw [setTwo_other h hne2, Function.update_of_ne h]
    rw [hc1, hc2]
  -- en las que evitan `i₀` y tocan `j₀`, ídem con `j₀`
  have h2 : (∏ e ∈ touch j₀ (avoid i₀ F),
        adjInd G (setTwo i₀ j₀ ψ a b e.1) (setTwo i₀ j₀ ψ a b e.2))
      = ∏ e ∈ touch j₀ (avoid i₀ F),
          adjInd G (Function.update ψ j₀ b e.1) (Function.update ψ j₀ b e.2) := by
    refine Finset.prod_congr rfl ?_
    intro e he
    rw [touch, Finset.mem_filter, avoid, Finset.mem_filter] at he
    have hav := he.1.2
    push_neg at hav
    have hc1 : setTwo i₀ j₀ ψ a b e.1 = Function.update ψ j₀ b e.1 := by
      by_cases h : e.1 = j₀
      · rw [h, setTwo_right hij, Function.update_self]
      · rw [setTwo_other hav.1 h, Function.update_of_ne h]
    have hc2 : setTwo i₀ j₀ ψ a b e.2 = Function.update ψ j₀ b e.2 := by
      by_cases h : e.2 = j₀
      · rw [h, setTwo_right hij, Function.update_self]
      · rw [setTwo_other hav.2 h, Function.update_of_ne h]
    rw [hc1, hc2]
  -- en las que no tocan ninguna, no hay sustitución
  have h3 : (∏ e ∈ avoid j₀ (avoid i₀ F),
        adjInd G (setTwo i₀ j₀ ψ a b e.1) (setTwo i₀ j₀ ψ a b e.2))
      = ∏ e ∈ avoid j₀ (avoid i₀ F), adjInd G (ψ e.1) (ψ e.2) := by
    refine Finset.prod_congr rfl ?_
    intro e he
    rw [avoid, Finset.mem_filter, avoid, Finset.mem_filter] at he
    have hi := he.1.2
    have hj := he.2
    push_neg at hi hj
    rw [setTwo_other hi.1 hj.1, setTwo_other hi.2 hj.2]
  rw [hsplit1, hsplit2, h1, h2, h3]

/-! ## 4. Los factores son indicadores: valen `0` o `1` -/

theorem prod_adjInd_zero_or_one (S : Finset (ι × ι)) (f : ι × ι → α) (g : ι × ι → α) :
    (∏ e ∈ S, adjInd G (f e) (g e)) = 0 ∨ (∏ e ∈ S, adjInd G (f e) (g e)) = 1 := by
  refine Finset.prod_induction _ (fun x => x = 0 ∨ x = 1) ?_ (Or.inr rfl) ?_
  · rintro x y (rfl | rfl) (rfl | rfl) <;> simp
  · intro e _
    unfold adjInd
    split
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem prod_adjInd_nonneg (S : Finset (ι × ι)) (f g : ι × ι → α) :
    0 ≤ ∏ e ∈ S, adjInd G (f e) (g e) :=
  Finset.prod_nonneg (fun e _ => adjInd_nonneg _ _)

theorem prod_adjInd_le_one (S : Finset (ι × ι)) (f g : ι × ι → α) :
    (∏ e ∈ S, adjInd G (f e) (g e)) ≤ 1 :=
  Finset.prod_le_one (fun e _ => adjInd_nonneg _ _) (fun e _ => adjInd_le_one _ _)

/-- La suma doble de indicadores **es** el número de aristas entre los dos conjuntos. -/
theorem sum_adjInd_eq_card_interedges (A B : Finset α) :
    ∑ a ∈ A, ∑ b ∈ B, adjInd G a b = ((G.interedges A B).card : ℚ) := by
  classical
  rw [SimpleGraph.interedges_def, Finset.card_filter]
  rw [← Finset.sum_product']
  push_cast
  refine Finset.sum_congr rfl ?_
  intro p _
  unfold adjInd
  split <;> simp_all


/-- Multiplicar por un indicador `0/1` es restringir la suma. -/
theorem sum_mul_indicator {s : Finset α} (f P : α → ℚ)
    (hP : ∀ x ∈ s, P x = 0 ∨ P x = 1) :
    ∑ x ∈ s, f x * P x = ∑ x ∈ s.filter (fun x => P x = 1), f x := by
  classical
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro x hx
  rcases hP x hx with h | h
  · rw [h, mul_zero, if_neg (by norm_num : ¬((0 : ℚ) = 1))]
  · rw [h, mul_one, if_pos (rfl : (1 : ℚ) = 1)]

/-- La cuenta de las partes congeladas: recuperar `∏_i |V_i|`. -/
theorem card_freeze_mul (V : ι → Finset α) {i₀ j₀ : ι} (hij : i₀ ≠ j₀) (a₀ : α) :
    ((Fintype.piFinset (freeze V i₀ j₀ a₀)).card : ℚ) * ((V i₀).card : ℚ)
        * ((V j₀).card : ℚ)
      = ∏ i, ((V i).card : ℚ) := by
  classical
  have hj₀mem : j₀ ∈ Finset.univ.erase i₀ :=
    Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ j₀⟩
  have hV : ∏ i, ((V i).card : ℚ)
      = ((V i₀).card : ℚ) * (((V j₀).card : ℚ)
          * ∏ i ∈ (Finset.univ.erase i₀).erase j₀, ((V i).card : ℚ)) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun i => ((V i).card : ℚ)) (Finset.mem_univ i₀),
      ← Finset.mul_prod_erase (Finset.univ.erase i₀) (fun i => ((V i).card : ℚ)) hj₀mem]
  have hF : ((Fintype.piFinset (freeze V i₀ j₀ a₀)).card : ℚ)
      = ∏ i ∈ (Finset.univ.erase i₀).erase j₀, ((V i).card : ℚ) := by
    rw [Fintype.card_piFinset, Nat.cast_prod,
      ← Finset.mul_prod_erase Finset.univ
        (fun i => ((freeze V i₀ j₀ a₀ i).card : ℚ)) (Finset.mem_univ i₀),
      ← Finset.mul_prod_erase (Finset.univ.erase i₀)
        (fun i => ((freeze V i₀ j₀ a₀ i).card : ℚ)) hj₀mem]
    have h1 : ((freeze V i₀ j₀ a₀ i₀).card : ℚ) = 1 := by simp [freeze]
    have h2 : ((freeze V i₀ j₀ a₀ j₀).card : ℚ) = 1 := by simp [freeze]
    rw [h1, h2, one_mul, one_mul]
    refine Finset.prod_congr rfl ?_
    intro i hi
    rw [Finset.mem_erase, Finset.mem_erase] at hi
    simp [freeze, hi.2.1, hi.1]
  rw [hF, hV]; ring

/-! ## 5. El paso del telescopado: sustituir una pareja por su densidad -/

set_option maxHeartbeats 1000000 in
/-- **Un paso.**  Sustituir el indicador de la pareja `(i₀,j₀)` por la densidad `d` cuesta a lo
sumo `ε·∏_i |V_i|`.

Fijadas las demás coordenadas, el producto se parte (`prod_setTwo_split`) en `P₁(a)·P₂(b)·C`
con los tres factores en `{0,1}`, así que la suma interna es exactamente
`C·(e(A,B) − d·|A||B|)` con `A ⊆ V_{i₀}`, `B ⊆ V_{j₀}`, y (3.2) se aplica sin más. -/
theorem patCount_step (V : ι → Finset α) {i₀ j₀ : ι} (hij : i₀ ≠ j₀) {d ε : ℚ}
    (hε : 0 ≤ ε) (F : Finset (ι × ι))
    (hnot : (i₀, j₀) ∉ F) (hnotSym : (j₀, i₀) ∉ F)
    (hdisc : DiscrepAt G ε d (V i₀) (V j₀)) :
    |patCount G V (insert (i₀, j₀) F) - d * patCount G V F|
      ≤ ε * ∏ i, ((V i).card : ℚ) := by
  classical
  rcases (V i₀).eq_empty_or_nonempty with hemp | ⟨a₀, ha₀⟩
  · have hzero : (Fintype.piFinset V) = ∅ := by
      rw [← Finset.card_eq_zero, Fintype.card_piFinset]
      exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by rw [hemp]; simp)
    have hprod : (∏ i, ((V i).card : ℚ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i₀) (by rw [hemp]; simp)
    simp [patCount, hzero, hprod]
  have hdiff : patCount G V (insert (i₀, j₀) F) - d * patCount G V F
      = ∑ φ ∈ Fintype.piFinset V,
          (adjInd G (φ i₀) (φ j₀) - d) * ∏ e ∈ F, adjInd G (φ e.1) (φ e.2) := by
    unfold patCount
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro φ _
    rw [Finset.prod_insert hnot]
    ring
  rw [hdiff, sum_piFinset_split V hij a₀
    (fun φ => (adjInd G (φ i₀) (φ j₀) - d) * ∏ e ∈ F, adjInd G (φ e.1) (φ e.2))]
  have hinner : ∀ ψ ∈ Fintype.piFinset (freeze V i₀ j₀ a₀),
      |∑ a ∈ V i₀, ∑ b ∈ V j₀,
          (adjInd G (setTwo i₀ j₀ ψ a b i₀) (setTwo i₀ j₀ ψ a b j₀) - d)
            * ∏ e ∈ F, adjInd G (setTwo i₀ j₀ ψ a b e.1) (setTwo i₀ j₀ ψ a b e.2)|
        ≤ ε * ((V i₀).card : ℚ) * ((V j₀).card : ℚ) := by
    intro ψ _
    set P1 : α → ℚ := fun a =>
      ∏ e ∈ touch i₀ F, adjInd G (Function.update ψ i₀ a e.1) (Function.update ψ i₀ a e.2)
      with hP1
    set P2 : α → ℚ := fun b =>
      ∏ e ∈ touch j₀ (avoid i₀ F),
        adjInd G (Function.update ψ j₀ b e.1) (Function.update ψ j₀ b e.2) with hP2
    set C : ℚ := ∏ e ∈ avoid j₀ (avoid i₀ F), adjInd G (ψ e.1) (ψ e.2) with hC
    set A : Finset α := (V i₀).filter (fun a => P1 a = 1) with hA
    set B : Finset α := (V j₀).filter (fun b => P2 b = 1) with hB
    have hstep : ∀ a ∈ V i₀, ∀ b ∈ V j₀,
        (adjInd G (setTwo i₀ j₀ ψ a b i₀) (setTwo i₀ j₀ ψ a b j₀) - d)
            * ∏ e ∈ F, adjInd G (setTwo i₀ j₀ ψ a b e.1) (setTwo i₀ j₀ ψ a b e.2)
          = ((adjInd G a b - d) * P2 b) * P1 a * C := by
      intro a _ b _
      rw [setTwo_left, setTwo_right hij,
        prod_setTwo_split hij F hnot hnotSym ψ a b, hP1, hP2, hC]
      ring
    have hrow : ∀ a ∈ V i₀,
        (∑ b ∈ V j₀, (adjInd G (setTwo i₀ j₀ ψ a b i₀) (setTwo i₀ j₀ ψ a b j₀) - d)
            * ∏ e ∈ F, adjInd G (setTwo i₀ j₀ ψ a b e.1) (setTwo i₀ j₀ ψ a b e.2))
          = (∑ b ∈ B, (adjInd G a b - d)) * P1 a * C := by
      intro a ha
      have h1 : (∑ b ∈ V j₀, (adjInd G (setTwo i₀ j₀ ψ a b i₀) (setTwo i₀ j₀ ψ a b j₀) - d)
            * ∏ e ∈ F, adjInd G (setTwo i₀ j₀ ψ a b e.1) (setTwo i₀ j₀ ψ a b e.2))
          = ∑ b ∈ V j₀, ((adjInd G a b - d) * P2 b) * (P1 a * C) := by
        refine Finset.sum_congr rfl ?_
        intro b hb
        rw [hstep a ha b hb]; ring
      rw [h1, ← Finset.sum_mul,
        sum_mul_indicator (fun b => adjInd G a b - d) P2
          (fun b _ => prod_adjInd_zero_or_one _ _ _)]
      ring
    have hall : (∑ a ∈ V i₀, ∑ b ∈ V j₀,
          (adjInd G (setTwo i₀ j₀ ψ a b i₀) (setTwo i₀ j₀ ψ a b j₀) - d)
            * ∏ e ∈ F, adjInd G (setTwo i₀ j₀ ψ a b e.1) (setTwo i₀ j₀ ψ a b e.2))
        = (∑ a ∈ A, ∑ b ∈ B, (adjInd G a b - d)) * C := by
      rw [Finset.sum_congr rfl hrow, ← Finset.sum_mul,
        sum_mul_indicator (fun a => ∑ b ∈ B, (adjInd G a b - d)) P1
          (fun a _ => prod_adjInd_zero_or_one _ _ _)]
    have hcore : (∑ a ∈ A, ∑ b ∈ B, (adjInd G a b - d))
        = ((G.interedges A B).card : ℚ) - d * (A.card : ℚ) * (B.card : ℚ) := by
      have hexp : ∀ a ∈ A, (∑ b ∈ B, (adjInd G a b - d))
          = (∑ b ∈ B, adjInd G a b) - (B.card : ℚ) * d := by
        intro a _
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib,
        sum_adjInd_eq_card_interedges, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hall, hcore, abs_mul]
    have hCabs : |C| ≤ 1 := by
      rcases prod_adjInd_zero_or_one (G := G) (avoid j₀ (avoid i₀ F))
        (fun e => ψ e.1) (fun e => ψ e.2) with h | h
      · rw [hC, h]; norm_num
      · rw [hC, h]; norm_num
    have hkey := hdisc A (Finset.filter_subset _ _) B (Finset.filter_subset _ _)
    have hnn : (0 : ℚ) ≤ |((G.interedges A B).card : ℚ) - d * (A.card : ℚ) * (B.card : ℚ)| :=
      abs_nonneg _
    calc |((G.interedges A B).card : ℚ) - d * (A.card : ℚ) * (B.card : ℚ)| * |C|
        ≤ |((G.interedges A B).card : ℚ) - d * (A.card : ℚ) * (B.card : ℚ)| * 1 :=
          mul_le_mul_of_nonneg_left hCabs hnn
      _ = |((G.interedges A B).card : ℚ) - d * (A.card : ℚ) * (B.card : ℚ)| := mul_one _
      _ ≤ ε * ((V i₀).card : ℚ) * ((V j₀).card : ℚ) := hkey
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [Finset.sum_const, nsmul_eq_mul, ← card_freeze_mul V hij a₀]
  ring_nf
  exact le_of_eq rfl


/-! ## 6. El lema de conteo de patrón -/

/-- Sin parejas, el conteo es el número de asignaciones. -/
theorem patCount_empty (V : ι → Finset α) :
    patCount G V ∅ = ∏ i, ((V i).card : ℚ) := by
  unfold patCount
  rw [Finset.sum_congr rfl (fun φ _ => Finset.prod_empty), Finset.sum_const, nsmul_eq_mul,
    mul_one, Fintype.card_piFinset, Nat.cast_prod]

set_option maxHeartbeats 1000000 in
/-- **El lema de conteo de patrón (RC01 §13.2, ec. (13.3)).**

Para un patrón arbitrario `F` —sin lazos y sin repetir una pareja en los dos órdenes— cuyas
parejas cumplen la discrepancia de cortes (3.2) con densidades `d`,

```
| hom_partes(F, G)  −  (∏_{e ∈ F} d_e) · ∏_i |V_i| |  ≤  |F| · ε · ∏_i |V_i|.
```

La constante es **el número de parejas**, que es lo que la fuente anuncia. -/
theorem patCount_approx {ε : ℚ} (hε : 0 ≤ ε) (V : ι → Finset α) (d : ι × ι → ℚ)
    (F : Finset (ι × ι))
    (hsym : ∀ e ∈ F, (e.2, e.1) ∉ F)
    (hne : ∀ e ∈ F, e.1 ≠ e.2)
    (hd0 : ∀ e ∈ F, 0 ≤ d e) (hd1 : ∀ e ∈ F, d e ≤ 1)
    (hdisc : ∀ e ∈ F, DiscrepAt G ε (d e) (V e.1) (V e.2)) :
    |patCount G V F - (∏ e ∈ F, d e) * ∏ i, ((V i).card : ℚ)|
      ≤ (F.card : ℚ) * ε * ∏ i, ((V i).card : ℚ) := by
  classical
  have hPi : (0 : ℚ) ≤ ∏ i, ((V i).card : ℚ) :=
    Finset.prod_nonneg (fun i _ => by positivity)
  revert hsym hne hd0 hd1 hdisc
  induction F using Finset.induction_on with
  | empty =>
    intro _ _ _ _ _
    rw [patCount_empty, Finset.prod_empty, one_mul, sub_self, abs_zero, Finset.card_empty]
    simp
  | @insert e₀ F' he₀ ih =>
    obtain ⟨i₀, j₀⟩ := e₀
    intro hsym hne hd0 hd1 hdisc
    -- las hipótesis se restringen al patrón menor
    have hsub : ∀ e, e ∈ F' → e ∈ insert (i₀, j₀) F' := fun e h => Finset.mem_insert_of_mem h
    have hsym' : ∀ e ∈ F', (e.2, e.1) ∉ F' :=
      fun e he h => hsym e (hsub e he) (hsub _ h)
    have hne' : ∀ e ∈ F', e.1 ≠ e.2 := fun e he => hne e (hsub e he)
    have hd0' : ∀ e ∈ F', 0 ≤ d e := fun e he => hd0 e (hsub e he)
    have hd1' : ∀ e ∈ F', d e ≤ 1 := fun e he => hd1 e (hsub e he)
    have hdisc' : ∀ e ∈ F', DiscrepAt G ε (d e) (V e.1) (V e.2) :=
      fun e he => hdisc e (hsub e he)
    have hih := ih hsym' hne' hd0' hd1' hdisc'
    -- datos de la pareja que se sustituye
    have hmem₀ : ((i₀, j₀) : ι × ι) ∈ insert (i₀, j₀) F' := Finset.mem_insert_self _ _
    have hij : i₀ ≠ j₀ := hne (i₀, j₀) hmem₀
    have hnotSym : ((j₀, i₀) : ι × ι) ∉ F' := fun h => hsym (i₀, j₀) hmem₀ (hsub _ h)
    have hd0e : 0 ≤ d (i₀, j₀) := hd0 (i₀, j₀) hmem₀
    have hd1e : d (i₀, j₀) ≤ 1 := hd1 (i₀, j₀) hmem₀
    have hstep := patCount_step V hij hε F' he₀ hnotSym (hdisc (i₀, j₀) hmem₀)
    -- el término de la hipótesis de inducción, escalado por la densidad
    have hsecond : |d (i₀, j₀) * patCount G V F'
          - (d (i₀, j₀) * ∏ e ∈ F', d e) * ∏ i, ((V i).card : ℚ)|
        ≤ (F'.card : ℚ) * ε * ∏ i, ((V i).card : ℚ) := by
      have hfac : d (i₀, j₀) * patCount G V F'
            - (d (i₀, j₀) * ∏ e ∈ F', d e) * ∏ i, ((V i).card : ℚ)
          = d (i₀, j₀)
              * (patCount G V F' - (∏ e ∈ F', d e) * ∏ i, ((V i).card : ℚ)) := by ring
      rw [hfac, abs_mul, abs_of_nonneg hd0e]
      have hnn : (0 : ℚ)
          ≤ |patCount G V F' - (∏ e ∈ F', d e) * ∏ i, ((V i).card : ℚ)| := abs_nonneg _
      calc d (i₀, j₀) * |patCount G V F' - (∏ e ∈ F', d e) * ∏ i, ((V i).card : ℚ)|
          ≤ 1 * |patCount G V F' - (∏ e ∈ F', d e) * ∏ i, ((V i).card : ℚ)| :=
            mul_le_mul_of_nonneg_right hd1e hnn
        _ = |patCount G V F' - (∏ e ∈ F', d e) * ∏ i, ((V i).card : ℚ)| := one_mul _
        _ ≤ (F'.card : ℚ) * ε * ∏ i, ((V i).card : ℚ) := hih
    have htri := abs_sub_le (patCount G V (insert (i₀, j₀) F'))
      (d (i₀, j₀) * patCount G V F')
      ((d (i₀, j₀) * ∏ e ∈ F', d e) * ∏ i, ((V i).card : ℚ))
    rw [Finset.prod_insert he₀, Finset.card_insert_of_notMem he₀]
    push_cast
    push_cast at hstep hsecond htri hih
    nlinarith [hstep, hsecond, htri, hPi, hε]


/-! ## 7. `patCount` **es** el conteo de homomorfismos transversales -/

/-- Certificación del modelo: el producto de indicadores suma exactamente el número de
asignaciones que realizan todas las parejas del patrón.  Sin esto, `patCount` sería «una suma»
y no «el conteo». -/
theorem patCount_eq_card (V : ι → Finset α) (F : Finset (ι × ι)) :
    patCount G V F
      = (((Fintype.piFinset V).filter
            (fun φ => ∀ e ∈ F, G.Adj (φ e.1) (φ e.2))).card : ℚ) := by
  classical
  unfold patCount
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro φ _
  by_cases h : ∀ e ∈ F, G.Adj (φ e.1) (φ e.2)
  · rw [if_pos h]
    refine Finset.prod_eq_one ?_
    intro e he
    unfold adjInd
    rw [if_pos (h e he)]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨e, he, hadj⟩ := h
    refine Finset.prod_eq_zero he ?_
    unfold adjInd
    rw [if_neg hadj]

/-! ## 8. Puente con la partición regular -/

section Regular

open PaperIV.RegularityFormat

variable {β : Type*} [DecidableEq β] [Fintype β] {H : SimpleGraph β} [DecidableRel H.Adj]

/-- **Conteo de patrón sobre partes de una partición regular.**  Las densidades son las de las
propias partes; las hipótesis son sólo estructurales sobre el patrón más «la pareja no es
excepcional». -/
theorem counting_of_regular {δ : ℚ} (hδ : 0 ≤ δ) (R : EqualRegularity H δ)
    (V : ι → Finset β) (F : Finset (ι × ι))
    (hV : ∀ i, V i ∈ R.parts)
    (hne : ∀ e ∈ F, e.1 ≠ e.2) (hsym : ∀ e ∈ F, (e.2, e.1) ∉ F)
    (hVne : ∀ e ∈ F, V e.1 ≠ V e.2)
    (hgood : ∀ e ∈ F, (V e.1, V e.2) ∉ R.bad) :
    |patCount H V F
        - (∏ e ∈ F, H.edgeDensity (V e.1) (V e.2)) * ∏ i, ((V i).card : ℚ)|
      ≤ (F.card : ℚ) * δ * ∏ i, ((V i).card : ℚ) :=
  patCount_approx hδ V (fun e => H.edgeDensity (V e.1) (V e.2)) F hsym hne
    (fun e _ => H.edgeDensity_nonneg _ _)
    (fun e _ => H.edgeDensity_le_one _ _)
    (fun e he => R.discrep (V e.1) (hV e.1) (V e.2) (hV e.2) (hVne e he) (hgood e he))

end Regular

/-! ## 9. La instancia que faltaba: el patrón doblado de `K₄` -/

/-- **Doblado de `K₄`**: dos `K₄` que comparten la arista raíz `01`.  Seis variables y **once**
parejas.  Es el patrón cuyo conteo cierra el segundo momento enraizado para `K₄`
(`RootedCountingBridge.sum_fiber_card_sq`), y el único de los cuatro que no se obtenía por
recorte del telescopado de `K₄`. -/
def doubledK4 : Finset (Fin 6 × Fin 6) :=
  {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3),
   (0, 4), (0, 5), (1, 4), (1, 5), (4, 5)}

theorem card_doubledK4 : doubledK4.card = 11 := by decide

theorem doubledK4_ne : ∀ e ∈ doubledK4, e.1 ≠ e.2 := by decide

theorem doubledK4_sym : ∀ e ∈ doubledK4, (e.2, e.1) ∉ doubledK4 := by decide

/-- **Conteo del patrón doblado de `K₄`**, con constante `11`. -/
theorem counting_doubledK4 {ε : ℚ} (hε : 0 ≤ ε) (V : Fin 6 → Finset α)
    (d : Fin 6 × Fin 6 → ℚ)
    (hd0 : ∀ e ∈ doubledK4, 0 ≤ d e) (hd1 : ∀ e ∈ doubledK4, d e ≤ 1)
    (hdisc : ∀ e ∈ doubledK4, DiscrepAt G ε (d e) (V e.1) (V e.2)) :
    |patCount G V doubledK4 - (∏ e ∈ doubledK4, d e) * ∏ i, ((V i).card : ℚ)|
      ≤ 11 * ε * ∏ i, ((V i).card : ℚ) := by
  have h := patCount_approx hε V d doubledK4 doubledK4_sym doubledK4_ne hd0 hd1 hdisc
  have hc : ((doubledK4.card : ℕ) : ℚ) = 11 := by rw [card_doubledK4]; norm_num
  rwa [hc] at h

/-- **`K₄` simple**, como instancia del lema general: cuatro variables y seis parejas. -/
def patK4 : Finset (Fin 4 × Fin 4) :=
  {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)}

theorem card_patK4 : patK4.card = 6 := by decide

theorem patK4_ne : ∀ e ∈ patK4, e.1 ≠ e.2 := by decide

theorem patK4_sym : ∀ e ∈ patK4, (e.2, e.1) ∉ patK4 := by decide

/-- **`K₃` simple**, como instancia del lema general. -/
def patK3 : Finset (Fin 3 × Fin 3) := {(0, 1), (0, 2), (1, 2)}

theorem card_patK3 : patK3.card = 3 := by decide

theorem patK3_ne : ∀ e ∈ patK3, e.1 ≠ e.2 := by decide

theorem patK3_sym : ∀ e ∈ patK3, (e.2, e.1) ∉ patK3 := by decide

/-- **Doblado de `K₃`**: dos triángulos que comparten la arista raíz `01`.  Cuatro variables y
cinco parejas. -/
def doubledK3 : Finset (Fin 4 × Fin 4) := {(0, 1), (0, 2), (1, 2), (0, 3), (1, 3)}

theorem card_doubledK3 : doubledK3.card = 5 := by decide

theorem doubledK3_ne : ∀ e ∈ doubledK3, e.1 ≠ e.2 := by decide

theorem doubledK3_sym : ∀ e ∈ doubledK3, (e.2, e.1) ∉ doubledK3 := by decide

end PaperIV.PatternCounting
