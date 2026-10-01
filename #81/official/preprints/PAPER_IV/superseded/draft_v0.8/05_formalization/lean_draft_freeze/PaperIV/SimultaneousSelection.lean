import PaperIV.PatternMass
import PaperIV.EighthMoment

/-!
# Selección simultánea (RC01 §16.5)

El motor del bloque probabilístico: si hay `N` condiciones de fallo, cada una de probabilidad
a lo sumo `p`, y `N·p < 1`, entonces **alguna realización las evita todas a la vez**.

## Lo que se demuestra

* `prob_univ` — la probabilidad total es `1`;
* `prob_biUnion_le` — subaditividad, por el mismo principio de cobertura por incidencias que
  `PatternMass.sum_weight_le_card_of_meets`: cada punto de la unión está en al menos un
  suceso;
* `exists_avoiding` — **la selección simultánea**.

## Por qué es lo que §16.5 necesita

La fuente cuenta `6L⁴t²` condiciones patrón–raíz y `12L⁴` condiciones de tamaño y
excepciones, acota cada una por (16.4)/(16.5) y concluye que el total es `< 1`.  Eso es
exactamente `exists_avoiding` con `s` la familia de condiciones.  La aritmética de los
parámetros (`L`, `t`, `u`, `a₀`) entra al instanciar; el principio es éste.

Obsérvese la advertencia de §16.3 que el enunciado respeta: *«la probabilidad no condicionada
del evento ‹la raíz se asignó a σ y su grado falla› es a lo sumo la cota condicional. No se
divide por la probabilidad de asignación de la raíz.»*  Aquí `A i` es directamente el suceso
no condicionado, así que no hay división que justificar.
-/

namespace PaperIV.SimultaneousSelection

open Finset
open PaperIV.EighthMoment

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- La probabilidad total es `1`. -/
theorem prob_univ (P : FinProb Ω) : P.prob (univ : Finset Ω) = 1 := P.w_total

/-- **Subaditividad.**  Cada punto de la unión pertenece a al menos un suceso; el doble conteo
sólo aumenta la cota. -/
theorem prob_biUnion_le {ι : Type*} [DecidableEq ι] (P : FinProb Ω) (s : Finset ι)
    (A : ι → Finset Ω) :
    P.prob (s.biUnion A) ≤ ∑ i ∈ s, P.prob (A i) := by
  classical
  have hrow : ∀ ω ∈ s.biUnion A,
      P.w ω ≤ ∑ i ∈ s, (if ω ∈ A i then P.w ω else 0) := by
    intro ω hω
    obtain ⟨i₀, hi₀s, hi₀A⟩ := Finset.mem_biUnion.1 hω
    have hsingle : (if ω ∈ A i₀ then P.w ω else 0)
        ≤ ∑ i ∈ s, (if ω ∈ A i then P.w ω else 0) := by
      refine Finset.single_le_sum (f := fun i => if ω ∈ A i then P.w ω else 0) ?_ hi₀s
      intro i _
      dsimp only
      by_cases hi : ω ∈ A i
      · rw [if_pos hi]; exact P.w_nonneg ω
      · rw [if_neg hi]
    rwa [if_pos hi₀A] at hsingle
  calc P.prob (s.biUnion A) = ∑ ω ∈ s.biUnion A, P.w ω := rfl
    _ ≤ ∑ ω ∈ s.biUnion A, ∑ i ∈ s, (if ω ∈ A i then P.w ω else 0) :=
        Finset.sum_le_sum hrow
    _ = ∑ i ∈ s, ∑ ω ∈ s.biUnion A, (if ω ∈ A i then P.w ω else 0) := Finset.sum_comm
    _ = ∑ i ∈ s, ∑ ω ∈ (s.biUnion A).filter (fun ω => ω ∈ A i), P.w ω := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.sum_filter]
    _ ≤ ∑ i ∈ s, P.prob (A i) := by
        refine Finset.sum_le_sum ?_
        intro i _
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun ω _ _ => P.w_nonneg ω)
        intro ω hω
        exact (Finset.mem_filter.1 hω).2

/-- **Selección simultánea (RC01 §16.5).**  Con `N` condiciones de fallo de probabilidad a lo
sumo `p` cada una y `N·p < 1`, existe una realización que las evita todas. -/
theorem exists_avoiding {ι : Type*} [DecidableEq ι] (P : FinProb Ω) (s : Finset ι)
    (A : ι → Finset Ω) {p : ℚ} (hp : ∀ i ∈ s, P.prob (A i) ≤ p)
    (hlt : (s.card : ℚ) * p < 1) :
    ∃ ω : Ω, ∀ i ∈ s, ω ∉ A i := by
  classical
  by_contra hcon
  push_neg at hcon
  -- si nadie las evita, la unión es todo
  have hcover : (univ : Finset Ω) ⊆ s.biUnion A := by
    intro ω _
    obtain ⟨i, his, hiA⟩ := hcon ω
    exact Finset.mem_biUnion.2 ⟨i, his, hiA⟩
  have h1 : (1 : ℚ) ≤ P.prob (s.biUnion A) := by
    rw [← prob_univ P]
    exact P.prob_mono hcover
  have h2 : P.prob (s.biUnion A) ≤ ∑ i ∈ s, P.prob (A i) := prob_biUnion_le P s A
  have h3 : ∑ i ∈ s, P.prob (A i) ≤ (s.card : ℚ) * p := by
    calc ∑ i ∈ s, P.prob (A i) ≤ ∑ _i ∈ s, p := Finset.sum_le_sum hp
      _ = (s.card : ℚ) * p := by rw [Finset.sum_const, nsmul_eq_mul]
  linarith

/-- Forma cuantitativa cómoda: con `N` condiciones y cota `p`, basta `p < 1/N`. -/
theorem exists_avoiding_of_lt {ι : Type*} [DecidableEq ι] (P : FinProb Ω) (s : Finset ι)
    (A : ι → Finset Ω) {p : ℚ} (hs : 0 < s.card)
    (hp : ∀ i ∈ s, P.prob (A i) ≤ p) (hlt : p < 1 / (s.card : ℚ)) :
    ∃ ω : Ω, ∀ i ∈ s, ω ∉ A i := by
  refine exists_avoiding P s A hp ?_
  have hcard : (0 : ℚ) < (s.card : ℚ) := by exact_mod_cast hs
  rw [lt_div_iff₀ hcard] at hlt
  linarith [hlt]

end PaperIV.SimultaneousSelection
