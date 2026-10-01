import MixedRounding.Defs

/-!
# El descarte cuesta `5|B|` (CMR, paso 1)

Primera pieza real del cono `G0 → G4`, y **incondicional**.

## Qué dice

Tras la regularización se descarta un conjunto `B` de aristas —internas a clusters, pares no
regulares, pares poco densos—.  Los items que tocan `B` se pierden.  El plan observa que ese
coste se acota *por capacidades*, sin ninguna hipótesis sobre la forma del soporte:

```
∑_{K ∈ D} x_K  ≤  ∑_{e ∈ B} ∑_{K ∋ e} x_K  ≤  |B|,
```

y como la ganancia máxima es `5`,

```
∑_{K ∈ D} g(K)·x_K  ≤  5|B|.
```

`discard_value_le`.  Es exactamente el argumento del plan, y es el que convierte
`|B| ≤ cεn²` en `pérdida ≤ 5cεn²` de una sola vez.

## Por qué funciona

Cada item que toca `B` tiene **alguna** arista en `B`, y la restricción de capacidad del LP
acota por `1` la masa total que pasa por cada arista.  Contando por aristas de `B` en vez de
por items, cada item se cuenta al menos una vez y el total no excede `|B|`.

No hay nada probabilístico ni asintótico aquí: es la desigualdad de capacidad más un cambio de
orden de sumación.

## Alcance

Esto es el paso 1 del plan.  Los pasos 3 y 4 —el productor de patrones y el matching casi
perfecto— no están aquí y son el grueso del trabajo; véase el documento de feedback.
-/

namespace MixedRounding

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Los items que **tocan** un conjunto de aristas descartadas. -/
def touching (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V)) :
    Finset (Finset V) :=
  (items G).filter (fun K => ∃ e ∈ B, e ∈ pairs K)

/-- **La masa descartada no excede `|B|`.**  Cada item tocado pasa por alguna arista de `B`, y
la capacidad acota por `1` la masa que pasa por cada arista. -/
theorem discard_mass_le (x : FracPacking G) (B : Finset (Sym2 V))
    (hB : B ⊆ G.edgeFinset) :
    ∑ K ∈ touching G B, x.weight K ≤ (B.card : ℚ) := by
  classical
  have key : ∀ K ∈ touching G B,
      x.weight K ≤ ∑ e ∈ B, (if e ∈ pairs K then x.weight K else 0) := by
    intro K hK
    rw [touching, Finset.mem_filter] at hK
    obtain ⟨e₀, he₀B, he₀K⟩ := hK.2
    have hle : (if e₀ ∈ pairs K then x.weight K else 0)
        ≤ ∑ e ∈ B, (if e ∈ pairs K then x.weight K else 0) := by
      refine Finset.single_le_sum
        (f := fun e => if e ∈ pairs K then x.weight K else 0) ?_ he₀B
      intro e _
      dsimp only
      by_cases h : e ∈ pairs K
      · rw [if_pos h]; exact x.weight_nonneg K
      · rw [if_neg h]
    rwa [if_pos he₀K] at hle
  have hcap : ∀ e ∈ B,
      ∑ K ∈ touching G B, (if e ∈ pairs K then x.weight K else 0) ≤ (1 : ℚ) := by
    intro e he
    refine le_trans ?_ (x.capacity e (hB he))
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro K _ _
    dsimp only
    by_cases h : e ∈ pairs K
    · rw [if_pos h]; exact x.weight_nonneg K
    · rw [if_neg h]
  calc ∑ K ∈ touching G B, x.weight K
      ≤ ∑ K ∈ touching G B, ∑ e ∈ B, (if e ∈ pairs K then x.weight K else 0) :=
        Finset.sum_le_sum key
    _ = ∑ e ∈ B, ∑ K ∈ touching G B, (if e ∈ pairs K then x.weight K else 0) :=
        Finset.sum_comm (s := touching G B) (t := B)
          (f := fun K e => if e ∈ pairs K then x.weight K else 0)
    _ ≤ ∑ _e ∈ B, (1 : ℚ) := Finset.sum_le_sum hcap
    _ = (B.card : ℚ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **(Paso 1).**  El valor LP que vive sobre los items descartados no pasa de `5|B|`.

Es el paso que convierte `|B| ≤ c·ε·n²` en `pérdida ≤ 5c·ε·n²`, sin hipótesis sobre el
soporte. -/
theorem discard_value_le (x : FracPacking G) (B : Finset (Sym2 V))
    (hB : B ⊆ G.edgeFinset) :
    ∑ K ∈ touching G B, gainF ℚ K * x.weight K ≤ 5 * (B.card : ℚ) := by
  have hterm : ∀ K ∈ touching G B, gainF ℚ K * x.weight K ≤ 5 * x.weight K := by
    intro K hK
    rw [touching, Finset.mem_filter] at hK
    exact mul_le_mul_of_nonneg_right (gainF_le_five (mem_items.1 hK.1)) (x.weight_nonneg K)
  calc ∑ K ∈ touching G B, gainF ℚ K * x.weight K
      ≤ ∑ K ∈ touching G B, 5 * x.weight K := Finset.sum_le_sum hterm
    _ = 5 * ∑ K ∈ touching G B, x.weight K := by rw [Finset.mul_sum]
    _ ≤ 5 * (B.card : ℚ) := by
        have := discard_mass_le x B hB
        linarith

/-- La forma que consume el presupuesto: si el descarte es `≤ c·ε·n²` aristas, la pérdida de
valor es `≤ 5c·ε·n²`. -/
theorem discard_value_le_target {c ε : ℚ} {n : ℕ} (x : FracPacking G) (B : Finset (Sym2 V))
    (hB : B ⊆ G.edgeFinset) (hcard : (B.card : ℚ) ≤ c * ε * (n : ℚ) ^ 2) :
    ∑ K ∈ touching G B, gainF ℚ K * x.weight K ≤ 5 * c * ε * (n : ℚ) ^ 2 := by
  have h := discard_value_le x B hB
  nlinarith [h, hcard]

/-! ## El presupuesto final del plan (NB03) -/

/-- **La suma de los tres términos del presupuesto es `< 1`.**

`3/50 + 1/10 + 1/16 = 89/400`, luego `w(x) − gain(P) < ε·n²`. -/
theorem budget_sum_lt_one : (3 / 50 : ℚ) + 1 / 10 + 1 / 16 = 89 / 400 := by norm_num

theorem budget_closes {ε : ℚ} (hε : 0 < ε) {n : ℕ} {loss : ℚ}
    (h : loss ≤ ((3 / 50 : ℚ) + 1 / 10 + 1 / 16) * (ε * (n : ℚ) ^ 2)) :
    loss ≤ (89 / 400 : ℚ) * (ε * (n : ℚ) ^ 2) := by
  rwa [budget_sum_lt_one] at h

end MixedRounding
