import PaperIV.RootedVariance

/-!
# Limpieza única de copias (RC01 §14)

Se retiran de la familia de copias transversales todas las que contienen **alguna** raíz mala
de **alguna** de las parejas del patrón, y se controla lo que queda.

## Lo que se demuestra

* `card_removed_le` — (14.1): el número de copias retiradas está acotado por la suma, sobre
  parejas y raíces malas, del número de completaciones.  Es una cota de unión.
* `sum_fiber_cleaned_add_removed` — (14.2): para una pareja fija, la pérdida total sobre sus
  raíces **es** exactamente el número de retiradas.  Sale de que cada copia retirada tiene una
  única arista en esa pareja, que es la descomposición en fibras.
* `card_bigLoss_le` — las raíces que pierden mucho son pocas: Markov sobre la pérdida.
* `cleaned_count_le` y `cleaned_count_ge` — (14.4) y (14.5).

## Por qué no se itera

La limpieza **no se repite**: las raíces afectadas se marcan como excepcionales y el nibble
las admite.  Aquí eso se refleja en que `cleaned` se define de una vez, por filtrado, y no por
un proceso iterativo: no hay recursión ni punto fijo que justificar.

## Nivel de abstracción

Todo se enuncia sobre una familia finita de copias, un mapa de raíces por pareja y un conjunto
de raíces malas por pareja.  Ni las partes ni las densidades aparecen: entran al instanciar,
al alimentar las hipótesis con `RootedVariance.rooted_variance_K3` / `_K4` y (13.8).
-/

namespace PaperIV.CopyCleanup

open Finset
open PaperIV.RootedCountingBridge

variable {κ ρ ι : Type*} [DecidableEq κ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι]

/-! ## 1. La limpieza -/

/-- Las copias que sobreviven: las que no tienen ninguna raíz mala en ninguna pareja. -/
def cleaned (Cs : Finset κ) (rt : ι → κ → ρ) (Bad : ι → Finset ρ) : Finset κ :=
  Cs.filter (fun K => ∀ i, rt i K ∉ Bad i)

/-- Las copias retiradas. -/
def removed (Cs : Finset κ) (rt : ι → κ → ρ) (Bad : ι → Finset ρ) : Finset κ :=
  Cs.filter (fun K => ¬ ∀ i, rt i K ∉ Bad i)

theorem cleaned_subset (Cs : Finset κ) (rt : ι → κ → ρ) (Bad : ι → Finset ρ) :
    cleaned Cs rt Bad ⊆ Cs := Finset.filter_subset _ _

theorem card_cleaned_add_removed (Cs : Finset κ) (rt : ι → κ → ρ) (Bad : ι → Finset ρ) :
    (cleaned Cs rt Bad).card + (removed Cs rt Bad).card = Cs.card := by
  classical
  rw [cleaned, removed]
  exact Finset.card_filter_add_card_filter_not (s := Cs) _

/-- La fibra de las copias limpias está contenida en la de todas. -/
theorem fiber_cleaned_subset (Cs : Finset κ) (rt : ι → κ → ρ) (Bad : ι → Finset ρ)
    (i : ι) (e : ρ) :
    fiber (cleaned Cs rt Bad) (rt i) e ⊆ fiber Cs (rt i) e := by
  intro K hK
  rw [fiber, Finset.mem_filter] at hK ⊢
  exact ⟨cleaned_subset Cs rt Bad hK.1, hK.2⟩

/-! ## 2. (14.1): cota de unión sobre las retiradas -/

/-- **(14.1).**  Cada copia retirada tiene alguna raíz mala; agrupando por pareja y por raíz,
el total está acotado por la suma de los tamaños de las fibras de las raíces malas. -/
theorem card_removed_le (Cs : Finset κ) (rt : ι → κ → ρ) (Bad : ι → Finset ρ) :
    (removed Cs rt Bad).card ≤ ∑ i, ∑ e ∈ Bad i, (fiber Cs (rt i) e).card := by
  classical
  have hsub : removed Cs rt Bad
      ⊆ (univ : Finset ι).biUnion
          (fun i => (Bad i).biUnion (fun e => fiber Cs (rt i) e)) := by
    intro K hK
    rw [removed, Finset.mem_filter] at hK
    have h2 := hK.2
    push_neg at h2
    obtain ⟨i, hi⟩ := h2
    refine Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, ?_⟩
    refine Finset.mem_biUnion.2 ⟨rt i K, hi, ?_⟩
    rw [fiber, Finset.mem_filter]
    exact ⟨hK.1, rfl⟩
  calc (removed Cs rt Bad).card
      ≤ ((univ : Finset ι).biUnion
          (fun i => (Bad i).biUnion (fun e => fiber Cs (rt i) e))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i, ((Bad i).biUnion (fun e => fiber Cs (rt i) e)).card := Finset.card_biUnion_le
    _ ≤ ∑ i, ∑ e ∈ Bad i, (fiber Cs (rt i) e).card :=
        Finset.sum_le_sum (fun i _ => Finset.card_biUnion_le)

/-- **(14.1) en forma cuantitativa.**  Con `#Bad i ≤ β` para cada pareja y `#fibra ≤ M` para
cada raíz, el total retirado es a lo sumo `ℓ · β · M`, donde `ℓ` es el número de parejas. -/
theorem card_removed_le_of_bounds (Cs : Finset κ) (rt : ι → κ → ρ) (Bad : ι → Finset ρ)
    {β M : ℕ} (hBad : ∀ i, (Bad i).card ≤ β)
    (hfib : ∀ i, ∀ e ∈ Bad i, (fiber Cs (rt i) e).card ≤ M) :
    (removed Cs rt Bad).card ≤ (Fintype.card ι) * (β * M) := by
  classical
  refine le_trans (card_removed_le Cs rt Bad) ?_
  have hrow : ∀ i : ι, ∑ e ∈ Bad i, (fiber Cs (rt i) e).card ≤ β * M := by
    intro i
    calc ∑ e ∈ Bad i, (fiber Cs (rt i) e).card ≤ ∑ _e ∈ Bad i, M :=
          Finset.sum_le_sum (fun e he => hfib i e he)
      _ = (Bad i).card * M := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ β * M := Nat.mul_le_mul_right M (hBad i)
  calc ∑ i, ∑ e ∈ Bad i, (fiber Cs (rt i) e).card ≤ ∑ _i : ι, β * M :=
        Finset.sum_le_sum (fun i _ => hrow i)
    _ = (Fintype.card ι) * (β * M) := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]

/-! ## 3. (14.2): la pérdida total es exactamente lo retirado -/

/-- **(14.2).**  Para una pareja fija, la suma de las pérdidas sobre sus raíces es el número
de copias retiradas.  Es la descomposición en fibras aplicada dos veces. -/
theorem sum_fiber_cleaned_add_removed (Cs : Finset κ) (rt : ι → κ → ρ) (Bad : ι → Finset ρ)
    (i : ι) (E : Finset ρ) (hroot : ∀ K ∈ Cs, rt i K ∈ E) :
    ∑ e ∈ E, (fiber (cleaned Cs rt Bad) (rt i) e).card + (removed Cs rt Bad).card
      = ∑ e ∈ E, (fiber Cs (rt i) e).card := by
  rw [sum_fiber_card (cleaned Cs rt Bad) (rt i) E
      (fun K hK => hroot K (cleaned_subset Cs rt Bad hK)),
    sum_fiber_card Cs (rt i) E hroot]
  exact card_cleaned_add_removed Cs rt Bad

/-! ## 4. Las raíces que pierden mucho son pocas -/

/-- La pérdida de una raíz. -/
def loss (Cs : Finset κ) (rt : ι → κ → ρ) (Bad : ι → Finset ρ) (i : ι) (e : ρ) : ℚ :=
  ((fiber Cs (rt i) e).card : ℚ) - ((fiber (cleaned Cs rt Bad) (rt i) e).card : ℚ)

theorem loss_nonneg (Cs : Finset κ) (rt : ι → κ → ρ) (Bad : ι → Finset ρ) (i : ι) (e : ρ) :
    0 ≤ loss Cs rt Bad i e := by
  have h : (fiber (cleaned Cs rt Bad) (rt i) e).card ≤ (fiber Cs (rt i) e).card :=
    Finset.card_le_card (fiber_cleaned_subset Cs rt Bad i e)
  have h' : ((fiber (cleaned Cs rt Bad) (rt i) e).card : ℚ)
      ≤ ((fiber Cs (rt i) e).card : ℚ) := by exact_mod_cast h
  rw [loss]
  linarith

theorem sum_loss (Cs : Finset κ) (rt : ι → κ → ρ) (Bad : ι → Finset ρ)
    (i : ι) (E : Finset ρ) (hroot : ∀ K ∈ Cs, rt i K ∈ E) :
    ∑ e ∈ E, loss Cs rt Bad i e = ((removed Cs rt Bad).card : ℚ) := by
  have h := sum_fiber_cleaned_add_removed Cs rt Bad i E hroot
  have h' : ((∑ e ∈ E, (fiber (cleaned Cs rt Bad) (rt i) e).card : ℕ) : ℚ)
      + ((removed Cs rt Bad).card : ℚ)
      = ((∑ e ∈ E, (fiber Cs (rt i) e).card : ℕ) : ℚ) := by exact_mod_cast h
  simp only [loss]
  rw [Finset.sum_sub_distrib]
  push_cast at h' ⊢
  linarith

/-- **Markov sobre la pérdida.**  Las raíces que pierden al menos `θ` son a lo sumo
`#retiradas / θ`. -/
theorem card_bigLoss_le (Cs : Finset κ) (rt : ι → κ → ρ) (Bad : ι → Finset ρ)
    (i : ι) (E : Finset ρ) (hroot : ∀ K ∈ Cs, rt i K ∈ E) {θ : ℚ} (hθ : 0 < θ) :
    θ * (((E.filter (fun e => θ ≤ loss Cs rt Bad i e)).card : ℚ))
      ≤ ((removed Cs rt Bad).card : ℚ) := by
  classical
  rw [← sum_loss Cs rt Bad i E hroot]
  calc θ * (((E.filter (fun e => θ ≤ loss Cs rt Bad i e)).card : ℚ))
      = ∑ _e ∈ E.filter (fun e => θ ≤ loss Cs rt Bad i e), θ := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ e ∈ E.filter (fun e => θ ≤ loss Cs rt Bad i e), loss Cs rt Bad i e :=
        Finset.sum_le_sum (fun e he => (Finset.mem_filter.1 he).2)
    _ ≤ ∑ e ∈ E, loss Cs rt Bad i e :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun e _ _ => loss_nonneg Cs rt Bad i e)

/-! ## 5. (14.4) y (14.5) -/

/-- **(14.4).**  La cota superior se conserva: limpiar sólo puede quitar copias. -/
theorem cleaned_count_le (Cs : Finset κ) (rt : ι → κ → ρ) (Bad : ι → Finset ρ)
    (i : ι) (e : ρ) {A u : ℚ}
    (hup : ((fiber Cs (rt i) e).card : ℚ) ≤ (1 + u) * A) :
    ((fiber (cleaned Cs rt Bad) (rt i) e).card : ℚ) ≤ (1 + u) * A := by
  have h : (fiber (cleaned Cs rt Bad) (rt i) e).card ≤ (fiber Cs (rt i) e).card :=
    Finset.card_le_card (fiber_cleaned_subset Cs rt Bad i e)
  have h' : ((fiber (cleaned Cs rt Bad) (rt i) e).card : ℚ)
      ≤ ((fiber Cs (rt i) e).card : ℚ) := by exact_mod_cast h
  linarith

/-- **(14.5).**  Fuera del excepcional —raíces originalmente malas o que perdieron más de
`u·A`— la cota inferior sobrevive con una `u` más de holgura. -/
theorem cleaned_count_ge (Cs : Finset κ) (rt : ι → κ → ρ) (Bad : ι → Finset ρ)
    (i : ι) (e : ρ) {A u : ℚ}
    (hlow : (1 - u) * A ≤ ((fiber Cs (rt i) e).card : ℚ))
    (hloss : loss Cs rt Bad i e ≤ u * A) :
    (1 - 2 * u) * A ≤ ((fiber (cleaned Cs rt Bad) (rt i) e).card : ℚ) := by
  rw [loss] at hloss
  nlinarith [hlow, hloss]

/-- Una raíz **mala** pierde todas sus copias: la limpieza la vacía. -/
theorem fiber_cleaned_eq_empty (Cs : Finset κ) (rt : ι → κ → ρ) (Bad : ι → Finset ρ)
    {i : ι} {e : ρ} (he : e ∈ Bad i) :
    fiber (cleaned Cs rt Bad) (rt i) e = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem ?_
  intro K hK
  rw [fiber, Finset.mem_filter, cleaned, Finset.mem_filter] at hK
  exact hK.1.2 i (hK.2 ▸ he)

end PaperIV.CopyCleanup
