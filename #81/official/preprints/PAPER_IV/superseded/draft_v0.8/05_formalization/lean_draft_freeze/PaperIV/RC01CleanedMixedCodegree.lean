import PaperIV.RC01CleanFiber
import PaperIV.RC01CanonicalSlackBridge

/-!
# RC01: el codegree mixto pequeño de las fibras limpias

Aquí se cierra la forma racional que consume
`RC01CanonicalSlackBridge.budgetPacking_joint_codegree_le`:

```
∑ σ ∈ Active, twoCount cleanFiber σ e f * budgetCoefficient mass budget σ ≤ γ
```

Las dos cotas de conteo son literales sobre las fibras de perfil:

* un patrón `K₃` deja **a lo sumo una** copia con dos recursos distintos
  (`card_two_resources_le_one`): los dos recursos ya ocupan tres de los tres
  vértices;
* un patrón `K₄` deja a lo sumo `t` copias (`card_two_resources_le_t`): los dos
  recursos fijan tres vértices y el cuarto vive en la única parte que queda, de
  tamaño `≤ t`.

La aritmética de denominadores final no se repite: pasa por
`RC01CanonicalSlackBridge.mixed_codegree_of_common_threshold`, la conclusión ya
certificada del fichero `checks/rc01_cleaned_mixed_codegree.py`.
-/

namespace PaperIV.RC01CleanedMixedCodegree

open Finset
open MixedRounding
open PaperIV.PatternTransfer
open PaperIV.RC01CleanFiber
open PaperIV.RC01CanonicalFractional
open PaperIV.RC01CanonicalNormalization
open PaperIV.RC01CanonicalSlackBridge

variable {V P : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype P] [DecidableEq P]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. El soporte de dos recursos distintos -/

omit [Nonempty V] in
theorem toFinset_subset_of_mem_pairs {K : Finset V} {e : Sym2 V}
    (he : e ∈ pairs K) : e.toFinset ⊆ K := by
  intro a ha
  rw [Sym2.mem_toFinset] at ha
  exact (mem_pairs.1 he).1 a ha

omit [Fintype V] [Nonempty V] in
theorem sym2_eq_of_toFinset_eq {e f : Sym2 V} (hf : ¬ f.IsDiag)
    (h : e.toFinset = f.toFinset) : e = f := by
  revert h
  induction e using Sym2.ind with
  | _ a b =>
    induction f using Sym2.ind with
    | _ c d =>
      intro h
      rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq] at h
      rw [Sym2.isDiag_iff_proj_eq] at hf
      have hc : c ∈ ({a, b} : Finset V) := by rw [h]; simp
      have hd : d ∈ ({a, b} : Finset V) := by rw [h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
      rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
      · exact absurd rfl hf
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hf

omit [Fintype V] [Nonempty V] in
/-- Dos recursos físicos distintos tocan al menos tres vértices. -/
theorem three_le_card_support {e f : Sym2 V} (he : ¬ e.IsDiag) (hf : ¬ f.IsDiag)
    (hef : e ≠ f) : 3 ≤ (e.toFinset ∪ f.toFinset).card := by
  by_contra hlt
  push_neg at hlt
  have hcarde : e.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag e he
  have hcardf : f.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag f hf
  have hsube : e.toFinset ⊆ e.toFinset ∪ f.toFinset := Finset.subset_union_left
  have hsubf : f.toFinset ⊆ e.toFinset ∪ f.toFinset := Finset.subset_union_right
  have hEq : e.toFinset = e.toFinset ∪ f.toFinset :=
    Finset.eq_of_subset_of_card_le hsube (by omega)
  have hsubf' : f.toFinset ⊆ e.toFinset := by rw [hEq]; exact hsubf
  have : f.toFinset = e.toFinset :=
    Finset.eq_of_subset_of_card_le hsubf' (by omega)
  exact hef (sym2_eq_of_toFinset_eq hf this.symm)

/-! ## 2. Las dos cotas de conteo -/

omit [Fintype P] in
/-- **K₃: a lo sumo una copia.**  Dos recursos distintos ocupan ya los tres
vértices de un triángulo del patrón. -/
theorem card_two_resources_le_one {part : V → P} {H : Finset P}
    {C : Finset (Finset V)} (hC : C ⊆ profileFiber G part H) (hH : H.card = 3)
    {e f : Sym2 V} (hef : e ≠ f) :
    (C.filter (fun K => e ∈ pairs K ∧ f ∈ pairs K)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro K hK L hL
  rw [Finset.mem_filter] at hK hL
  have hsupp : ∀ M : Finset V, M ∈ C → e ∈ pairs M → f ∈ pairs M →
      M = e.toFinset ∪ f.toFinset := by
    intro M hM he hf
    obtain ⟨-, -, hcard⟩ := mem_profileFiber.1 (hC hM)
    have hMcard : M.card = 3 := by rw [hcard, hH]
    have hsub : e.toFinset ∪ f.toFinset ⊆ M :=
      Finset.union_subset (toFinset_subset_of_mem_pairs he)
        (toFinset_subset_of_mem_pairs hf)
    have h3 := three_le_card_support (mem_pairs.1 he).2 (mem_pairs.1 hf).2 hef
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  rw [hsupp K hK.1 hK.2.1 hK.2.2, hsupp L hL.1 hL.2.1 hL.2.2]

/-- **K₄: a lo sumo `t` copias.**  Los dos recursos fijan tres vértices; el
cuarto vive en la única parte del patrón que queda libre, de tamaño `≤ t`. -/
theorem card_two_resources_le_t {part : V → P} {H : Finset P}
    {C : Finset (Finset V)} (hC : C ⊆ profileFiber G part H) (hH : H.card = 4)
    (t : ℕ) (ht : 1 ≤ t)
    (hpart : ∀ p ∈ H, (univ.filter (fun v => part v = p)).card ≤ t)
    {e f : Sym2 V} (hef : e ≠ f) :
    (C.filter (fun K => e ∈ pairs K ∧ f ∈ pairs K)).card ≤ t := by
  classical
  set T := C.filter (fun K => e ∈ pairs K ∧ f ∈ pairs K) with hT
  rcases T.eq_empty_or_nonempty with hempty | ⟨K₀, hK₀⟩
  · rw [hempty]
    simpa using ht
  set S := e.toFinset ∪ f.toFinset with hS
  have hmemT : ∀ M ∈ T, M ∈ C ∧ e ∈ pairs M ∧ f ∈ pairs M := by
    intro M hM
    have := Finset.mem_filter.1 hM
    exact ⟨this.1, this.2.1, this.2.2⟩
  have hSsub : ∀ M ∈ T, S ⊆ M := by
    intro M hM
    obtain ⟨-, he, hf⟩ := hmemT M hM
    exact Finset.union_subset (toFinset_subset_of_mem_pairs he)
      (toFinset_subset_of_mem_pairs hf)
  have hMcard : ∀ M ∈ T, M.card = 4 := by
    intro M hM
    obtain ⟨hMC, -, -⟩ := hmemT M hM
    obtain ⟨-, -, hcard⟩ := mem_profileFiber.1 (hC hMC)
    rw [hcard, hH]
  obtain ⟨hK₀C, hK₀e, hK₀f⟩ := hmemT K₀ hK₀
  have h3 : 3 ≤ S.card :=
    three_le_card_support (mem_pairs.1 hK₀e).2 (mem_pairs.1 hK₀f).2 hef
  have h4 : S.card ≤ 4 := by
    have hle := Finset.card_union_le e.toFinset f.toFinset
    rw [Sym2.card_toFinset_of_not_isDiag e (mem_pairs.1 hK₀e).2,
      Sym2.card_toFinset_of_not_isDiag f (mem_pairs.1 hK₀f).2] at hle
    exact hle
  by_cases hS4 : S.card = 4
  · -- los dos recursos son disjuntos: la copia está determinada
    have hall : ∀ M ∈ T, M = S := by
      intro M hM
      exact (Finset.eq_of_subset_of_card_le (hSsub M hM)
        (by rw [hMcard M hM, hS4])).symm
    have hsub : T ⊆ {S} := by
      intro M hM
      rw [Finset.mem_singleton]
      exact hall M hM
    have := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at this
    omega
  · have hS3 : S.card = 3 := by omega
    -- la parte libre del patrón
    obtain ⟨-, himg₀, hcard₀⟩ := mem_profileFiber.1 (hC hK₀C)
    have hinj₀ := injOn_of_mem_profileFiber (hC hK₀C)
    have hSK₀ : S ⊆ K₀ := hSsub K₀ hK₀
    have himgS : (S.image part).card = 3 := by
      rw [← hS3]
      refine Finset.card_image_of_injOn ?_
      intro a ha b hb hab
      exact hinj₀ a (hSK₀ ha) b (hSK₀ hb) hab
    have hsubH : S.image part ⊆ H := by
      rw [← himg₀]
      exact Finset.image_subset_image hSK₀
    have hone : (H \ S.image part).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsubH, hH, himgS]
    obtain ⟨p₀, hp₀⟩ := Finset.card_eq_one.1 hone
    -- la copia queda determinada por su cuarto vértice
    have hmaps : ∀ M ∈ T, M \ S ∈ (univ.filter (fun v => part v = p₀)).powersetCard 1 := by
      intro M hM
      obtain ⟨hMC, -, -⟩ := hmemT M hM
      obtain ⟨-, himgM, -⟩ := mem_profileFiber.1 (hC hMC)
      have hinjM := injOn_of_mem_profileFiber (hC hMC)
      have hSM : S ⊆ M := hSsub M hM
      rw [Finset.mem_powersetCard]
      constructor
      · intro w hw
        rw [Finset.mem_sdiff] at hw
        have hwH : part w ∈ H := by
          rw [← himgM]
          exact Finset.mem_image_of_mem part hw.1
        have hwnot : part w ∉ S.image part := by
          intro hmem
          obtain ⟨s, hs, hps⟩ := Finset.mem_image.1 hmem
          exact hw.2 (hinjM w hw.1 s (hSM hs) hps.symm ▸ hs)
        have : part w ∈ H \ S.image part := Finset.mem_sdiff.2 ⟨hwH, hwnot⟩
        rw [hp₀, Finset.mem_singleton] at this
        exact Finset.mem_filter.2 ⟨Finset.mem_univ w, this⟩
      · rw [Finset.card_sdiff_of_subset hSM, hMcard M hM, hS3]
    have hinjOn : Set.InjOn (fun M => M \ S) (T : Set (Finset V)) := by
      intro M hM N hN hMN
      have hSM : S ⊆ M := hSsub M hM
      have hSN : S ⊆ N := hSsub N hN
      have hMN' : M \ S = N \ S := hMN
      have : (M \ S) ∪ S = (N \ S) ∪ S := by rw [hMN']
      rwa [Finset.sdiff_union_of_subset hSM, Finset.sdiff_union_of_subset hSN] at this
    refine le_trans (Finset.card_le_card_of_injOn (fun M => M \ S) hmaps hinjOn) ?_
    rw [Finset.card_powersetCard, Nat.choose_one_right]
    have hp₀H : p₀ ∈ H := by
      have hp₀diff : p₀ ∈ H \ S.image part := by rw [hp₀]; simp
      exact (Finset.mem_sdiff.1 hp₀diff).1
    exact hpart p₀ hp₀H

/-! ## 3. El codegree mixto -/

/-- **(B)** La forma racional del codegree mixto para dos recursos distintos.
Las dos cotas de conteo son las del apartado anterior; la aritmética final es
`mixed_codegree_of_common_threshold`. -/
theorem cleaned_mixed_codegree_le (part : V → P)
    (A : Finset P → Finset P → ℚ) (vol mass : Finset P → ℚ)
    (u : ℚ) (Pats : Finset (Finset P)) (t : ℕ) (k3 k4 a2 a5 gamma : ℚ)
    (ht : 1 ≤ t) (ha2 : 0 < a2) (ha5 : 0 < a5)
    (hmass0 : ∀ H, 0 ≤ mass H) (hmass1 : ∀ H ∈ Pats, mass H ≤ 1)
    (hcard : ∀ H ∈ Pats, H.card = 3 ∨ H.card = 4)
    (hpart : ∀ H ∈ Pats, ∀ p ∈ H,
      (univ.filter (fun v => part v = p)).card ≤ t)
    (hk3 : ((Pats.filter (fun H => H.card = 3)).card : ℚ) ≤ k3)
    (hk4 : ((Pats.filter (fun H => ¬ H.card = 3)).card : ℚ) ≤ k4)
    (hb3 : ∀ H ∈ Pats, H.card = 3 → a2 * (t : ℚ) ≤ (1 + u) * vol H)
    (hb4 : ∀ H ∈ Pats, H.card = 4 → a5 * (t : ℚ) ^ 2 ≤ (1 + u) * vol H)
    (hthreshold : k3 * a5 + k4 * a2 ≤ gamma * a2 * a5 * (t : ℚ))
    (e f : Sym2 V) (hef : e ≠ f) :
    ∑ H ∈ Pats, (twoCount (cleanFiber G part A u) H e f : ℚ) *
        budgetCoefficient mass (fun H => (1 + u) * vol H) H ≤ gamma := by
  classical
  have htQ : (0 : ℚ) < (t : ℚ) := by exact_mod_cast ht
  -- cota término a término en el brazo K₃
  have hterm3 : ∀ H ∈ Pats.filter (fun H => H.card = 3),
      (twoCount (cleanFiber G part A u) H e f : ℚ) *
        budgetCoefficient mass (fun H => (1 + u) * vol H) H
        ≤ 1 / (a2 * (t : ℚ)) := by
    intro H hH
    rw [Finset.mem_filter] at hH
    have hbud : a2 * (t : ℚ) ≤ (1 + u) * vol H := hb3 H hH.1 hH.2
    have hbudpos : (0 : ℚ) < (1 + u) * vol H := lt_of_lt_of_le (by positivity) hbud
    have hcount : (twoCount (cleanFiber G part A u) H e f : ℚ) ≤ 1 := by
      have := card_two_resources_le_one (G := G)
        (cleanFiber_subset (G := G) part A u H) hH.2 hef
      rw [twoCount]
      exact_mod_cast this
    have hcoeff : budgetCoefficient mass (fun H => (1 + u) * vol H) H
        ≤ 1 / (a2 * (t : ℚ)) := by
      rw [budgetCoefficient, div_le_div_iff₀ hbudpos (by positivity)]
      nlinarith [hmass0 H, hmass1 H hH.1]
    have hcoeff0 : 0 ≤ budgetCoefficient mass (fun H => (1 + u) * vol H) H :=
      div_nonneg (hmass0 H) hbudpos.le
    have hcount0 : (0 : ℚ) ≤ (twoCount (cleanFiber G part A u) H e f : ℚ) := by
      positivity
    nlinarith
  -- cota término a término en el brazo K₄
  have hterm4 : ∀ H ∈ Pats.filter (fun H => ¬ H.card = 3),
      (twoCount (cleanFiber G part A u) H e f : ℚ) *
        budgetCoefficient mass (fun H => (1 + u) * vol H) H
        ≤ 1 / (a5 * (t : ℚ)) := by
    intro H hH
    rw [Finset.mem_filter] at hH
    have hH4 : H.card = 4 := by
      rcases hcard H hH.1 with h | h
      · exact absurd h hH.2
      · exact h
    have hbud : a5 * (t : ℚ) ^ 2 ≤ (1 + u) * vol H := hb4 H hH.1 hH4
    have hbudpos : (0 : ℚ) < (1 + u) * vol H := lt_of_lt_of_le (by positivity) hbud
    have hcount : (twoCount (cleanFiber G part A u) H e f : ℚ) ≤ (t : ℚ) := by
      have := card_two_resources_le_t (G := G)
        (cleanFiber_subset (G := G) part A u H) hH4 t ht (hpart H hH.1) hef
      rw [twoCount]
      exact_mod_cast this
    have hcoeff : budgetCoefficient mass (fun H => (1 + u) * vol H) H
        ≤ 1 / (a5 * (t : ℚ) ^ 2) := by
      rw [budgetCoefficient, div_le_div_iff₀ hbudpos (by positivity)]
      nlinarith [hmass0 H, hmass1 H hH.1]
    have hcoeff0 : 0 ≤ budgetCoefficient mass (fun H => (1 + u) * vol H) H :=
      div_nonneg (hmass0 H) hbudpos.le
    have hcount0 : (0 : ℚ) ≤ (twoCount (cleanFiber G part A u) H e f : ℚ) := by
      positivity
    have hstep : (twoCount (cleanFiber G part A u) H e f : ℚ) *
        budgetCoefficient mass (fun H => (1 + u) * vol H) H
        ≤ (t : ℚ) * (1 / (a5 * (t : ℚ) ^ 2)) := by
      have h1 : (twoCount (cleanFiber G part A u) H e f : ℚ) *
          budgetCoefficient mass (fun H => (1 + u) * vol H) H
          ≤ (t : ℚ) * budgetCoefficient mass (fun H => (1 + u) * vol H) H :=
        mul_le_mul_of_nonneg_right hcount hcoeff0
      have h2 : (t : ℚ) * budgetCoefficient mass (fun H => (1 + u) * vol H) H
          ≤ (t : ℚ) * (1 / (a5 * (t : ℚ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hcoeff htQ.le
      linarith
    have hsimp : (t : ℚ) * (1 / (a5 * (t : ℚ) ^ 2)) = 1 / (a5 * (t : ℚ)) := by
      field_simp
    rw [hsimp] at hstep
    exact hstep
  -- suma de los dos brazos
  have hsplit : ∑ H ∈ Pats, (twoCount (cleanFiber G part A u) H e f : ℚ) *
        budgetCoefficient mass (fun H => (1 + u) * vol H) H
      ≤ k3 / (a2 * (t : ℚ)) + k4 / (a5 * (t : ℚ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Pats (fun H => H.card = 3)]
    have harm3 : ∑ H ∈ Pats.filter (fun H => H.card = 3),
        (twoCount (cleanFiber G part A u) H e f : ℚ) *
          budgetCoefficient mass (fun H => (1 + u) * vol H) H
        ≤ k3 / (a2 * (t : ℚ)) := by
      calc ∑ H ∈ Pats.filter (fun H => H.card = 3),
            (twoCount (cleanFiber G part A u) H e f : ℚ) *
              budgetCoefficient mass (fun H => (1 + u) * vol H) H
          ≤ ∑ _H ∈ Pats.filter (fun H => H.card = 3), 1 / (a2 * (t : ℚ)) :=
            Finset.sum_le_sum hterm3
        _ = ((Pats.filter (fun H => H.card = 3)).card : ℚ) * (1 / (a2 * (t : ℚ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ k3 * (1 / (a2 * (t : ℚ))) :=
            mul_le_mul_of_nonneg_right hk3 (by positivity)
        _ = k3 / (a2 * (t : ℚ)) := by ring
    have harm4 : ∑ H ∈ Pats.filter (fun H => ¬ H.card = 3),
        (twoCount (cleanFiber G part A u) H e f : ℚ) *
          budgetCoefficient mass (fun H => (1 + u) * vol H) H
        ≤ k4 / (a5 * (t : ℚ)) := by
      calc ∑ H ∈ Pats.filter (fun H => ¬ H.card = 3),
            (twoCount (cleanFiber G part A u) H e f : ℚ) *
              budgetCoefficient mass (fun H => (1 + u) * vol H) H
          ≤ ∑ _H ∈ Pats.filter (fun H => ¬ H.card = 3), 1 / (a5 * (t : ℚ)) :=
            Finset.sum_le_sum hterm4
        _ = ((Pats.filter (fun H => ¬ H.card = 3)).card : ℚ) * (1 / (a5 * (t : ℚ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ k4 * (1 / (a5 * (t : ℚ))) :=
            mul_le_mul_of_nonneg_right hk4 (by positivity)
        _ = k4 / (a5 * (t : ℚ)) := by ring
    linarith
  exact mixed_codegree_of_common_threshold htQ ha2 ha5 hsplit hthreshold

/-- Dimensionally scaled form of `cleaned_mixed_codegree_le`.

The transferred mass of one reduced pattern is not normally bounded by `1`;
it is bounded by a physical pair scale `D` (in the equitable application,
`D ≤ t^2`).  Dividing both mass and budget by `D` reduces exactly to the
normalized theorem, without changing any budget coefficient. -/
theorem cleaned_mixed_codegree_le_of_mass_le (part : V → P)
    (A : Finset P → Finset P → ℚ) (vol mass : Finset P → ℚ)
    (u : ℚ) (Pats : Finset (Finset P))
    (t : ℕ) (D k3 k4 a2 a5 gamma : ℚ)
    (ht : 1 ≤ t) (hD : 0 < D) (ha2 : 0 < a2) (ha5 : 0 < a5)
    (hmass0 : ∀ H, 0 ≤ mass H) (hmassD : ∀ H ∈ Pats, mass H ≤ D)
    (hcard : ∀ H ∈ Pats, H.card = 3 ∨ H.card = 4)
    (hpart : ∀ H ∈ Pats, ∀ p ∈ H,
      (univ.filter (fun v => part v = p)).card ≤ t)
    (hk3 : ((Pats.filter (fun H => H.card = 3)).card : ℚ) ≤ k3)
    (hk4 : ((Pats.filter (fun H => ¬ H.card = 3)).card : ℚ) ≤ k4)
    (hb3 : ∀ H ∈ Pats, H.card = 3 → a2 * D * (t : ℚ) ≤ (1 + u) * vol H)
    (hb4 : ∀ H ∈ Pats, H.card = 4 → a5 * D * (t : ℚ) ^ 2 ≤ (1 + u) * vol H)
    (hthreshold : k3 * a5 + k4 * a2 ≤ gamma * a2 * a5 * (t : ℚ))
    (e f : Sym2 V) (hef : e ≠ f) :
    ∑ H ∈ Pats, (twoCount (cleanFiber G part A u) H e f : ℚ) *
        budgetCoefficient mass (fun H => (1 + u) * vol H) H ≤ gamma := by
  have hmass0' : ∀ H, 0 ≤ mass H / D := fun H => div_nonneg (hmass0 H) hD.le
  have hmass1' : ∀ H ∈ Pats, mass H / D ≤ 1 := by
    intro H hH
    exact (div_le_one hD).2 (hmassD H hH)
  have hb3' : ∀ H ∈ Pats, H.card = 3 →
      a2 * (t : ℚ) ≤ (1 + u) * (vol H / D) := by
    intro H hH hH3
    rw [show (1 + u) * (vol H / D) = ((1 + u) * vol H) / D by ring,
      le_div_iff₀ hD]
    nlinarith [hb3 H hH hH3]
  have hb4' : ∀ H ∈ Pats, H.card = 4 →
      a5 * (t : ℚ) ^ 2 ≤ (1 + u) * (vol H / D) := by
    intro H hH hH4
    rw [show (1 + u) * (vol H / D) = ((1 + u) * vol H) / D by ring,
      le_div_iff₀ hD]
    nlinarith [hb4 H hH hH4]
  have hbase := cleaned_mixed_codegree_le (G := G) part A (fun H => vol H / D)
    (fun H => mass H / D) u Pats t k3 k4 a2 a5 gamma ht ha2 ha5 hmass0'
    hmass1' hcard hpart hk3 hk4 hb3' hb4' hthreshold e f hef
  have hcoeff : ∀ H,
      budgetCoefficient (fun J => mass J / D)
          (fun J => (1 + u) * (vol J / D)) H =
        budgetCoefficient mass (fun J => (1 + u) * vol J) H := by
    intro H
    simp only [budgetCoefficient]
    field_simp [ne_of_gt hD]
  calc
    ∑ H ∈ Pats, (twoCount (cleanFiber G part A u) H e f : ℚ) *
          budgetCoefficient mass (fun H => (1 + u) * vol H) H =
        ∑ H ∈ Pats, (twoCount (cleanFiber G part A u) H e f : ℚ) *
          budgetCoefficient (fun J => mass J / D)
            (fun J => (1 + u) * (vol J / D)) H := by
              apply Finset.sum_congr rfl
              intro H _
              rw [hcoeff H]
    _ ≤ gamma := hbase

end PaperIV.RC01CleanedMixedCodegree
