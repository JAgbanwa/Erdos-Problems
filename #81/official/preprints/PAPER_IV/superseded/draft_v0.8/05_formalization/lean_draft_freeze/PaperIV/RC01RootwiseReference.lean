import PaperIV.RC01CleanFiber

/-!
# RC01: referencia exacta dependiente de la posición de raíz

La limpieza de una fibra no puede usar, en general, un único centro para sus
tres o seis posiciones de raíz.  Este módulo fija la referencia correcta sin
ninguna elección: para una posición física `pq` del perfil `H`, el centro es el
promedio exacto

```
card (profileFiber G part H) / max 1 (card (crossPair G part pq)).
```

Fuera de las posiciones de dos partes contenidas en `H` se usa cero.  La
identidad centro por escala de la pareja = volumen de la fibra descarga de
forma literal la hipótesis `hvol` de `RC01CleanedGate`; la regularidad sólo se
necesita después para controlar la varianza alrededor de este promedio.
-/

namespace PaperIV.RC01RootwiseReference

open Finset
open PaperIV.PatternTransfer
open PaperIV.RC01CleanFiber

variable {V P : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype P] [DecidableEq P]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Escala física de una posición de raíz, con el mismo `max 1` que `densT`. -/
noncomputable def pairScale (part : V → P) (pq : Finset P) : ℚ :=
  max 1 ((crossPair G part pq).card : ℚ)

/-- Volumen literal de un perfil. -/
noncomputable def profileVolume (part : V → P) (H : Finset P) : ℚ :=
  ((profileFiber G part H).card : ℚ)

/-- Centro exacto de la cuenta enraizada en la posición `pq`. -/
noncomputable def rootwiseReference (part : V → P) (H pq : Finset P) : ℚ :=
  if pq.card = 2 ∧ pq ⊆ H then profileVolume (G := G) part H / pairScale (G := G) part pq
  else 0

theorem pairScale_pos (part : V → P) (pq : Finset P) :
    0 < pairScale (G := G) part pq := by
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem densT_eq_pairScale (part : V → P) (e : Sym2 V) :
    densT G part e = pairScale (G := G) part (partsOf part e) := rfl

theorem profileVolume_nonneg (part : V → P) (H : Finset P) :
    0 ≤ profileVolume (G := G) part H := by
  rw [profileVolume]
  exact_mod_cast Nat.zero_le (profileFiber G part H).card

/-- La referencia exacta satisface el presupuesto de dispersión para toda
arista. En una posición activa hay igualdad; fuera de ella el lado izquierdo
es cero. -/
theorem rootwiseReference_mul_densT_le_profileVolume
    (part : V → P) (H : Finset P) (e : Sym2 V) :
    rootwiseReference (G := G) part H (partsOf part e) * densT G part e
      ≤ profileVolume (G := G) part H := by
  rw [densT_eq_pairScale]
  unfold rootwiseReference
  split_ifs with h
  · have hs : pairScale (G := G) part (partsOf part e) ≠ 0 :=
      ne_of_gt (pairScale_pos (G := G) part (partsOf part e))
    rw [div_mul_cancel₀ _ hs]
  · simpa using profileVolume_nonneg (G := G) part H

/-- La cota anterior en la forma funcional consumida por
`RC01CleanedGate.cleanedPacking`. -/
theorem rootwiseReference_volume_budget (part : V → P) :
    ∀ H : Finset P, ∀ e : Sym2 V,
      rootwiseReference (G := G) part H (partsOf part e) * densT G part e
        ≤ profileVolume (G := G) part H := by
  exact fun H e => rootwiseReference_mul_densT_le_profileVolume
    (G := G) part H e

theorem profileVolume_eq_card (part : V → P) (H : Finset P) :
    profileVolume (G := G) part H = ((profileFiber G part H).card : ℚ) := rfl

theorem profileVolume_pos_iff (part : V → P) (H : Finset P) :
    0 < profileVolume (G := G) part H ↔ (profileFiber G part H).Nonempty := by
  rw [profileVolume]
  exact_mod_cast Finset.card_pos

/-- A fixed two-colour root set is exactly the symmetrised graph interedge set
between the two literal colour classes. -/
theorem crossPair_pair_eq_interedges_image (part : V → P) {p q : P}
    (hpq : p ≠ q) :
    crossPair G part {p, q} =
      (G.interedges (univ.filter (fun v => part v = p))
        (univ.filter (fun v => part v = q))).image (fun ab => s(ab.1, ab.2)) := by
  classical
  ext e
  constructor
  · intro he
    have he' := Finset.mem_filter.1 he
    obtain ⟨hEdge, hprof⟩ := he'
    induction e using Sym2.ind with
    | _ a b =>
      rw [partsOf_mk] at hprof
      rw [SimpleGraph.mem_edgeFinset] at hEdge
      have ha : part a = p ∨ part a = q := by
        have : part a ∈ ({p, q} : Finset P) := by rw [← hprof]; simp
        simpa using this
      have hb : part b = p ∨ part b = q := by
        have : part b ∈ ({p, q} : Finset P) := by rw [← hprof]; simp
        simpa using this
      rcases ha with hap | haq <;> rcases hb with hbp | hbq
      · rw [hap, hbp] at hprof
        have hcards := congrArg Finset.card hprof
        simp [hpq] at hcards
      · rw [Finset.mem_image]
        refine ⟨(a, b), ?_, rfl⟩
        rw [SimpleGraph.mem_interedges_iff]
        exact ⟨by simp [hap], by simp [hbq], hEdge⟩
      · rw [Finset.mem_image]
        refine ⟨(b, a), ?_, Sym2.eq_swap⟩
        rw [SimpleGraph.mem_interedges_iff]
        exact ⟨by simp [hbp], by simp [haq], G.symm hEdge⟩
      · rw [haq, hbq] at hprof
        have hcards := congrArg Finset.card hprof
        simp [hpq] at hcards
  · intro he
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.1 he
    rw [SimpleGraph.mem_interedges_iff] at hab
    rw [crossPair, Finset.mem_filter, SimpleGraph.mem_edgeFinset, partsOf_mk]
    have hap : part ab.1 = p := (Finset.mem_filter.1 hab.1).2
    have hbq : part ab.2 = q := (Finset.mem_filter.1 hab.2.1).2
    exact ⟨hab.2.2, by rw [hap, hbq]⟩

/-- En una posición genuina del perfil, la raíz canónica de cada copia de la
fibra pertenece al conjunto físico `crossPair` correspondiente. -/
theorem rootEdge_mem_crossPair_of_active {part : V → P} {H pq : Finset P}
    (hpqcard : pq.card = 2) (hpqsub : pq ⊆ H)
    {K : Finset V} (hK : K ∈ profileFiber G part H) :
    rootEdge part pq K ∈ crossPair G part pq := by
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hpqcard
  have hprof := mem_profileFiber.1 hK
  have hpH : p ∈ H := hpqsub (by simp)
  have hqH : q ∈ H := hpqsub (by simp)
  have hpim : p ∈ K.image part := by simpa [hprof.2.1] using hpH
  have hqim : q ∈ K.image part := by simpa [hprof.2.1] using hqH
  obtain ⟨a, haK, ha⟩ := Finset.mem_image.mp hpim
  obtain ⟨b, hbK, hb⟩ := Finset.mem_image.mp hqim
  have hab : a ≠ b := by
    intro hab
    apply hpq
    rw [← ha, ← hb, hab]
  have he : s(a, b) ∈ MixedRounding.pairs K := by
    rw [MixedRounding.mk_mem_pairs]
    exact ⟨haK, hbK, hab⟩
  have hparts : partsOf part s(a, b) = {p, q} := by
    rw [partsOf_mk, ha, hb]
  have hroot₀ := rootEdge_eq_of_mem_pairs hK he
  have hroot : rootEdge part {p, q} K = s(a, b) := by
    rw [hparts] at hroot₀
    exact hroot₀
  rw [hroot, crossPair, Finset.mem_filter]
  refine ⟨MixedRounding.pairs_subset_edgeFinset (MixedRounding.mem_items.1 hprof.1) he, ?_⟩
  rw [partsOf_mk, ha, hb]

/-- Primer momento literal de una posición activa: sumar sus cuentas
enraizadas recupera exactamente el volumen de la fibra. -/
theorem sum_rootCount_eq_profileVolume {part : V → P} {H pq : Finset P}
    (hpqcard : pq.card = 2) (hpqsub : pq ⊆ H) :
    ∑ e ∈ crossPair G part pq, rootCount G part H pq e
      = profileVolume (G := G) part H := by
  have hsum := PaperIV.RootedCountingBridge.sum_fiber_card
    (profileFiber G part H) (rootEdge part pq) (crossPair G part pq)
    (fun K hK => rootEdge_mem_crossPair_of_active
      (G := G) hpqcard hpqsub hK)
  change (∑ e ∈ crossPair G part pq,
      (((PaperIV.RootedCountingBridge.fiber (profileFiber G part H)
        (rootEdge part pq) e).card : ℕ) : ℚ))
      = (((profileFiber G part H).card : ℕ) : ℚ)
  exact_mod_cast hsum

theorem crossPair_nonempty_of_profileFiber_nonempty_active
    {part : V → P} {H pq : Finset P}
    (hpqcard : pq.card = 2) (hpqsub : pq ⊆ H)
    (hne : (profileFiber G part H).Nonempty) :
    (crossPair G part pq).Nonempty := by
  obtain ⟨K, hK⟩ := hne
  exact ⟨rootEdge part pq K,
    rootEdge_mem_crossPair_of_active (G := G) hpqcard hpqsub hK⟩

theorem pairScale_eq_card_of_profileFiber_nonempty_active
    {part : V → P} {H pq : Finset P}
    (hpqcard : pq.card = 2) (hpqsub : pq ⊆ H)
    (hne : (profileFiber G part H).Nonempty) :
    pairScale (G := G) part pq = ((crossPair G part pq).card : ℚ) := by
  rw [pairScale, max_eq_right]
  exact_mod_cast (crossPair_nonempty_of_profileFiber_nonempty_active
    (G := G) hpqcard hpqsub hne).card_pos

theorem rootwiseReference_pos_of_profileFiber_nonempty_active
    {part : V → P} {H pq : Finset P}
    (hpqcard : pq.card = 2) (hpqsub : pq ⊆ H)
    (hne : (profileFiber G part H).Nonempty) :
    0 < rootwiseReference (G := G) part H pq := by
  rw [rootwiseReference, if_pos ⟨hpqcard, hpqsub⟩]
  apply div_pos
  · rw [profileVolume_eq_card]
    exact_mod_cast hne.card_pos
  · exact pairScale_pos (G := G) part pq

theorem rootwiseReference_mul_pairScale_eq_profileVolume
    {part : V → P} {H pq : Finset P}
    (hpqcard : pq.card = 2) (hpqsub : pq ⊆ H) :
    rootwiseReference (G := G) part H pq * pairScale (G := G) part pq
      = profileVolume (G := G) part H := by
  rw [rootwiseReference, if_pos ⟨hpqcard, hpqsub⟩]
  field_simp [ne_of_gt (pairScale_pos (G := G) part pq)]

/-- A lower volume bound and an upper root-scale bound give a lower bound on
the exact mean, without dividing by a model density. -/
theorem rootwiseReference_lower_of_volume_scale
    {part : V → P} {H pq : Finset P} {c M : ℚ}
    (hpqcard : pq.card = 2) (hpqsub : pq ⊆ H)
    (hM : 0 < M)
    (hvol : c * M ≤ profileVolume (G := G) part H)
    (hscale : pairScale (G := G) part pq ≤ M) :
    c ≤ rootwiseReference (G := G) part H pq := by
  have href0 : 0 ≤ rootwiseReference (G := G) part H pq := by
    rw [rootwiseReference, if_pos ⟨hpqcard, hpqsub⟩]
    exact div_nonneg (profileVolume_nonneg (G := G) part H)
      (le_of_lt (pairScale_pos (G := G) part pq))
  have hid := rootwiseReference_mul_pairScale_eq_profileVolume
    (G := G) (part := part) hpqcard hpqsub
  have hupper : profileVolume (G := G) part H
      ≤ rootwiseReference (G := G) part H pq * M := by
    rw [← hid]
    exact mul_le_mul_of_nonneg_left hscale href0
  exact le_of_mul_le_mul_right (hvol.trans hupper) hM

theorem sum_rootCount_sub_rootwiseReference_eq_zero
    {part : V → P} {H pq : Finset P}
    (hpqcard : pq.card = 2) (hpqsub : pq ⊆ H)
    (hne : (profileFiber G part H).Nonempty) :
    ∑ e ∈ crossPair G part pq,
      (rootCount G part H pq e - rootwiseReference (G := G) part H pq) = 0 := by
  have hscale := pairScale_eq_card_of_profileFiber_nonempty_active
    (G := G) hpqcard hpqsub hne
  have hcardpos : (0 : ℚ) < ((crossPair G part pq).card : ℚ) := by
    exact_mod_cast (crossPair_nonempty_of_profileFiber_nonempty_active
      (G := G) hpqcard hpqsub hne).card_pos
  rw [rootwiseReference, if_pos ⟨hpqcard, hpqsub⟩, hscale]
  rw [Finset.sum_sub_distrib, sum_rootCount_eq_profileVolume
    (G := G) hpqcard hpqsub, Finset.sum_const, nsmul_eq_mul]
  field_simp
  ring

/-! ## El promedio exacto sólo mejora el segundo momento -/

/-- Entre todos los centros escalares, el promedio minimiza la suma de
desviaciones cuadráticas. La hipótesis se da en la forma sin división que
produce `RootedCountingBridge.sum_fiber_card`. -/
theorem sum_sq_sub_mean_le {I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → ℚ) (mean a : ℚ)
    (hmean : ∑ i ∈ s, (f i - mean) = 0) :
    ∑ i ∈ s, (f i - mean) ^ 2 ≤ ∑ i ∈ s, (f i - a) ^ 2 := by
  have hid :
      (∑ i ∈ s, (f i - a) ^ 2)
        = (∑ i ∈ s, (f i - mean) ^ 2)
          + 2 * (mean - a) * (∑ i ∈ s, (f i - mean))
          + (s.card : ℚ) * (mean - a) ^ 2 := by
    calc
      (∑ i ∈ s, (f i - a) ^ 2)
          = ∑ i ∈ s,
              ((f i - mean) ^ 2 + 2 * (mean - a) * (f i - mean)
                + (mean - a) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = (∑ i ∈ s, (f i - mean) ^ 2)
          + 2 * (mean - a) * (∑ i ∈ s, (f i - mean))
          + (s.card : ℚ) * (mean - a) ^ 2 := by
              simp only [Finset.sum_add_distrib, Finset.mul_sum]
              rw [Finset.sum_const, nsmul_eq_mul]
  rw [hid, hmean]
  have hcard : (0 : ℚ) ≤ (s.card : ℚ) := by positivity
  nlinarith [sq_nonneg (mean - a)]

/-- Any rooted second-moment estimate around a model centre remains valid
after recentering at the exact physical mean. -/
theorem second_moment_rootwiseReference_le
    {part : V → P} {H pq : Finset P}
    (hpqcard : pq.card = 2) (hpqsub : pq ⊆ H)
    (hne : (profileFiber G part H).Nonempty) (model B : ℚ)
    (hmodel : ∑ e ∈ crossPair G part pq,
      (rootCount G part H pq e - model) ^ 2 ≤ B) :
    ∑ e ∈ crossPair G part pq,
      (rootCount G part H pq e - rootwiseReference (G := G) part H pq) ^ 2 ≤ B := by
  exact (sum_sq_sub_mean_le (crossPair G part pq)
    (rootCount G part H pq) (rootwiseReference (G := G) part H pq) model
    (sum_rootCount_sub_rootwiseReference_eq_zero
      (G := G) hpqcard hpqsub hne)).trans hmodel

/-- Chebyshev for the literal cleanup set after recentering a rooted counting
estimate at the exact physical mean. -/
theorem badRoots_card_mul_sq_le_of_model_second_moment
    {part : V → P} {H pq : Finset P}
    (hpqcard : pq.card = 2) (hpqsub : pq ⊆ H)
    (hne : (profileFiber G part H).Nonempty) {u model B : ℚ}
    (hu : 0 < u)
    (hmodel : ∑ e ∈ crossPair G part pq,
      (rootCount G part H pq e - model) ^ 2 ≤ B) :
    ((badRoots G part (rootwiseReference (G := G) part) u H pq).card : ℚ) *
        (u * rootwiseReference (G := G) part H pq) ^ 2 ≤ B := by
  exact PaperIV.RC01DeviationCleanup.card_deviationBad_mul_le
    (crossPair G part pq) (rootCount G part H pq)
    (rootwiseReference (G := G) part H pq) u B hu
    (rootwiseReference_pos_of_profileFiber_nonempty_active
      (G := G) hpqcard hpqsub hne)
    (second_moment_rootwiseReference_le
      (G := G) hpqcard hpqsub hne model B hmodel)

end PaperIV.RC01RootwiseReference
