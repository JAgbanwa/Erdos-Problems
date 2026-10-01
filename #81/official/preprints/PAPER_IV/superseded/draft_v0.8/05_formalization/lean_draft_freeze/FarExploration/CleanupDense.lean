import FarExploration.CleanupThreshold

/-!
# El extremo denso: en `K_n` la limpieza es gratis

Este módulo formaliza el extremo opuesto al rígido: en el grafo **completo** la limpieza de
codegrado no cuesta casi nada.  El testigo es el reparto uniforme sobre **todos** los `K₄`,
mezclado con una fracción `θ` de reparto uniforme sobre todos los triángulos:

```
w = 2(1-θ)/((n-2)(n-3))   sobre cada K₄,      u = θ/(n-2)   sobre cada triángulo.
```

* la carga de cada arista es exactamente `(1-θ) + θ = 1`;
* el codegrado de cualquier par de aristas distintas es `≤ u + w(n-3) ≤ 3/(n-2) → 0`;
* la masa triangular es `θ·n(n-1)/6`, que supera cualquier constante;
* y el valor es `(1-θ)·5n(n-1)/12 + θ·n(n-1)/3`, a distancia `θ·n(n-1)/12` del **máximo
  posible** `5n(n-1)/12` de cualquier empaquetamiento fraccional de `K_n`.

Tomando `θ = min 1 (12·xi)` la pérdida cabe en `xi·n²`.  Es decir: en el extremo denso el
enunciado `CodegreeCleanupAt` se cumple **sin hipótesis de masa sobre `x`** y con umbral
explícito.  Confirma que el enunciado no es vacuo y muestra la forma del operador de suavizado:
repartir el peso entre todos los items competidores.
-/

namespace FarExploration.CleanupDense

open Finset MixedRounding

/-! ## 1. Conteo de superconjuntos -/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Cuántos conjuntos de tamaño `r` contienen a un conjunto dado.** -/
lemma card_filter_superset (S : Finset α) (r : ℕ) (h : S.card ≤ r) :
    (((univ : Finset α).powersetCard r).filter (fun K => S ⊆ K)).card
      = (Fintype.card α - S.card).choose (r - S.card) := by
  classical
  have hcard : (((univ : Finset α) \ S).powersetCard (r - S.card)).card
      = (Fintype.card α - S.card).choose (r - S.card) := by
    rw [Finset.card_powersetCard, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  rw [← hcard]
  refine Finset.card_bij' (fun K _ => K \ S) (fun L _ => L ∪ S) ?_ ?_ ?_ ?_
  · intro K hK
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hK
    obtain ⟨⟨-, hKcard⟩, hSK⟩ := hK
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.sdiff_subset_sdiff (Finset.subset_univ K) (le_refl S), ?_⟩
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 hSK, hKcard]
  · intro L hL
    rw [Finset.mem_powersetCard] at hL
    obtain ⟨hLsub, hLcard⟩ := hL
    have hdisj : Disjoint L S := by
      refine Finset.disjoint_left.2 fun a haL haS => ?_
      have := hLsub haL
      rw [Finset.mem_sdiff] at this
      exact this.2 haS
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.subset_union_right⟩
    rw [Finset.card_union_of_disjoint hdisj, hLcard]
    omega
  · intro K hK
    rw [Finset.mem_filter] at hK
    exact Finset.sdiff_union_of_subset hK.2
  · intro L hL
    rw [Finset.mem_powersetCard] at hL
    have hdisj : Disjoint L S := by
      refine Finset.disjoint_left.2 fun a haL haS => ?_
      have := hL.1 haL
      rw [Finset.mem_sdiff] at this
      exact this.2 haS
    show (L ∪ S) \ S = L
    rw [Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint hdisj]

/-! ## 2. La cota universal de valor por número de aristas -/

section ValueBound

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **El valor de un empaquetamiento fraccional no pasa de `(5/6)·|E|`.**  Cada item gana a lo
sumo `5/6` por arista que ocupa, y la carga total sobre cada arista es `≤ 1`. -/
lemma value_le_edges (x : FracPacking G) :
    x.value ≤ (5 / 6 : ℚ) * (G.edgeFinset.card : ℚ) := by
  classical
  have hgain : ∀ K ∈ items G, gainF ℚ K * x.weight K
      ≤ (5 / 6 : ℚ) * (((pairs K).card : ℕ) : ℚ) * x.weight K := by
    intro K hK
    have hitem := mem_items.1 hK
    have hw := x.weight_nonneg K
    have e32 : Nat.choose 3 2 = 3 := by decide
    have e42 : Nat.choose 4 2 = 6 := by decide
    rcases hitem.2 with h3 | h4
    · rw [card_pairs, h3, e32, gainF, h3, e32]
      nlinarith [hw]
    · rw [card_pairs, h4, e42, gainF, h4, e42]
      nlinarith [hw]
  have hsum1 : x.value ≤ (5 / 6 : ℚ) * ∑ K ∈ items G, (((pairs K).card : ℕ) : ℚ) * x.weight K := by
    rw [FracPacking.value, Finset.mul_sum]
    refine Finset.sum_le_sum fun K hK => ?_
    have := hgain K hK
    linarith [this]
  have hcount : ∀ K ∈ items G, (((pairs K).card : ℕ) : ℚ)
      = ∑ e ∈ G.edgeFinset, (if e ∈ pairs K then (1 : ℚ) else 0) := by
    intro K hK
    rw [Finset.sum_ite_mem]
    have hsub : G.edgeFinset ∩ pairs K = pairs K :=
      Finset.inter_eq_right.2 (pairs_subset_edgeFinset (mem_items.1 hK))
    rw [hsub, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hdouble : ∑ K ∈ items G, (((pairs K).card : ℕ) : ℚ) * x.weight K
      = ∑ e ∈ G.edgeFinset, ∑ K ∈ items G, (if e ∈ pairs K then x.weight K else 0) := by
    rw [Finset.sum_congr rfl (fun K hK => by rw [hcount K hK, Finset.sum_mul]), Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun K _ => ?_
    by_cases h : e ∈ pairs K <;> simp [h]
  have hload : ∑ e ∈ G.edgeFinset, ∑ K ∈ items G, (if e ∈ pairs K then x.weight K else 0)
      ≤ (G.edgeFinset.card : ℚ) := by
    calc ∑ e ∈ G.edgeFinset, ∑ K ∈ items G, (if e ∈ pairs K then x.weight K else 0)
        ≤ ∑ _e ∈ G.edgeFinset, (1 : ℚ) := Finset.sum_le_sum fun e he => x.capacity e he
      _ = (G.edgeFinset.card : ℚ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hdouble] at hsum1
  linarith [hsum1, hload]

/-- El codegrado ponderado de un empaquetamiento, escrito como suma sobre items. -/
lemma codeg_eq_sum_items (x : FracPacking G) (e f : Sym2 V) :
    ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter (fun S => e ∈ S ∧ f ∈ S),
        inducedWeight x S
      = ((∑ K ∈ (items G).filter (fun K => e ∈ pairs K ∧ f ∈ pairs K), x.weight K : ℚ) : ℝ) := by
  classical
  rw [FarExploration.CleanupBridge.jointSupports_eq_supports (G := G),
    FarExploration.CleanupBridge.sum_supports_filter (M := ℝ) (fun S => e ∈ S ∧ f ∈ S)
      (fun S => inducedWeight x S), Rat.cast_sum]
  refine Finset.sum_congr rfl fun K hK => ?_
  exact inducedWeight_pairs x (mem_items.1 (Finset.mem_filter.1 hK).1)

end ValueBound

/-! ## 3. El grafo completo: items, conteos y el empaquetamiento uniforme -/

section Complete

variable {n : ℕ}

lemma mem_items_top {K : Finset (Fin n)} :
    K ∈ items (⊤ : SimpleGraph (Fin n)) ↔ (K.card = 3 ∨ K.card = 4) := by
  rw [mem_items]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨fun a _ b _ hab => by simpa [SimpleGraph.top_adj] using hab, h⟩

lemma items_top_eq : items (⊤ : SimpleGraph (Fin n))
    = (univ.powersetCard 3) ∪ (univ.powersetCard 4) := by
  ext K
  rw [mem_items_top, Finset.mem_union, Finset.mem_powersetCard_univ,
    Finset.mem_powersetCard_univ]

lemma sum_items_top {M : Type*} [AddCommMonoid M] (g : Finset (Fin n) → M) :
    ∑ K ∈ items (⊤ : SimpleGraph (Fin n)), g K
      = ∑ K ∈ univ.powersetCard 3, g K + ∑ K ∈ univ.powersetCard 4, g K := by
  classical
  rw [items_top_eq, Finset.sum_union]
  refine Finset.disjoint_left.2 fun K h3 h4 => ?_
  rw [Finset.mem_powersetCard_univ] at h3 h4
  omega

/-- Cuántos items de tamaño `r` contienen a `S`. -/
def cnt (S : Finset (Fin n)) (r : ℕ) : ℕ :=
  ((univ.powersetCard r).filter (fun K => S ⊆ K)).card

lemma cnt_eq (S : Finset (Fin n)) (r : ℕ) (h : S.card ≤ r) :
    cnt S r = (n - S.card).choose (r - S.card) := by
  rw [cnt, card_filter_superset S r h, Fintype.card_fin]

lemma cnt_eq_zero (S : Finset (Fin n)) (r : ℕ) (h : r < S.card) : cnt S r = 0 := by
  rw [cnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro K hK hsub
  rw [Finset.mem_powersetCard_univ] at hK
  have := Finset.card_le_card hsub
  omega

lemma sum_powersetCard_filter (S : Finset (Fin n)) (r : ℕ) (c : ℚ) :
    ∑ K ∈ univ.powersetCard r, (if S ⊆ K then c else 0) = c * (cnt S r : ℚ) := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, cnt, mul_comm]

/-! ### Los pesos -/

/-- Peso uniforme sobre cada `K₄`. -/
def dw (n : ℕ) (θ : ℚ) : ℚ := (1 - θ) / (((n - 2).choose 2 : ℕ) : ℚ)

/-- Peso uniforme sobre cada triángulo. -/
def du (n : ℕ) (θ : ℚ) : ℚ := θ / (((n - 2).choose 1 : ℕ) : ℚ)

/-- El peso conjunto. -/
def dwt (n : ℕ) (θ : ℚ) (K : Finset (Fin n)) : ℚ :=
  if K.card = 4 then dw n θ else if K.card = 3 then du n θ else 0

lemma choose_one_pos (hn : 5 ≤ n) : 0 < ((n - 2).choose 1) := by
  rw [Nat.choose_one_right]
  omega

lemma choose_two_pos (hn : 5 ≤ n) : 0 < ((n - 2).choose 2) :=
  Nat.choose_pos (by omega)

lemma dw_nonneg (hn : 5 ≤ n) {θ : ℚ} (hθ1 : θ ≤ 1) : 0 ≤ dw n θ := by
  have h := choose_two_pos hn
  have : (0 : ℚ) < (((n - 2).choose 2 : ℕ) : ℚ) := by exact_mod_cast h
  exact div_nonneg (by linarith) this.le

lemma du_nonneg (hn : 5 ≤ n) {θ : ℚ} (hθ0 : 0 ≤ θ) : 0 ≤ du n θ := by
  have h := choose_one_pos hn
  have : (0 : ℚ) < (((n - 2).choose 1 : ℕ) : ℚ) := by exact_mod_cast h
  exact div_nonneg hθ0 this.le

lemma dwt_nonneg (hn : 5 ≤ n) {θ : ℚ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (K : Finset (Fin n)) :
    0 ≤ dwt n θ K := by
  unfold dwt
  split
  · exact dw_nonneg hn hθ1
  · split
    · exact du_nonneg hn hθ0
    · exact le_refl 0

lemma sum_dwt_filter (S : Finset (Fin n)) (θ : ℚ) :
    ∑ K ∈ items (⊤ : SimpleGraph (Fin n)), (if S ⊆ K then dwt n θ K else 0)
      = du n θ * (cnt S 3 : ℚ) + dw n θ * (cnt S 4 : ℚ) := by
  classical
  rw [sum_items_top]
  congr 1
  · rw [← sum_powersetCard_filter S 3 (du n θ)]
    refine Finset.sum_congr rfl fun K hK => ?_
    rw [Finset.mem_powersetCard_univ] at hK
    by_cases h : S ⊆ K <;> simp [h, dwt, hK]
  · rw [← sum_powersetCard_filter S 4 (dw n θ)]
    refine Finset.sum_congr rfl fun K hK => ?_
    rw [Finset.mem_powersetCard_univ] at hK
    by_cases h : S ⊆ K <;> simp [h, dwt, hK]

/-! ### Aristas y soportes -/

lemma pairs_iff_toFinset_subset {e : Sym2 (Fin n)} (he : ¬ e.IsDiag) {K : Finset (Fin n)} :
    e ∈ pairs K ↔ e.toFinset ⊆ K := by
  rw [mem_pairs]
  constructor
  · rintro ⟨h, -⟩ a ha
    exact h a (Sym2.mem_toFinset.1 ha)
  · intro h
    exact ⟨fun a ha => h (Sym2.mem_toFinset.2 ha), he⟩

lemma card_toFinset_of_not_isDiag {e : Sym2 (Fin n)} (he : ¬ e.IsDiag) : e.toFinset.card = 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := by simpa [Sym2.isDiag_iff_proj_eq] using he
    have : (s(a, b) : Sym2 (Fin n)).toFinset = ({a, b} : Finset (Fin n)) := by
      ext c
      simp [Sym2.mem_toFinset]
    rw [this, Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]

end Complete

/-! ## 4. El empaquetamiento denso y sus tres propiedades -/

section DensePacking

variable {n : ℕ}

/-- **El empaquetamiento uniforme de `K_n`**: peso `dw` en cada `K₄` y `du` en cada triángulo.
La carga de cada arista es exactamente `(1-θ) + θ = 1`. -/
def densePacking (n : ℕ) (θ : ℚ) (hn : 5 ≤ n) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    FracPacking (⊤ : SimpleGraph (Fin n)) where
  weight := dwt n θ
  weight_nonneg := dwt_nonneg hn hθ0 hθ1
  capacity := by
    intro e he
    have hdiag : ¬ e.IsDiag :=
      SimpleGraph.not_isDiag_of_mem_edgeSet _ (SimpleGraph.mem_edgeFinset.1 he)
    have hcond : ∀ K : Finset (Fin n), (if e ∈ pairs K then dwt n θ K else 0)
        = (if e.toFinset ⊆ K then dwt n θ K else 0) := by
      intro K
      by_cases h : e.toFinset ⊆ K
      · rw [if_pos ((pairs_iff_toFinset_subset hdiag).2 h), if_pos h]
      · rw [if_neg (fun hc => h ((pairs_iff_toFinset_subset hdiag).1 hc)), if_neg h]
    rw [Finset.sum_congr rfl (fun K _ => hcond K), sum_dwt_filter]
    have hcard : e.toFinset.card = 2 := card_toFinset_of_not_isDiag hdiag
    rw [cnt_eq _ _ (by omega), cnt_eq _ _ (by omega), hcard]
    have h1 : (0 : ℚ) < (((n - 2).choose 1 : ℕ) : ℚ) := by exact_mod_cast choose_one_pos hn
    have h2 : (0 : ℚ) < (((n - 2).choose 2 : ℕ) : ℚ) := by exact_mod_cast choose_two_pos hn
    rw [show (3 - 2 : ℕ) = 1 from rfl, show (4 - 2 : ℕ) = 2 from rfl, du, dw,
      div_mul_cancel₀ _ (ne_of_gt h1), div_mul_cancel₀ _ (ne_of_gt h2)]
    linarith

@[simp] lemma densePacking_weight (θ : ℚ) (hn : 5 ≤ n) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (K : Finset (Fin n)) : (densePacking n θ hn hθ0 hθ1).weight K = dwt n θ K := rfl

/-! ### Identidades binomiales -/

lemma choose_three_id (hn : 5 ≤ n) :
    ((n.choose 3 : ℕ) : ℚ) * 3 = ((n.choose 2 : ℕ) : ℚ) * (((n - 2).choose 1 : ℕ) : ℚ) := by
  have h := Nat.choose_mul (n := n) (k := 3) (s := 2) (by norm_num)
  have h32 : Nat.choose 3 2 = 3 := by decide
  rw [h32] at h
  exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) h

lemma choose_four_id (hn : 5 ≤ n) :
    ((n.choose 4 : ℕ) : ℚ) * 6 = ((n.choose 2 : ℕ) : ℚ) * (((n - 2).choose 2 : ℕ) : ℚ) := by
  have h := Nat.choose_mul (n := n) (k := 4) (s := 2) (by norm_num)
  have h42 : Nat.choose 4 2 = 6 := by decide
  rw [h42] at h
  exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) h

lemma choose_two_sub_id (hn : 5 ≤ n) :
    (((n - 2).choose 2 : ℕ) : ℚ) * 2 = ((n : ℚ) - 2) * ((n : ℚ) - 3) := by
  have h := Nat.choose_mul (n := n - 2) (k := 2) (s := 1) (by norm_num)
  have h21 : Nat.choose 2 1 = 2 := by decide
  rw [h21, Nat.choose_one_right, Nat.choose_one_right] at h
  have hQ : (((n - 2).choose 2 : ℕ) : ℚ) * 2 = ((n - 2 : ℕ) : ℚ) * ((n - 2 - 1 : ℕ) : ℚ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) h
  rw [hQ]
  have e1 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by
    have : (2 : ℕ) ≤ n := by omega
    push_cast [Nat.cast_sub this]
    ring
  have e2 : ((n - 2 - 1 : ℕ) : ℚ) = (n : ℚ) - 3 := by
    have : (3 : ℕ) ≤ n := by omega
    have hn3 : n - 2 - 1 = n - 3 := by omega
    rw [hn3, Nat.cast_sub this]
    push_cast
    ring
  rw [e1, e2]

lemma choose_one_sub_id (hn : 5 ≤ n) : (((n - 2).choose 1 : ℕ) : ℚ) = (n : ℚ) - 2 := by
  rw [Nat.choose_one_right]
  have : (2 : ℕ) ≤ n := by omega
  rw [Nat.cast_sub this]
  push_cast
  ring

/-! ### Masa y valor -/

lemma filter_items_top_three :
    (items (⊤ : SimpleGraph (Fin n))).filter (fun K => K.card = 3) = univ.powersetCard 3 := by
  ext K
  simp only [Finset.mem_filter, mem_items_top, Finset.mem_powersetCard_univ]
  tauto

lemma densePacking_mass (θ : ℚ) (hn : 5 ≤ n) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    PaperIV.JointTwoQuotaPhysical.triangleMass (densePacking n θ hn hθ0 hθ1)
      = ((θ * ((n.choose 2 : ℕ) : ℚ) / 3 : ℚ) : ℝ) := by
  classical
  rw [PaperIV.JointTwoQuotaPhysical.triangleMass, filter_items_top_three]
  have hterm : ∀ K ∈ (univ.powersetCard 3 : Finset (Finset (Fin n))),
      (((densePacking n θ hn hθ0 hθ1).weight K : ℚ) : ℝ) = ((du n θ : ℚ) : ℝ) := by
    intro K hK
    rw [Finset.mem_powersetCard_univ] at hK
    rw [densePacking_weight, dwt, if_neg (by omega), if_pos hK]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have h1 : (((n - 2).choose 1 : ℕ) : ℚ) = (n : ℚ) - 2 := choose_one_sub_id hn
  have hne : ((n : ℚ) - 2) ≠ 0 := by
    have hn5 : (5 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    intro hc; linarith
  have hC3' : ((n.choose 3 : ℕ) : ℚ) = ((n.choose 2 : ℕ) : ℚ) * ((n : ℚ) - 2) / 3 := by
    have hid := choose_three_id hn
    rw [h1] at hid
    linarith
  have hq : ((n.choose 3 : ℕ) : ℚ) * du n θ = θ * ((n.choose 2 : ℕ) : ℚ) / 3 := by
    rw [du, h1, hC3']
    field_simp
  have hR := congrArg (fun q : ℚ => (q : ℝ)) hq
  push_cast at hR ⊢
  linarith [hR]

lemma densePacking_value (θ : ℚ) (hn : 5 ≤ n) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (densePacking n θ hn hθ0 hθ1).value = (5 - θ) / 6 * ((n.choose 2 : ℕ) : ℚ) := by
  classical
  rw [FracPacking.value, sum_items_top]
  have h3 : ∀ K ∈ (univ.powersetCard 3 : Finset (Finset (Fin n))),
      gainF ℚ K * (densePacking n θ hn hθ0 hθ1).weight K = 2 * du n θ := by
    intro K hK
    rw [Finset.mem_powersetCard_univ] at hK
    have e32 : Nat.choose 3 2 = 3 := by decide
    rw [densePacking_weight, dwt, if_neg (by omega), if_pos hK, gainF, hK, e32]
    norm_num
  have h4 : ∀ K ∈ (univ.powersetCard 4 : Finset (Finset (Fin n))),
      gainF ℚ K * (densePacking n θ hn hθ0 hθ1).weight K = 5 * dw n θ := by
    intro K hK
    rw [Finset.mem_powersetCard_univ] at hK
    have e42 : Nat.choose 4 2 = 6 := by decide
    rw [densePacking_weight, dwt, if_pos hK, gainF, hK, e42]
    norm_num
  rw [Finset.sum_congr rfl h3, Finset.sum_congr rfl h4, Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul, Finset.card_powersetCard, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin]
  have hA1 : (0 : ℚ) < (((n - 2).choose 1 : ℕ) : ℚ) := by exact_mod_cast choose_one_pos hn
  have hA2 : (0 : ℚ) < (((n - 2).choose 2 : ℕ) : ℚ) := by exact_mod_cast choose_two_pos hn
  have hC3 : ((n.choose 3 : ℕ) : ℚ)
      = ((n.choose 2 : ℕ) : ℚ) * (((n - 2).choose 1 : ℕ) : ℚ) / 3 := by
    have := choose_three_id hn
    linarith
  have hC4 : ((n.choose 4 : ℕ) : ℚ)
      = ((n.choose 2 : ℕ) : ℚ) * (((n - 2).choose 2 : ℕ) : ℚ) / 6 := by
    have := choose_four_id hn
    linarith
  rw [hC3, hC4, du, dw]
  field_simp
  ring

end DensePacking

/-! ## 5. El codegrado del empaquetamiento denso -/

section Codeg

variable {n : ℕ}

lemma sym2_eq_of_toFinset_eq {e f : Sym2 (Fin n)} (he : ¬ e.IsDiag) (hf : ¬ f.IsDiag)
    (h : e.toFinset = f.toFinset) : e = f := by
  induction e using Sym2.ind with
  | _ a b =>
    induction f using Sym2.ind with
    | _ c d =>
      have hab : a ≠ b := by simpa [Sym2.isDiag_iff_proj_eq] using he
      have hcd : c ≠ d := by simpa [Sym2.isDiag_iff_proj_eq] using hf
      have hmem : ∀ z : Fin n, (z = a ∨ z = b) ↔ (z = c ∨ z = d) := by
        intro z
        have := congrArg (fun T => z ∈ T) h
        simpa [Sym2.mem_toFinset] using this
      have ha : a = c ∨ a = d := (hmem a).1 (Or.inl rfl)
      have hb : b = c ∨ b = d := (hmem b).1 (Or.inr rfl)
      rcases ha with rfl | rfl
      · rcases hb with rfl | rfl
        · exact absurd rfl hab
        · rfl
      · rcases hb with rfl | rfl
        · exact Sym2.eq_swap
        · exact absurd rfl hab

lemma three_le_card_union {e f : Sym2 (Fin n)} (he : ¬ e.IsDiag) (hf : ¬ f.IsDiag)
    (hef : e ≠ f) : 3 ≤ (e.toFinset ∪ f.toFinset).card := by
  by_contra hcon
  push_neg at hcon
  have hcarde : e.toFinset.card = 2 := card_toFinset_of_not_isDiag he
  have hcardf : f.toFinset.card = 2 := card_toFinset_of_not_isDiag hf
  have h1 : e.toFinset = e.toFinset ∪ f.toFinset :=
    Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
  have h2 : f.toFinset = e.toFinset ∪ f.toFinset :=
    Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
  exact hef (sym2_eq_of_toFinset_eq he hf (h1.trans h2.symm))

/-- **El codegrado del empaquetamiento denso tiende a cero**: nunca pasa de `3/(n-2)`. -/
lemma densePacking_codeg_le (θ : ℚ) (hn : 5 ≤ n) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (e f : Sym2 (Fin n)) (hef : e ≠ f) :
    ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports (⊤ : SimpleGraph (Fin n))).filter
        (fun S => e ∈ S ∧ f ∈ S), inducedWeight (densePacking n θ hn hθ0 hθ1) S
      ≤ (3 : ℝ) / ((n : ℝ) - 2) := by
  classical
  rw [codeg_eq_sum_items]
  have hnQ : (5 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn2 : (0 : ℚ) < (n : ℚ) - 2 := by linarith
  have hQ : ∑ K ∈ (items (⊤ : SimpleGraph (Fin n))).filter
      (fun K => e ∈ pairs K ∧ f ∈ pairs K), (densePacking n θ hn hθ0 hθ1).weight K
      ≤ 3 / ((n : ℚ) - 2) := by
    by_cases hde : e.IsDiag
    · have hempty : (items (⊤ : SimpleGraph (Fin n))).filter
          (fun K => e ∈ pairs K ∧ f ∈ pairs K) = ∅ :=
        Finset.filter_false_of_mem fun K _ hc => (mem_pairs.1 hc.1).2 hde
      rw [hempty, Finset.sum_empty]
      positivity
    by_cases hdf : f.IsDiag
    · have hempty : (items (⊤ : SimpleGraph (Fin n))).filter
          (fun K => e ∈ pairs K ∧ f ∈ pairs K) = ∅ :=
        Finset.filter_false_of_mem fun K _ hc => (mem_pairs.1 hc.2).2 hdf
      rw [hempty, Finset.sum_empty]
      positivity
    set S : Finset (Fin n) := e.toFinset ∪ f.toFinset with hS
    have hcond : ∀ K : Finset (Fin n),
        (if (e ∈ pairs K ∧ f ∈ pairs K) then dwt n θ K else 0)
          = (if S ⊆ K then dwt n θ K else 0) := by
      intro K
      have hiff : (e ∈ pairs K ∧ f ∈ pairs K) ↔ S ⊆ K := by
        rw [pairs_iff_toFinset_subset hde, pairs_iff_toFinset_subset hdf, hS,
          Finset.union_subset_iff]
      by_cases h : S ⊆ K
      · rw [if_pos (hiff.2 h), if_pos h]
      · rw [if_neg (fun hc => h (hiff.1 hc)), if_neg h]
    rw [Finset.sum_filter]
    have : ∀ K ∈ items (⊤ : SimpleGraph (Fin n)),
        (if (e ∈ pairs K ∧ f ∈ pairs K) then (densePacking n θ hn hθ0 hθ1).weight K else 0)
          = (if S ⊆ K then dwt n θ K else 0) := fun K _ => hcond K
    rw [Finset.sum_congr rfl this, sum_dwt_filter]
    -- ahora los dos casos: `|S| = 3` y `|S| = 4`
    have hS3 : 3 ≤ S.card := three_le_card_union hde hdf hef
    have hS4 : S.card ≤ 4 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [card_toFinset_of_not_isDiag hde, card_toFinset_of_not_isDiag hdf]
    have hdu : du n θ ≤ 1 / ((n : ℚ) - 2) := by
      rw [du, choose_one_sub_id hn]
      gcongr
    have hdwpos : 0 ≤ dw n θ := dw_nonneg hn hθ1
    have hdw3 : dw n θ * ((n : ℚ) - 3) ≤ 2 / ((n : ℚ) - 2) := by
      have hid := choose_two_sub_id hn
      have hA2 : (0 : ℚ) < (((n - 2).choose 2 : ℕ) : ℚ) := by exact_mod_cast choose_two_pos hn
      rw [dw, div_mul_eq_mul_div, div_le_div_iff₀ hA2 hn2]
      nlinarith [hid, hθ0, hθ1, hn2]
    rcases (by omega : S.card = 3 ∨ S.card = 4) with h3 | h4
    · rw [cnt_eq S 3 (by omega), cnt_eq S 4 (by omega), h3]
      have e1 : ((n - 3).choose (3 - 3) : ℕ) = 1 := by simp
      have e2 : (((n - 3).choose (4 - 3) : ℕ) : ℚ) = (n : ℚ) - 3 := by
        rw [show (4 - 3 : ℕ) = 1 from rfl, Nat.choose_one_right, Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [e1, e2]
      push_cast
      have hsum : 1 / ((n : ℚ) - 2) + 2 / ((n : ℚ) - 2) = 3 / ((n : ℚ) - 2) := by
        rw [div_add_div_same]
        norm_num
      linarith [hdu, hdw3, hsum]
    · rw [cnt_eq_zero S 3 (by omega), cnt_eq S 4 (by omega), h4]
      have e2 : ((n - 4).choose (4 - 4) : ℕ) = 1 := by simp
      rw [e2]
      push_cast
      have hge : dw n θ * 1 ≤ dw n θ * ((n : ℚ) - 3) := by nlinarith [hdwpos, hnQ]
      have hdu0 : 0 ≤ du n θ := du_nonneg hn hθ0
      have hcmp : (2 : ℚ) / ((n : ℚ) - 2) ≤ 3 / ((n : ℚ) - 2) := by gcongr <;> norm_num
      linarith [hdw3, hge, hdu0, hcmp]
  have hcast := (Rat.cast_le (K := ℝ)).2 hQ
  push_cast at hcast ⊢
  linarith [hcast]

end Codeg

/-! ## 6. La limpieza de codegrado en el extremo denso -/

/-- **En el grafo completo la limpieza vale, sin hipótesis de masa y con umbral explícito.**

Para cada `gam > 0`, `Cst` y `xi > 0` existe `N` tal que, para `n ≥ N` y **cualquier**
empaquetamiento fraccional `x` de `K_n`, el empaquetamiento uniforme
`densePacking n (min 1 (12·xi))` tiene codegrado `≤ gam`, masa triangular `≥ Cst` y valor a
distancia `≤ xi·n²` del de `x`.

Obsérvese que aquí no se usa la hipótesis de masa cuadrática sobre `x`: en `K_n` la limpieza es
gratis porque el reparto uniforme sobre todos los `K₄` ya alcanza el óptimo del LP salvo
`θ·n²/12`.  El enunciado, por tanto, **no es vacuo**: su extremo denso es demostrable en
cerrado.  Lo que este módulo *no* dice es nada sobre grafos incompletos; el caso general sigue
abierto y su umbral está acotado por debajo en `FarExploration.CleanupRigidVerdict`. -/
theorem dense_cleanup (gam Cst : ℝ) (xi : ℚ) (hgam : 0 < gam) (hxi : 0 < xi) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : FracPacking (⊤ : SimpleGraph (Fin n)),
      ∃ y : FracPacking (⊤ : SimpleGraph (Fin n)),
        (∀ e f : Sym2 (Fin n), e ≠ f →
          ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports (⊤ : SimpleGraph (Fin n))).filter
              (fun S => e ∈ S ∧ f ∈ S), inducedWeight y S ≤ gam) ∧
        Cst ≤ PaperIV.JointTwoQuotaPhysical.triangleMass y ∧
        x.value - y.value ≤ xi * (n : ℚ) ^ 2 := by
  classical
  set θ : ℚ := min 1 (12 * xi) with hθdef
  have hθ0 : 0 < θ := lt_min one_pos (by linarith)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθxi : θ ≤ 12 * xi := min_le_right _ _
  have hθR : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  refine ⟨max 5 (max ⌈3 / gam + 2⌉₊ ⌈3 * Cst / (θ : ℝ)⌉₊), ?_⟩
  intro n hn x
  have hn5 : 5 ≤ n := le_trans (le_max_left _ _) hn
  have hngam : ⌈3 / gam + 2⌉₊ ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnCst : ⌈3 * Cst / (θ : ℝ)⌉₊ ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hnQ : (5 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn5
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn5
  -- la cota `C(n,2) = n(n-1)/2`
  have hC2 : ((n.choose 2 : ℕ) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 :=
    Nat.cast_choose_two (K := ℚ) n
  refine ⟨densePacking n θ hn5 hθ0.le hθ1, ?_, ?_, ?_⟩
  · -- codegrado
    intro e f hef
    refine le_trans (densePacking_codeg_le θ hn5 hθ0.le hθ1 e f hef) ?_
    have hceil : (3 : ℝ) / gam + 2 ≤ (n : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hngam)
    have h2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
    have hdiv : (3 : ℝ) / gam ≤ (n : ℝ) - 2 := by linarith
    rw [div_le_iff₀ h2]
    rw [div_le_iff₀ hgam] at hdiv
    linarith
  · -- masa
    rw [densePacking_mass]
    have hmassQ : (θ : ℚ) * (n : ℚ) / 3 ≤ θ * ((n.choose 2 : ℕ) : ℚ) / 3 := by
      rw [hC2]
      have : (n : ℚ) ≤ (n : ℚ) * ((n : ℚ) - 1) / 2 := by nlinarith
      nlinarith [hθ0.le, this]
    have hmassR : ((θ * (n : ℚ) / 3 : ℚ) : ℝ) ≤ ((θ * ((n.choose 2 : ℕ) : ℚ) / 3 : ℚ) : ℝ) := by
      exact_mod_cast hmassQ
    refine le_trans ?_ hmassR
    have hceil : 3 * Cst / (θ : ℝ) ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hnCst)
    rw [div_le_iff₀ hθR] at hceil
    push_cast
    linarith
  · -- valor
    have hxval : x.value ≤ (5 / 6 : ℚ) * ((n.choose 2 : ℕ) : ℚ) := by
      have h := value_le_edges x
      have hcard : ((⊤ : SimpleGraph (Fin n)).edgeFinset.card : ℚ) = ((n.choose 2 : ℕ) : ℚ) := by
        rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
      rwa [hcard] at h
    rw [densePacking_value]
    have hC2le : ((n.choose 2 : ℕ) : ℚ) ≤ (n : ℚ) ^ 2 / 2 := by
      rw [hC2]
      nlinarith
    have hC2nonneg : (0 : ℚ) ≤ ((n.choose 2 : ℕ) : ℚ) := by positivity
    nlinarith [hxval, hC2le, hθxi, hθ0.le, hC2nonneg]

end FarExploration.CleanupDense

