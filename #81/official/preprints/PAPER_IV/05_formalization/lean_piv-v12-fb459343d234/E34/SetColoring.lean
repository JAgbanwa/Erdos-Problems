import E34.Sampling

/-!
# E34 — set colouring problems (Definition 1 of arXiv:1902.06135) and their potential

A set colouring problem on `Fin n` with colours `Finset (Fin K)`: lists `L v`, and for ordered
pairs `(u, v)` two maps `mm u v`, `MM u v`.  A colouring `φ` is proper on `S` if `φ v ∈ L v` and
`mm u v (φ u) ⊆ φ v ⊆ MM u v (φ u)` for all distinct `u, v ∈ S` (both orders).

For a partial colouring `(S, φ)` we define (following the appendix of the paper, with one
correction): the admissible colours `Lφ v`, the windows `mφ v ⊆ c ⊆ Mφ v`, the potential
`energy = Σ_v |Mφ v| + |mφ vᶜ|` (between `0` and `2Kn`), and the number `aff u c` of vertices
whose window strictly shrinks when `u` receives `c`.  (The paper uses the total shrinkage
`δ^c_φ(u)`, which can exceed `n`; counting affected vertices instead keeps `aff ≤ n`, which is
what the paper's Claim 2 needs.)
-/

namespace E34

open Finset

open scoped Classical

/-- A set colouring problem. -/
structure SetColoring (n K : ℕ) where
  L : Fin n → Finset (Finset (Fin K))
  mm : Fin n → Fin n → Finset (Fin K) → Finset (Fin K)
  MM : Fin n → Fin n → Finset (Fin K) → Finset (Fin K)

namespace SetColoring

variable {n K : ℕ} (P : SetColoring n K)

/-- The constraint for the ordered pair `(u, v)`. -/
def ok (u : Fin n) (c : Finset (Fin K)) (v : Fin n) (d : Finset (Fin K)) : Prop :=
  P.mm u v c ⊆ d ∧ d ⊆ P.MM u v c

/-- Both constraints. -/
def compat (u : Fin n) (c : Finset (Fin K)) (v : Fin n) (d : Finset (Fin K)) : Prop :=
  P.ok u c v d ∧ P.ok v d u c

theorem compat_comm {u v : Fin n} {c d : Finset (Fin K)} :
    P.compat u c v d ↔ P.compat v d u c := And.comm

/-- `φ` is a proper colouring of `S`. -/
def ProperOn (φ : Fin n → Finset (Fin K)) (S : Finset (Fin n)) : Prop :=
  (∀ v ∈ S, φ v ∈ P.L v) ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → P.compat u (φ u) v (φ v)

theorem ProperOn.mono {φ : Fin n → Finset (Fin K)} {S S' : Finset (Fin n)} (h : P.ProperOn φ S)
    (hS : S' ⊆ S) : P.ProperOn φ S' :=
  ⟨fun v hv => h.1 v (hS hv), fun u hu v hv huv => h.2 u (hS hu) v (hS hv) huv⟩

/-- Ordered conflicting pairs of a colouring. -/
noncomputable def conf (φ : Fin n → Finset (Fin K)) : ℕ :=
  (univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ ¬ P.compat p.1 (φ p.1) p.2 (φ p.2))).card

/-! ## The potential of a partial colouring -/

variable (S : Finset (Fin n)) (φ : Fin n → Finset (Fin K))

/-- Admissible colours of `v` given `(S, φ)`. -/
noncomputable def Lφ (v : Fin n) : Finset (Finset (Fin K)) :=
  (P.L v).filter (fun c => ∀ u ∈ S, u ≠ v → P.compat u (φ u) v c)

/-- Lower window. -/
noncomputable def mφ (v : Fin n) : Finset (Fin K) := (S.erase v).biUnion (fun u => P.mm u v (φ u))

/-- Upper window. -/
noncomputable def Mφ (v : Fin n) : Finset (Fin K) := (S.erase v).inf (fun u => P.MM u v (φ u))

/-- Vertices whose window strictly shrinks when `u` gets colour `c`. -/
noncomputable def affS (u : Fin n) (c : Finset (Fin K)) : Finset (Fin n) :=
  univ.filter (fun v => v ≠ u ∧ (¬ P.Mφ S φ v ⊆ P.MM u v c ∨ ¬ P.mm u v c ⊆ P.mφ S φ v))

/-- The potential. -/
noncomputable def energy : ℕ :=
  ∑ v, ((P.Mφ S φ v).card + (univ \ P.mφ S φ v).card)

theorem window_of_mem_Lφ {v : Fin n} {c : Finset (Fin K)} (hc : c ∈ P.Lφ S φ v) :
    P.mφ S φ v ⊆ c ∧ c ⊆ P.Mφ S φ v := by
  rw [Lφ, mem_filter] at hc
  constructor
  · refine biUnion_subset.2 (fun u hu => ?_)
    rw [mem_erase] at hu
    exact (hc.2 u hu.2 hu.1).1.1
  · show c ≤ (S.erase v).inf (fun u => P.MM u v (φ u))
    refine Finset.le_inf ?_
    intro u hu
    rw [mem_erase] at hu
    exact (hc.2 u hu.2 hu.1).1.2

theorem energy_le : P.energy S φ ≤ 2 * K * n := by
  unfold energy
  calc ∑ v, ((P.Mφ S φ v).card + (univ \ P.mφ S φ v).card) ≤ ∑ _v : Fin n, (K + K) := by
        refine sum_le_sum (fun v _ => Nat.add_le_add ?_ ?_)
        · simpa using card_le_univ (P.Mφ S φ v)
        · simpa using card_le_univ (univ \ P.mφ S φ v)
    _ = 2 * K * n := by simp; ring

/-- **Potential drop**: colouring a new vertex `u` with `c` lowers the potential by at least
the number of affected vertices. -/
theorem energy_insert (u : Fin n) (hu : u ∉ S) (c : Finset (Fin K)) :
    P.energy (insert u S) (Function.update φ u c) + (P.affS S φ u c).card ≤ P.energy S φ := by
  unfold energy
  rw [card_eq_sum_ones, affS, sum_filter, ← sum_add_distrib]
  refine sum_le_sum (fun v _ => ?_)
  by_cases hvu : v = u
  · subst hvu
    have e1 : (insert v S).erase v = S.erase v := by
      rw [erase_insert hu, erase_eq_of_notMem hu]
    have hm : P.mφ (insert v S) (Function.update φ v c) v = P.mφ S φ v := by
      unfold mφ; rw [e1]
      refine biUnion_congr rfl (fun w hw => ?_)
      rw [Function.update_of_ne (mem_erase.1 hw).1]
    have hM : P.Mφ (insert v S) (Function.update φ v c) v = P.Mφ S φ v := by
      unfold Mφ; rw [e1]
      refine inf_congr rfl (fun w hw => ?_)
      rw [Function.update_of_ne (mem_erase.1 hw).1]
    rw [hm, hM]; simp
  · have e1 : (insert u S).erase v = insert u (S.erase v) := erase_insert_of_ne (Ne.symm hvu)
    have huS : u ∉ S.erase v := fun h => hu (mem_of_mem_erase h)
    have hm : P.mφ (insert u S) (Function.update φ u c) v = P.mm u v c ∪ P.mφ S φ v := by
      unfold mφ; rw [e1, biUnion_insert, Function.update_self]
      congr 1
      refine biUnion_congr rfl (fun w hw => ?_)
      have : w ≠ u := fun h => huS (h ▸ hw)
      rw [Function.update_of_ne this]
    have hM : P.Mφ (insert u S) (Function.update φ u c) v = P.MM u v c ⊓ P.Mφ S φ v := by
      unfold Mφ; rw [e1, inf_insert, Function.update_self]
      congr 1
      refine inf_congr rfl (fun w hw => ?_)
      have : w ≠ u := fun h => huS (h ▸ hw)
      rw [Function.update_of_ne this]
    rw [hm, hM]
    have h1 : (P.MM u v c ⊓ P.Mφ S φ v).card ≤ (P.Mφ S φ v).card :=
      card_le_card (inf_le_right : P.MM u v c ⊓ P.Mφ S φ v ≤ P.Mφ S φ v)
    have h2 : (univ \ (P.mm u v c ∪ P.mφ S φ v)).card ≤ (univ \ P.mφ S φ v).card :=
      card_le_card (sdiff_subset_sdiff (Subset.refl _) subset_union_right)
    split_ifs with haff
    · simp only [hvu, ne_eq, not_false_eq_true, true_and] at haff
      rcases haff with h | h
      · have : (P.MM u v c ⊓ P.Mφ S φ v).card < (P.Mφ S φ v).card := by
          refine card_lt_card ⟨(inf_le_right : P.MM u v c ⊓ P.Mφ S φ v ≤ P.Mφ S φ v), fun hsub => h ?_⟩
          exact fun x hx => (Finset.mem_inter.1 (hsub hx)).1
        omega
      · have : (univ \ (P.mm u v c ∪ P.mφ S φ v)).card < (univ \ P.mφ S φ v).card := by
          refine card_lt_card ⟨sdiff_subset_sdiff (Subset.refl _) subset_union_right, ?_⟩
          intro hsub
          apply h
          intro x hx
          by_contra hxm
          have : x ∈ univ \ P.mφ S φ v := mem_sdiff.2 ⟨mem_univ _, hxm⟩
          have := hsub this
          exact (mem_sdiff.1 this).2 (mem_union_left _ hx)
        omega
    · omega

/-! ## Claims 1–2: many successful vertices -/

/-- Successful vertices: outside `S`, and every admissible colour affects at least `εn/4`
vertices (this includes the colourless vertices). -/
noncomputable def succ (ε : ℝ) : Finset (Fin n) :=
  (Sᶜ).filter (fun v => ∀ c ∈ P.Lφ S φ v, ε * n / 4 ≤ ((P.affS S φ v c).card : ℝ))

theorem card_affS_le (u : Fin n) (c : Finset (Fin K)) : (P.affS S φ u c).card ≤ n := by
  simpa using card_le_univ (P.affS S φ u c)

/-- **Claims 1–2** of the appendix: for a proper partial colouring, at least `εn/4` vertices are
successful. -/
theorem card_succ (hLne : ∀ v, (P.L v).Nonempty) (ε : ℝ) (hε : 0 ≤ ε)
    (hfar : ∀ ψ : Fin n → Finset (Fin K), (∀ v, ψ v ∈ P.L v) → ε * (n : ℝ) ^ 2 ≤ P.conf ψ)
    (hprop : P.ProperOn φ S) : ε * n / 4 ≤ ((P.succ S φ ε).card : ℝ) := by
  set U' := (Sᶜ).filter (fun v => P.Lφ S φ v = ∅)
  set T := Sᶜ \ U'
  have hmin : ∀ v, (P.Lφ S φ v).Nonempty → ∃ c ∈ P.Lφ S φ v,
      ∀ c' ∈ P.Lφ S φ v, (P.affS S φ v c).card ≤ (P.affS S φ v c').card :=
    fun v h => exists_min_image _ _ h
  let α : Fin n → Finset (Fin K) := fun v =>
    if v ∈ S then φ v else if h : (P.Lφ S φ v).Nonempty then (hmin v h).choose
    else (hLne v).choose
  have hαS : ∀ v ∈ S, α v = φ v := fun v hv => by simp [α, hv]
  have hαT : ∀ v, v ∉ S → (P.Lφ S φ v).Nonempty → α v ∈ P.Lφ S φ v ∧
      ∀ c' ∈ P.Lφ S φ v, (P.affS S φ v (α v)).card ≤ (P.affS S φ v c').card := by
    intro v hv h
    simp only [α, hv, if_false, h, dif_pos]
    exact (hmin v h).choose_spec
  have hαL : ∀ v, α v ∈ P.L v := by
    intro v
    by_cases hv : v ∈ S
    · rw [hαS v hv]; exact hprop.1 v hv
    · by_cases h : (P.Lφ S φ v).Nonempty
      · exact (mem_filter.1 (hαT v hv h).1).1
      · simp only [α, hv, if_false, h, dif_neg, not_false_eq_true]
        exact (hLne v).choose_spec
  have hT : ∀ v ∈ T, v ∉ S ∧ (P.Lφ S φ v).Nonempty := by
    intro v hv
    rw [mem_sdiff, mem_compl] at hv
    refine ⟨hv.1, ?_⟩
    rw [nonempty_iff_ne_empty]
    intro h; exact hv.2 (mem_filter.2 ⟨mem_compl.2 hv.1, h⟩)
  have hgood : ∀ v, v ∉ U' → v ∈ S ∨ v ∈ T := by
    intro v hv
    by_cases h : v ∈ S
    · exact Or.inl h
    · exact Or.inr (mem_sdiff.2 ⟨mem_compl.2 h, hv⟩)
  -- the conflicting pairs
  set A3 := T.biUnion (fun u => (P.affS S φ u (α u)).image (fun v => (u, v)))
  set A4 := T.biUnion (fun v => (P.affS S φ v (α v)).image (fun u => (u, v)))
  have hsub : univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧
      ¬ P.compat p.1 (α p.1) p.2 (α p.2)) ⊆ (U' ×ˢ univ ∪ univ ×ˢ U') ∪ (A3 ∪ A4) := by
    rintro ⟨u, v⟩ hp
    simp only [mem_filter, mem_univ, true_and] at hp
    obtain ⟨huv, hnc⟩ := hp
    by_cases hu : u ∈ U'
    · exact mem_union_left _ (mem_union_left _ (mem_product.2 ⟨hu, mem_univ _⟩))
    by_cases hv : v ∈ U'
    · exact mem_union_left _ (mem_union_right _ (mem_product.2 ⟨mem_univ _, hv⟩))
    refine mem_union_right _ ?_
    rcases hgood u hu with huS | huT <;> rcases hgood v hv with hvS | hvT
    · exact absurd (by rw [hαS u huS, hαS v hvS]; exact hprop.2 u huS v hvS huv) hnc
    · exfalso; apply hnc
      obtain ⟨hvS, hvne⟩ := hT v hvT
      have := (mem_filter.1 (hαT v hvS hvne).1).2 u huS huv
      rwa [hαS u huS]
    · exfalso; apply hnc
      obtain ⟨huS, hune⟩ := hT u huT
      have := (mem_filter.1 (hαT u huS hune).1).2 v hvS (Ne.symm huv)
      rw [hαS v hvS]
      exact (P.compat_comm).1 this
    · obtain ⟨huS, hune⟩ := hT u huT
      obtain ⟨hvS, hvne⟩ := hT v hvT
      have hwu := P.window_of_mem_Lφ S φ (hαT u huS hune).1
      have hwv := P.window_of_mem_Lφ S φ (hαT v hvS hvne).1
      unfold compat at hnc
      rw [not_and_or] at hnc
      rcases hnc with h | h
      · refine mem_union_left _ (mem_biUnion.2 ⟨u, huT, mem_image.2 ⟨v, ?_, rfl⟩⟩)
        simp only [affS, mem_filter, mem_univ, true_and]
        refine ⟨Ne.symm huv, ?_⟩
        by_contra hc
        push_neg at hc
        exact h ⟨hc.2.trans hwv.1, hwv.2.trans hc.1⟩
      · refine mem_union_right _ (mem_biUnion.2 ⟨v, hvT, mem_image.2 ⟨u, ?_, rfl⟩⟩)
        simp only [affS, mem_filter, mem_univ, true_and]
        refine ⟨huv, ?_⟩
        by_contra hc
        push_neg at hc
        exact h ⟨hc.2.trans hwu.1, hwu.2.trans hc.1⟩
  have hA3 : A3.card ≤ ∑ u ∈ T, (P.affS S φ u (α u)).card :=
    card_biUnion_le.trans (sum_le_sum (fun u _ => card_image_le))
  have hA4 : A4.card ≤ ∑ u ∈ T, (P.affS S φ u (α u)).card :=
    card_biUnion_le.trans (sum_le_sum (fun u _ => card_image_le))
  have hconf : P.conf α ≤ 2 * n * U'.card + 2 * ∑ u ∈ T, (P.affS S φ u (α u)).card := by
    unfold conf
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    have h1 := card_union_le (U' ×ˢ (univ : Finset (Fin n))) (univ ×ˢ U')
    have h2 := card_union_le A3 A4
    rw [card_product, card_product, card_univ, Fintype.card_fin] at h1
    nlinarith
  -- the sum over `T`
  have hsumT : (∑ u ∈ T, ((P.affS S φ u (α u)).card : ℝ)) ≤
      n * (T.filter (fun u => u ∈ P.succ S φ ε)).card + ε * n / 4 * n := by
    rw [← sum_filter_add_sum_filter_not T (fun u => u ∈ P.succ S φ ε)]
    have hTc : ((T.filter (fun u => u ∉ P.succ S φ ε)).card : ℝ) ≤ n := by
      exact_mod_cast (card_le_univ _).trans (by simp)
    have e1 : ∑ u ∈ T.filter (fun u => u ∈ P.succ S φ ε), ((P.affS S φ u (α u)).card : ℝ) ≤
        ∑ _u ∈ T.filter (fun u => u ∈ P.succ S φ ε), (n : ℝ) :=
      sum_le_sum (fun u _ => by exact_mod_cast P.card_affS_le S φ u (α u))
    have e2 : ∑ u ∈ T.filter (fun u => u ∉ P.succ S φ ε), ((P.affS S φ u (α u)).card : ℝ) ≤
        ∑ _u ∈ T.filter (fun u => u ∉ P.succ S φ ε), ε * n / 4 := by
      refine sum_le_sum (fun u hu => ?_)
      rw [mem_filter] at hu
      obtain ⟨huS, hune⟩ := hT u hu.1
      have : ¬ ∀ c ∈ P.Lφ S φ u, ε * n / 4 ≤ ((P.affS S φ u c).card : ℝ) :=
        fun h => hu.2 (mem_filter.2 ⟨mem_compl.2 huS, h⟩)
      push_neg at this
      obtain ⟨c, hc, hlt⟩ := this
      have := (hαT u huS hune).2 c hc
      have : ((P.affS S φ u (α u)).card : ℝ) ≤ (P.affS S φ u c).card := by exact_mod_cast this
      linarith
    simp only [sum_const, nsmul_eq_mul] at e1 e2
    have h4 : 0 ≤ ε * n / 4 := by positivity
    have := mul_le_mul_of_nonneg_right hTc h4
    nlinarith
  -- `U'` and the successful part of `T` are disjoint pieces of `succ`
  have hsucc : U'.card + (T.filter (fun u => u ∈ P.succ S φ ε)).card ≤ (P.succ S φ ε).card := by
    rw [← card_union_of_disjoint]
    · refine card_le_card (union_subset ?_ (fun u hu => (mem_filter.1 hu).2))
      intro u hu
      rw [mem_filter] at hu
      refine mem_filter.2 ⟨hu.1, fun c hc => ?_⟩
      rw [hu.2] at hc; exact absurd hc (notMem_empty c)
    · rw [disjoint_left]
      intro u hu hu'
      exact (mem_sdiff.1 (mem_filter.1 hu').1).2 hu
  have hf := hfar α hαL
  have hconf' : (P.conf α : ℝ) ≤ 2 * n * U'.card + 2 * ∑ u ∈ T, ((P.affS S φ u (α u)).card : ℝ) := by
    exact_mod_cast hconf
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsucc' : (U'.card : ℝ) + (T.filter (fun u => u ∈ P.succ S φ ε)).card ≤
      (P.succ S φ ε).card := by exact_mod_cast hsucc
  have key : ε * (n : ℝ) ^ 2 ≤ 2 * n * (P.succ S φ ε).card + ε * n ^ 2 / 2 := by nlinarith
  have : ε * n / 4 * (2 * n) ≤ (P.succ S φ ε).card * (2 * n) := by nlinarith
  exact le_of_mul_le_mul_right this (by positivity)

end SetColoring

end E34
