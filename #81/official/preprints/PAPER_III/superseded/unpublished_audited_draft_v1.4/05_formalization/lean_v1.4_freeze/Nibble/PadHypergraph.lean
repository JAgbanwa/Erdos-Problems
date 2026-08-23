/-
# Nibble — the explicit degree-balancing padding of a hypergraph

Given a `3`-uniform hypergraph `H` on a finite vertex type `R` and a *deficiency* function
`a : R → ℕ`, we build a `3`-uniform hypergraph `padHyper` on `R ⊕ Fin MD` whose hyperedges are

* the hyperedges of `H` (transported along `Sum.inl`), and
* one *padding* hyperedge `{inl r, inr x, inr y}` for each `r : R` and each `k < a r`.

The padding hyperedges are laid out along a single global counter `gI`, which enumerates the pairs
`(r, k)` bijectively onto `range (∑ r, a r)`.  The two dummy vertices attached to the global index
`t` are `t % MD` and `(t % MD + 1 + (t / MD) % K) % MD`.  This makes the dummy degrees *balanced*
(each dummy vertex is hit `2·(T/MD)` times up to an additive error `2`, `T = ∑ r, a r`) and keeps
the dummy codegrees down to `≈ T/(MD·K)`, while the degree of `inl r` is exactly
`degree H r + a r`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.PadCount
import Nibble.Basic

open Finset Hypergraph

namespace Nibble.Pad

variable {R : Type} [Fintype R] [DecidableEq R]

/-! ### The global enumeration of the padding slots -/

/-- A fixed enumeration of the vertex type `R`. -/
noncomputable def enumR (R : Type) [Fintype R] : R ≃ Fin (Fintype.card R) := Fintype.equivFin R

/-- The index of a vertex under the fixed enumeration. -/
noncomputable def idxOf (r : R) : ℕ := ((enumR R) r : ℕ)

omit [DecidableEq R] in
theorem idxOf_lt (r : R) : idxOf r < Fintype.card R := (enumR R r).isLt

omit [DecidableEq R] in
theorem idxOf_injective : Function.Injective (idxOf : R → ℕ) := by
  intro r r' h
  have : (enumR R) r = (enumR R) r' := Fin.ext h
  exact (enumR R).injective this

/-- The deficiency of the `j`-th vertex (zero past the end of the enumeration). -/
noncomputable def aAt (a : R → ℕ) (j : ℕ) : ℕ :=
  if h : j < Fintype.card R then a ((enumR R).symm ⟨j, h⟩) else 0

/-- The cumulative deficiency of the first `i` vertices. -/
noncomputable def cum (a : R → ℕ) (i : ℕ) : ℕ := ∑ j ∈ Finset.range i, aAt a j

/-- The total deficiency. -/
def padTot (a : R → ℕ) : ℕ := ∑ r : R, a r

omit [DecidableEq R] in
theorem aAt_idxOf (a : R → ℕ) (r : R) : aAt a (idxOf r) = a r := by
  rw [aAt, dif_pos (idxOf_lt r)]
  congr 1
  rw [show (⟨idxOf r, idxOf_lt r⟩ : Fin (Fintype.card R)) = (enumR R) r from rfl,
    Equiv.symm_apply_apply]

omit [DecidableEq R] in
theorem cum_succ (a : R → ℕ) (i : ℕ) : cum a (i + 1) = cum a i + aAt a i := by
  rw [cum, cum, Finset.sum_range_succ]

omit [DecidableEq R] in
theorem cum_mono (a : R → ℕ) : Monotone (cum a) := by
  intro i j hij
  exact Finset.sum_le_sum_of_subset
    (fun t ht => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp ht) hij))

omit [DecidableEq R] in
theorem cum_card (a : R → ℕ) : cum a (Fintype.card R) = padTot a := by
  rw [cum, padTot]
  calc ∑ j ∈ Finset.range (Fintype.card R), aAt a j
      = ∑ i : Fin (Fintype.card R), aAt a (i : ℕ) :=
        (Fin.sum_univ_eq_sum_range (fun j => aAt a j) (Fintype.card R)).symm
    _ = ∑ r : R, a r := by
        refine Fintype.sum_equiv (enumR R).symm _ _ (fun i => ?_)
        rw [← aAt_idxOf a ((enumR R).symm i)]
        congr 1
        simp [idxOf]

/-! ### The padding index set -/

/-- The set of padding slots: pairs `(r, k)` with `k < a r`. -/
def padIdx (a : R → ℕ) : Finset (R × ℕ) :=
  Finset.univ.biUnion (fun r : R => (Finset.range (a r)).image (fun k => (r, k)))

theorem mem_padIdx {a : R → ℕ} {p : R × ℕ} : p ∈ padIdx a ↔ p.2 < a p.1 := by
  classical
  simp only [padIdx, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_range, Prod.ext_iff]
  constructor
  · rintro ⟨r, k, hk, rfl, rfl⟩
    exact hk
  · intro h
    exact ⟨p.1, p.2, h, rfl, rfl⟩

theorem card_padIdx (a : R → ℕ) : (padIdx a).card = padTot a := by
  classical
  rw [padIdx, Finset.card_biUnion, padTot]
  · exact Finset.sum_congr rfl (fun r _ => by
      rw [Finset.card_image_of_injective _ (fun k k' h => (Prod.mk.injEq _ _ _ _ ▸ h).2),
        Finset.card_range])
  · intro r _ r' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro p hp hp'
    rw [Finset.mem_image] at hp hp'
    obtain ⟨k, _, rfl⟩ := hp
    obtain ⟨k', _, hk'⟩ := hp'
    exact hne (congrArg Prod.fst hk').symm

/-- The global index of a padding slot. -/
noncomputable def gI (a : R → ℕ) (p : R × ℕ) : ℕ := cum a (idxOf p.1) + p.2

theorem gI_lt {a : R → ℕ} {p : R × ℕ} (hp : p ∈ padIdx a) : gI a p < padTot a := by
  rw [mem_padIdx] at hp
  have h1 : cum a (idxOf p.1) + p.2 < cum a (idxOf p.1 + 1) := by
    rw [cum_succ, aAt_idxOf]
    omega
  have h2 : cum a (idxOf p.1 + 1) ≤ cum a (Fintype.card R) :=
    cum_mono a (idxOf_lt p.1)
  rw [cum_card] at h2
  exact lt_of_lt_of_le h1 h2

theorem gI_injOn (a : R → ℕ) : Set.InjOn (gI a) (padIdx a) := by
  intro p hp p' hp' heq
  rw [Finset.mem_coe, mem_padIdx] at hp hp'
  rcases lt_trichotomy (idxOf p.1) (idxOf p'.1) with hlt | heq' | hgt
  · exfalso
    have h1 : cum a (idxOf p.1 + 1) ≤ cum a (idxOf p'.1) := cum_mono a hlt
    have h2 : cum a (idxOf p.1 + 1) = cum a (idxOf p.1) + a p.1 := by
      rw [cum_succ, aAt_idxOf]
    rw [gI, gI] at heq
    omega
  · have hr : p.1 = p'.1 := idxOf_injective heq'
    rw [gI, gI, heq'] at heq
    exact Prod.ext hr (by omega)
  · exfalso
    have h1 : cum a (idxOf p'.1 + 1) ≤ cum a (idxOf p.1) := cum_mono a hgt
    have h2 : cum a (idxOf p'.1 + 1) = cum a (idxOf p'.1) + a p'.1 := by
      rw [cum_succ, aAt_idxOf]
    rw [gI, gI] at heq
    omega

/-- **The global counter enumerates the padding slots bijectively.** -/
theorem gI_image (a : R → ℕ) : (padIdx a).image (gI a) = Finset.range (padTot a) := by
  classical
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    exact Finset.mem_range.mpr (gI_lt hp)
  · rw [Finset.card_image_of_injOn (gI_injOn a), card_padIdx, Finset.card_range]

/-- Counting padding slots by a property of their global index. -/
theorem card_filter_padIdx (a : R → ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((padIdx a).filter (fun p => P (gI a p))).card
      = ((Finset.range (padTot a)).filter P).card := by
  classical
  rw [← gI_image a, Finset.filter_image]
  exact (Finset.card_image_of_injOn
    (Set.InjOn.mono (Finset.filter_subset _ _) (gI_injOn a))).symm

/-! ### The padded hypergraph -/

theorem blockFun_lt (MD : ℕ) (hMD : 0 < MD) (c : ℕ → ℕ) (t : ℕ) : blockFun MD c t < MD :=
  Nat.mod_lt _ hMD

/-- The shift used on the `q`-th block of dummy vertices. -/
def shiftK (K : ℕ) : ℕ → ℕ := fun q => 1 + q % K

/-- The dummy vertex attached to the global index `t` by the block map `c`. -/
def dv (MD : ℕ) [NeZero MD] (c : ℕ → ℕ) (t : ℕ) : Fin MD :=
  ⟨blockFun MD c t, blockFun_lt MD (Nat.pos_of_ne_zero (NeZero.ne MD)) c t⟩

/-- The `t`-th padding hyperedge at the real vertex `r`. -/
noncomputable def padEdge (MD : ℕ) [NeZero MD] (a : R → ℕ) (K : ℕ) (p : R × ℕ) :
    Finset (R ⊕ Fin MD) :=
  {Sum.inl p.1, Sum.inr (dv MD (fun _ => 0) (gI a p)), Sum.inr (dv MD (shiftK K) (gI a p))}

/-- The family of padding hyperedges. -/
noncomputable def padFam (MD : ℕ) [NeZero MD] (a : R → ℕ) (K : ℕ) :
    Finset (Finset (R ⊕ Fin MD)) :=
  (padIdx a).image (padEdge MD a K)

/-- The original hyperedges, transported to the padded vertex type. -/
def realFam (MD : ℕ) (H : Finset (Finset R)) : Finset (Finset (R ⊕ Fin MD)) :=
  H.image (Finset.image Sum.inl)

/-- **The padded hypergraph.** -/
noncomputable def padHyper (MD : ℕ) [NeZero MD] (H : Finset (Finset R)) (a : R → ℕ) (K : ℕ) :
    Finset (Finset (R ⊕ Fin MD)) :=
  realFam MD H ∪ padFam MD a K

/-- A nonzero shift never fixes a residue. -/
theorem add_mod_ne (MD s c : ℕ) (hs : s < MD) (hc0 : 0 < c) (hcMD : c < MD) :
    (s + c) % MD ≠ s := by
  intro h
  have hmod : (s + c) % MD = s % MD := by rw [h, Nat.mod_eq_of_lt hs]
  have hdvd : MD ∣ c := by
    have h1 : s ≡ s + c [MOD MD] := hmod.symm
    have h2 := (Nat.modEq_iff_dvd' (Nat.le_add_right s c)).mp h1
    simpa using h2
  exact absurd (Nat.le_of_dvd hc0 hdvd) (not_le.mpr hcMD)

theorem shiftK_pos (K q : ℕ) : 0 < shiftK K q := by
  rw [shiftK]; omega

theorem shiftK_le {K : ℕ} (hK : 0 < K) (q : ℕ) : shiftK K q ≤ K := by
  have := Nat.mod_lt q hK
  rw [shiftK]; omega

/-- The two dummy vertices of a padding hyperedge are distinct. -/
theorem dv_ne (MD : ℕ) [NeZero MD] {K : ℕ} (hK : 0 < K) (hKMD : K < MD) (t : ℕ) :
    dv MD (fun _ => 0) t ≠ dv MD (shiftK K) t := by
  have hMD : 0 < MD := Nat.pos_of_ne_zero (NeZero.ne MD)
  intro h
  have hval : blockFun MD (fun _ => 0) t = blockFun MD (shiftK K) t := congrArg Fin.val h
  have h0 : blockFun MD (fun _ => 0) t = t % MD := by
    rw [blockFun, Nat.add_zero]
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ hMD)
  rw [h0, blockFun] at hval
  exact add_mod_ne MD (t % MD) (shiftK K (t / MD)) (Nat.mod_lt _ hMD) (shiftK_pos _ _)
    (lt_of_le_of_lt (shiftK_le hK _) hKMD) hval.symm

/-- Cancellation of a common summand modulo `MD`. -/
theorem add_mod_cancel {MD x c c' : ℕ} (hc : c < MD) (hc' : c' < MD)
    (h : (x + c) % MD = (x + c') % MD) : c = c' := by
  have h1 : (x + c) ≡ (x + c') [MOD MD] := h
  have h2 : c ≡ c' [MOD MD] := Nat.ModEq.add_left_cancel' x h1
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at h2

theorem blockFun_zero (MD : ℕ) (hMD : 0 < MD) (t : ℕ) : blockFun MD (fun _ => 0) t = t % MD := by
  rw [blockFun, Nat.add_zero]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ hMD)

section Padded

variable (MD : ℕ) [NeZero MD] {H : Finset (Finset R)} {a : R → ℕ} {K : ℕ}

theorem dv_val (c : ℕ → ℕ) (t : ℕ) : (dv MD c t).val = blockFun MD c t := rfl

theorem dv_eq_iff {c c' : ℕ → ℕ} {t t' : ℕ} :
    dv MD c t = dv MD c' t' ↔ blockFun MD c t = blockFun MD c' t' := by
  rw [Fin.ext_iff, dv_val, dv_val]

theorem dv_eq_fin_iff {c : ℕ → ℕ} {t : ℕ} {x : Fin MD} :
    dv MD c t = x ↔ blockFun MD c t = x.val := by
  rw [Fin.ext_iff, dv_val]

theorem mem_padEdge {p : R × ℕ} {v : R ⊕ Fin MD} :
    v ∈ padEdge MD a K p ↔
      v = Sum.inl p.1 ∨ v = Sum.inr (dv MD (fun _ => 0) (gI a p)) ∨
        v = Sum.inr (dv MD (shiftK K) (gI a p)) := by
  simp [padEdge]

/-- The padding hyperedges have three vertices. -/
theorem padEdge_card (hK : 0 < K) (hKMD : K < MD) (p : R × ℕ) :
    (padEdge MD a K p).card = 3 := by
  have hne := dv_ne MD hK hKMD (gI a p)
  rw [padEdge, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  · simpa using hne
  · simp

/-- **The padding hyperedges are pairwise distinct.** -/
theorem padEdge_injOn (hK : 0 < K) (hKMD : 2 * K < MD) (ha : ∀ r, a r ≤ MD) :
    Set.InjOn (padEdge MD a K) (padIdx a) := by
  have hMD : 0 < MD := Nat.pos_of_ne_zero (NeZero.ne MD)
  intro p hp p' hp' heq
  rw [Finset.mem_coe, mem_padIdx] at hp hp'
  -- the real vertex is determined
  have hfst : p.1 = p'.1 := by
    have h1 : Sum.inl p.1 ∈ padEdge MD a K p' := by
      rw [← heq, mem_padEdge]; exact Or.inl rfl
    rw [mem_padEdge] at h1
    rcases h1 with h | h | h
    · exact Sum.inl_injective h
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  set t := gI a p with ht
  set t' := gI a p' with ht'
  set c := shiftK K (t / MD) with hc
  set c' := shiftK K (t' / MD) with hc'
  have hcpos : 0 < c := shiftK_pos _ _
  have hc'pos : 0 < c' := shiftK_pos _ _
  have hcle : c ≤ K := shiftK_le hK _
  have hc'le : c' ≤ K := shiftK_le hK _
  have hA : dv MD (fun _ => 0) t = dv MD (fun _ => 0) t' ∨
      dv MD (fun _ => 0) t = dv MD (shiftK K) t' := by
    have h1 : Sum.inr (dv MD (fun _ => 0) t) ∈ padEdge MD a K p' := by
      rw [← heq, mem_padEdge]; exact Or.inr (Or.inl rfl)
    rw [mem_padEdge] at h1
    rcases h1 with h | h | h
    · exact absurd h (by simp)
    · exact Or.inl (Sum.inr_injective h)
    · exact Or.inr (Sum.inr_injective h)
  have hAsame : dv MD (fun _ => 0) t = dv MD (fun _ => 0) t' := by
    rcases hA with h | h
    · exact h
    · -- the swapped case is impossible
      exfalso
      have h2 : dv MD (fun _ => 0) t' = dv MD (shiftK K) t := by
        have h1 : Sum.inr (dv MD (fun _ => 0) t') ∈ padEdge MD a K p := by
          rw [heq, mem_padEdge]; exact Or.inr (Or.inl rfl)
        rw [mem_padEdge] at h1
        rcases h1 with h1 | h1 | h1
        · exact absurd h1 (by simp)
        · exact absurd ((Sum.inr_injective h1).trans h) (dv_ne MD hK (by omega) t')
        · exact Sum.inr_injective h1
      -- `s = (s' + c') % MD` and `s' = (s + c) % MD`
      have e1 : t % MD = (t' % MD + c') % MD := by
        have h3 := (dv_eq_iff MD).mp h
        rwa [blockFun_zero MD hMD, blockFun] at h3
      have e2 : t' % MD = (t % MD + c) % MD := by
        have h3 := (dv_eq_iff MD).mp h2
        rwa [blockFun_zero MD hMD, blockFun] at h3
      have e3 : t' % MD = (t' % MD + (c' + c)) % MD := by
        calc t' % MD = (t % MD + c) % MD := e2
          _ = ((t' % MD + c') % MD + c) % MD := by rw [e1]
          _ = (t' % MD + c' + c) % MD := by rw [Nat.mod_add_mod]
          _ = (t' % MD + (c' + c)) % MD := by rw [Nat.add_assoc]
      exact add_mod_ne MD (t' % MD) (c' + c) (Nat.mod_lt _ hMD) (by omega) (by omega) e3.symm
  -- with the same residue and the same real vertex, the slots agree
  have hres : t % MD = t' % MD := by
    have h3 := (dv_eq_iff MD).mp hAsame
    rwa [blockFun_zero MD hMD, blockFun_zero MD hMD] at h3
  have hk : p.2 = p'.2 := by
    have hteq : t = cum a (idxOf p.1) + p.2 := rfl
    have ht'eq : t' = cum a (idxOf p.1) + p'.2 := by rw [ht', gI, hfst]
    have hb : p.2 < MD := lt_of_lt_of_le hp (ha p.1)
    have hb' : p'.2 < MD := lt_of_lt_of_le hp' (ha p'.1)
    rcases le_total t t' with hle | hle
    · have hdvd : MD ∣ (t' - t) := (Nat.modEq_iff_dvd' hle).mp hres
      have hlt : t' - t < MD := by omega
      have : t' - t = 0 := by
        rcases Nat.eq_zero_or_pos (t' - t) with h0 | h0
        · exact h0
        · exact absurd (Nat.le_of_dvd h0 hdvd) (by omega)
      omega
    · have hdvd : MD ∣ (t - t') := (Nat.modEq_iff_dvd' hle).mp hres.symm
      have hlt : t - t' < MD := by omega
      have : t - t' = 0 := by
        rcases Nat.eq_zero_or_pos (t - t') with h0 | h0
        · exact h0
        · exact absurd (Nat.le_of_dvd h0 hdvd) (by omega)
      omega
  exact Prod.ext hfst hk

/-! ### Uniformity and disjointness of the two families -/

omit [Fintype R] [NeZero MD] in
theorem realFam_uniform (hH : IsUniform H 3) : IsUniform (realFam MD H) 3 := by
  intro e he
  rw [realFam, Finset.mem_image] at he
  obtain ⟨f, hf, rfl⟩ := he
  rw [Finset.card_image_of_injective _ Sum.inl_injective]
  exact hH f hf

theorem padFam_uniform (hK : 0 < K) (hKMD : K < MD) : IsUniform (padFam MD a K) 3 := by
  intro e he
  rw [padFam, Finset.mem_image] at he
  obtain ⟨p, hp, rfl⟩ := he
  exact padEdge_card MD hK hKMD p

theorem padHyper_uniform (hH : IsUniform H 3) (hK : 0 < K) (hKMD : K < MD) :
    IsUniform (padHyper MD H a K) 3 := by
  intro e he
  rw [padHyper, Finset.mem_union] at he
  rcases he with he | he
  · exact realFam_uniform MD hH e he
  · exact padFam_uniform MD hK hKMD e he

theorem realFam_disjoint_padFam : Disjoint (realFam MD H) (padFam MD a K) := by
  rw [Finset.disjoint_left]
  intro e he he'
  rw [realFam, Finset.mem_image] at he
  rw [padFam, Finset.mem_image] at he'
  obtain ⟨f, hf, rfl⟩ := he
  obtain ⟨p, hp, hpe⟩ := he'
  have hmem : Sum.inr (dv MD (fun _ => 0) (gI a p)) ∈ Finset.image Sum.inl f := by
    rw [← hpe, mem_padEdge]; exact Or.inr (Or.inl rfl)
  rw [Finset.mem_image] at hmem
  obtain ⟨v, -, hv⟩ := hmem
  exact absurd hv (by simp)

/-! ### Degrees -/

theorem degree_union {W : Type} [Fintype W] [DecidableEq W] {A B : Finset (Finset W)}
    (h : Disjoint A B) (v : W) : degree (A ∪ B) v = degree A v + degree B v := by
  classical
  rw [degree, degree, degree, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

theorem codegree_union {W : Type} [Fintype W] [DecidableEq W] {A B : Finset (Finset W)}
    (h : Disjoint A B) (u v : W) :
    codegree (A ∪ B) u v = codegree A u v + codegree B u v := by
  classical
  rw [codegree, codegree, codegree, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

omit [Fintype R] [NeZero MD] in
theorem degree_realFam_inl (r : R) : degree (realFam MD H) (Sum.inl r) = degree H r := by
  classical
  have hset : (realFam MD H).filter (fun e => Sum.inl r ∈ e)
      = (H.filter (fun f => r ∈ f)).image (Finset.image Sum.inl) := by
    ext e
    simp only [realFam, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨f, hf, rfl⟩, hmem⟩
      refine ⟨f, ⟨hf, ?_⟩, rfl⟩
      rw [Finset.mem_image] at hmem
      obtain ⟨v, hv, hveq⟩ := hmem
      rwa [Sum.inl_injective hveq] at hv
    · rintro ⟨f, ⟨hf, hrf⟩, rfl⟩
      exact ⟨⟨f, hf, rfl⟩, Finset.mem_image_of_mem _ hrf⟩
  rw [degree, hset,
    Finset.card_image_of_injective _ (Finset.image_injective Sum.inl_injective), degree]

omit [Fintype R] [NeZero MD] in
theorem degree_realFam_inr (x : Fin MD) : degree (realFam MD H) (Sum.inr x) = 0 := by
  classical
  rw [degree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he
  rw [realFam, Finset.mem_image] at he
  obtain ⟨f, -, rfl⟩ := he
  intro hmem
  rw [Finset.mem_image] at hmem
  obtain ⟨v, -, hv⟩ := hmem
  exact absurd hv (by simp)

theorem card_padIdx_fst (r : R) : ((padIdx a).filter (fun p => p.1 = r)).card = a r := by
  classical
  have hset : (padIdx a).filter (fun p => p.1 = r)
      = (Finset.range (a r)).image (fun k => (r, k)) := by
    ext p
    simp only [Finset.mem_filter, mem_padIdx, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, rfl⟩
      exact ⟨p.2, h1, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨hk, rfl⟩
  rw [hset, Finset.card_image_of_injective _ (fun k k' h => (Prod.mk.injEq _ _ _ _ ▸ h).2),
    Finset.card_range]

theorem degree_padFam_inl (hK : 0 < K) (hKMD : 2 * K < MD) (ha : ∀ r, a r ≤ MD) (r : R) :
    degree (padFam MD a K) (Sum.inl r) = a r := by
  classical
  have hset : (padFam MD a K).filter (fun e => Sum.inl r ∈ e)
      = ((padIdx a).filter (fun p => p.1 = r)).image (padEdge MD a K) := by
    ext e
    simp only [padFam, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hmem⟩
      rw [mem_padEdge] at hmem
      refine ⟨p, ⟨hp, ?_⟩, rfl⟩
      rcases hmem with h | h | h
      · exact (Sum.inl_injective h).symm
      · exact absurd h (by simp)
      · exact absurd h (by simp)
    · rintro ⟨p, ⟨hp, rfl⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, by rw [mem_padEdge]; exact Or.inl rfl⟩
  rw [degree, hset, Finset.card_image_of_injOn
    (Set.InjOn.mono (Finset.filter_subset _ _) (padEdge_injOn MD hK hKMD ha)),
    card_padIdx_fst]

/-- Counting padding hyperedges with a property, by counting padding slots. -/
theorem card_padFam_filter (hK : 0 < K) (hKMD : 2 * K < MD) (ha : ∀ r, a r ≤ MD)
    (Q : Finset (R ⊕ Fin MD) → Prop) [DecidablePred Q] :
    ((padFam MD a K).filter Q).card
      = ((padIdx a).filter (fun p => Q (padEdge MD a K p))).card := by
  classical
  rw [padFam, Finset.filter_image, Finset.card_image_of_injOn
    (Set.InjOn.mono (Finset.filter_subset _ _) (padEdge_injOn MD hK hKMD ha))]

/-- **The dummy degrees are the two block counts.** -/
theorem degree_padFam_inr (hK : 0 < K) (hKMD : 2 * K < MD) (ha : ∀ r, a r ≤ MD) (x : Fin MD) :
    degree (padFam MD a K) (Sum.inr x)
      = blockCount MD (fun _ => 0) x.val (padTot a)
        + blockCount MD (shiftK K) x.val (padTot a) := by
  classical
  have hMD : 0 < MD := Nat.pos_of_ne_zero (NeZero.ne MD)
  rw [degree, card_padFam_filter MD hK hKMD ha]
  have hsplit : (padIdx a).filter (fun p => Sum.inr x ∈ padEdge MD a K p)
      = ((padIdx a).filter (fun p => blockFun MD (fun _ => 0) (gI a p) = x.val))
        ∪ ((padIdx a).filter (fun p => blockFun MD (shiftK K) (gI a p) = x.val)) := by
    rw [← Finset.filter_or]
    refine Finset.filter_congr (fun p _ => ?_)
    rw [mem_padEdge]
    simp only [Sum.inr.injEq, reduceCtorEq, false_or, Fin.ext_iff, dv_val]
    constructor
    · rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm]
    · rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm]
  have hdisj : Disjoint ((padIdx a).filter (fun p => blockFun MD (fun _ => 0) (gI a p) = x.val))
      ((padIdx a).filter (fun p => blockFun MD (shiftK K) (gI a p) = x.val)) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    rw [Finset.mem_filter] at h1 h2
    exact absurd ((dv_eq_iff MD).mpr (h1.2.trans h2.2.symm))
      (dv_ne MD hK (by omega) (gI a p))
  rw [hsplit, Finset.card_union_of_disjoint hdisj,
    card_filter_padIdx a (fun t => blockFun MD (fun _ => 0) t = x.val),
    card_filter_padIdx a (fun t => blockFun MD (shiftK K) t = x.val),
    ← blockCount_eq_filter_range, ← blockCount_eq_filter_range]

/-- **The dummy degrees are balanced**: they equal `2·(T/MD)` up to an additive error `2`. -/
theorem degree_padFam_inr_bounds (hK : 0 < K) (hKMD : 2 * K < MD) (ha : ∀ r, a r ≤ MD)
    (x : Fin MD) :
    2 * (padTot a / MD) ≤ degree (padFam MD a K) (Sum.inr x) ∧
      degree (padFam MD a K) (Sum.inr x) ≤ 2 * (padTot a / MD) + 2 := by
  rw [degree_padFam_inr MD hK hKMD ha]
  have h1 := blockCount_ge MD (fun _ => 0) x.isLt (padTot a)
  have h2 := blockCount_le MD (fun _ => 0) x.isLt (padTot a)
  have h3 := blockCount_ge MD (shiftK K) x.isLt (padTot a)
  have h4 := blockCount_le MD (shiftK K) x.isLt (padTot a)
  omega

/-! ### Codegrees -/

omit [Fintype R] [NeZero MD] in
theorem codegree_realFam_inl (r r' : R) :
    codegree (realFam MD H) (Sum.inl r) (Sum.inl r') = codegree H r r' := by
  classical
  have hset : (realFam MD H).filter (fun e => Sum.inl r ∈ e ∧ Sum.inl r' ∈ e)
      = (H.filter (fun f => r ∈ f ∧ r' ∈ f)).image (Finset.image Sum.inl) := by
    ext e
    simp only [realFam, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨f, hf, rfl⟩, hm1, hm2⟩
      refine ⟨f, ⟨hf, ?_, ?_⟩, rfl⟩
      · rw [Finset.mem_image] at hm1
        obtain ⟨v, hv, hveq⟩ := hm1
        rwa [Sum.inl_injective hveq] at hv
      · rw [Finset.mem_image] at hm2
        obtain ⟨v, hv, hveq⟩ := hm2
        rwa [Sum.inl_injective hveq] at hv
    · rintro ⟨f, ⟨hf, h1, h2⟩, rfl⟩
      exact ⟨⟨f, hf, rfl⟩, Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2⟩
  rw [codegree, hset,
    Finset.card_image_of_injective _ (Finset.image_injective Sum.inl_injective), codegree]

omit [Fintype R] [NeZero MD] in
theorem codegree_realFam_inr_left (x : Fin MD) (v : R ⊕ Fin MD) :
    codegree (realFam MD H) (Sum.inr x) v = 0 := by
  classical
  rw [codegree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he
  rw [realFam, Finset.mem_image] at he
  obtain ⟨f, -, rfl⟩ := he
  rintro ⟨hmem, -⟩
  rw [Finset.mem_image] at hmem
  obtain ⟨w, -, hw⟩ := hmem
  exact absurd hw (by simp)

omit [Fintype R] [NeZero MD] in
theorem codegree_realFam_inr_right (x : Fin MD) (v : R ⊕ Fin MD) :
    codegree (realFam MD H) v (Sum.inr x) = 0 := by
  classical
  rw [codegree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he
  rw [realFam, Finset.mem_image] at he
  obtain ⟨f, -, rfl⟩ := he
  rintro ⟨-, hmem⟩
  rw [Finset.mem_image] at hmem
  obtain ⟨w, -, hw⟩ := hmem
  exact absurd hw (by simp)

theorem codegree_padFam_inl_inl (hK : 0 < K) (hKMD : 2 * K < MD) (ha : ∀ r, a r ≤ MD)
    {r r' : R} (hne : r ≠ r') : codegree (padFam MD a K) (Sum.inl r) (Sum.inl r') = 0 := by
  classical
  rw [codegree, card_padFam_filter MD hK hKMD ha, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro p _
  rintro ⟨h1, h2⟩
  rw [mem_padEdge] at h1 h2
  have e1 : r = p.1 := by
    rcases h1 with h | h | h
    · exact Sum.inl_injective h
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  have e2 : r' = p.1 := by
    rcases h2 with h | h | h
    · exact Sum.inl_injective h
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  exact hne (e1.trans e2.symm)

/-- A window of length at most `MD` meets each fibre of a block map at most twice. -/
theorem intervalCount_le_two (MD : ℕ) (c : ℕ → ℕ) {x : ℕ} (hx : x < MD) (C L : ℕ) (hL : L ≤ MD) :
    intervalCount MD c x C (C + L) ≤ 2 := by
  have hMD : 0 < MD := lt_of_le_of_lt (Nat.zero_le x) hx
  have hadd : blockCount MD c x C + intervalCount MD c x C (C + L) = blockCount MD c x (C + L) := by
    rw [blockCount, blockCount]
    exact intervalCount_add MD c x (Nat.zero_le C) (Nat.le_add_right C L)
  have h1 := blockCount_ge MD c hx C
  have h2 := blockCount_le MD c hx (C + L)
  have h3 : (C + L) / MD ≤ C / MD + 1 := by
    calc (C + L) / MD ≤ (C + MD) / MD := Nat.div_le_div_right (by omega)
      _ = C / MD + 1 := by rw [Nat.add_div_right _ hMD]
  omega

omit [NeZero MD] in
/-- The padding slots at a fixed real vertex, counted by a block condition on the global index. -/
theorem card_filter_fst_block (c : ℕ → ℕ) (r : R) (x : ℕ) :
    ((padIdx a).filter (fun p => p.1 = r ∧ blockFun MD c (gI a p) = x)).card
      = intervalCount MD c x (cum a (idxOf r)) (cum a (idxOf r) + a r) := by
  classical
  rw [← intervalCount_shift]
  refine Finset.card_nbij' (fun p => p.2) (fun k => (r, k)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_padIdx] at hp
    obtain ⟨hlt, hfst, hbf⟩ := hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
    refine ⟨by rw [← hfst]; exact hlt, ?_⟩
    rw [← hbf, gI, hfst]
  · intro k hk
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hk
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_padIdx]
    exact ⟨hk.1, trivial, hk.2⟩
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp
    exact Prod.ext_iff.mpr ⟨hp.2.1.symm, rfl⟩
  · intro k _
    rfl

theorem codegree_padFam_inl_inr (hK : 0 < K) (hKMD : 2 * K < MD) (ha : ∀ r, a r ≤ MD)
    (r : R) (x : Fin MD) : codegree (padFam MD a K) (Sum.inl r) (Sum.inr x) ≤ 4 := by
  classical
  rw [codegree, card_padFam_filter MD hK hKMD ha]
  have hsub : (padIdx a).filter (fun p => Sum.inl r ∈ padEdge MD a K p ∧
        Sum.inr x ∈ padEdge MD a K p)
      ⊆ ((padIdx a).filter (fun p => p.1 = r ∧ blockFun MD (fun _ => 0) (gI a p) = x.val))
        ∪ ((padIdx a).filter (fun p => p.1 = r ∧ blockFun MD (shiftK K) (gI a p) = x.val)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hmem, h1, h2⟩ := hp
    rw [mem_padEdge] at h1 h2
    have hfst : p.1 = r := by
      rcases h1 with h | h | h
      · exact (Sum.inl_injective h).symm
      · exact absurd h (by simp)
      · exact absurd h (by simp)
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases h2 with h | h | h
    · exact absurd h (by simp)
    · exact Or.inl ⟨hmem, hfst, (dv_eq_fin_iff MD).mp (Sum.inr_injective h).symm⟩
    · exact Or.inr ⟨hmem, hfst, (dv_eq_fin_iff MD).mp (Sum.inr_injective h).symm⟩
  calc ((padIdx a).filter (fun p => Sum.inl r ∈ padEdge MD a K p ∧
          Sum.inr x ∈ padEdge MD a K p)).card
      ≤ (((padIdx a).filter (fun p => p.1 = r ∧ blockFun MD (fun _ => 0) (gI a p) = x.val))
          ∪ ((padIdx a).filter (fun p => p.1 = r ∧ blockFun MD (shiftK K) (gI a p) = x.val))).card :=
        Finset.card_le_card hsub
    _ ≤ ((padIdx a).filter (fun p => p.1 = r ∧ blockFun MD (fun _ => 0) (gI a p) = x.val)).card
          + ((padIdx a).filter (fun p => p.1 = r ∧ blockFun MD (shiftK K) (gI a p) = x.val)).card :=
        Finset.card_union_le _ _
    _ ≤ 2 + 2 := by
        rw [card_filter_fst_block MD (fun _ => 0) r x.val,
          card_filter_fst_block MD (shiftK K) r x.val]
        exact Nat.add_le_add (intervalCount_le_two MD _ x.isLt _ _ (ha r))
          (intervalCount_le_two MD _ x.isLt _ _ (ha r))
    _ = 4 := by norm_num

/-- **The dummy codegrees are small**: a fixed *ordered* dummy pair occurs at most
`(T/MD + 1)/K + 1` times. -/
theorem card_ordered_pair_le (MD K T x y : ℕ) (hMD : 0 < MD) (hK : 0 < K) (hKMD : K < MD) :
    ((Finset.range T).filter (fun t => blockFun MD (fun _ => 0) t = x ∧
        blockFun MD (shiftK K) t = y)).card ≤ (T / MD + 1) / K + 1 := by
  classical
  set S := (Finset.range T).filter (fun t => blockFun MD (fun _ => 0) t = x ∧
      blockFun MD (shiftK K) t = y) with hS
  rcases Finset.eq_empty_or_nonempty S with hemp | ⟨t₀, ht₀⟩
  · rw [hemp]; simp
  set j₀ := (t₀ / MD) % K with hj₀
  have hj₀lt : j₀ < K := Nat.mod_lt _ hK
  have hmemS : ∀ t ∈ S, t < T ∧ t % MD = x ∧ (x + shiftK K (t / MD)) % MD = y := by
    intro t ht
    rw [hS, Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨hlt, h1, h2⟩ := ht
    rw [blockFun_zero MD hMD] at h1
    rw [blockFun, h1] at h2
    exact ⟨hlt, h1, h2⟩
  have hshift : ∀ t ∈ S, (t / MD) % K = j₀ := by
    intro t ht
    obtain ⟨-, -, h2⟩ := hmemS t ht
    obtain ⟨-, -, h2'⟩ := hmemS t₀ ht₀
    have hc : shiftK K (t / MD) = shiftK K (t₀ / MD) :=
      add_mod_cancel (lt_of_le_of_lt (shiftK_le hK _) hKMD)
        (lt_of_le_of_lt (shiftK_le hK _) hKMD) (h2.trans h2'.symm)
    rw [shiftK, shiftK] at hc
    omega
  have hsub : S.image (fun t => t / MD)
      ⊆ (Finset.range (T / MD + 1)).filter (fun q => q % K = j₀) := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    obtain ⟨hlt, -, -⟩ := hmemS t ht
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by
      have : t / MD ≤ T / MD := Nat.div_le_div_right (le_of_lt hlt)
      omega, hshift t ht⟩
  have hinj : Set.InjOn (fun t => t / MD) S := by
    intro t ht t' ht' heq
    obtain ⟨-, h1, -⟩ := hmemS t ht
    obtain ⟨-, h1', -⟩ := hmemS t' ht'
    have e1 := Nat.div_add_mod t MD
    have e2 := Nat.div_add_mod t' MD
    simp only at heq
    rw [← e1, ← e2, heq, h1, h1']
  have hcount : ((Finset.range (T / MD + 1)).filter (fun q => q % K = j₀)).card
      ≤ (T / MD + 1) / K + 1 := by
    have hrw : ((Finset.range (T / MD + 1)).filter (fun q => q % K = j₀)).card
        = blockCount K (fun _ => 0) j₀ (T / MD + 1) := by
      rw [blockCount_eq_filter_range]
      congr 1
      refine Finset.filter_congr (fun q _ => ?_)
      rw [blockFun_zero K hK]
    rw [hrw]
    exact blockCount_le K (fun _ => 0) hj₀lt _
  calc S.card = (S.image (fun t => t / MD)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((Finset.range (T / MD + 1)).filter (fun q => q % K = j₀)).card :=
        Finset.card_le_card hsub
    _ ≤ (T / MD + 1) / K + 1 := hcount

theorem codegree_padFam_inr_inr (hK : 0 < K) (hKMD : 2 * K < MD) (ha : ∀ r, a r ≤ MD)
    {x y : Fin MD} (hne : x ≠ y) :
    codegree (padFam MD a K) (Sum.inr x) (Sum.inr y)
      ≤ 2 * ((padTot a / MD + 1) / K + 1) := by
  classical
  have hMD : 0 < MD := Nat.pos_of_ne_zero (NeZero.ne MD)
  rw [codegree, card_padFam_filter MD hK hKMD ha]
  have hsub : (padIdx a).filter (fun p => Sum.inr x ∈ padEdge MD a K p ∧
        Sum.inr y ∈ padEdge MD a K p)
      ⊆ ((padIdx a).filter (fun p => blockFun MD (fun _ => 0) (gI a p) = x.val ∧
            blockFun MD (shiftK K) (gI a p) = y.val))
        ∪ ((padIdx a).filter (fun p => blockFun MD (fun _ => 0) (gI a p) = y.val ∧
            blockFun MD (shiftK K) (gI a p) = x.val)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hmem, h1, h2⟩ := hp
    rw [mem_padEdge] at h1 h2
    have hxne : x.val ≠ y.val := fun h => hne (Fin.ext h)
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases h1 with h | h | h
    · exact absurd h (by simp)
    · have hx' : blockFun MD (fun _ => 0) (gI a p) = x.val :=
        (dv_eq_fin_iff MD).mp (Sum.inr_injective h).symm
      rcases h2 with h' | h' | h'
      · exact absurd h' (by simp)
      · exact absurd (hx'.symm.trans ((dv_eq_fin_iff MD).mp (Sum.inr_injective h').symm)) hxne
      · exact Or.inl ⟨hmem, hx', (dv_eq_fin_iff MD).mp (Sum.inr_injective h').symm⟩
    · have hx' : blockFun MD (shiftK K) (gI a p) = x.val :=
        (dv_eq_fin_iff MD).mp (Sum.inr_injective h).symm
      rcases h2 with h' | h' | h'
      · exact absurd h' (by simp)
      · exact Or.inr ⟨hmem, (dv_eq_fin_iff MD).mp (Sum.inr_injective h').symm, hx'⟩
      · exact absurd (hx'.symm.trans ((dv_eq_fin_iff MD).mp (Sum.inr_injective h').symm)) hxne
  calc ((padIdx a).filter (fun p => Sum.inr x ∈ padEdge MD a K p ∧
          Sum.inr y ∈ padEdge MD a K p)).card
      ≤ (((padIdx a).filter (fun p => blockFun MD (fun _ => 0) (gI a p) = x.val ∧
            blockFun MD (shiftK K) (gI a p) = y.val))
          ∪ ((padIdx a).filter (fun p => blockFun MD (fun _ => 0) (gI a p) = y.val ∧
            blockFun MD (shiftK K) (gI a p) = x.val))).card := Finset.card_le_card hsub
    _ ≤ ((padIdx a).filter (fun p => blockFun MD (fun _ => 0) (gI a p) = x.val ∧
            blockFun MD (shiftK K) (gI a p) = y.val)).card
          + ((padIdx a).filter (fun p => blockFun MD (fun _ => 0) (gI a p) = y.val ∧
            blockFun MD (shiftK K) (gI a p) = x.val)).card := Finset.card_union_le _ _
    _ ≤ ((padTot a / MD + 1) / K + 1) + ((padTot a / MD + 1) / K + 1) := by
        rw [card_filter_padIdx a (fun t => blockFun MD (fun _ => 0) t = x.val ∧
              blockFun MD (shiftK K) t = y.val),
          card_filter_padIdx a (fun t => blockFun MD (fun _ => 0) t = y.val ∧
              blockFun MD (shiftK K) t = x.val)]
        exact Nat.add_le_add
          (card_ordered_pair_le MD K (padTot a) x.val y.val hMD hK (by omega))
          (card_ordered_pair_le MD K (padTot a) y.val x.val hMD hK (by omega))
    _ = 2 * ((padTot a / MD + 1) / K + 1) := by ring

/-! ### The padded hypergraph: degrees and codegrees -/

theorem codegree_symm {W : Type} [Fintype W] [DecidableEq W] (A : Finset (Finset W)) (u v : W) :
    codegree A u v = codegree A v u := by
  classical
  rw [codegree, codegree]
  congr 1
  exact Finset.filter_congr (fun e _ => by tauto)

theorem degree_padHyper_inl (hK : 0 < K) (hKMD : 2 * K < MD) (ha : ∀ r, a r ≤ MD) (r : R) :
    degree (padHyper MD H a K) (Sum.inl r) = degree H r + a r := by
  rw [padHyper, degree_union (realFam_disjoint_padFam MD), degree_realFam_inl,
    degree_padFam_inl MD hK hKMD ha]

theorem degree_padHyper_inr (hK : 0 < K) (hKMD : 2 * K < MD) (ha : ∀ r, a r ≤ MD) (x : Fin MD) :
    2 * (padTot a / MD) ≤ degree (padHyper MD H a K) (Sum.inr x) ∧
      degree (padHyper MD H a K) (Sum.inr x) ≤ 2 * (padTot a / MD) + 2 := by
  rw [padHyper, degree_union (realFam_disjoint_padFam MD), degree_realFam_inr, Nat.zero_add]
  exact degree_padFam_inr_bounds MD hK hKMD ha x

theorem codegree_padHyper_inl_inl (hK : 0 < K) (hKMD : 2 * K < MD) (ha : ∀ r, a r ≤ MD)
    {r r' : R} (hne : r ≠ r') :
    codegree (padHyper MD H a K) (Sum.inl r) (Sum.inl r') = codegree H r r' := by
  rw [padHyper, codegree_union (realFam_disjoint_padFam MD), codegree_realFam_inl,
    codegree_padFam_inl_inl MD hK hKMD ha hne, Nat.add_zero]

theorem codegree_padHyper_inl_inr (hK : 0 < K) (hKMD : 2 * K < MD) (ha : ∀ r, a r ≤ MD)
    (r : R) (x : Fin MD) : codegree (padHyper MD H a K) (Sum.inl r) (Sum.inr x) ≤ 4 := by
  rw [padHyper, codegree_union (realFam_disjoint_padFam MD),
    codegree_realFam_inr_right MD x (Sum.inl r), Nat.zero_add]
  exact codegree_padFam_inl_inr MD hK hKMD ha r x

theorem codegree_padHyper_inr_inr (hK : 0 < K) (hKMD : 2 * K < MD) (ha : ∀ r, a r ≤ MD)
    {x y : Fin MD} (hne : x ≠ y) :
    codegree (padHyper MD H a K) (Sum.inr x) (Sum.inr y)
      ≤ 2 * ((padTot a / MD + 1) / K + 1) := by
  rw [padHyper, codegree_union (realFam_disjoint_padFam MD),
    codegree_realFam_inr_left MD x (Sum.inr y), Nat.zero_add]
  exact codegree_padFam_inr_inr MD hK hKMD ha hne

/-! ### Pulling a matching back to the original hypergraph -/

/-- The real part of a matching of the padded hypergraph, as a matching of `H`. -/
def pullback (H : Finset (Finset R)) (M : Finset (Finset (R ⊕ Fin MD))) : Finset (Finset R) :=
  H.filter (fun T => Finset.image Sum.inl T ∈ M)

theorem pullback_isMatching {M : Finset (Finset (R ⊕ Fin MD))}
    (hM : IsMatching (padHyper MD H a K) M) : IsMatching H (pullback MD H M) := by
  classical
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro T hT T' hT' hne
  rw [pullback, Finset.mem_filter] at hT hT'
  have hneimg : (Finset.image Sum.inl T : Finset (R ⊕ Fin MD)) ≠ Finset.image Sum.inl T' :=
    fun h => hne (Finset.image_injective Sum.inl_injective h)
  have hdisj := hM.disjoint _ hT.2 _ hT'.2 hneimg
  rw [Finset.disjoint_left]
  intro v hv hv'
  exact Finset.disjoint_left.mp hdisj (Finset.mem_image_of_mem _ hv)
    (Finset.mem_image_of_mem _ hv')

/-- The dummy vertices of a hyperedge of the padded hypergraph. -/
def dummySet (e : Finset (R ⊕ Fin MD)) : Finset (Fin MD) :=
  Finset.univ.filter (fun y : Fin MD => Sum.inr y ∈ e)

theorem card_dummySet_padEdge (hK : 0 < K) (hKMD : K < MD) (p : R × ℕ) :
    (dummySet MD (padEdge MD a K p)).card = 2 := by
  classical
  have hset : dummySet MD (padEdge MD a K p)
      = {dv MD (fun _ => 0) (gI a p), dv MD (shiftK K) (gI a p)} := by
    ext y
    simp only [dummySet, Finset.mem_filter, Finset.mem_univ, true_and, mem_padEdge,
      Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, false_or, Sum.inr.injEq]
  rw [hset, Finset.card_insert_of_notMem (by simpa using dv_ne MD hK hKMD (gI a p)),
    Finset.card_singleton]

/-- **The padding hyperedges of a matching are few**: they use up two dummy vertices each. -/
theorem card_sdiff_realFam_le (hK : 0 < K) (hKMD : 2 * K < MD)
    {M : Finset (Finset (R ⊕ Fin MD))} (hM : IsMatching (padHyper MD H a K) M) :
    2 * (M \ realFam MD H).card ≤ MD := by
  classical
  set S := M \ realFam MD H with hS
  have hcard : ∀ e ∈ S, (dummySet MD e).card = 2 := by
    intro e he
    rw [hS, Finset.mem_sdiff] at he
    have hmem := hM.subset he.1
    rw [padHyper, Finset.mem_union] at hmem
    rcases hmem with h | h
    · exact absurd h he.2
    · rw [padFam, Finset.mem_image] at h
      obtain ⟨p, -, rfl⟩ := h
      exact card_dummySet_padEdge MD hK (by omega) p
  have hdisj : ∀ e ∈ S, ∀ e' ∈ S, e ≠ e' → Disjoint (dummySet MD e) (dummySet MD e') := by
    intro e he e' he' hne
    have hd := hM.disjoint e (Finset.mem_sdiff.mp he).1 e' (Finset.mem_sdiff.mp he').1 hne
    rw [Finset.disjoint_left]
    intro y hy hy'
    rw [dummySet, Finset.mem_filter] at hy hy'
    exact Finset.disjoint_left.mp hd hy.2 hy'.2
  have hsum : (S.biUnion (dummySet MD)).card = ∑ e ∈ S, (dummySet MD e).card :=
    Finset.card_biUnion hdisj
  have hle : (S.biUnion (dummySet MD)).card ≤ MD := by
    calc (S.biUnion (dummySet MD)).card ≤ (Finset.univ : Finset (Fin MD)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = MD := by rw [Finset.card_univ, Fintype.card_fin]
  have hval : ∑ e ∈ S, (dummySet MD e).card = 2 * S.card := by
    rw [Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  omega

/-- **The real part of a matching of the padded hypergraph is almost all of it.** -/
theorem card_le_pullback_add (hK : 0 < K) (hKMD : 2 * K < MD)
    {M : Finset (Finset (R ⊕ Fin MD))} (hM : IsMatching (padHyper MD H a K) M) :
    2 * M.card ≤ 2 * (pullback MD H M).card + MD := by
  classical
  have hsplit : (M ∩ realFam MD H).card + (M \ realFam MD H).card = M.card :=
    Finset.card_inter_add_card_sdiff _ _
  have hinter : M ∩ realFam MD H = (pullback MD H M).image (Finset.image Sum.inl) := by
    ext e
    simp only [Finset.mem_inter, realFam, pullback, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨hMe, T, hT, rfl⟩
      exact ⟨T, ⟨hT, hMe⟩, rfl⟩
    · rintro ⟨T, ⟨hT, hTM⟩, rfl⟩
      exact ⟨hTM, T, hT, rfl⟩
  have hcardinter : (M ∩ realFam MD H).card = (pullback MD H M).card := by
    rw [hinter, Finset.card_image_of_injective _ (Finset.image_injective Sum.inl_injective)]
  have hpad := card_sdiff_realFam_le MD hK hKMD hM
  omega

end Padded

end Nibble.Pad
