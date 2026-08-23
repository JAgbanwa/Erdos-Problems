/-
# Nibble — the flow route carried out unconditionally at minimum degree `(15/16)|V|`

`Nibble/DrossFlowRoute.lean` reduces the spread Dross input to the existence of a **transfer
certificate**: capacities on the opposite pairs of `K₄`s whose throughput at every triangle is at
most the base weight, and which satisfy the cut condition for the deficiency demands.

This file verifies both conditions for the *uniform* capacity `c = 2/(3|V|²)` whenever
`δ(G) ≥ (15/16)|V|`:

* `Nibble.card_transferPairs_le` — a triangle is touched by at most `6|V|` transfer arcs;
* `Nibble.throughput_uniformCap_le` — hence the uniform capacity respects the throughput budget;
* `Nibble.card_oppPartners_ge` — at this density every edge has at least `(91/256)|V|²`
  opposite partners, i.e. the *opposite-pair graph* has huge minimum degree;
* `Nibble.crossSum_ge` — a minimum-degree bound on the crossing pairs of any cut;
* `Nibble.cut_bound_refined` — the cut arithmetic, using the balance of the deficiencies on both
  sides of the cut;
* `Nibble.isDrossTransferCert_uniform_of_dense` — the certificate;
* `Nibble.hasSpreadFracTriangleDecomp_of_dense` — **the theorem**: every graph with
  `16 δ(G) ≥ 15 |V|` carries an exact fractional triangle decomposition all of whose weights are at
  most `3/|V|`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DrossFlowRoute

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Counting the transfer arcs at a triangle -/

instance instDecidableIsOppPair (G : SimpleGraph V) [DecidableRel G.Adj] (e₁ e₂ : EdgeV G) :
    Decidable (IsOppPair G e₁ e₂) := by
  unfold IsOppPair; infer_instance

/-- An arc with a nonzero effect on `T` has one of its two edges inside the triangle and spans it. -/
theorem transferSign_ne_zero_imp (G : SimpleGraph V) [DecidableRel G.Adj] (e₁ e₂ : EdgeV G)
    (T : Finset (EdgeV G)) (h : transferSign G e₁ e₂ T ≠ 0) :
    (e₂.val ⊆ triOf G T ∧ triOf G T ⊆ e₁.val ∪ e₂.val)
      ∨ (e₁.val ⊆ triOf G T ∧ triOf G T ⊆ e₁.val ∪ e₂.val) := by
  by_contra hcon
  rw [not_or] at hcon
  rw [transferSign, if_neg hcon.1, if_neg hcon.2, sub_zero] at h
  exact h rfl

/-- **The one-sided count.**  At most `3|V|` arcs have their *first* edge inside the triangle. -/
theorem card_pairs_le_aux (G : SimpleGraph V) [DecidableRel G.Adj] {t : Finset V}
    (ht3 : t.card = 3) (A : Finset (EdgeV G × EdgeV G))
    (hA : ∀ p ∈ A, IsOppPair G p.1 p.2 ∧ p.1.val ⊆ t ∧ t ⊆ p.1.val ∪ p.2.val) :
    A.card ≤ 3 * Fintype.card V := by
  classical
  have hstruct : ∀ p ∈ A, (p.2.val \ t).card = 1 ∧ p.2.val = (t \ p.1.val) ∪ (p.2.val \ t) := by
    intro p hp
    obtain ⟨hopp, hsub, hcov⟩ := hA p hp
    have hca : p.1.val.card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp p.1.property).card_eq
    have hcb : p.2.val.card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp p.2.property).card_eq
    have hdisj : ∀ x ∈ p.1.val, x ∉ p.2.val := fun x hx => hopp.not_mem hx
    have hta : (t \ p.1.val).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub, ht3, hca]
    have htb : t \ p.1.val ⊆ p.2.val := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      rcases Finset.mem_union.mp (hcov hx.1) with h | h
      · exact absurd h hx.2
      · exact h
    have hint1 : 1 ≤ (p.2.val ∩ t).card := by
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hta
      have hmem : y ∈ p.2.val ∩ t := by
        have hy1 : y ∈ t \ p.1.val := by rw [hy]; simp
        exact Finset.mem_inter.mpr ⟨htb hy1, (Finset.mem_sdiff.mp hy1).1⟩
      exact Finset.card_pos.mpr ⟨y, hmem⟩
    have hint2 : (p.2.val ∩ t).card ≤ 1 := by
      by_contra hcon
      push_neg at hcon
      have heq : p.2.val ∩ t = p.2.val :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hcb]; exact hcon)
      have hbt : p.2.val ⊆ t := by rw [← heq]; exact Finset.inter_subset_right
      have hunion : p.1.val ∪ p.2.val ⊆ t := Finset.union_subset hsub hbt
      have hcard4 : (p.1.val ∪ p.2.val).card = 4 := by
        rw [Finset.card_union_of_disjoint (Finset.disjoint_left.mpr hdisj), hca, hcb]
      have := Finset.card_le_card hunion
      omega
    have hsplit := Finset.card_sdiff_add_card_inter p.2.val t
    refine ⟨by omega, ?_⟩
    apply Finset.Subset.antisymm
    · intro x hx
      by_cases hxt : x ∈ t
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxt, fun hxa => hdisj x hxa hx⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hxt⟩)
    · exact Finset.union_subset htb Finset.sdiff_subset
  have hmaps : ∀ p ∈ A, (p.1.val, p.2.val \ t)
      ∈ (t.powersetCard 2) ×ˢ ((Finset.univ : Finset V).image (fun y : V => ({y} : Finset V))) := by
    intro p hp
    obtain ⟨-, hsub, -⟩ := hA p hp
    have hca : p.1.val.card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp p.1.property).card_eq
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (hstruct p hp).1
    refine Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨hsub, hca⟩, ?_⟩
    rw [hy]
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ y, rfl⟩
  have hinj : ∀ p ∈ A, ∀ q ∈ A, (p.1.val, p.2.val \ t) = (q.1.val, q.2.val \ t) → p = q := by
    intro p hp q hq h
    have h1 : p.1.val = q.1.val := congrArg Prod.fst h
    have h2 : p.2.val \ t = q.2.val \ t := congrArg Prod.snd h
    refine Prod.ext (Subtype.ext h1) (Subtype.ext ?_)
    rw [(hstruct p hp).2, (hstruct q hq).2, h1, h2]
  calc A.card ≤ ((t.powersetCard 2) ×ˢ
        ((Finset.univ : Finset V).image (fun y : V => ({y} : Finset V)))).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (t.powersetCard 2).card * ((Finset.univ : Finset V).image
        (fun y : V => ({y} : Finset V))).card := Finset.card_product _ _
    _ ≤ 3 * Fintype.card V := by
        have h1 : (t.powersetCard 2).card = 3 := by
          rw [Finset.card_powersetCard, ht3]; decide
        have h2 : ((Finset.univ : Finset V).image (fun y : V => ({y} : Finset V))).card
            ≤ Fintype.card V := le_trans Finset.card_image_le (by simp)
        rw [h1]
        omega

/-- **The transfer arcs at a triangle**: a triangle is touched by at most `6|V|` arcs. -/
theorem card_transferPairs_le (G : SimpleGraph V) [DecidableRel G.Adj] {T : Finset (EdgeV G)}
    (hT : T ∈ triangleHypergraphSub G) :
    ((Finset.univ : Finset (EdgeV G × EdgeV G)).filter
      (fun p => IsOppPair G p.1 p.2 ∧ transferSign G p.1 p.2 T ≠ 0)).card
      ≤ 6 * Fintype.card V := by
  classical
  set t : Finset V := triOf G T with ht_def
  have ht3 : t.card = 3 := (triOf_isNClique G hT).card_eq
  set A₁ : Finset (EdgeV G × EdgeV G) := (Finset.univ : Finset (EdgeV G × EdgeV G)).filter
    (fun p => IsOppPair G p.1 p.2 ∧ p.1.val ⊆ t ∧ t ⊆ p.1.val ∪ p.2.val) with hA₁
  set A₂ : Finset (EdgeV G × EdgeV G) := (Finset.univ : Finset (EdgeV G × EdgeV G)).filter
    (fun p => IsOppPair G p.2 p.1 ∧ p.2.val ⊆ t ∧ t ⊆ p.2.val ∪ p.1.val) with hA₂
  have hsub : ((Finset.univ : Finset (EdgeV G × EdgeV G)).filter
      (fun p => IsOppPair G p.1 p.2 ∧ transferSign G p.1 p.2 T ≠ 0)) ⊆ A₁ ∪ A₂ := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨-, hopp, hne⟩ := hp
    rcases transferSign_ne_zero_imp G p.1 p.2 T hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Finset.mem_union_right _ ?_
      rw [hA₂, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hopp.symm, h1, by rwa [Finset.union_comm]⟩
    · refine Finset.mem_union_left _ ?_
      rw [hA₁, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hopp, h1, h2⟩
  have hc₁ : A₁.card ≤ 3 * Fintype.card V := by
    refine card_pairs_le_aux G ht3 A₁ (fun p hp => ?_)
    rw [hA₁, Finset.mem_filter] at hp
    exact hp.2
  have hc₂ : A₂.card ≤ 3 * Fintype.card V := by
    have himg : A₂.card = (A₂.image (fun p : EdgeV G × EdgeV G => (p.2, p.1))).card := by
      refine (Finset.card_image_of_injOn (fun p _ q _ h => ?_)).symm
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    rw [himg]
    refine card_pairs_le_aux G ht3 _ (fun p hp => ?_)
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    rw [hA₂, Finset.mem_filter] at hq
    exact hq.2
  calc ((Finset.univ : Finset (EdgeV G × EdgeV G)).filter
        (fun p => IsOppPair G p.1 p.2 ∧ transferSign G p.1 p.2 T ≠ 0)).card
      ≤ (A₁ ∪ A₂).card := Finset.card_le_card hsub
    _ ≤ A₁.card + A₂.card := Finset.card_union_le _ _
    _ ≤ 6 * Fintype.card V := by omega

/-! ### The uniform capacity -/

/-- The uniform capacity `c` on the opposite pairs of `K₄`s. -/
noncomputable def uniformCap (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) :
    EdgeV G → EdgeV G → ℝ :=
  fun e₁ e₂ => if IsOppPair G e₁ e₂ then c else 0

/-- **The throughput of the uniform capacity** at a triangle is at most `(3/2)|V|c`. -/
theorem throughput_uniformCap_le (G : SimpleGraph V) [DecidableRel G.Adj] {c : ℝ} (hc : 0 ≤ c)
    {T : Finset (EdgeV G)} (hT : T ∈ triangleHypergraphSub G) :
    (1 / 4) * ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G,
      uniformCap G c e₁ e₂ * |transferSign G e₁ e₂ T|
      ≤ (3 / 2) * (Fintype.card V : ℝ) * c := by
  classical
  have hswap : ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G,
      uniformCap G c e₁ e₂ * |transferSign G e₁ e₂ T|
      = ∑ p : EdgeV G × EdgeV G, uniformCap G c p.1 p.2 * |transferSign G p.1 p.2 T| := by
    rw [Fintype.sum_prod_type]
  have hbound : ∀ p : EdgeV G × EdgeV G,
      uniformCap G c p.1 p.2 * |transferSign G p.1 p.2 T|
      ≤ (if IsOppPair G p.1 p.2 ∧ transferSign G p.1 p.2 T ≠ 0 then c else 0) := by
    intro p
    by_cases hopp : IsOppPair G p.1 p.2
    · by_cases hne : transferSign G p.1 p.2 T ≠ 0
      · rw [if_pos ⟨hopp, hne⟩, uniformCap, if_pos hopp]
        simpa using mul_le_mul_of_nonneg_left (abs_transferSign_le G p.1 p.2 T) hc
      · push_neg at hne
        rw [if_neg (by tauto), hne]
        simp
    · rw [if_neg (by tauto), uniformCap, if_neg hopp, zero_mul]
  have hsum : (∑ p : EdgeV G × EdgeV G, uniformCap G c p.1 p.2 * |transferSign G p.1 p.2 T|)
      ≤ c * (((Finset.univ : Finset (EdgeV G × EdgeV G)).filter
        (fun p => IsOppPair G p.1 p.2 ∧ transferSign G p.1 p.2 T ≠ 0)).card : ℝ) := by
    calc (∑ p : EdgeV G × EdgeV G, uniformCap G c p.1 p.2 * |transferSign G p.1 p.2 T|)
        ≤ ∑ p : EdgeV G × EdgeV G,
            (if IsOppPair G p.1 p.2 ∧ transferSign G p.1 p.2 T ≠ 0 then c else 0) :=
          Finset.sum_le_sum (fun p _ => hbound p)
      _ = c * (((Finset.univ : Finset (EdgeV G × EdgeV G)).filter
            (fun p => IsOppPair G p.1 p.2 ∧ transferSign G p.1 p.2 T ≠ 0)).card : ℝ) := by
          rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
            mul_comm]
  have hcard : (((Finset.univ : Finset (EdgeV G × EdgeV G)).filter
      (fun p => IsOppPair G p.1 p.2 ∧ transferSign G p.1 p.2 T ≠ 0)).card : ℝ)
      ≤ 6 * (Fintype.card V : ℝ) := by
    exact_mod_cast card_transferPairs_le G hT
  rw [hswap]
  have h1 := hsum.trans (mul_le_mul_of_nonneg_left hcard hc)
  have h2 : c * (6 * (Fintype.card V : ℝ)) = 4 * ((3 / 2) * (Fintype.card V : ℝ) * c) := by ring
  linarith

/-! ### The opposite-pair graph and its cuts -/

/-- The edges opposite to `e` in some `K₄`: precisely the edges inside the common neighbourhood
of `e`. -/
noncomputable def oppPartners (G : SimpleGraph V) [DecidableRel G.Adj] (e : EdgeV G) :
    Finset (EdgeV G) :=
  Finset.univ.filter (fun e₂ => IsOppPair G e e₂)

/-- The number of *crossing* opposite pairs of a cut. -/
noncomputable def crossSum (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (EdgeV G)) : ℝ :=
  ∑ x ∈ Sᶜ, ∑ y ∈ S, (if IsOppPair G x y then (1 : ℝ) else 0)

/-- The capacity of a cut under the uniform capacity. -/
theorem cut_uniformCap (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) (S : Finset (EdgeV G)) :
    ∑ x ∈ Sᶜ, ∑ y ∈ S, uniformCap G c x y = c * crossSum G S := by
  rw [crossSum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [uniformCap]
  split_ifs <;> ring

/-- Crossing pairs are counted the same from either side. -/
theorem crossSum_compl (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (EdgeV G)) :
    crossSum G S = crossSum G Sᶜ := by
  rw [crossSum, crossSum, compl_compl, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
  by_cases h : IsOppPair G x y
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]

/-- **The minimum-degree bound on a cut** in the opposite-pair graph. -/
theorem crossSum_ge (G : SimpleGraph V) [DecidableRel G.Adj] {D : ℝ}
    (hD : ∀ e : EdgeV G, D ≤ ((oppPartners G e).card : ℝ)) (S : Finset (EdgeV G)) :
    (Sᶜ.card : ℝ) * (D - (Sᶜ.card : ℝ)) ≤ crossSum G S := by
  classical
  have hpt : ∀ x : EdgeV G, D - (Sᶜ.card : ℝ)
      ≤ ∑ y ∈ S, (if IsOppPair G x y then (1 : ℝ) else 0) := by
    intro x
    have hval : ∑ y ∈ S, (if IsOppPair G x y then (1 : ℝ) else 0)
        = ((S.filter (fun y => IsOppPair G x y)).card : ℝ) := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]
    have hcov : oppPartners G x ⊆ (S.filter (fun y => IsOppPair G x y)) ∪ Sᶜ := by
      intro y hy
      rw [oppPartners, Finset.mem_filter] at hy
      by_cases hyS : y ∈ S
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hyS, hy.2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hyS)
    have hcard : (oppPartners G x).card
        ≤ (S.filter (fun y => IsOppPair G x y)).card + Sᶜ.card :=
      le_trans (Finset.card_le_card hcov) (Finset.card_union_le _ _)
    have hcardR : ((oppPartners G x).card : ℝ)
        ≤ ((S.filter (fun y => IsOppPair G x y)).card : ℝ) + (Sᶜ.card : ℝ) := by
      exact_mod_cast hcard
    have := hD x
    rw [hval]
    linarith
  calc (Sᶜ.card : ℝ) * (D - (Sᶜ.card : ℝ))
      = ∑ _x ∈ Sᶜ, (D - (Sᶜ.card : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ crossSum G S := Finset.sum_le_sum (fun x _ => hpt x)

/-! ### Counting the opposite partners -/

/-- **Double counting the edges inside a set of vertices.** -/
theorem two_mul_card_edges_inside (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    ∑ u ∈ A, (A.filter (fun w => G.Adj u w)).card
      = 2 * ((Finset.univ : Finset (EdgeV G)).filter (fun e => e.val ⊆ A)).card := by
  classical
  set S : Finset (EdgeV G) := (Finset.univ : Finset (EdgeV G)).filter (fun e => e.val ⊆ A)
    with hS
  have hstep1 : ∀ u ∈ A, (A.filter (fun w => G.Adj u w)).card
      = (S.filter (fun e => u ∈ e.val)).card := by
    intro u hu
    refine Finset.card_bij (fun w hw => (⟨{u, w}, pair_mem_cliqueFinset_two G
      (by simpa using (Finset.mem_filter.mp hw).2)⟩ : EdgeV G)) ?_ ?_ ?_
    · intro w hw
      rw [Finset.mem_filter] at hw
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hu
      · rw [Finset.mem_singleton] at hx; subst hx; exact hw.1
    · intro a ha b hb hab
      rw [Finset.mem_filter] at ha hb
      simp only [Subtype.mk.injEq] at hab
      have hb' : b ∈ ({u, a} : Finset V) := by rw [hab]; simp
      rcases Finset.mem_insert.mp hb' with h | h
      · exact absurd h (G.ne_of_adj hb.2).symm
      · exact (Finset.mem_singleton.mp h).symm
    · intro e he
      rw [Finset.mem_filter, hS, Finset.mem_filter] at he
      obtain ⟨⟨-, hsub⟩, hue⟩ := he
      obtain ⟨a, b, hab, hadj, hval⟩ := exists_pair_of_edgeV G e
      rw [hval] at hue hsub
      rcases Finset.mem_insert.mp hue with rfl | h
      · exact ⟨b, Finset.mem_filter.mpr ⟨hsub (by simp), hadj⟩,
          Subtype.ext (by simp [hval])⟩
      · rw [Finset.mem_singleton] at h
        subst h
        exact ⟨a, Finset.mem_filter.mpr ⟨hsub (by simp), hadj.symm⟩,
          Subtype.ext (by simp [hval, Finset.pair_comm])⟩
  rw [Finset.sum_congr rfl hstep1]
  have hcount : ∀ u : V, (S.filter (fun e => u ∈ e.val)).card
      = ∑ e ∈ S, if u ∈ e.val then 1 else 0 := by
    intro u; rw [Finset.card_filter]
  rw [Finset.sum_congr rfl (fun u _ => hcount u), Finset.sum_comm]
  have hinner : ∀ e ∈ S, (∑ u ∈ A, if u ∈ e.val then 1 else 0) = 2 := by
    intro e he
    rw [hS, Finset.mem_filter] at he
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr he.2, Finset.sum_const, smul_eq_mul,
      mul_one]
    exact (SimpleGraph.mem_cliqueFinset_iff.mp e.property).card_eq
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Every edge has many opposite partners at high minimum degree.** -/
theorem card_oppPartners_ge (G : SimpleGraph V) [DecidableRel G.Adj] {c : ℝ}
    (hc3 : 3 * c ≤ 1) (hmin : (1 - c) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ))
    (e : EdgeV G) :
    (1 / 2) * ((1 - 2 * c) * (Fintype.card V : ℝ)) * ((1 - 3 * c) * (Fintype.card V : ℝ))
      ≤ ((oppPartners G e).card : ℝ) := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set A : Finset V := commonNbrs G e with hA
  have hApart : oppPartners G e
      = (Finset.univ : Finset (EdgeV G)).filter (fun e₂ => e₂.val ⊆ A) := by
    ext e₂
    simp only [oppPartners, Finset.mem_filter, Finset.mem_univ, true_and, hA, commonNbrs,
      IsOppPair]
    constructor
    · intro h y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x hx => h x hx y hy⟩
    · intro h x hx y hy
      exact (Finset.mem_filter.mp (h hy)).2 x hx
  have hAcard : (1 - 2 * c) * n ≤ (A.card : ℝ) := card_commonNbrs_ge_of_minDegree G hmin e
  have hdeg : ∀ u ∈ A, (1 - 3 * c) * n ≤ ((A.filter (fun w => G.Adj u w)).card : ℝ) := by
    intro u _
    have hun : A.filter (fun w => G.Adj u w) = A ∩ G.neighborFinset u := by
      ext w; simp [Finset.mem_inter]
    have hunion : (A ∪ G.neighborFinset u).card + (A ∩ G.neighborFinset u).card
        = A.card + (G.neighborFinset u).card := Finset.card_union_add_card_inter _ _
    have hle : (A ∪ G.neighborFinset u).card ≤ Fintype.card V := Finset.card_le_univ _
    have hdegu : (G.minDegree : ℝ) ≤ (G.degree u : ℝ) := by
      exact_mod_cast G.minDegree_le_degree u
    have hnb : ((G.neighborFinset u).card : ℝ) = (G.degree u : ℝ) := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
    have hR : ((A ∪ G.neighborFinset u).card : ℝ) + ((A ∩ G.neighborFinset u).card : ℝ)
        = (A.card : ℝ) + ((G.neighborFinset u).card : ℝ) := by exact_mod_cast hunion
    have hleR : ((A ∪ G.neighborFinset u).card : ℝ) ≤ n := by rw [hn]; exact_mod_cast hle
    rw [hun]
    linarith
  have hsum : (A.card : ℝ) * ((1 - 3 * c) * n)
      ≤ 2 * (((Finset.univ : Finset (EdgeV G)).filter (fun e₂ => e₂.val ⊆ A)).card : ℝ) := by
    have h1 : (A.card : ℝ) * ((1 - 3 * c) * n)
        ≤ ∑ u ∈ A, ((A.filter (fun w => G.Adj u w)).card : ℝ) := by
      calc (A.card : ℝ) * ((1 - 3 * c) * n) = ∑ _u ∈ A, ((1 - 3 * c) * n) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hdeg
    have h2 : ∑ u ∈ A, ((A.filter (fun w => G.Adj u w)).card : ℝ)
        = 2 * (((Finset.univ : Finset (EdgeV G)).filter (fun e₂ => e₂.val ⊆ A)).card : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (two_mul_card_edges_inside G A)
    linarith
  rw [hApart]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hnn : (0 : ℝ) ≤ (1 - 3 * c) * n := by nlinarith
  nlinarith [hAcard, hsum]

/-! ### The base weight, framed by the codegrees -/

/-- If every edge lies in at least `L > 0` triangles, the base weight is at most `1/L`. -/
theorem baseWeight_le_of_codegree_ge (G : SimpleGraph V) [DecidableRel G.Adj] {L : ℝ}
    (hL : 0 < L) (hcod : ∀ e : EdgeV G, L ≤ ((trianglesThrough G e).card : ℝ))
    (hm : 0 < Fintype.card (EdgeV G)) : baseWeight G ≤ 1 / L := by
  classical
  have hmR : (0 : ℝ) < (Fintype.card (EdgeV G) : ℝ) := by exact_mod_cast hm
  have hsum : ∑ e : EdgeV G, ((trianglesThrough G e).card : ℝ)
      = 3 * ((triangleHypergraphSub G).card : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (sum_card_trianglesThrough G)
  have hlow : (Fintype.card (EdgeV G) : ℝ) * L ≤ 3 * ((triangleHypergraphSub G).card : ℝ) := by
    rw [← hsum]
    calc (Fintype.card (EdgeV G) : ℝ) * L = ∑ _e : EdgeV G, L := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun e _ => hcod e)
  have hTpos : (0 : ℝ) < 3 * ((triangleHypergraphSub G).card : ℝ) := by nlinarith
  rw [baseWeight, div_le_div_iff₀ hTpos hL]
  linarith

/-- If every edge lies in at most `U` triangles, the base weight is at least `1/U`. -/
theorem baseWeight_ge_of_codegree_le (G : SimpleGraph V) [DecidableRel G.Adj] {U : ℝ}
    (hU : 0 < U) (hcod : ∀ e : EdgeV G, ((trianglesThrough G e).card : ℝ) ≤ U)
    (hT : 0 < (triangleHypergraphSub G).card) : 1 / U ≤ baseWeight G := by
  classical
  have hTR : (0 : ℝ) < ((triangleHypergraphSub G).card : ℝ) := by exact_mod_cast hT
  have hsum : ∑ e : EdgeV G, ((trianglesThrough G e).card : ℝ)
      = 3 * ((triangleHypergraphSub G).card : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (sum_card_trianglesThrough G)
  have hhigh : 3 * ((triangleHypergraphSub G).card : ℝ)
      ≤ (Fintype.card (EdgeV G) : ℝ) * U := by
    rw [← hsum]
    calc ∑ e : EdgeV G, ((trianglesThrough G e).card : ℝ) ≤ ∑ _e : EdgeV G, U :=
          Finset.sum_le_sum (fun e _ => hcod e)
      _ = (Fintype.card (EdgeV G) : ℝ) * U := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [baseWeight, le_div_iff₀ (by positivity)]
  have hUinv : (1 / U) * U = 1 := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hhigh (by positivity : (0:ℝ) ≤ 1 / U)]

/-! ### The arithmetic behind the cut condition -/

/-- **The cut arithmetic.**  Write `K = |S|` and `L = |Sᶜ|` for the two sides of a cut.  The
balance of the deficiencies forces the demand `B` across the cut to satisfy
`(L + (7/8)K)·B ≤ (1/8)·K·L`, while the opposite-pair graph sends at least `K(D-K)` and at least
`L(D-L)` pairs across the cut.  At `D ≥ (91/256)|V|²` and `2(K+L) ≤ |V|²` the uniform capacity
`2/(3|V|²)` then covers the demand. -/
theorem cut_bound_refined {n D K L X B : ℝ} (hn : 0 < n)
    (hD : (91 / 256) * n ^ 2 ≤ D) (hK : 0 ≤ K) (hL : 0 ≤ L) (hpos : 0 < K + L)
    (hKL : 2 * (K + L) ≤ n ^ 2)
    (hdem : (L + (7 / 8) * K) * B ≤ (1 / 8) * K * L)
    (hcrossK : K * (D - K) ≤ X) (hcrossL : L * (D - L) ≤ X) :
    B ≤ (2 / (3 * n ^ 2)) * X := by
  have hne : n ≠ 0 := ne_of_gt hn
  have hn2 : (0 : ℝ) < n ^ 2 := by positivity
  have hcc : (0 : ℝ) < 2 / (3 * n ^ 2) := by positivity
  have hden : (0 : ℝ) < L + (7 / 8) * K := by linarith
  have hkey : (1 / 8) * K * L ≤ (2 / (3 * n ^ 2)) * X * (L + (7 / 8) * K) := by
    have hstep : (3 / 16) * n ^ 2 * K * L ≤ X * (L + (7 / 8) * K) := by
      rcases le_total K L with h | h
      · have h1 : (3 / 16) * n ^ 2 * K * L ≤ K * (D - K) * (L + (7 / 8) * K) := by
          nlinarith [mul_nonneg hK hL, sq_nonneg (K - L), mul_nonneg (mul_nonneg hK hK) hL,
            mul_nonneg hK (sq_nonneg (K - L)), sq_nonneg n, mul_nonneg hK hK]
        have h2 : K * (D - K) * (L + (7 / 8) * K) ≤ X * (L + (7 / 8) * K) :=
          mul_le_mul_of_nonneg_right hcrossK hden.le
        linarith
      · have h1 : (3 / 16) * n ^ 2 * K * L ≤ L * (D - L) * (L + (7 / 8) * K) := by
          nlinarith [mul_nonneg hK hL, sq_nonneg (K - L), mul_nonneg (mul_nonneg hL hL) hK,
            mul_nonneg hL (sq_nonneg (K - L)), sq_nonneg n, mul_nonneg hL hL]
        have h2 : L * (D - L) * (L + (7 / 8) * K) ≤ X * (L + (7 / 8) * K) :=
          mul_le_mul_of_nonneg_right hcrossL hden.le
        linarith
    calc (1 / 8) * K * L = (2 / (3 * n ^ 2)) * ((3 / 16) * n ^ 2 * K * L) := by field_simp; ring
      _ ≤ (2 / (3 * n ^ 2)) * (X * (L + (7 / 8) * K)) :=
          mul_le_mul_of_nonneg_left hstep hcc.le
      _ = (2 / (3 * n ^ 2)) * X * (L + (7 / 8) * K) := by ring
  have hcomm : (L + (7 / 8) * K) * ((2 / (3 * n ^ 2)) * X)
      = (2 / (3 * n ^ 2)) * X * (L + (7 / 8) * K) := by ring
  have hfin : (L + (7 / 8) * K) * B ≤ (L + (7 / 8) * K) * ((2 / (3 * n ^ 2)) * X) := by
    rw [hcomm]; linarith
  exact le_of_mul_le_mul_left hfin hden

/-! ### The certificate at minimum degree `(15/16)|V|` -/

/-- **The uniform transfer certificate.**  Every graph with `15|V| ≤ 16 δ(G)` and at least one
edge admits the uniform capacity `2/(3|V|²)` on the opposite pairs of its `K₄`s as a Dross
transfer certificate at its balanced base weight. -/
theorem isDrossTransferCert_uniform_of_dense (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 15 * Fintype.card V ≤ 16 * G.minDegree) (e0 : EdgeV G) :
    IsDrossTransferCert G (baseWeight G)
      (uniformCap G (2 / (3 * (Fintype.card V : ℝ) ^ 2))) := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hv : V := (nonempty_of_edgeV G e0).some
  have hV16 : 16 ≤ Fintype.card V := by
    have h1 : G.minDegree ≤ G.degree hv := G.minDegree_le_degree hv
    have h2 : G.degree hv < Fintype.card V := G.degree_lt_card_verts hv
    omega
  have hn16 : (16 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hV16
  have hn0 : (0 : ℝ) < n := by linarith
  have hne : n ≠ 0 := ne_of_gt hn0
  have hdense9 : 9 * Fintype.card V ≤ 10 * G.minDegree := by omega
  have hmin : (1 - (1 / 16 : ℝ)) * n ≤ (G.minDegree : ℝ) := by
    have : (15 : ℝ) * n ≤ 16 * (G.minDegree : ℝ) := by rw [hn]; exact_mod_cast hdense
    linarith
  have hcodeq : ∀ e : EdgeV G,
      ((trianglesThrough G e).card : ℝ) = ((commonNbrs G e).card : ℝ) := fun e => by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (card_trianglesThrough_eq_commonNbrs G e)
  have hcodlow : ∀ e : EdgeV G, (7 / 8 : ℝ) * n ≤ ((trianglesThrough G e).card : ℝ) := by
    intro e
    have h := card_commonNbrs_ge_of_minDegree G hmin e
    rw [hcodeq e]
    linarith
  have hcodhigh : ∀ e : EdgeV G, ((trianglesThrough G e).card : ℝ) ≤ n := by
    intro e
    rw [hcodeq e, hn]
    exact_mod_cast Finset.card_le_univ (commonNbrs G e)
  have hmpos : 0 < Fintype.card (EdgeV G) := Fintype.card_pos_iff.mpr ⟨e0⟩
  have hTpos : 0 < (triangleHypergraphSub G).card :=
    triangleHypergraphSub_nonempty_of_dense G hdense9 e0
  have hw0low : 1 / n ≤ baseWeight G := baseWeight_ge_of_codegree_le G hn0 hcodhigh hTpos
  have hw0high : baseWeight G ≤ 1 / ((7 / 8 : ℝ) * n) :=
    baseWeight_le_of_codegree_ge G (by linarith) hcodlow hmpos
  have hw0nn : 0 ≤ baseWeight G := le_trans (le_of_lt (div_pos one_pos hn0)) hw0low
  -- the two pointwise deficiency bounds, in terms of `x = w₀|V|`
  have hbhigh : ∀ e : EdgeV G,
      1 - baseWeight G * ((trianglesThrough G e).card : ℝ)
        ≤ 1 - (7 / 8 : ℝ) * (baseWeight G * n) := by
    intro e
    have h1 := hcodlow e
    have h2 := mul_le_mul_of_nonneg_left h1 hw0nn
    linarith
  have hblow : ∀ e : EdgeV G,
      -(baseWeight G * n - 1) ≤ 1 - baseWeight G * ((trianglesThrough G e).card : ℝ) := by
    intro e
    have h1 := hcodhigh e
    have h2 := mul_le_mul_of_nonneg_left h1 hw0nn
    linarith
  -- the opposite-pair graph has huge minimum degree
  have hD : ∀ e : EdgeV G, (91 / 256 : ℝ) * n ^ 2 ≤ ((oppPartners G e).card : ℝ) := by
    intro e
    have h := card_oppPartners_ge G (c := 1 / 16) (by norm_num) hmin e
    have heq : (1 / 2 : ℝ) * ((1 - 2 * (1 / 16 : ℝ)) * n) * ((1 - 3 * (1 / 16 : ℝ)) * n)
        = (91 / 256 : ℝ) * n ^ 2 := by ring
    rw [heq] at h
    exact h
  -- there are at most `|V|²/2` edges
  have hm2 : 2 * (Fintype.card (EdgeV G) : ℝ) ≤ n ^ 2 := by
    rw [two_mul_card_edgeV G]
    calc ∑ v : V, (G.degree v : ℝ) ≤ ∑ _v : V, n := by
          refine Finset.sum_le_sum (fun v _ => ?_)
          have := (G.degree_lt_card_verts v).le
          rw [hn]; exact_mod_cast this
      _ = n ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]; ring
  have hccnn : (0 : ℝ) ≤ 2 / (3 * n ^ 2) := by positivity
  refine ⟨fun e₁ e₂ => ?_, fun e₁ e₂ => ?_, fun e₁ e₂ h => ?_, fun T hT => ?_, fun S => ?_⟩
  · rw [uniformCap]; split_ifs
    · exact hccnn
    · exact le_rfl
  · rw [uniformCap, uniformCap]
    by_cases hopp : IsOppPair G e₁ e₂
    · rw [if_pos hopp, if_pos hopp.symm]
    · rw [if_neg hopp, if_neg (fun hc => hopp hc.symm)]
  · by_contra hopp
    rw [uniformCap, if_neg hopp] at h
    exact h rfl
  · refine le_trans (throughput_uniformCap_le G hccnn hT) ?_
    have heq : (3 / 2 : ℝ) * n * (2 / (3 * n ^ 2)) = 1 / n := by field_simp
    rw [heq]
    exact hw0low
  · rw [cut_uniformCap]
    have hbal : (∑ e ∈ S, (1 - baseWeight G * ((trianglesThrough G e).card : ℝ)))
        + ∑ e ∈ Sᶜ, (1 - baseWeight G * ((trianglesThrough G e).card : ℝ)) = 0 := by
      rw [Finset.sum_add_sum_compl]
      exact sum_deficiency_baseWeight G hTpos
    have hcards : (S.card : ℝ) + (Sᶜ.card : ℝ) = (Fintype.card (EdgeV G) : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (Finset.card_add_card_compl S)
    have hS0 : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hSc0 : (0 : ℝ) ≤ (Sᶜ.card : ℝ) := Nat.cast_nonneg _
    have hmposR : (0 : ℝ) < (Fintype.card (EdgeV G) : ℝ) := by exact_mod_cast hmpos
    have hcrossL : (Sᶜ.card : ℝ) * ((91 / 256 : ℝ) * n ^ 2 - (Sᶜ.card : ℝ))
        ≤ crossSum G S := crossSum_ge G hD S
    have hcrossK : (S.card : ℝ) * ((91 / 256 : ℝ) * n ^ 2 - (S.card : ℝ))
        ≤ crossSum G S := by
      have h := crossSum_ge G hD Sᶜ
      rw [compl_compl, ← crossSum_compl] at h
      exact h
    -- the two demand bounds
    have hB1 : (∑ e ∈ S, (1 - baseWeight G * ((trianglesThrough G e).card : ℝ)))
        ≤ (S.card : ℝ) * (1 - (7 / 8 : ℝ) * (baseWeight G * n)) := by
      calc (∑ e ∈ S, (1 - baseWeight G * ((trianglesThrough G e).card : ℝ)))
          ≤ ∑ _e ∈ S, (1 - (7 / 8 : ℝ) * (baseWeight G * n)) :=
            Finset.sum_le_sum (fun e _ => hbhigh e)
        _ = (S.card : ℝ) * (1 - (7 / 8 : ℝ) * (baseWeight G * n)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hB2 : (∑ e ∈ S, (1 - baseWeight G * ((trianglesThrough G e).card : ℝ)))
        ≤ (Sᶜ.card : ℝ) * (baseWeight G * n - 1) := by
      have hlow : -((Sᶜ.card : ℝ) * (baseWeight G * n - 1))
          ≤ ∑ e ∈ Sᶜ, (1 - baseWeight G * ((trianglesThrough G e).card : ℝ)) := by
        calc -((Sᶜ.card : ℝ) * (baseWeight G * n - 1))
            = ∑ _e ∈ Sᶜ, -(baseWeight G * n - 1) := by
              rw [Finset.sum_const, nsmul_eq_mul]; ring
          _ ≤ _ := Finset.sum_le_sum (fun e _ => hblow e)
      linarith
    have hdem : ((Sᶜ.card : ℝ) + (7 / 8 : ℝ) * (S.card : ℝ))
        * (∑ e ∈ S, (1 - baseWeight G * ((trianglesThrough G e).card : ℝ)))
        ≤ (1 / 8 : ℝ) * (S.card : ℝ) * (Sᶜ.card : ℝ) := by
      have e1 := mul_le_mul_of_nonneg_left hB1 hSc0
      have e2 := mul_le_mul_of_nonneg_left hB2 (by linarith : (0 : ℝ) ≤ (7 / 8 : ℝ) * (S.card : ℝ))
      linarith only [e1, e2]
    refine cut_bound_refined hn0 le_rfl hS0 hSc0 (by linarith) (by linarith) hdem
      hcrossK hcrossL

/-- **The main theorem of this file.**  Every graph with `15|V| ≤ 16 δ(G)` has an exact
fractional triangle decomposition all of whose weights are at most `3/|V|`. -/
theorem hasSpreadFracTriangleDecomp_of_dense (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 15 * Fintype.card V ≤ 16 * G.minDegree) :
    HasSpreadFracTriangleDecomp G 3 := by
  classical
  by_cases hedge : Nonempty (EdgeV G)
  · obtain ⟨e0⟩ := hedge
    have hv : V := (nonempty_of_edgeV G e0).some
    have hV16 : 16 ≤ Fintype.card V := by
      have h1 : G.minDegree ≤ G.degree hv := G.minDegree_le_degree hv
      have h2 : G.degree hv < Fintype.card V := G.degree_lt_card_verts hv
      omega
    have hn16 : (16 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV16
    have hn0 : (0 : ℝ) < (Fintype.card V : ℝ) := by linarith
    have hdense9 : 9 * Fintype.card V ≤ 10 * G.minDegree := by omega
    have hTpos : 0 < (triangleHypergraphSub G).card :=
      triangleHypergraphSub_nonempty_of_dense G hdense9 e0
    obtain ⟨w, hw, hwb⟩ := exists_spread_decomp_of_cert G (sum_deficiency_baseWeight G hTpos)
      (isDrossTransferCert_uniform_of_dense G hdense e0)
    refine ⟨w, hw, fun T hT => le_trans (hwb T hT) ?_⟩
    have hmin : (1 - (1 / 16 : ℝ)) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) := by
      have : (15 : ℝ) * (Fintype.card V : ℝ) ≤ 16 * (G.minDegree : ℝ) := by exact_mod_cast hdense
      linarith
    have hcodlow : ∀ e : EdgeV G,
        (7 / 8 : ℝ) * (Fintype.card V : ℝ) ≤ ((trianglesThrough G e).card : ℝ) := by
      intro e
      have h := card_commonNbrs_ge_of_minDegree G hmin e
      rw [show ((trianglesThrough G e).card : ℝ) = ((commonNbrs G e).card : ℝ) from by
        exact_mod_cast congrArg (fun k : ℕ => (k : ℝ))
          (card_trianglesThrough_eq_commonNbrs G e)]
      linarith
    have hmpos : 0 < Fintype.card (EdgeV G) := Fintype.card_pos_iff.mpr ⟨e0⟩
    have hw0high : baseWeight G ≤ 1 / ((7 / 8 : ℝ) * (Fintype.card V : ℝ)) :=
      baseWeight_le_of_codegree_ge G (by linarith) hcodlow hmpos
    have hne : (Fintype.card V : ℝ) ≠ 0 := ne_of_gt hn0
    have hpos : (0 : ℝ) ≤ (5 / 7 : ℝ) / (Fintype.card V : ℝ) := by positivity
    have heq : 3 / (Fintype.card V : ℝ) - 2 * (1 / ((7 / 8 : ℝ) * (Fintype.card V : ℝ)))
        = (5 / 7 : ℝ) / (Fintype.card V : ℝ) := by field_simp; ring
    linarith
  · refine ⟨fun _ => 0, ⟨fun _ _ => le_rfl, fun e => absurd ⟨e⟩ hedge⟩, fun T hT => ?_⟩
    obtain ⟨e, -⟩ := exists_edge_of_mem_triangleHypergraphSub G hT
    exact absurd ⟨e⟩ hedge

/-- **The main theorem, in minimum-degree form.**  Every graph with `δ(G) ≥ (1 - 1/16)|V|` has an
exact fractional triangle decomposition all of whose weights are at most `3/|V|`. -/
theorem hasSpreadFracTriangleDecomp_of_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : (1 - 1 / 16 : ℝ) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ)) :
    HasSpreadFracTriangleDecomp G 3 := by
  refine hasSpreadFracTriangleDecomp_of_dense G ?_
  have h : (15 : ℝ) * (Fintype.card V : ℝ) ≤ 16 * (G.minDegree : ℝ) := by linarith
  exact_mod_cast h

end Nibble
