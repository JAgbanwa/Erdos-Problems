import PaperIV.MarkedQuotaPairing
import PaperIV.JointTypedNibbleGate
import PaperIV.MixedRoundingAdapter
import MixedRounding.Producer

/-!
# RC01: the literal mixed physical packing with the `2/5` objective

This is the end of the chain.  Starting from the **single-rank** residue
`PaperIV.TwoQuotaNibble.PartitionQuotaNibbleAt 6`, and from the *actual induced fractional
weights* of a `MixedRounding.FracPacking` — not from unweighted support cardinalities — one
nibble run on the joint hypergraph `jointSupports G` produces a literal `Packing G` whose gain
dominates the mixed fractional objective

```text
2 * triangleMass x + 5 * fourCliqueMass x
```

up to the factor `1 - β`.

The pieces:

* the triangle pairing (`PaperIV.TrianglePairingNibble.jointTwoQuota_threshold`) supplies the
  two quotas;
* `PaperIV.JointTypedQuota.typed_gain_of_total_and_four_quota` turns the two quotas into the
  typed objective — this is where the `2 = 2`, `5 = 2 + 3` bookkeeping happens;
* `PaperIV.JointTypedNibbleGate.packing_of_joint_matching_counted` turns the joint matching
  into a physical packing with gain `2·#triangles + 5·#K₄`.

The structural side condition of the pairing is discharged here, once and for all:
`k4Supports_disjoint_pairFam` — the six edges of a `K₄` are never the disjoint union of the
edge sets of two triangles, because two triangles inside a `K₄` always share an edge.
-/

namespace PaperIV.JointTwoQuotaPhysical

open Finset
open PaperIV.FarRounding
open PaperIV.NibblePort
open PaperIV.JointTypedNibbleGate
open PaperIV.TrianglePairingDefs

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. The structural side condition -/

/-- If the edge set of a triple is contained in the edge set of an item, the triple's vertices
are vertices of the item. -/
theorem subset_of_pairs_subset {T K : Finset V} (hT : 2 ≤ T.card)
    (h : pairs T ⊆ pairs K) : T ⊆ K := by
  classical
  intro v hv
  have hne : (T.erase v).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hv]; omega
  obtain ⟨u, hu⟩ := hne
  obtain ⟨huv, huT⟩ := Finset.mem_erase.1 hu
  have hmem : s(v, u) ∈ pairs T := by
    rw [mk_mem_pairs]
    exact ⟨hv, huT, fun hc => huv hc.symm⟩
  have := h hmem
  rw [mk_mem_pairs] at this
  exact this.1

/-- **The six edges of a `K₄` are not the disjoint union of two triangles.**  Two triangles
whose vertices lie in a `4`-set share at least two vertices, hence an edge. -/
theorem k4Supports_disjoint_pairFam :
    Disjoint (k4Supports G) (pairFam (k3Supports G)) := by
  classical
  rw [Finset.disjoint_left]
  intro S hS hS'
  obtain ⟨K, hK, hK4, rfl⟩ := mem_k4Supports.1 hS
  obtain ⟨q, hq, hqU⟩ := mem_pairFam.1 hS'
  obtain ⟨hq1, hq2, hqd⟩ := mem_pairDom.1 hq
  obtain ⟨T, hT, hT3, hTq⟩ := mem_k3Supports.1 hq1
  obtain ⟨T', hT', hT'3, hT'q⟩ := mem_k3Supports.1 hq2
  -- both triples sit inside `K`
  have hsub1 : pairs T ⊆ pairs K := by
    rw [hTq, ← hqU]
    exact Finset.subset_union_left
  have hsub2 : pairs T' ⊆ pairs K := by
    rw [hT'q, ← hqU]
    exact Finset.subset_union_right
  have hTK : T ⊆ K := subset_of_pairs_subset (by omega) hsub1
  have hT'K : T' ⊆ K := subset_of_pairs_subset (by omega) hsub2
  -- hence they share two vertices
  have hunion : (T ∪ T').card ≤ 4 := by
    rw [← hK4]
    exact Finset.card_le_card (Finset.union_subset hTK hT'K)
  have hinter : 2 ≤ (T ∩ T').card := by
    have := Finset.card_union_add_card_inter T T'
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < (T ∩ T').card)
  have haT := Finset.mem_inter.1 ha
  have hbT := Finset.mem_inter.1 hb
  have hmem1 : s(a, b) ∈ q.1 := by
    rw [← hTq, mk_mem_pairs]
    exact ⟨haT.1, hbT.1, hab⟩
  have hmem2 : s(a, b) ∈ q.2 := by
    rw [← hT'q, mk_mem_pairs]
    exact ⟨haT.2, hbT.2, hab⟩
  exact (Finset.disjoint_left.1 hqd) hmem1 hmem2

/-! ## 2. The joint hypergraph and the induced fractional weights -/

/-- The joint hypergraph of `PaperIV` is the support hypergraph of `MixedRounding`. -/
theorem jointSupports_eq_supports : jointSupports G = MixedRounding.supports G := by
  classical
  ext S
  rw [mem_jointSupports, MixedRounding.mem_supports]
  constructor
  · rintro ⟨K, hK, rfl⟩
    exact ⟨K, (MixedRoundingAdapter.isItem_iff K).2 hK, rfl⟩
  · rintro ⟨K, hK, rfl⟩
    exact ⟨K, (MixedRoundingAdapter.isItem_iff K).1 hK, rfl⟩

theorem k3Supports_eq_supportsOfCard : k3Supports G = MixedRounding.supportsOfCard G 3 := by
  classical
  ext S
  rw [mem_k3Supports]
  simp only [MixedRounding.supportsOfCard, Finset.mem_image, Finset.mem_filter,
    MixedRounding.mem_items]
  constructor
  · rintro ⟨K, hK, h3, rfl⟩
    exact ⟨K, ⟨(MixedRoundingAdapter.isItem_iff K).2 hK, h3⟩, rfl⟩
  · rintro ⟨K, ⟨hK, h3⟩, rfl⟩
    exact ⟨K, (MixedRoundingAdapter.isItem_iff K).1 hK, h3, rfl⟩

theorem k4Supports_eq_supportsOfCard : k4Supports G = MixedRounding.supportsOfCard G 4 := by
  classical
  ext S
  rw [mem_k4Supports]
  simp only [MixedRounding.supportsOfCard, Finset.mem_image, Finset.mem_filter,
    MixedRounding.mem_items]
  constructor
  · rintro ⟨K, hK, h4, rfl⟩
    exact ⟨K, ⟨(MixedRoundingAdapter.isItem_iff K).2 hK, h4⟩, rfl⟩
  · rintro ⟨K, ⟨hK, h4⟩, rfl⟩
    exact ⟨K, (MixedRoundingAdapter.isItem_iff K).1 hK, h4, rfl⟩

/-- The `K₃` and `K₄` support families are disjoint: `3 ≠ 6`. -/
theorem k3Supports_disjoint_k4Supports : Disjoint (k3Supports G) (k4Supports G) := by
  rw [Finset.disjoint_left]
  intro S hS hS'
  have h3 := k3Supports_uniform S hS
  have h6 := k4Supports_uniform S hS'
  omega

/-- Sums over the joint hypergraph split into the two ranks. -/
theorem joint_sum_split (x : MixedRounding.FracPacking G) (p : Finset (Sym2 V) → Prop)
    [DecidablePred p] :
    ∑ S ∈ (jointSupports G).filter p, MixedRounding.inducedWeight x S
      = (∑ S ∈ (k3Supports G).filter p, MixedRounding.inducedWeight x S)
        + ∑ S ∈ (k4Supports G).filter p, MixedRounding.inducedWeight x S := by
  classical
  have hsplit : (jointSupports G).filter p
      = (k3Supports G).filter p ∪ (k4Supports G).filter p := by
    rw [jointSupports, Finset.filter_union]
  rw [hsplit, Finset.sum_union (Finset.disjoint_filter_filter k3Supports_disjoint_k4Supports)]

/-- The support hypergraph load of a resource, in terms of the LP. -/
theorem supports_load_eq (x : MixedRounding.FracPacking G) (e : Sym2 V) :
    ∑ S ∈ (MixedRounding.supports G).filter (fun S => e ∈ S), MixedRounding.inducedWeight x S
      = ∑ K ∈ (MixedRounding.items G).filter (fun K => e ∈ MixedRounding.pairs K),
          ((x.weight K : ℚ) : ℝ) := by
  classical
  have hset : (MixedRounding.supports G).filter (fun S => e ∈ S)
      = ((MixedRounding.items G).filter (fun K => e ∈ MixedRounding.pairs K)).image
          MixedRounding.pairs := by
    ext S
    simp only [MixedRounding.supports, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨K, hK, rfl⟩, heS⟩
      exact ⟨K, ⟨hK, heS⟩, rfl⟩
    · rintro ⟨K, ⟨hK, heK⟩, rfl⟩
      exact ⟨⟨K, hK, rfl⟩, heK⟩
  rw [hset]
  refine (Finset.sum_image ?_).trans ?_
  · intro K hK L hL h
    simp only [Finset.mem_coe, Finset.mem_filter] at hK hL
    exact MixedRounding.pairs_injOn_items (MixedRounding.mem_items.1 hK.1)
      (MixedRounding.mem_items.1 hL.1) h
  · refine Finset.sum_congr rfl fun K hK => ?_
    rw [Finset.mem_filter] at hK
    exact MixedRounding.inducedWeight_pairs x (MixedRounding.mem_items.1 hK.1)

/-- **The capacity constraint of the LP is the load hypothesis of the nibble**, for the joint
hypergraph carrying both ranks at once. -/
theorem joint_load_le_one (x : MixedRounding.FracPacking G) (e : Sym2 V) :
    ∑ S ∈ (MixedRounding.supports G).filter (fun S => e ∈ S), MixedRounding.inducedWeight x S
      ≤ 1 := by
  classical
  by_cases he : e ∈ G.edgeFinset
  · rw [supports_load_eq]
    have hcap : ∑ K ∈ (MixedRounding.items G).filter (fun K => e ∈ MixedRounding.pairs K),
        x.weight K ≤ (1 : ℚ) := by
      rw [Finset.sum_filter]
      exact x.capacity e he
    have hcast : ∑ K ∈ (MixedRounding.items G).filter (fun K => e ∈ MixedRounding.pairs K),
        ((x.weight K : ℚ) : ℝ)
        = ((∑ K ∈ (MixedRounding.items G).filter (fun K => e ∈ MixedRounding.pairs K),
            x.weight K : ℚ) : ℝ) := by push_cast; ring
    rw [hcast]
    exact_mod_cast hcap
  · rw [supports_load_eq]
    have hzero : ∀ K ∈ (MixedRounding.items G).filter (fun K => e ∈ MixedRounding.pairs K),
        ((x.weight K : ℚ) : ℝ) = 0 := by
      intro K hK
      rw [Finset.mem_filter] at hK
      exact absurd (MixedRounding.pairs_subset_edgeFinset
        (MixedRounding.mem_items.1 hK.1) hK.2) he
    rw [Finset.sum_congr rfl hzero, Finset.sum_const, smul_zero]
    norm_num

/-! ## 3. The masses -/

/-- The fractional mass carried by triangles. -/
noncomputable def triangleMass (x : MixedRounding.FracPacking G) : ℝ :=
  ∑ K ∈ (MixedRounding.items G).filter (fun K => K.card = 3), ((x.weight K : ℚ) : ℝ)

/-- The fractional mass carried by `K₄`s. -/
noncomputable def fourCliqueMass (x : MixedRounding.FracPacking G) : ℝ :=
  ∑ K ∈ (MixedRounding.items G).filter (fun K => K.card = 4), ((x.weight K : ℚ) : ℝ)

theorem sum_k3Supports_eq (x : MixedRounding.FracPacking G) :
    ∑ S ∈ k3Supports G, MixedRounding.inducedWeight x S = triangleMass x := by
  rw [k3Supports_eq_supportsOfCard, MixedRounding.mass_eq, triangleMass]

theorem sum_k4Supports_eq (x : MixedRounding.FracPacking G) :
    ∑ S ∈ k4Supports G, MixedRounding.inducedWeight x S = fourCliqueMass x := by
  rw [k4Supports_eq_supportsOfCard, MixedRounding.mass_eq, fourCliqueMass]

/-! ## 4. The mixed physical packing -/

set_option maxHeartbeats 4000000 in
/-- **RC01's mixed physical selector from the proved marked-quota gate.**

The only remaining instance hypotheses are the ordinary near-perfect load,
small exceptional set and small weighted codegree conditions.  The output is a
literal mixed packing, and the additive loss is explicit. -/
theorem mixed_physical_packing_of_markedQuota (β ε : ℝ)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (x : MixedRounding.FracPacking G) (Exc : Finset (Sym2 V)),
        (∀ e : Sym2 V, e ∉ Exc → 1 - γ ≤
          ∑ S ∈ (jointSupports G).filter (fun S => e ∈ S), MixedRounding.inducedWeight x S) →
        (Exc.card : ℝ) ≤ η * (Fintype.card (Sym2 V) : ℝ) →
        (∀ e f : Sym2 V, e ≠ f →
          ∑ S ∈ (jointSupports G).filter (fun S => e ∈ S ∧ f ∈ S),
            MixedRounding.inducedWeight x S ≤ γ) →
        C ≤ triangleMass x →
        ∃ P : MixedRounding.Packing G,
          (1 - β) * (2 * triangleMass x + 5 * fourCliqueMass x - 6)
              - 5 * (ε * (Fintype.card (Sym2 V) : ℝ))
            ≤ (P.gain : ℝ) := by
  classical
  obtain ⟨γ, hγ, η, hη, C, hC, hmain⟩ :=
    MarkedQuotaPairing.paired_typed_gain β ε hβ hβ1 hε
  refine ⟨γ, hγ, η, hη, C, hC, ?_⟩
  intro V _ _ G _ x Exc hlow hExc hcod hmass
  set w : Finset (Sym2 V) → ℝ := MixedRounding.inducedWeight x with hw_def
  have hwnn : ∀ T, 0 ≤ w T := fun T => MixedRounding.inducedWeight_nonneg x T
  have hload : ∀ e : Sym2 V,
      (∑ S ∈ (k3Supports G).filter (fun S => e ∈ S), w S)
        + (∑ S ∈ (k4Supports G).filter (fun S => e ∈ S), w S) ≤ 1 := by
    intro e
    rw [← joint_sum_split x (fun S => e ∈ S), jointSupports_eq_supports]
    exact joint_load_le_one x e
  have hlow' : ∀ e : Sym2 V, e ∉ Exc → 1 - γ ≤
      (∑ S ∈ (k3Supports G).filter (fun S => e ∈ S), w S)
        + (∑ S ∈ (k4Supports G).filter (fun S => e ∈ S), w S) := by
    intro e he
    rw [← joint_sum_split x (fun S => e ∈ S)]
    exact hlow e he
  have hcod' : ∀ e f : Sym2 V, e ≠ f →
      (∑ S ∈ (k3Supports G).filter (fun S => e ∈ S ∧ f ∈ S), w S)
        + (∑ S ∈ (k4Supports G).filter (fun S => e ∈ S ∧ f ∈ S), w S) ≤ γ := by
    intro e f hef
    rw [← joint_sum_split x (fun S => e ∈ S ∧ f ∈ S)]
    exact hcod e f hef
  have hmass' : C ≤ ∑ S ∈ k3Supports G, w S := by
    rw [sum_k3Supports_eq]
    exact hmass
  obtain ⟨Mstar, hMstar, hgain⟩ :=
    hmain (k3Supports G) (k4Supports G) w Exc
      k3Supports_uniform k4Supports_uniform k4Supports_disjoint_pairFam
      hwnn hload hlow' hExc hcod' hmass'
  set M := TrianglePairingSplit.unfoldMatching (k3Supports G) (k4Supports G) Mstar with hMdef
  have hMmatch : NibblePort.Hypergraph.IsMatching (k3Supports G ∪ k4Supports G) M := by
    rw [hMdef]
    exact TrianglePairingSplit.unfold_isMatching k3Supports_uniform hMstar
  have hMjoint : NibblePort.Hypergraph.IsMatching (jointSupports G) M := by
    rw [jointSupports]
    exact hMmatch
  obtain ⟨P, hP⟩ := packing_of_joint_matching_counted M hMjoint
  have hsix : M.filter (fun S => S.card = 6) = M.filter (fun S => S ∈ k4Supports G) := by
    apply Finset.filter_congr
    intro S hS
    constructor
    · intro h6
      rcases Finset.mem_union.1 (hMjoint.subset hS) with h | h
      · have h3 := k3Supports_uniform S h
        omega
      · exact h
    · intro h
      exact k4Supports_uniform S h
  have hfour : M.filter (fun S => S ∈ k4Supports G)
      = Mstar.filter (fun S => S ∈ k4Supports G) := by
    rw [hMdef]
    exact TrianglePairingSplit.unfold_filter_four
      k3Supports_uniform k4Supports_uniform hMstar
  have hcardsplit : (M.filter (fun S => S.card = 3)).card
      + (M.filter (fun S => S.card = 6)).card = M.card := by
    have hcompl : M.filter (fun S => ¬ S.card = 3) = M.filter (fun S => S.card = 6) := by
      apply Finset.filter_congr
      intro S hS
      rcases jointSupports_card (hMjoint.subset hS) with h | h <;> simp [h]
    rw [← hcompl]
    exact Finset.card_filter_add_card_filter_not (s := M) (p := fun S => S.card = 3)
  have hMcard : M.card
      = (Mstar.filter (fun S => S ∈ k4Supports G)).card
        + 2 * (Mstar.filter (fun S => S ∉ k4Supports G)).card := by
    rw [hMdef]
    exact TrianglePairingSplit.unfold_card
      k3Supports_uniform k4Supports_uniform hMstar
  have hthree : (M.filter (fun S => S.card = 3)).card
      = 2 * (Mstar.filter (fun S => S ∉ k4Supports G)).card := by
    rw [hsix, hfour] at hcardsplit
    omega
  refine ⟨MixedRoundingAdapter.ofFarPacking P, ?_⟩
  rw [MixedRoundingAdapter.gain_ofFarPacking, hP]
  rw [hthree, hsix, hfour]
  rw [sum_k3Supports_eq, sum_k4Supports_eq] at hgain
  norm_num at hgain ⊢
  convert hgain using 1 <;> ring

set_option maxHeartbeats 4000000 in
/-- **RC01's mixed physical selector from the slack marked-quota gate.**

The near-perfect load hypothesis and the exceptional set are gone: the upper
load is automatic (`joint_load_le_one`, i.e. the LP capacity constraint), so
the only remaining instance hypotheses are the weighted codegree bound and the
constant lower bound on the triangle mass.  The additive loss is explicit and
now also carries the slack constant `5 * D`. -/
theorem mixed_physical_packing_of_slackMarkedQuota (β ε : ℝ)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (x : MixedRounding.FracPacking G),
        (∀ e f : Sym2 V, e ≠ f →
          ∑ S ∈ (jointSupports G).filter (fun S => e ∈ S ∧ f ∈ S),
            MixedRounding.inducedWeight x S ≤ γ) →
        C ≤ triangleMass x →
        ∃ P : MixedRounding.Packing G,
          (1 - β) * (2 * triangleMass x + 5 * fourCliqueMass x - 6)
              - 5 * (ε * (Fintype.card (Sym2 V) : ℝ)) - 5 * D
            ≤ (P.gain : ℝ) := by
  classical
  obtain ⟨γ, hγ, C, hC, D, hD, hmain⟩ :=
    MarkedQuotaPairing.paired_typed_gain_slack β ε hβ hβ1 hε
  refine ⟨γ, hγ, C, hC, D, hD, ?_⟩
  intro V _ _ G _ x hcod hmass
  set w : Finset (Sym2 V) → ℝ := MixedRounding.inducedWeight x with hw_def
  have hwnn : ∀ T, 0 ≤ w T := fun T => MixedRounding.inducedWeight_nonneg x T
  have hload : ∀ e : Sym2 V,
      (∑ S ∈ (k3Supports G).filter (fun S => e ∈ S), w S)
        + (∑ S ∈ (k4Supports G).filter (fun S => e ∈ S), w S) ≤ 1 := by
    intro e
    rw [← joint_sum_split x (fun S => e ∈ S), jointSupports_eq_supports]
    exact joint_load_le_one x e
  have hcod' : ∀ e f : Sym2 V, e ≠ f →
      (∑ S ∈ (k3Supports G).filter (fun S => e ∈ S ∧ f ∈ S), w S)
        + (∑ S ∈ (k4Supports G).filter (fun S => e ∈ S ∧ f ∈ S), w S) ≤ γ := by
    intro e f hef
    rw [← joint_sum_split x (fun S => e ∈ S ∧ f ∈ S)]
    exact hcod e f hef
  have hmass' : C ≤ ∑ S ∈ k3Supports G, w S := by
    rw [sum_k3Supports_eq]
    exact hmass
  obtain ⟨Mstar, hMstar, hgain⟩ :=
    hmain (k3Supports G) (k4Supports G) w
      k3Supports_uniform k4Supports_uniform k4Supports_disjoint_pairFam
      hwnn hload hcod' hmass'
  set M := TrianglePairingSplit.unfoldMatching (k3Supports G) (k4Supports G) Mstar with hMdef
  have hMmatch : NibblePort.Hypergraph.IsMatching (k3Supports G ∪ k4Supports G) M := by
    rw [hMdef]
    exact TrianglePairingSplit.unfold_isMatching k3Supports_uniform hMstar
  have hMjoint : NibblePort.Hypergraph.IsMatching (jointSupports G) M := by
    rw [jointSupports]
    exact hMmatch
  obtain ⟨P, hP⟩ := packing_of_joint_matching_counted M hMjoint
  have hsix : M.filter (fun S => S.card = 6) = M.filter (fun S => S ∈ k4Supports G) := by
    apply Finset.filter_congr
    intro S hS
    constructor
    · intro h6
      rcases Finset.mem_union.1 (hMjoint.subset hS) with h | h
      · have h3 := k3Supports_uniform S h
        omega
      · exact h
    · intro h
      exact k4Supports_uniform S h
  have hfour : M.filter (fun S => S ∈ k4Supports G)
      = Mstar.filter (fun S => S ∈ k4Supports G) := by
    rw [hMdef]
    exact TrianglePairingSplit.unfold_filter_four
      k3Supports_uniform k4Supports_uniform hMstar
  have hcardsplit : (M.filter (fun S => S.card = 3)).card
      + (M.filter (fun S => S.card = 6)).card = M.card := by
    have hcompl : M.filter (fun S => ¬ S.card = 3) = M.filter (fun S => S.card = 6) := by
      apply Finset.filter_congr
      intro S hS
      rcases jointSupports_card (hMjoint.subset hS) with h | h <;> simp [h]
    rw [← hcompl]
    exact Finset.card_filter_add_card_filter_not (s := M) (p := fun S => S.card = 3)
  have hMcard : M.card
      = (Mstar.filter (fun S => S ∈ k4Supports G)).card
        + 2 * (Mstar.filter (fun S => S ∉ k4Supports G)).card := by
    rw [hMdef]
    exact TrianglePairingSplit.unfold_card
      k3Supports_uniform k4Supports_uniform hMstar
  have hthree : (M.filter (fun S => S.card = 3)).card
      = 2 * (Mstar.filter (fun S => S ∉ k4Supports G)).card := by
    rw [hsix, hfour] at hcardsplit
    omega
  refine ⟨MixedRoundingAdapter.ofFarPacking P, ?_⟩
  rw [MixedRoundingAdapter.gain_ofFarPacking, hP]
  rw [hthree, hsix, hfour]
  rw [sum_k3Supports_eq, sum_k4Supports_eq] at hgain
  norm_num at hgain ⊢
  convert hgain using 1 <;> ring

end PaperIV.JointTwoQuotaPhysical
