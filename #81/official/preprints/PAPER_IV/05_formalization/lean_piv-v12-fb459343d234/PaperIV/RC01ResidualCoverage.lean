import PaperIV.RC01CanonicalValueAccounting
import PaperIV.DiscardCounts

/-!
# RC01: the residual-coverage gate

This module closes the last geometric step of the RC01 residual account.  The
exact algebraic reduction is already available:

* `RC01CanonicalValueAccounting.value_eq_canonical_add_off` splits the objective
  into the canonical value of a selected family of literal K3/K4 fibres and one
  nonnegative remainder `offCanonicalValue`;
* `PatternMass.gain_of_discards_le` pays for every item that touches a
  physically discarded edge;
* `PatternMass.gain_small_le` pays for every canonical pattern whose raw mass is
  below the selection threshold.

What was still missing is the *classification*: an item of `G` which avoids all
discarded edges of the literal discard set of (15.1) is necessarily a
transversal copy of a canonical reduced pattern.  This is proved here from the
literal definitions (`DiscardCounts.B₀`, `B₁`, `B₂`, `B₃`,
`RC01K3Pool.goodK3Tuples`, `RC01CandidatePool.goodK4Tuples`) with no extra
hypothesis beyond the fact that `V₀` really contains every uncoloured vertex —
a property that the literal garbage set `garbage R` satisfies by definition.

Consequently, selecting the canonical patterns of raw mass at least `θ` costs at
most

```
offCanonicalValue ≤ 5 · |B_desc| + 5 · |mixedPatterns R| · θ
```

and the retained canonical value is at least `x.value` minus that budget.

No rounding statement, no uniformity hypothesis and no imported conclusion is
used.
-/

namespace PaperIV.RC01ResidualCoverage

open Finset
open PaperIV.PatternCounting
open PaperIV.RegularityFormat
open PaperIV.PartitionBridge
open PaperIV.FarRounding
open PaperIV.PatternMass
open PaperIV.RC01Candidates
open PaperIV.RC01CandidatePool
open PaperIV.RC01CanonicalSlots
open PaperIV.RC01K3Pool
open PaperIV.RC01CleanFiber
open PaperIV.RC01MixedPatterns
open PaperIV.RC01CanonicalProfile
open PaperIV.RC01CanonicalFiberProfile
open PaperIV.RC01PatternCapacity
open PaperIV.RC01CanonicalValueAccounting
open PaperIV.DiscardCounts

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-! ## 1. Enumerating a finite slot -/

/-- A concrete injective enumeration of a finite set of known cardinality. -/
noncomputable def slotEnum {β : Type*} (S : Finset β) {n : ℕ} (h : S.card = n) :
    Fin n → β :=
  fun i => ((S.equivFin.symm (Fin.cast h.symm i) : {x // x ∈ S}) : β)

theorem slotEnum_mem {β : Type*} (S : Finset β) {n : ℕ} (h : S.card = n) (i : Fin n) :
    slotEnum S h i ∈ S :=
  (S.equivFin.symm (Fin.cast h.symm i)).2

theorem slotEnum_injective {β : Type*} (S : Finset β) {n : ℕ} (h : S.card = n) :
    Function.Injective (slotEnum S h) := by
  intro i j hij
  have h1 : S.equivFin.symm (Fin.cast h.symm i) = S.equivFin.symm (Fin.cast h.symm j) :=
    Subtype.ext hij
  have h2 : Fin.cast h.symm i = Fin.cast h.symm j := S.equivFin.symm.injective h1
  exact Fin.ext (by simpa using congrArg Fin.val h2)

theorem image_slotEnum {β : Type*} [DecidableEq β] (S : Finset β) {n : ℕ}
    (h : S.card = n) : Finset.univ.image (slotEnum S h) = S := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro b hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hb
    exact slotEnum_mem S h i
  · rw [Finset.card_image_of_injective _ (slotEnum_injective S h), Finset.card_univ,
      Fintype.card_fin, h]

/-! ## 2. The literal discard set as unordered edges -/

omit [Fintype α] [DecidableEq α] in
/-- Every ordered pair produced by `SimpleGraph.interedges` is adjacent. -/
theorem adj_of_mem_interedges {A B : Finset α} {p : α × α}
    (hp : p ∈ G.interedges A B) : G.Adj p.1 p.2 := by
  rw [SimpleGraph.interedges_def, Finset.mem_filter] at hp
  exact hp.2

/-- The four literal discard families of (15.1), as one set of ordered pairs. -/
noncomputable def discardPairs (G : SimpleGraph α) [DecidableRel G.Adj] {δ : ℚ}
    (R : EqualRegularity G δ) (V₀ : Finset α) (d : ℚ) : Finset (α × α) :=
  B₀ G V₀ ∪ B₁ R ∪ B₂ R ∪ B₃ R d

theorem adj_of_mem_discardPairs {δ : ℚ} {R : EqualRegularity G δ} {V₀ : Finset α}
    {d : ℚ} {p : α × α} (hp : p ∈ discardPairs G R V₀ d) : G.Adj p.1 p.2 := by
  classical
  rw [discardPairs, Finset.mem_union, Finset.mem_union, Finset.mem_union] at hp
  rcases hp with ((hp | hp) | hp) | hp
  · rcases Finset.mem_union.1 hp with hp | hp <;> exact adj_of_mem_interedges hp
  · obtain ⟨P, -, hp⟩ := Finset.mem_biUnion.1 hp
    exact adj_of_mem_interedges hp
  · obtain ⟨q, -, hp⟩ := Finset.mem_biUnion.1 hp
    exact adj_of_mem_interedges hp
  · obtain ⟨q, -, hp⟩ := Finset.mem_biUnion.1 hp
    exact adj_of_mem_interedges hp

/-- **`B_desc`.**  The literal physical discard set of (15.1), read as a set of
unordered edges of `G`. -/
noncomputable def discardEdges (G : SimpleGraph α) [DecidableRel G.Adj] {δ : ℚ}
    (R : EqualRegularity G δ) (V₀ : Finset α) (d : ℚ) : Finset (Sym2 α) :=
  (discardPairs G R V₀ d).image (fun p => s(p.1, p.2))

theorem discardEdges_subset_edgeFinset {δ : ℚ} (R : EqualRegularity G δ)
    (V₀ : Finset α) (d : ℚ) {e : Sym2 α} (he : e ∈ discardEdges G R V₀ d) :
    e ∈ G.edgeFinset := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 he
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact adj_of_mem_discardPairs hp

theorem mem_discardEdges {δ : ℚ} {R : EqualRegularity G δ} {V₀ : Finset α} {d : ℚ}
    {u v : α} (h : (u, v) ∈ discardPairs G R V₀ d) :
    s(u, v) ∈ discardEdges G R V₀ d :=
  Finset.mem_image.2 ⟨(u, v), h, rfl⟩

theorem card_discardEdges_le {δ : ℚ} (R : EqualRegularity G δ) (V₀ : Finset α)
    (d : ℚ) : (discardEdges G R V₀ d).card ≤ (discardPairs G R V₀ d).card :=
  Finset.card_image_le

/-- The literal garbage set: the vertices covered by no regularity part. -/
noncomputable def garbage {δ : ℚ} (R : EqualRegularity G δ) : Finset α :=
  Finset.univ.filter (fun v => ∀ Q ∈ R.parts, v ∉ Q)

theorem cover_of_notMem_garbage {δ : ℚ} (R : EqualRegularity G δ) {v : α}
    (hv : v ∉ garbage R) : ∃ Q ∈ R.parts, v ∈ Q := by
  classical
  by_contra hcon
  exact hv (Finset.mem_filter.2 ⟨Finset.mem_univ v, by
    intro Q hQ hvQ
    exact hcon ⟨Q, hQ, hvQ⟩⟩)

/-! ## 3. The geometric classification -/

/-- The underlying untagged set of regularity parts of a mixed pattern. -/
def patternParts : MixedPattern α → Finset (Finset α)
  | Sum.inl S => S
  | Sum.inr S => S

/-- A canonical mixed pattern is `d`-dense when every ordered pair of distinct
parts in its profile has density at least `d`.  This is the exact property
needed by the regular counting references consumed by the cleaned gate. -/
def IsDensePattern {δ : ℚ} (G : SimpleGraph α) [DecidableRel G.Adj]
    (R : EqualRegularity G δ) (d : ℚ) (σ : MixedPattern α) : Prop :=
  ∀ P ∈ patternParts σ, ∀ Q ∈ patternParts σ, P ≠ Q →
    d ≤ G.edgeDensity P Q

/-- **Classification.**  An item of `G` that meets no discarded edge is the
transversal copy of a canonical reduced K3/K4 pattern, and every pair of parts
of that pattern has density at least the cutoff `d`.

Only `hcover` is required of `V₀`: every vertex outside `V₀` must genuinely lie
in a regularity part.  The literal garbage set satisfies it by definition. -/
theorem exists_dense_mixedPattern_of_avoids_discards {δ : ℚ} (R : EqualRegularity G δ)
    (V₀ : Finset α) (d : ℚ)
    (hcover : ∀ v : α, v ∉ V₀ → ∃ Q ∈ R.parts, v ∈ Q)
    {K : Finset α} (hK : K ∈ items G)
    (hmiss : ∀ e ∈ discardEdges G R V₀ d, e ∉ pairs K) :
    ∃ σ ∈ mixedPatterns R, K ∈ mixedFiber R σ ∧ IsDensePattern G R d σ := by
  classical
  obtain ⟨hclique, hcard⟩ := mem_items.1 hK
  -- (a) no vertex of `K` is uncoloured: otherwise an edge of `K` lies in `B₀`
  have hcolour : ∀ v ∈ K, ∃ Q ∈ R.parts, v ∈ Q := by
    intro v hv
    by_cases hv0 : v ∈ V₀
    · exfalso
      have h1 : 1 < K.card := by rcases hcard with h | h <;> omega
      obtain ⟨w, hw, hwv⟩ := Finset.exists_mem_ne h1 v
      have hadj : G.Adj v w := hclique v hv w hw (Ne.symm hwv)
      have hmem : (v, w) ∈ discardPairs G R V₀ d := by
        rw [discardPairs]
        refine Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ ?_))
        rw [B₀]
        refine Finset.mem_union_left _ ?_
        rw [SimpleGraph.interedges_def, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hv0, Finset.mem_univ _⟩, hadj⟩
      exact hmiss _ (mem_discardEdges hmem) (mk_mem_pairs.2 ⟨hv, hw, Ne.symm hwv⟩)
    · exact hcover v hv0
  -- (b) distinct vertices of `K` have distinct colours: otherwise `B₁`
  have hinj : ∀ u ∈ K, ∀ v ∈ K, partOf R u = partOf R v → u = v := by
    intro u hu v hv huv
    by_contra hne
    obtain ⟨Q, hQ, hQu⟩ := hcolour u hu
    have h1 : partOf R u = some Q := partOf_eq_some R hQ hQu
    have hQv : v ∈ Q := mem_of_partOf_eq_some R (huv.symm.trans h1)
    have hadj : G.Adj u v := hclique u hu v hv hne
    have hmem : (u, v) ∈ discardPairs G R V₀ d := by
      rw [discardPairs]
      refine Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ ?_))
      rw [B₁]
      refine Finset.mem_biUnion.2 ⟨Q, hQ, ?_⟩
      rw [SimpleGraph.interedges_def, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hQu, hQv⟩, hadj⟩
    exact hmiss _ (mem_discardEdges hmem) (mk_mem_pairs.2 ⟨hu, hv, hne⟩)
  -- (c) no two colours of `K` form an exceptional pair: otherwise `B₂`
  have hnotbad : ∀ u ∈ K, ∀ v ∈ K, ∀ P ∈ R.parts, ∀ Q ∈ R.parts,
      u ∈ P → v ∈ Q → u ≠ v → (P, Q) ∉ R.bad := by
    intro u hu v hv P hP Q hQ huP hvQ hne hbad
    have hadj : G.Adj u v := hclique u hu v hv hne
    have hmem : (u, v) ∈ discardPairs G R V₀ d := by
      rw [discardPairs]
      refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      rw [B₂]
      refine Finset.mem_biUnion.2 ⟨(P, Q), ?_, ?_⟩
      · rw [bad₂, Finset.mem_filter]
        exact ⟨hbad, hP, hQ⟩
      · rw [SimpleGraph.interedges_def, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨huP, hvQ⟩, hadj⟩
    exact hmiss _ (mem_discardEdges hmem) (mk_mem_pairs.2 ⟨hu, hv, hne⟩)
  -- the literal colour profile of `K`, and the set of parts realizing it
  set H : Finset (Option (Finset α)) := K.image (partOf R) with hH
  set S : Finset (Finset α) := R.parts.filter (fun P => some P ∈ H) with hSdef
  have hSparts : ∀ P ∈ S, P ∈ R.parts := fun P hP => (Finset.mem_filter.1 hP).1
  have hSmem : ∀ P ∈ S, ∃ v ∈ K, partOf R v = some P := by
    intro P hP
    have := (Finset.mem_filter.1 hP).2
    rw [hH] at this
    obtain ⟨v, hv, hvP⟩ := Finset.mem_image.1 this
    exact ⟨v, hv, hvP⟩
  have hSimage : S.image some = H := by
    ext o
    constructor
    · intro ho
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 ho
      exact (Finset.mem_filter.1 hP).2
    · intro ho
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 ho
      obtain ⟨Q, hQ, hvQ⟩ := hcolour v hv
      have hvs : partOf R v = some Q := partOf_eq_some R hQ hvQ
      refine Finset.mem_image.2 ⟨Q, Finset.mem_filter.2 ⟨hQ, ?_⟩, hvs.symm⟩
      rw [← hvs]
      exact ho
  have hcardH : H.card = K.card := by
    rw [hH]
    exact Finset.card_image_of_injOn (fun u hu v hv h => hinj u hu v hv h)
  have hcardS : S.card = K.card := by
    have h1 : (S.image some).card = S.card :=
      Finset.card_image_of_injective _ (Option.some_injective _)
    rw [hSimage, hcardH] at h1
    exact h1.symm
  have hSbad : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → (P, Q) ∉ R.bad := by
    intro P hP Q hQ hPQ
    obtain ⟨u, hu, hup⟩ := hSmem P hP
    obtain ⟨v, hv, hvq⟩ := hSmem Q hQ
    have hne : u ≠ v := by
      intro h
      rw [h, hvq] at hup
      exact hPQ (Option.some.inj hup).symm
    exact hnotbad u hu v hv P (hSparts P hP) Q (hSparts Q hQ)
      (mem_of_partOf_eq_some R hup) (mem_of_partOf_eq_some R hvq) hne
  -- (d) no two colours of `K` form a low-density pair: otherwise `B₃`
  have hSdense : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → d ≤ G.edgeDensity P Q := by
    intro P hP Q hQ hPQ
    obtain ⟨u, hu, hup⟩ := hSmem P hP
    obtain ⟨v, hv, hvq⟩ := hSmem Q hQ
    have hne : u ≠ v := by
      intro h
      rw [h, hvq] at hup
      exact hPQ (Option.some.inj hup).symm
    by_contra hden
    have hlt : G.edgeDensity P Q < d := lt_of_not_ge hden
    have hadj : G.Adj u v := hclique u hu v hv hne
    have hmem : (u, v) ∈ discardPairs G R V₀ d := by
      rw [discardPairs]
      refine Finset.mem_union_right _ ?_
      rw [B₃]
      refine Finset.mem_biUnion.2 ⟨(P, Q), ?_, ?_⟩
      · rw [lowPairs, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hSparts P hP, hSparts Q hQ⟩, hlt⟩
      · rw [SimpleGraph.interedges_def, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨mem_of_partOf_eq_some R hup, mem_of_partOf_eq_some R hvq⟩, hadj⟩
    exact hmiss _ (mem_discardEdges hmem) (mk_mem_pairs.2 ⟨hu, hv, hne⟩)
  rcases hcard with hc3 | hc4
  · -- a canonical triangle slot
    have hS3 : S.card = 3 := by rw [hcardS, hc3]
    set V : Fin 3 → Finset α := slotEnum S hS3 with hV
    have hVmem : ∀ i, V i ∈ S := fun i => slotEnum_mem S hS3 i
    have hVinj : Function.Injective V := slotEnum_injective S hS3
    have hgood : V ∈ goodK3Tuples R := by
      refine mem_goodK3Tuples.2 ⟨fun i => hSparts _ (hVmem i), ?_, ?_⟩
      · intro i j hij h
        exact hij (hVinj h)
      · intro e he
        exact hSbad _ (hVmem e.1) _ (hVmem e.2)
          (fun h => patK3_ne e he (hVinj h))
    have hslot : S ∈ goodK3Slots R :=
      Finset.mem_image.2 ⟨V, hgood, image_slotEnum S hS3⟩
    refine ⟨Sum.inl S, mem_mixedPatterns_iff.2 (Or.inl ⟨S, hslot, rfl⟩), ?_, ?_⟩
    have hσ : (Sum.inl S : MixedPattern α) ∈ mixedPatterns R :=
      mem_mixedPatterns_iff.2 (Or.inl ⟨S, hslot, rfl⟩)
    have hprof : profileOfMixed (Sum.inl S : MixedPattern α) = H := hSimage
    refine (mem_mixedFiber_iff_mem_profileFiber R hσ).2 (mem_profileFiber.2 ⟨hK, ?_, ?_⟩)
    · rw [hprof]
    · rw [hprof, hcardH]
    · simpa [IsDensePattern, patternParts] using hSdense
  · -- a canonical four-clique slot
    have hS4 : S.card = 4 := by rw [hcardS, hc4]
    set V : Fin 4 → Finset α := slotEnum S hS4 with hV
    have hVmem : ∀ i, V i ∈ S := fun i => slotEnum_mem S hS4 i
    have hVinj : Function.Injective V := slotEnum_injective S hS4
    have hgood : V ∈ goodK4Tuples R := by
      refine mem_goodK4Tuples.2 ⟨fun i => hSparts _ (hVmem i), ?_, ?_⟩
      · intro i j hij h
        exact hij (hVinj h)
      · intro e he
        exact hSbad _ (hVmem e.1) _ (hVmem e.2)
          (fun h => patK4_ne e he (hVinj h))
    have hslot : S ∈ goodK4Slots R :=
      Finset.mem_image.2 ⟨V, hgood, image_slotEnum S hS4⟩
    refine ⟨Sum.inr S, mem_mixedPatterns_iff.2 (Or.inr ⟨S, hslot, rfl⟩), ?_, ?_⟩
    have hσ : (Sum.inr S : MixedPattern α) ∈ mixedPatterns R :=
      mem_mixedPatterns_iff.2 (Or.inr ⟨S, hslot, rfl⟩)
    have hprof : profileOfMixed (Sum.inr S : MixedPattern α) = H := hSimage
    refine (mem_mixedFiber_iff_mem_profileFiber R hσ).2 (mem_profileFiber.2 ⟨hK, ?_, ?_⟩)
    · rw [hprof]
    · rw [hprof, hcardH]
    · simpa [IsDensePattern, patternParts] using hSdense

/-- Backwards-compatible projection of the strengthened dense classification. -/
theorem exists_mixedPattern_of_avoids_discards {δ : ℚ} (R : EqualRegularity G δ)
    (V₀ : Finset α) (d : ℚ)
    (hcover : ∀ v : α, v ∉ V₀ → ∃ Q ∈ R.parts, v ∈ Q)
    {K : Finset α} (hK : K ∈ items G)
    (hmiss : ∀ e ∈ discardEdges G R V₀ d, e ∉ pairs K) :
    ∃ σ ∈ mixedPatterns R, K ∈ mixedFiber R σ := by
  obtain ⟨σ, hσ, hKσ, -⟩ :=
    exists_dense_mixedPattern_of_avoids_discards R V₀ d hcover hK hmiss
  exact ⟨σ, hσ, hKσ⟩

/-! ## 4. The residual budget -/

/-- The canonical patterns selected above the threshold `θ`. -/
noncomputable def heavyPatterns {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (θ : ℚ) : Finset (MixedPattern α) :=
  (mixedPatterns R).filter (fun σ => θ ≤ rawMass x (mixedFiber R) σ)

/-- The patterns that are simultaneously heavy and genuinely above the
low-density cutoff already charged to `B₃`. -/
noncomputable def denseHeavyPatterns {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (d θ : ℚ) : Finset (MixedPattern α) :=
  by
    classical
    exact (mixedPatterns R).filter (fun σ =>
      IsDensePattern G R d σ ∧ θ ≤ rawMass x (mixedFiber R) σ)

theorem heavyPatterns_subset {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (θ : ℚ) : heavyPatterns R x θ ⊆ mixedPatterns R :=
  Finset.filter_subset _ _

theorem denseHeavyPatterns_subset {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (d θ : ℚ) : denseHeavyPatterns R x d θ ⊆ mixedPatterns R :=
  by
    classical
    exact Finset.filter_subset _ _

/-- **The residual-coverage budget.**  Selecting the canonical K3/K4 patterns of
raw mass at least `θ` leaves a residual value paid by five times the physical
discard count plus five times the small-pattern budget. -/
theorem offCanonicalValue_le_discards_add_small {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (V₀ : Finset α) (d θ : ℚ) (hθ : 0 ≤ θ)
    (hcover : ∀ v : α, v ∉ V₀ → ∃ Q ∈ R.parts, v ∈ Q) :
    offCanonicalValue R x (heavyPatterns R x θ)
      ≤ 5 * ((discardEdges G R V₀ d).card : ℚ)
        + 5 * (((mixedPatterns R).card : ℚ) * θ) := by
  set B : Finset (Sym2 α) := discardEdges G R V₀ d with hBdef
  set D : Finset (Finset α) :=
    (items G).filter (fun K => K ∉ (heavyPatterns R x θ).biUnion (mixedFiber R)) with hDdef
  set Light : Finset (MixedPattern α) :=
    (mixedPatterns R).filter (fun σ => rawMass x (mixedFiber R) σ < θ) with hLdef
  have hLsub : Light ⊆ mixedPatterns R := Finset.filter_subset _ _
  -- split the residual sum according to incidence with a discarded edge
  have hsplit : offCanonicalValue R x (heavyPatterns R x θ)
      = (∑ K ∈ D.filter (fun K => ∃ e ∈ B, e ∈ pairs K), gainF ℚ K * x.weight K)
        + ∑ K ∈ D.filter (fun K => ¬ ∃ e ∈ B, e ∈ pairs K), gainF ℚ K * x.weight K := by
    rw [offCanonicalValue, ← hDdef]
    exact (Finset.sum_filter_add_sum_filter_not D _ _).symm
  -- (a) the items touching a discarded edge are paid by the incidence budget
  have h1 : (∑ K ∈ D.filter (fun K => ∃ e ∈ B, e ∈ pairs K), gainF ℚ K * x.weight K)
      ≤ 5 * (B.card : ℚ) :=
    PaperIV.PatternMass.gain_of_discards_le x B
      (fun e he => discardEdges_subset_edgeFinset R V₀ d he) _
      (fun K hK => (Finset.mem_filter.1 (Finset.mem_filter.1 hK).1).1)
      (fun K hK => (Finset.mem_filter.1 hK).2)
  -- (b) the remaining items belong to canonical fibres of small raw mass
  have hsub : D.filter (fun K => ¬ ∃ e ∈ B, e ∈ pairs K) ⊆ Light.biUnion (mixedFiber R) := by
    intro K hK
    have hKD := (Finset.mem_filter.1 hK).1
    have hKmiss := (Finset.mem_filter.1 hK).2
    have hKitem : K ∈ items G := (Finset.mem_filter.1 hKD).1
    have hKnot : K ∉ (heavyPatterns R x θ).biUnion (mixedFiber R) :=
      (Finset.mem_filter.1 hKD).2
    obtain ⟨σ, hσ, hKσ⟩ := exists_mixedPattern_of_avoids_discards R V₀ d hcover hKitem
      (fun e he hpe => hKmiss ⟨e, he, hpe⟩)
    refine Finset.mem_biUnion.2 ⟨σ, Finset.mem_filter.2 ⟨hσ, ?_⟩, hKσ⟩
    by_contra hge
    push_neg at hge
    exact hKnot (Finset.mem_biUnion.2
      ⟨σ, Finset.mem_filter.2 ⟨hσ, hge⟩, hKσ⟩)
  have hnn : ∀ K ∈ Light.biUnion (mixedFiber R), 0 ≤ gainF ℚ K * x.weight K := by
    intro K hK
    obtain ⟨σ, hσ, hKσ⟩ := Finset.mem_biUnion.1 hK
    exact mul_nonneg
      (PaperIV.PatternMass.gainF_nonneg
        (mem_items.1 (mixedFiber_subset_items R (hLsub hσ) hKσ)))
      (x.weight_nonneg K)
  have h2 : (∑ K ∈ D.filter (fun K => ¬ ∃ e ∈ B, e ∈ pairs K), gainF ℚ K * x.weight K)
      ≤ ∑ K ∈ Light.biUnion (mixedFiber R), gainF ℚ K * x.weight K :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun K hK _ => hnn K hK)
  have h3 : (∑ K ∈ Light.biUnion (mixedFiber R), gainF ℚ K * x.weight K)
      = ∑ σ ∈ Light, ∑ K ∈ mixedFiber R σ, gainF ℚ K * x.weight K :=
    Finset.sum_biUnion (mixedFiber_pairwiseDisjoint_of_subset R Light hLsub)
  have h4 : ∀ σ ∈ Light, (∑ K ∈ mixedFiber R σ, gainF ℚ K * x.weight K)
      ≤ 5 * rawMass x (mixedFiber R) σ := by
    intro σ hσ
    rw [rawMass, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro K hK
    exact mul_le_mul_of_nonneg_right
      (PaperIV.PatternMass.gainF_le_five
        (mem_items.1 (mixedFiber_subset_items R (hLsub hσ) hK)))
      (x.weight_nonneg K)
  have h5 : (∑ σ ∈ Light, 5 * rawMass x (mixedFiber R) σ)
      ≤ 5 * (((mixedPatterns R).card : ℚ) * θ) :=
    PaperIV.PatternMass.gain_small_le (mixedPatterns R) (rawMass x (mixedFiber R))
      (fun σ => 5 * rawMass x (mixedFiber R) σ) θ hθ
      (fun σ => rawMass_nonneg x (mixedFiber R) σ) (fun σ => le_refl _)
  have h6 : (∑ σ ∈ Light, ∑ K ∈ mixedFiber R σ, gainF ℚ K * x.weight K)
      ≤ ∑ σ ∈ Light, 5 * rawMass x (mixedFiber R) σ := Finset.sum_le_sum h4
  rw [hsplit]
  linarith [h1, h2, h3.le, h3.ge, h6, h5]

/-- Dense version of the residual budget.  Unlike the earlier heavy family,
this family is ready for the positive-volume regular counting lemmas: every
surviving reduced pair has density at least `d`. -/
theorem offCanonicalValue_le_dense_discards_add_small {δ : ℚ}
    (R : EqualRegularity G δ) (x : FracPacking G ℚ) (V₀ : Finset α)
    (d θ : ℚ) (hθ : 0 ≤ θ)
    (hcover : ∀ v : α, v ∉ V₀ → ∃ Q ∈ R.parts, v ∈ Q) :
    offCanonicalValue R x (denseHeavyPatterns R x d θ)
      ≤ 5 * ((discardEdges G R V₀ d).card : ℚ)
        + 5 * (((mixedPatterns R).card : ℚ) * θ) := by
  classical
  set B : Finset (Sym2 α) := discardEdges G R V₀ d with hBdef
  set D : Finset (Finset α) :=
    (items G).filter (fun K => K ∉ (denseHeavyPatterns R x d θ).biUnion (mixedFiber R))
      with hDdef
  set Light : Finset (MixedPattern α) :=
    (mixedPatterns R).filter (fun σ => rawMass x (mixedFiber R) σ < θ) with hLdef
  have hLsub : Light ⊆ mixedPatterns R := Finset.filter_subset _ _
  have hsplit : offCanonicalValue R x (denseHeavyPatterns R x d θ)
      = (∑ K ∈ D.filter (fun K => ∃ e ∈ B, e ∈ pairs K), gainF ℚ K * x.weight K)
        + ∑ K ∈ D.filter (fun K => ¬ ∃ e ∈ B, e ∈ pairs K), gainF ℚ K * x.weight K := by
    rw [offCanonicalValue, ← hDdef]
    exact (Finset.sum_filter_add_sum_filter_not D _ _).symm
  have h1 : (∑ K ∈ D.filter (fun K => ∃ e ∈ B, e ∈ pairs K), gainF ℚ K * x.weight K)
      ≤ 5 * (B.card : ℚ) :=
    PaperIV.PatternMass.gain_of_discards_le x B
      (fun e he => discardEdges_subset_edgeFinset R V₀ d he) _
      (fun K hK => (Finset.mem_filter.1 (Finset.mem_filter.1 hK).1).1)
      (fun K hK => (Finset.mem_filter.1 hK).2)
  have hsub : D.filter (fun K => ¬ ∃ e ∈ B, e ∈ pairs K) ⊆
      Light.biUnion (mixedFiber R) := by
    intro K hK
    have hKD := (Finset.mem_filter.1 hK).1
    have hKmiss := (Finset.mem_filter.1 hK).2
    have hKitem : K ∈ items G := (Finset.mem_filter.1 hKD).1
    have hKnot : K ∉ (denseHeavyPatterns R x d θ).biUnion (mixedFiber R) :=
      (Finset.mem_filter.1 hKD).2
    obtain ⟨σ, hσ, hKσ, hdense⟩ :=
      exists_dense_mixedPattern_of_avoids_discards R V₀ d hcover hKitem
        (fun e he hpe => hKmiss ⟨e, he, hpe⟩)
    refine Finset.mem_biUnion.2 ⟨σ, Finset.mem_filter.2 ⟨hσ, ?_⟩, hKσ⟩
    by_contra hge
    push_neg at hge
    exact hKnot (Finset.mem_biUnion.2 ⟨σ,
      Finset.mem_filter.2 ⟨hσ, hdense, hge⟩, hKσ⟩)
  have hnn : ∀ K ∈ Light.biUnion (mixedFiber R), 0 ≤ gainF ℚ K * x.weight K := by
    intro K hK
    obtain ⟨σ, hσ, hKσ⟩ := Finset.mem_biUnion.1 hK
    exact mul_nonneg
      (PaperIV.PatternMass.gainF_nonneg
        (mem_items.1 (mixedFiber_subset_items R (hLsub hσ) hKσ)))
      (x.weight_nonneg K)
  have h2 : (∑ K ∈ D.filter (fun K => ¬ ∃ e ∈ B, e ∈ pairs K), gainF ℚ K * x.weight K)
      ≤ ∑ K ∈ Light.biUnion (mixedFiber R), gainF ℚ K * x.weight K :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun K hK _ => hnn K hK)
  have h3 : (∑ K ∈ Light.biUnion (mixedFiber R), gainF ℚ K * x.weight K)
      = ∑ σ ∈ Light, ∑ K ∈ mixedFiber R σ, gainF ℚ K * x.weight K :=
    Finset.sum_biUnion (mixedFiber_pairwiseDisjoint_of_subset R Light hLsub)
  have h4 : ∀ σ ∈ Light, (∑ K ∈ mixedFiber R σ, gainF ℚ K * x.weight K)
      ≤ 5 * rawMass x (mixedFiber R) σ := by
    intro σ hσ
    rw [rawMass, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro K hK
    exact mul_le_mul_of_nonneg_right
      (PaperIV.PatternMass.gainF_le_five
        (mem_items.1 (mixedFiber_subset_items R (hLsub hσ) hK)))
      (x.weight_nonneg K)
  have h5 : (∑ σ ∈ Light, 5 * rawMass x (mixedFiber R) σ)
      ≤ 5 * (((mixedPatterns R).card : ℚ) * θ) :=
    PaperIV.PatternMass.gain_small_le (mixedPatterns R) (rawMass x (mixedFiber R))
      (fun σ => 5 * rawMass x (mixedFiber R) σ) θ hθ
      (fun σ => rawMass_nonneg x (mixedFiber R) σ) (fun σ => le_refl _)
  have h6 : (∑ σ ∈ Light, ∑ K ∈ mixedFiber R σ, gainF ℚ K * x.weight K)
      ≤ ∑ σ ∈ Light, 5 * rawMass x (mixedFiber R) σ := Finset.sum_le_sum h4
  rw [hsplit]
  linarith [h1, h2, h3.le, h3.ge, h6, h5]

/-- Dense residual budget with the literal garbage set. -/
theorem offCanonicalValue_le_dense_garbage_discards {δ : ℚ}
    (R : EqualRegularity G δ) (x : FracPacking G ℚ) (d θ : ℚ) (hθ : 0 ≤ θ) :
    offCanonicalValue R x (denseHeavyPatterns R x d θ)
      ≤ 5 * ((discardEdges G R (garbage R) d).card : ℚ)
        + 5 * (((mixedPatterns R).card : ℚ) * θ) :=
  offCanonicalValue_le_dense_discards_add_small R x (garbage R) d θ hθ
    (fun _ hv => cover_of_notMem_garbage R hv)

/-- The same budget with the literal garbage set, hence with no hypothesis on
the uncoloured vertices. -/
theorem offCanonicalValue_le_garbage_discards {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (d θ : ℚ) (hθ : 0 ≤ θ) :
    offCanonicalValue R x (heavyPatterns R x θ)
      ≤ 5 * ((discardEdges G R (garbage R) d).card : ℚ)
        + 5 * (((mixedPatterns R).card : ℚ) * θ) :=
  offCanonicalValue_le_discards_add_small R x (garbage R) d θ hθ
    (fun _ hv => cover_of_notMem_garbage R hv)

/-! ## 5. The literal `(15.1)` numerical form -/

/-- The literal garbage set really is the complement of the union of the parts,
so the format bound `|V₀| ≤ δn` of `EqualRegularity` applies to it. -/
theorem card_garbage_le {δ : ℚ} (R : EqualRegularity G δ) :
    ((garbage R).card : ℚ) ≤ δ * (Fintype.card α : ℚ) := by
  classical
  have hcardU : (R.parts.biUnion (fun P => P)).card = R.parts.card * R.size := by
    rw [Finset.card_biUnion (fun P hP Q hQ h => R.pairwise_disjoint P hP Q hQ h),
      Finset.sum_congr rfl (fun P hP => R.card_part P hP), Finset.sum_const, smul_eq_mul]
  have hgU : garbage R = Finset.univ \ R.parts.biUnion (fun P => P) := by
    ext v
    simp only [garbage, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_biUnion]
    constructor
    · rintro h ⟨Q, hQ, hvQ⟩
      exact h Q hQ hvQ
    · intro h Q hQ hvQ
      exact h ⟨Q, hQ, hvQ⟩
  have hUle : (R.parts.biUnion (fun P => P)).card ≤ Fintype.card α := by
    simpa using Finset.card_le_card (Finset.subset_univ (R.parts.biUnion (fun P => P)))
  have hcast : ((garbage R).card : ℚ)
      = (Fintype.card α : ℚ) - (R.parts.card : ℚ) * (R.size : ℚ) := by
    rw [hgU, Finset.card_univ_diff, Nat.cast_sub hUle, hcardU]
    push_cast
    ring
  rw [hcast]
  exact R.garbage

/-- **The literal (15.1) budget.**  Combining the residual-coverage gate with
the four discard counts of `DiscardCounts` gives an explicit bound in terms of
the regularity parameters only. -/
theorem offCanonicalValue_le_regularity_budget {δ : ℚ} (hδ : 0 ≤ δ)
    (R : EqualRegularity G δ) (x : FracPacking G ℚ) (d θ : ℚ) (hd : 0 ≤ d)
    (hθ : 0 ≤ θ) {k₀ : ℕ} (hk₀ : 0 < k₀) (hk : k₀ ≤ R.parts.card) :
    offCanonicalValue R x (heavyPatterns R x θ)
      ≤ 5 * ((3 * δ + 1 / (k₀ : ℚ) + d) * (Fintype.card α : ℚ) ^ 2)
        + 5 * (((mixedPatterns R).card : ℚ) * θ) := by
  have hgate := offCanonicalValue_le_garbage_discards R x d θ hθ
  have hcard : ((discardEdges G R (garbage R) d).card : ℚ)
      ≤ ((discardPairs G R (garbage R) d).card : ℚ) := by
    exact_mod_cast card_discardEdges_le R (garbage R) d
  have hpairs : ((discardPairs G R (garbage R) d).card : ℚ)
      ≤ (3 * δ + 1 / (k₀ : ℚ) + d) * (Fintype.card α : ℚ) ^ 2 := by
    rw [discardPairs]
    exact card_discards_le hδ R d hd hk₀ hk (garbage R) (card_garbage_le R)
  linarith

/-- Numerical `(15.1)` budget whose surviving family is already dense enough
for the regular-volume construction. -/
theorem offCanonicalValue_le_dense_regularity_budget {δ : ℚ} (hδ : 0 ≤ δ)
    (R : EqualRegularity G δ) (x : FracPacking G ℚ) (d θ : ℚ)
    (hd : 0 ≤ d) (hθ : 0 ≤ θ) {k₀ : ℕ} (hk₀ : 0 < k₀)
    (hk : k₀ ≤ R.parts.card) :
    offCanonicalValue R x (denseHeavyPatterns R x d θ)
      ≤ 5 * ((3 * δ + 1 / (k₀ : ℚ) + d) * (Fintype.card α : ℚ) ^ 2)
        + 5 * (((mixedPatterns R).card : ℚ) * θ) := by
  have hgate := offCanonicalValue_le_dense_garbage_discards R x d θ hθ
  have hcard : ((discardEdges G R (garbage R) d).card : ℚ)
      ≤ ((discardPairs G R (garbage R) d).card : ℚ) := by
    exact_mod_cast card_discardEdges_le R (garbage R) d
  have hpairs : ((discardPairs G R (garbage R) d).card : ℚ)
      ≤ (3 * δ + 1 / (k₀ : ℚ) + d) * (Fintype.card α : ℚ) ^ 2 := by
    rw [discardPairs]
    exact card_discards_le hδ R d hd hk₀ hk (garbage R) (card_garbage_le R)
  linarith

/-- **The retained canonical value.**  What survives the selection is the whole
objective minus the residual budget. -/
theorem canonicalValue_ge {δ : ℚ} (R : EqualRegularity G δ) (x : FracPacking G ℚ)
    (d θ : ℚ) (hθ : 0 ≤ θ) :
    x.value - 5 * ((discardEdges G R (garbage R) d).card : ℚ)
        - 5 * (((mixedPatterns R).card : ℚ) * θ)
      ≤ canonicalValue R x (heavyPatterns R x θ) := by
  have hsplit := value_eq_canonical_add_off R x (heavyPatterns R x θ)
    (heavyPatterns_subset R x θ)
  have hoff := offCanonicalValue_le_garbage_discards R x d θ hθ
  linarith

end PaperIV.RC01ResidualCoverage
