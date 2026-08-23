/-
  Part B (Phase 2) — the CORRECTED absorber interface: **flexible transformer banks**.

  `BankElim.lean` shows that the rigid bank interface consumed by `absorber_of_transformer_bank`
  is unsatisfiable: there each unit `i` owns ONE config `S i`, the configs are pairwise disjoint,
  and every admissible leftover has to be a union of configs — which forces a config of size `1`
  as soon as one edge lies in two triangles of the residual graph.

  The fix is to let each unit own a *family* of possible configs: a unit `i` reserves a base
  triangle family `base i` (these ARE pairwise edge-disjoint across units, since they are the
  edges of the absorber that get re-decomposed), and for every admissible config `S` in its
  family `cfg i` it has an alternative decomposition `absorb i S` with
      `coveredEdges (absorb i S) = coveredEdges (base i) ∪ S`.
  Nothing is assumed about how configs of different units interact: at absorption time the
  configs actually used are pairwise disjoint because they partition the leftover `L`, and they
  are disjoint from all reserved edges because `L` is.

  `absorber_of_flexBank` (proved here, sorry-free) is the generalised rerouting move: a rich
  flexible bank is a `β`-absorber.  This is the live replacement for
  `absorber_of_transformer_bank`.
-/
import Ax2.PartB.BKLO.AbsorberCore
import Ax2.PartB.BKLO.Absorber

namespace Ax2.BKLO

open SimpleGraph Finset Ax2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A **flexible transformer bank** for `G`: finitely many units, each reserving an edge-disjoint
triangle family `base i` (pairwise edge-disjoint across units), each able to re-decompose its
reserved edges together with any config `S` from its own admissible family `cfg i`. -/
structure FlexBank (G : SimpleGraph V) [DecidableRel G.Adj] where
  /-- The (finite) set of units of the bank. -/
  I : Finset ℕ
  /-- The reserved triangle family of a unit. -/
  base : ℕ → Finset (Finset V)
  /-- The configs a unit is able to absorb. -/
  cfg : ℕ → Finset (Sym2 V) → Prop
  /-- The alternative decomposition of a unit absorbing a given config. -/
  absorb : ℕ → Finset (Sym2 V) → Finset (Finset V)
  base_clique : ∀ i ∈ I, ∀ t ∈ base i, G.IsNClique 3 t
  base_disj : ∀ i ∈ I, EdgeDisjoint (base i)
  base_cross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
    Disjoint (coveredEdges (base i)) (coveredEdges (base j))
  absorb_clique : ∀ i ∈ I, ∀ S, cfg i S → ∀ t ∈ absorb i S, G.IsNClique 3 t
  absorb_disj : ∀ i ∈ I, ∀ S, cfg i S → EdgeDisjoint (absorb i S)
  absorb_cov : ∀ i ∈ I, ∀ S, cfg i S → coveredEdges (absorb i S) = coveredEdges (base i) ∪ S

namespace FlexBank

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The absorber core of a bank: all reserved triangles. -/
def core (K : FlexBank G) : Finset (Finset V) := K.I.biUnion K.base

/-- A bank is **`β`-rich** if every admissible leftover of density `≤ β` splits into pairwise
disjoint configs assigned to distinct units. -/
def Rich (K : FlexBank G) (β : ℝ) : Prop :=
  ∀ L : Finset (Sym2 V), L ⊆ G.edgeFinset → Disjoint L (coveredEdges K.core) →
    (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 → 3 ∣ L.card →
    (∀ v : V, Even ((L.filter (fun e => v ∈ e)).card)) →
    ∃ (J : Finset ℕ) (f : ℕ → Finset (Sym2 V)), J ⊆ K.I ∧ (∀ i ∈ J, K.cfg i (f i)) ∧
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (f i) (f j)) ∧ J.biUnion f = L

end FlexBank

omit [Fintype V] in
/-- Edge-disjointness of a union of families is implied by edge-disjointness of each family
together with pairwise disjoint "spans" containing their covered edges. -/
theorem edgeDisjoint_biUnion_of_spans {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (U : ι → Finset (Finset V)) (sp : ι → Finset (Sym2 V))
    (hUd : ∀ i ∈ I, EdgeDisjoint (U i)) (hspan : ∀ i ∈ I, coveredEdges (U i) ⊆ sp i)
    (hcross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (sp i) (sp j)) :
    EdgeDisjoint (I.biUnion U) := by
  intro t₁ ht₁ t₂ ht₂ hne
  obtain ⟨i, hi, ht₁i⟩ := Finset.mem_biUnion.mp ht₁
  obtain ⟨j, hj, ht₂j⟩ := Finset.mem_biUnion.mp ht₂
  by_cases hij : i = j
  · subst hij; exact hUd i hi t₁ ht₁i t₂ ht₂j hne
  · have h1 : triEdges t₁ ⊆ sp i :=
      (Finset.subset_biUnion_of_mem triEdges ht₁i).trans (hspan i hi)
    have h2 : triEdges t₂ ⊆ sp j :=
      (Finset.subset_biUnion_of_mem triEdges ht₂j).trans (hspan j hj)
    exact Finset.disjoint_of_subset_left h1
      (Finset.disjoint_of_subset_right h2 (hcross i hi j hj hij))

/-- **Generalised rerouting move.** Given a flexible bank, a set `J` of units and a choice `f i`
of config for each `i ∈ J` such that the chosen configs are pairwise disjoint and disjoint from
all reserved edges, using `absorb i (f i)` on `J` and `base i` off `J` gives an edge-disjoint
family of `G`-triangles covering exactly the reserved edges together with `⋃_{i∈J} f i`. -/
theorem flex_reroute {G : SimpleGraph V} [DecidableRel G.Adj] (K : FlexBank G)
    (J : Finset ℕ) (f : ℕ → Finset (Sym2 V)) (hJI : J ⊆ K.I)
    (hf : ∀ i ∈ J, K.cfg i (f i))
    (hfdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (f i) (f j))
    (hfbase : ∀ i ∈ J, Disjoint (f i) (coveredEdges K.core)) :
    ∃ P : Finset (Finset V), (∀ t ∈ P, G.IsNClique 3 t) ∧ EdgeDisjoint P ∧
      coveredEdges P = coveredEdges K.core ∪ J.biUnion f := by
  classical
  -- the family used at unit `i`, and the config it contributes
  set f' : ℕ → Finset (Sym2 V) := fun i => if i ∈ J then f i else ∅ with hf'def
  set U : ℕ → Finset (Finset V) := fun i => if i ∈ J then K.absorb i (f i) else K.base i
    with hUdef
  have hcore : coveredEdges K.core = K.I.biUnion (fun i => coveredEdges (K.base i)) :=
    coveredEdges_biUnion K.I K.base
  have hbsub : ∀ j ∈ K.I, coveredEdges (K.base j) ⊆ coveredEdges K.core := by
    intro j hj; rw [hcore]
    exact Finset.subset_biUnion_of_mem (fun i => coveredEdges (K.base i)) hj
  have hUcov : ∀ i ∈ K.I, coveredEdges (U i) = coveredEdges (K.base i) ∪ f' i := by
    intro i hi
    by_cases hiJ : i ∈ J
    · simp only [hUdef, hf'def, if_pos hiJ]
      exact K.absorb_cov i hi (f i) (hf i hiJ)
    · simp only [hUdef, hf'def, if_neg hiJ, Finset.union_empty]
  have hUcl : ∀ i ∈ K.I, ∀ t ∈ U i, G.IsNClique 3 t := by
    intro i hi t ht
    by_cases hiJ : i ∈ J
    · simp only [hUdef, if_pos hiJ] at ht
      exact K.absorb_clique i hi (f i) (hf i hiJ) t ht
    · simp only [hUdef, if_neg hiJ] at ht
      exact K.base_clique i hi t ht
  have hUd : ∀ i ∈ K.I, EdgeDisjoint (U i) := by
    intro i hi
    by_cases hiJ : i ∈ J
    · simpa only [hUdef, if_pos hiJ] using K.absorb_disj i hi (f i) (hf i hiJ)
    · simpa only [hUdef, if_neg hiJ] using K.base_disj i hi
  have hf'core : ∀ i, Disjoint (f' i) (coveredEdges K.core) := by
    intro i
    by_cases hiJ : i ∈ J
    · simpa only [hf'def, if_pos hiJ] using hfbase i hiJ
    · simp only [hf'def, if_neg hiJ]; exact Finset.disjoint_empty_left _
  have hf'disj : ∀ i, ∀ j, i ≠ j → Disjoint (f' i) (f' j) := by
    intro i j hij
    by_cases hiJ : i ∈ J
    · by_cases hjJ : j ∈ J
      · simpa only [hf'def, if_pos hiJ, if_pos hjJ] using hfdisj i hiJ j hjJ hij
      · simp only [hf'def, if_neg hjJ]; exact Finset.disjoint_empty_right _
    · simp only [hf'def, if_neg hiJ]; exact Finset.disjoint_empty_left _
  have hUcross : ∀ i ∈ K.I, ∀ j ∈ K.I, i ≠ j →
      Disjoint (coveredEdges (K.base i) ∪ f' i) (coveredEdges (K.base j) ∪ f' j) := by
    intro i hi j hj hij
    refine Finset.disjoint_union_left.mpr ⟨?_, ?_⟩ <;>
      refine Finset.disjoint_union_right.mpr ⟨?_, ?_⟩
    · exact K.base_cross i hi j hj hij
    · exact (Finset.disjoint_of_subset_right (hbsub i hi) (hf'core j)).symm
    · exact Finset.disjoint_of_subset_right (hbsub j hj) (hf'core i)
    · exact hf'disj i j hij
  refine ⟨K.I.biUnion U, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨i, hi, hti⟩ := Finset.mem_biUnion.mp ht
    exact hUcl i hi t hti
  · refine edgeDisjoint_biUnion_of_spans K.I U (fun i => coveredEdges (K.base i) ∪ f' i)
      hUd (fun i hi => by rw [hUcov i hi]) hUcross
  · rw [coveredEdges_biUnion K.I U]
    have : K.I.biUnion (fun i => coveredEdges (U i))
        = K.I.biUnion (fun i => coveredEdges (K.base i) ∪ f' i) :=
      Finset.biUnion_congr rfl (fun i hi => hUcov i hi)
    rw [this, hcore]
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_union, hf'def]
    constructor
    · rintro ⟨i, hi, h | h⟩
      · exact Or.inl ⟨i, hi, h⟩
      · by_cases hiJ : i ∈ J
        · rw [if_pos hiJ] at h; exact Or.inr ⟨i, hiJ, h⟩
        · rw [if_neg hiJ] at h; simp at h
    · rintro (⟨i, hi, h⟩ | ⟨i, hiJ, h⟩)
      · exact ⟨i, hi, Or.inl h⟩
      · exact ⟨i, hJI hiJ, Or.inr (by rw [if_pos hiJ]; exact h)⟩

/-- **Absorber from a flexible transformer bank.** A `β`-rich flexible bank is a `β`-absorber
with core `⋃_{i∈I} base i`.  (Corrected replacement for `absorber_of_transformer_bank`, whose
rigid `hrich` hypothesis is refuted in `BankElim.lean`.) -/
theorem absorber_of_flexBank {G : SimpleGraph V} [DecidableRel G.Adj] (β : ℝ)
    (K : FlexBank G) (hK : K.Rich β) : TriangleAbsorber G K.core β := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨i, hi, hti⟩ := Finset.mem_biUnion.mp ht
    exact K.base_clique i hi t hti
  · exact edgeDisjoint_biUnion_of_spans K.I K.base (fun i => coveredEdges (K.base i))
      K.base_disj (fun _ _ => Finset.Subset.refl _) K.base_cross
  · intro L hLsub hLdisj hLcard hLdiv hLeven
    obtain ⟨J, f, hJI, hf, hfd, hfL⟩ := hK L hLsub hLdisj hLcard hLdiv hLeven
    have hfbase : ∀ i ∈ J, Disjoint (f i) (coveredEdges K.core) := by
      intro i hi
      refine Finset.disjoint_of_subset_left ?_ hLdisj
      rw [← hfL]
      exact Finset.subset_biUnion_of_mem f hi
    obtain ⟨P, hcl, hd, hcov⟩ := flex_reroute K J f hJI hf hfd hfbase
    exact ⟨P, hcl, hd, by rw [hcov, hfL]⟩

/-- **Richness from a chunk decomposition.**  Suppose all units of the bank can absorb every
config in a common family `C` of "chunks", and every admissible leftover `L` splits into at most
`|I|` pairwise disjoint chunks of `C`.  Then the bank is `β`-rich.  This separates the two
independent obligations: (i) building *interchangeable* chunk-absorbing units, (ii) the purely
combinatorial splitting of a triangle-divisible leftover into absorbable chunks. -/
theorem rich_of_chunk_split {G : SimpleGraph V} [DecidableRel G.Adj] (β : ℝ)
    (K : FlexBank G) (C : Finset (Sym2 V) → Prop)
    (huniv : ∀ i ∈ K.I, ∀ S, C S → K.cfg i S)
    (hsplit : ∀ L : Finset (Sym2 V), L ⊆ G.edgeFinset → Disjoint L (coveredEdges K.core) →
      (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 → 3 ∣ L.card →
      (∀ v : V, Even ((L.filter (fun e => v ∈ e)).card)) →
      ∃ parts : Finset (Finset (Sym2 V)), (∀ p ∈ parts, C p) ∧
        (∀ p ∈ parts, ∀ q ∈ parts, p ≠ q → Disjoint p q) ∧ parts.biUnion id = L ∧ parts.card ≤ K.I.card) :
    K.Rich β := by
  classical
  intro L hLsub hLdisj hLcard hLdiv hLeven
  obtain ⟨parts, hC, hpd, hcov, hcard⟩ := hsplit L hLsub hLdisj hLcard hLdiv hLeven
  -- choose `|parts|` distinct units and a bijection onto the chunks
  obtain ⟨J, hJI, hJcard⟩ := Finset.exists_subset_card_eq hcard
  let g : {i // i ∈ J} ≃ {p // p ∈ parts} :=
    J.equivFin.trans ((finCongr hJcard).trans parts.equivFin.symm)
  refine ⟨J, fun i => if h : i ∈ J then (g ⟨i, h⟩ : Finset (Sym2 V)) else ∅, hJI, ?_, ?_, ?_⟩
  · intro i hi
    dsimp only
    rw [dif_pos hi]
    exact huniv i (hJI hi) _ (hC _ (g ⟨i, hi⟩).2)
  · intro i hi j hj hij
    dsimp only
    rw [dif_pos hi, dif_pos hj]
    refine hpd _ (g ⟨i, hi⟩).2 _ (g ⟨j, hj⟩).2 ?_
    intro h
    exact hij (congrArg Subtype.val (g.injective (Subtype.ext h)))
  · rw [← hcov]
    ext e
    simp only [Finset.mem_biUnion, id]
    constructor
    · rintro ⟨i, hi, he⟩
      rw [dif_pos hi] at he
      exact ⟨_, (g ⟨i, hi⟩).2, he⟩
    · rintro ⟨p, hp, he⟩
      refine ⟨(g.symm ⟨p, hp⟩ : ℕ), (g.symm ⟨p, hp⟩).2, ?_⟩
      rw [dif_pos (g.symm ⟨p, hp⟩).2]
      simpa using he

/-- A witness that the flexible interface is **not** subject to the obstruction that kills the
rigid one: a single unit with empty base whose configs are the edge sets of all triangles of
`G`.  It absorbs each such config by the corresponding triangle. -/
noncomputable def triangleUnitBank (G : SimpleGraph V) [DecidableRel G.Adj] : FlexBank G where
  I := {0}
  base := fun _ => ∅
  cfg := fun _ S => ∃ t : Finset V, G.IsNClique 3 t ∧ S = triEdges t
  absorb := fun _ S => if h : ∃ t : Finset V, G.IsNClique 3 t ∧ S = triEdges t then {h.choose}
    else ∅
  base_clique := by intro i _ t ht; simp at ht
  base_disj := by intro i _ t ht; simp at ht
  base_cross := by intro i hi j hj hij; simp only [Finset.mem_singleton] at hi hj; omega
  absorb_clique := by
    intro i _ S hS t ht
    rw [dif_pos hS, Finset.mem_singleton] at ht
    subst ht
    exact hS.choose_spec.1
  absorb_disj := by
    intro i _ S hS t₁ ht₁ t₂ ht₂ hne
    rw [dif_pos hS, Finset.mem_singleton] at ht₁ ht₂
    exact absurd (ht₁.trans ht₂.symm) hne
  absorb_cov := by
    intro i _ S hS
    rw [dif_pos hS]
    simp only [coveredEdges, Finset.biUnion_empty, Finset.empty_union,
      Finset.singleton_biUnion]
    exact hS.choose_spec.2.symm

/-- **The flexible interface is genuinely more permissive.**  A single unit of
`triangleUnitBank` absorbs the edge set of *every* triangle of `G`; in particular it absorbs two
triangles sharing an edge, which is exactly what the rigid bank interface cannot do
(`rigid_bank_hrich_elim`). -/
theorem triangleUnitBank_cfg (G : SimpleGraph V) [DecidableRel G.Adj] {t : Finset V}
    (ht : G.IsNClique 3 t) : (triangleUnitBank G).cfg 0 (triEdges t) := ⟨t, ht, rfl⟩

/-- The remaining research kernel of B2/B3, isolated: for every `ε > 0` there are thresholds
`n₀, β₀ > 0` such that every graph with `n ≥ n₀` and `δ(G) ≥ (9/10+ε)n` carries a `β`-rich
flexible transformer bank whose removal leaves min degree `≥ 9n/10`. -/
def FlexBankExists (ε : ℝ) : Prop :=
  ∃ (n₀ : ℕ) (β₀ : ℝ), 0 < β₀ ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ),
      n₀ ≤ Fintype.card V → 0 < β → β ≤ β₀ →
      (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
      ∃ K : FlexBank G, K.Rich β ∧
        ∀ v, 9 * Fintype.card V ≤ 10 * (residual G K.core).degree v

end Ax2.BKLO
