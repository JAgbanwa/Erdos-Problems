import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!

This file formalizes the proof that any finite simple graph
`G` on `n` vertices satisfying the weak Clique-Drop Hypothesis (`wCDH`) has
`cp(G) ≤ 2 + (2n-1)^2 / 24`, where `cp(G)` is the minimum size of a clique edge-partition.
 This formalization was obtained by Aristotle from Harmonic (aristotle-harmonic@harmonic.fun).
 Lean version: leanprover/lean4:v4.28.0
-/

namespace WCDH

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `edgesIn G S` is the finset of edges of `G` with both endpoints in `S`. -/
noncomputable def edgesIn (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => e ∈ S.sym2)

/-- A clique edge-partition of `G`: a finset of cliques, each with at least two vertices, whose
internal edge sets are pairwise disjoint and cover all edges of `G`. -/
def IsCliqueEdgePartition (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ C ∈ P, G.IsClique (C : Set V)) ∧
  (∀ C ∈ P, 2 ≤ C.card) ∧
  ((P : Set (Finset V)).PairwiseDisjoint (edgesIn G)) ∧
  (P.biUnion (edgesIn G) = G.edgeFinset)

/-- The clique edge-partition number `cp(G)`: the minimum size of a clique edge-partition. -/
noncomputable def cp (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ P, IsCliqueEdgePartition G P ∧ P.card = k}

/-- Forward neighbours (as indices) of the `i`-th vertex under the ordering `σ`. -/
noncomputable def fwdIdx (G : SimpleGraph V) (σ : Fin (Fintype.card V) ≃ V)
    (i : Fin (Fintype.card V)) : Finset (Fin (Fintype.card V)) :=
  Finset.univ.filter (fun j => i < j ∧ G.Adj (σ i) (σ j))

/-- The forward degree `d_i^+`. -/
noncomputable def dPlus (G : SimpleGraph V) (σ : Fin (Fintype.card V) ≃ V)
    (i : Fin (Fintype.card V)) : ℕ := (fwdIdx G σ i).card

/-- `σ` is a perfect elimination ordering of `G` if each forward neighbourhood is a clique. -/
def IsPEO (G : SimpleGraph V) (σ : Fin (Fintype.card V) ≃ V) : Prop :=
  ∀ i, G.IsClique (((fwdIdx G σ i).image σ : Finset V) : Set V)

/-- `G` is chordal if it admits a perfect elimination ordering. -/
def IsChordal (G : SimpleGraph V) : Prop :=
  ∃ σ : Fin (Fintype.card V) ≃ V, IsPEO G σ

/-- The weak Clique-Drop Hypothesis: `G` is chordal and has a maximum clique `K` such that
deleting its internal edges drops the clique number by at most one. -/
def wCDH (G : SimpleGraph V) : Prop :=
  IsChordal G ∧
  ∃ K : Finset V, G.IsNClique G.cliqueNum K ∧
    G.cliqueNum - 1 ≤ (G.deleteEdges ↑(edgesIn G K)).cliqueNum

/-
Basic clique-number bounds 
-/
omit [DecidableEq V] in
lemma one_le_cliqueNum [Nonempty V] (G : SimpleGraph V) : 1 ≤ G.cliqueNum := by
  refine' le_csSup _ _;
  · exact ⟨ Fintype.card V, fun n hn => by obtain ⟨ s, hs ⟩ := hn; exact hs.card_eq ▸ Finset.card_le_univ _ ⟩;
  · exact ⟨ { Classical.arbitrary V }, by simp +decide [ SimpleGraph.isNClique_iff ] ⟩

omit [DecidableEq V] in
lemma cliqueNum_le_card (G : SimpleGraph V) : G.cliqueNum ≤ Fintype.card V := by
  obtain ⟨ s, hs ⟩ := G.exists_isNClique_cliqueNum;
  exact hs.card_eq.symm ▸ Finset.card_le_univ _

lemma choose_two_mono {a b : ℕ} (h : a ≤ b) : a.choose 2 ≤ b.choose 2 := by
  exact Nat.choose_le_choose _ h

/-
Edges within a clique
-/
lemma edgesIn_subset (G : SimpleGraph V) (S : Finset V) : edgesIn G S ⊆ G.edgeFinset := by
  exact Finset.filter_subset _ _

/-
A clique of cardinality `r` has exactly `C(r,2)` internal edges.
-/
lemma card_edgesIn_clique {G : SimpleGraph V} {r : ℕ} {C : Finset V}
    (hC : G.IsNClique r C) : (edgesIn G C).card = r.choose 2 := by
  obtain ⟨hC_sub, hC_card⟩ := hC;
  -- Since $C$ is a clique, $edgesIn G C$ is exactly the set of pairs $\{a, b\}$ with $a, b \in C$ and $a \neq b$.
  have h_edgesIn_eq : edgesIn G C = Finset.image (fun (e : V × V) => s(e.1, e.2)) (Finset.offDiag C) := by
    ext e; simp [edgesIn];
    constructor <;> intro h;
    · rcases e with ⟨ a, b ⟩ ; use a, b ; aesop;
    · rcases h with ⟨ a, b, ⟨ ha, hb, hab ⟩, rfl ⟩ ; exact ⟨ by simpa [ hab ] using hC_sub ha hb hab, by simp +decide [ ha, hb ] ⟩ ;
  rw [ h_edgesIn_eq, Nat.choose_two_right ];
  have h_card_image : Finset.card (Finset.image (fun (e : V × V) => s(e.1, e.2)) (Finset.offDiag C)) * 2 = Finset.card (Finset.offDiag C) := by
    grind +suggestions;
  simp_all +decide [ mul_tsub, Finset.offDiag_card ];
  rw [ ← h_card_image, Nat.mul_div_cancel _ two_pos ]

/-
Trivial clique edge-partition into single edges.
-/
lemma cp_le_card_edges (G : SimpleGraph V) : cp G ≤ G.edgeFinset.card := by
  refine' csInf_le _ _;
  · exact ⟨ 0, fun k hk => Nat.zero_le _ ⟩;
  · refine' ⟨ G.edgeFinset.image fun e => e.toFinset, _, _ ⟩;
    · refine' ⟨ _, _, _, _ ⟩;
      · simp +decide [SimpleGraph.isClique_iff];
        rintro ⟨ a, b ⟩ hab ; simp_all +decide [ Set.Pairwise ];
        exact fun _ => hab.symm;
      · simp +decide [ SimpleGraph.edgeSet ];
        intro e he; rw [ Sym2.card_toFinset ] ; aesop;
      · intro x hx y hy hxy;
        simp_all +decide [ Finset.disjoint_left, edgesIn ];
        rcases hx with ⟨ e, he, rfl ⟩ ; rcases hy with ⟨ f, hf, rfl ⟩ ; simp_all +decide [ Finset.ext_iff, Sym2.forall ] ;
        grind +suggestions;
      · ext e; simp +decide [ edgesIn ] ;
        grind +splitIndPred;
    · refine' Finset.card_image_of_injOn _;
      intro e he e' he' h; rw [ Finset.ext_iff ] at h; aesop;

/-
One-clique compression (additive form).
-/
lemma cp_one_clique {G : SimpleGraph V} {r : ℕ} {C : Finset V} (hC : G.IsNClique r C) :
    cp G + r.choose 2 ≤ 1 + G.edgeFinset.card := by
  by_cases hr : r ≥ 2;
  · -- Exhibit the partition $P := insert C ((G.edgeFinset \ edgesIn G C).image Sym2.toFinset)$ and use `Nat.sInf_le` to get `cp G ≤ #P`.
    have hP : ∃ P : Finset (Finset V), IsCliqueEdgePartition G P ∧ P.card = 1 + (G.edgeFinset \ edgesIn G C).card := by
      refine' ⟨ Insert.insert C ( Finset.image ( fun e => e.toFinset ) ( G.edgeFinset \ edgesIn G C ) ), _, _ ⟩;
      · refine' ⟨ _, _, _, _ ⟩;
        · simp +zetaDelta at *;
          refine' ⟨ hC.1, _ ⟩;
          rintro a x hx hx' rfl; rcases x with ⟨ u, v ⟩ ; simp_all +decide [SimpleGraph.isClique_iff] ;
          simp +decide [ Set.Pairwise, hx ];
          exact fun _ => hx.symm;
        · simp +zetaDelta at *;
          refine' ⟨ _, _ ⟩;
          · exact hC.card_eq.symm ▸ hr;
          · rintro a x hx hx' rfl; exact by rw [ Sym2.card_toFinset ] ; aesop;
        · intro x hx y hy hxy;
          by_cases hx' : x = C <;> by_cases hy' : y = C <;> simp_all +decide [ Finset.disjoint_left ];
          · intro a ha hb; obtain ⟨ e, he, rfl ⟩ := hy; simp_all +decide [ edgesIn ] ;
            rcases e with ⟨ u, v ⟩ ; simp_all +decide [ Sym2.mem_iff ] ;
            cases a ; aesop;
          · intro a ha hb; obtain ⟨ e, he, rfl ⟩ := hx; simp_all +decide [ edgesIn ] ;
            rcases e with ⟨ x, y ⟩ ; rcases a with ⟨ u, v ⟩ ; aesop;
          · rcases hx with ⟨ e, ⟨ he₁, he₂ ⟩, rfl ⟩ ; rcases hy with ⟨ f, ⟨ hf₁, hf₂ ⟩, rfl ⟩ ; simp_all +decide [ edgesIn ] ;
            intro a ha ha'; contrapose! hxy; ext x; simp_all +decide [Finset.ext_iff] ;
            cases a ; cases e ; cases f ; aesop;
        · ext e; simp +decide [ edgesIn ] ;
          by_cases he : ∀ a ∈ e, a ∈ C <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
          grind;
      · rw [ Finset.card_insert_of_notMem, Finset.card_image_of_injOn ];
        · ring;
        · intro e he e' he' h; simp_all +decide [ Sym2.ext_iff ] ;
          intro x; replace h := Finset.ext_iff.mp h x; aesop;
        · simp +decide [ edgesIn ];
          intro e he h; contrapose! h; aesop;
    obtain ⟨ P, hP₁, hP₂ ⟩ := hP;
    have hP_card : cp G ≤ P.card := by
      exact Nat.sInf_le ⟨ P, hP₁, rfl ⟩;
    have hP_card : (G.edgeFinset \ edgesIn G C).card = G.edgeFinset.card - (edgesIn G C).card := by
      grind +suggestions;
    linarith [ Nat.sub_add_cancel ( show ( edgesIn G C ).card ≤ G.edgeFinset.card from Finset.card_le_card ( edgesIn_subset G C ) ), card_edgesIn_clique hC ];
  · interval_cases r <;> simp_all +decide;
    · exact le_trans ( cp_le_card_edges G ) ( Nat.le_add_left _ _ );
    · exact le_trans ( cp_le_card_edges G ) ( by simp +arith +decide )

/-
Compression by a lower bound on clique size (additive form).
-/
lemma cp_large_clique {G : SimpleGraph V} {s : ℕ} {C : Finset V}
    (hCclique : G.IsClique (C : Set V)) (hs : s ≤ C.card) :
    cp G + s.choose 2 ≤ 1 + G.edgeFinset.card := by
  refine' le_trans _ ( cp_one_clique _ );
  convert Nat.add_le_add_left ( choose_two_mono hs ) _;
  exacts [ C, ⟨ hCclique, rfl ⟩ ]

/-
Lifting across clique-edge deletion.
-/
lemma cp_lift {G : SimpleGraph V} {C : Finset V} (hC : G.IsClique (C : Set V)) :
    cp G ≤ 1 + cp (G.deleteEdges ↑(edgesIn G C)) := by
  by_cases hC2 : 2 ≤ C.card;
  · obtain ⟨Q, hQ⟩ : ∃ Q : Finset (Finset V), IsCliqueEdgePartition (G.deleteEdges (edgesIn G C)) Q ∧ Q.card = cp (G.deleteEdges (edgesIn G C)) := by
      have := Nat.sInf_mem ( show { k : ℕ | ∃ P : Finset ( Finset V ), IsCliqueEdgePartition ( G.deleteEdges ( edgesIn G C ) ) P ∧ Finset.card P = k }.Nonempty from ?_ );
      · exact this;
      · refine' ⟨ _, ⟨ Finset.image ( fun e => e.toFinset ) ( G.deleteEdges ( edgesIn G C ) |> SimpleGraph.edgeFinset ), _, rfl ⟩ ⟩;
        refine' ⟨ _, _, _, _ ⟩;
        · simp +decide [SimpleGraph.isClique_iff];
          rintro _ x hx hx' rfl; rcases x with ⟨ a, b ⟩ ; simp_all +decide [edgesIn] ;
          simp +decide [ Set.Pairwise, hx.ne ];
          exact ⟨ ⟨ hx, fun _ => hx' ⟩, fun _ => ⟨ hx.symm, fun _ => by tauto ⟩ ⟩;
        · simp +decide [ SimpleGraph.edgeSet ];
          rintro _ x hx₁ hx₂ rfl; rcases x with ⟨ u, v ⟩ ; simp_all +decide [ edgeSetEmbedding ] ;
          simp +decide [Sym2.toFinset];
          simp +decide [ Sym2.toMultiset, hx₁.ne ];
        · intro e he f hf hne; simp_all +decide [ Finset.disjoint_left, edgesIn ] ;
          rcases he with ⟨ e, ⟨ he₁, x, hx₁, hx₂ ⟩, rfl ⟩ ; rcases hf with ⟨ f, ⟨ hf₁, y, hy₁, hy₂ ⟩, rfl ⟩ ; simp_all +decide [ Finset.ext_iff, Sym2.forall ] ;
          grind +suggestions;
        · ext e; simp +decide [ edgesIn ] ;
          grind +qlia;
    -- Set `P := insert C Q`; it suffices to show `IsCliqueEdgePartition G P`, because then `cp G ≤ #P ≤ 1 + #Q = 1 + cp H` (`Finset.card_insert_le`).
    set P : Finset (Finset V) := insert C Q
    have hP : IsCliqueEdgePartition G P := by
      refine' ⟨ _, _, _, _ ⟩;
      · simp +zetaDelta at *;
        exact ⟨ hC, fun a ha => hQ.1.1 a ha |> fun h => h.mono ( by aesop_cat ) ⟩;
      · exact fun x hx => by rcases Finset.mem_insert.mp hx with ( rfl | hx ) <;> [ exact hC2; exact hQ.1.2.1 x hx ] ;
      · have h_disjoint : ∀ D ∈ Q, Disjoint (edgesIn G D) (edgesIn G C) := by
          intro D hD
          have hD_clique : (G.deleteEdges (edgesIn G C)).IsClique (D : Set V) := by
            exact hQ.1.1 D hD;
          simp_all +decide [ Finset.disjoint_left, edgesIn ];
          intro e he hD; contrapose! hD_clique; simp_all +decide [ SimpleGraph.isClique_iff, SimpleGraph.deleteEdges ] ;
          rcases e with ⟨ a, b ⟩ ; simp_all +decide ;
          exact fun h => by have := h hD.1 hD.2 ( by aesop ) ; aesop;
        intro D hD E hE hDE; by_cases hDQ : D ∈ Q <;> by_cases hEQ : E ∈ Q <;> simp_all +decide [ Finset.disjoint_left ] ;
        · intro a ha hb; have := hQ.1.2.2.1 hDQ hEQ; simp_all +decide [ Finset.disjoint_left ] ;
          contrapose! this; simp_all +decide [ edgesIn ] ;
          exact ⟨ a, ⟨ ⟨ ha.1, fun _ => h_disjoint D hDQ ha.1 ha.2 ⟩, ha.2 ⟩, ⟨ ha.1, fun _ => h_disjoint D hDQ ha.1 ha.2 ⟩, hb ⟩;
        · grind;
        · grind +splitImp;
        · grind;
      · have h_biUnion : P.biUnion (edgesIn G) = edgesIn G C ∪ Q.biUnion (edgesIn (G.deleteEdges (edgesIn G C))) := by
          ext e; simp [P, edgesIn];
          grind;
        have := hQ.1.2.2.2;
        simp_all +decide [ SimpleGraph.edgeFinset_deleteEdges ];
        exact fun x hx => Finset.mem_filter.mp hx |>.1;
    exact le_trans ( Nat.sInf_le ⟨ P, hP, rfl ⟩ ) ( by rw [ ← hQ.2 ] ; exact Nat.le_trans ( Finset.card_insert_le _ _ ) ( by linarith ) );
  · interval_cases _ : #C <;> simp_all +decide [ edgesIn ];
    rw [ Finset.card_eq_one ] at *;
    convert Nat.le_add_left _ _;
    ext v w; aesop;

/-
Deleting the internal edges of `S` removes exactly `edgesIn G S` from the edge set.
-/
lemma card_edges_delete (G : SimpleGraph V) (S : Finset V) :
    (G.deleteEdges ↑(edgesIn G S)).edgeFinset.card + (edgesIn G S).card
      = G.edgeFinset.card := by
  rw [ ← Finset.card_union_of_disjoint, Finset.union_comm ];
  · congr with e ; simp +contextual [ edgesIn ];
  · simp +decide;
    exact Finset.sdiff_disjoint

/-
Two-step compression (additive form).
-/
lemma cp_two_step {G : SimpleGraph V} {K : Finset V}
    (hK : G.IsNClique G.cliqueNum K)
    (hdrop : G.cliqueNum - 1 ≤ (G.deleteEdges ↑(edgesIn G K)).cliqueNum) :
    cp G + (G.cliqueNum).choose 2 + (G.cliqueNum - 1).choose 2 ≤ 2 + G.edgeFinset.card := by
  -- By `cp_lift` with `C := K` (clique `hK.isClique`): `cp G ≤ 1 + cp (G.deleteEdges ↑(edgesIn G K))`.
  have cp_lift' : cp G ≤ 1 + cp (G.deleteEdges ↑(edgesIn G K)) := by
    apply cp_lift; exact hK.isClique;
  -- By `cp_large_clique` to `H` with this clique and `s := ω - 1`:
  have cp_large_clique' : cp (G.deleteEdges ↑(edgesIn G K)) + (G.cliqueNum - 1).choose 2 ≤ 1 + (G.deleteEdges ↑(edgesIn G K)).edgeFinset.card := by
    obtain ⟨ s, hs ⟩ := ( G.deleteEdges ↑ ( edgesIn G K ) ).exists_isNClique_cliqueNum;
    convert cp_large_clique _ _;
    exacts [ s, hs.1, by simpa [ hs.2 ] using hdrop ];
  linarith [ card_edges_delete G K, card_edgesIn_clique hK ]

/-
Forward-edge count: the number of edges equals the sum of forward degrees.
-/
lemma forward_count (G : SimpleGraph V) (σ : Fin (Fintype.card V) ≃ V) :
    G.edgeFinset.card = ∑ i, dPlus G σ i := by
  have h_bij : G.edgeFinset.card = (∑ i : Fin (Fintype.card V), (Finset.univ.filter (fun j => i < j ∧ G.Adj (σ i) (σ j))).card) := by
    have : G.edgeFinset = Finset.image (fun (p : Fin (Fintype.card V) × Fin (Fintype.card V)) => Sym2.mk (σ p.1, σ p.2)) (Finset.filter (fun (p : Fin (Fintype.card V) × Fin (Fintype.card V)) => p.1 < p.2 ∧ G.Adj (σ p.1) (σ p.2)) (Finset.univ : Finset (Fin (Fintype.card V) × Fin (Fintype.card V)))) := by
      ext ⟨ u, v ⟩ ; simp +decide ;
      constructor;
      · intro huv
        obtain ⟨a, b, hab⟩ : ∃ a b : Fin (Fintype.card V), σ a = u ∧ σ b = v ∧ a ≠ b := by
          exact ⟨ σ.symm u, σ.symm v, by simp +decide, by simp +decide, by intro h; have := σ.symm.injective h; aesop ⟩;
        cases lt_or_gt_of_ne hab.2.2 <;> [ exact ⟨ a, b, ⟨ ‹_›, by aesop ⟩, Or.inl ⟨ hab.1, hab.2.1 ⟩ ⟩ ; exact ⟨ b, a, ⟨ ‹_›, by simpa [ SimpleGraph.adj_comm, hab.1, hab.2.1 ] using huv ⟩, Or.inr ⟨ hab.2.1, hab.1 ⟩ ⟩ ];
      · rintro ⟨ a, b, ⟨ hab, h ⟩, ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) ⟩ <;> simp_all +decide [ SimpleGraph.adj_comm ]
    rw [ this, Finset.card_image_of_injOn, Finset.card_filter ];
    · erw [ Finset.sum_product ] ; aesop;
    · intro p hp q hq h; simp_all +decide ;
      grind;
  exact h_bij

/-
Forward-degree bound from the clique number.
-/
lemma dPlus_le_cliqueNum {G : SimpleGraph V} {σ : Fin (Fintype.card V) ≃ V}
    (hσ : IsPEO G σ) (i : Fin (Fintype.card V)) :
    dPlus G σ i + 1 ≤ G.cliqueNum := by
  have h_insert : G.IsClique ({σ i} ∪ (fwdIdx G σ i).image σ) := by
    simp_all +decide [ IsPEO, Set.Pairwise ];
    simp_all +decide [ fwdIdx ];
    exact hσ i;
  refine' le_csSup _ _ <;> norm_num +zetaDelta at *;
  · exact ⟨ Fintype.card V, fun n hn => by obtain ⟨ s, hs ⟩ := hn; exact hs.card_eq ▸ Finset.card_le_univ _ ⟩;
  · refine' ⟨ { σ i } ∪ ( fwdIdx G σ i ).image σ, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.IsClique ];
    rw [ Finset.card_insert_of_notMem, Finset.card_image_of_injective _ σ.injective ] <;> simp +decide [ dPlus ];
    exact fun h => lt_irrefl _ ( Finset.mem_filter.mp h |>.2.1 )

/-
Forward-degree bound from the position in the ordering.
-/
omit [DecidableEq V] in
lemma dPlus_le_index (G : SimpleGraph V) (σ : Fin (Fintype.card V) ≃ V)
    (i : Fin (Fintype.card V)) :
    dPlus G σ i ≤ Fintype.card V - 1 - (i : ℕ) := by
  convert Set.ncard_le_ncard ( show ( Set.Ioi i : Set ( Fin ( Fintype.card V ) ) ) ⊇ ( fun j => j ) '' { j | i < j ∧ G.Adj ( σ i ) ( σ j ) } from ?_ ) using 1;
  · simp +decide [ dPlus, Set.ncard_eq_toFinset_card' ];
    exact congr_arg Finset.card ( by ext; simp +decide [ fwdIdx ] );
  · simp +decide [ Set.ncard_eq_toFinset_card' ];
  · grind

/-
A triangular-sum identity: `∑_{m<n} min (ω-1) m = C(ω,2) + (n-ω)(ω-1)` when `ω ≤ n`.
-/
lemma sum_min_eq {n omega : ℕ} (h : omega ≤ n) :
    ∑ m ∈ Finset.range n, min (omega - 1) m = omega.choose 2 + (n - omega) * (omega - 1) := by
  induction' omega with omega ih;
  · norm_num;
  · rcases omega with ( _ | omega ) <;> simp_all +decide [ Nat.choose_two_right ];
    convert congr_arg ( · + ( n - ( omega + 1 ) ) ) ( ih ( Nat.lt_of_succ_lt h ) ) using 1;
    · rw [ show ( ∑ x ∈ Finset.range n, min ( omega + 1 ) x ) = ∑ x ∈ Finset.range n, min omega x + ∑ x ∈ Finset.range n, if x ≥ omega + 1 then 1 else 0 from ?_, Finset.sum_ite ];
      · rw [ show ( Finset.filter ( fun x => omega + 1 ≤ x ) ( Finset.range n ) ) = Finset.Ico ( omega + 1 ) n by ext; aesop ] ; simp +arith +decide;
      · rw [ ← Finset.sum_add_distrib ] ; congr ; ext x ; split_ifs <;> cases min_cases ( omega + 1 ) x <;> cases min_cases omega x <;> linarith;
    · rw [ show n - ( omega + 1 ) = ( n - ( omega + 1 + 1 ) ) + 1 by omega ] ; grind

/-
The combined sum bound on forward degrees.
-/
lemma sum_dPlus_le {G : SimpleGraph V} {σ : Fin (Fintype.card V) ≃ V} (hσ : IsPEO G σ) :
    ∑ i, dPlus G σ i
      ≤ (G.cliqueNum).choose 2 + (Fintype.card V - G.cliqueNum) * (G.cliqueNum - 1) := by
  refine' le_trans _ ( sum_min_eq _ |> le_of_eq );
  · convert Finset.sum_le_sum fun i _ => show dPlus G σ i ≤ min ( G.cliqueNum - 1 ) ( Fintype.card V - 1 - ( i : ℕ ) ) from ?_ using 1;
    · rw [ ← Finset.sum_range_reflect, Finset.sum_range ];
    · exact le_min ( Nat.le_sub_one_of_lt ( dPlus_le_cliqueNum hσ i ) ) ( dPlus_le_index G σ i );
  · exact cliqueNum_le_card G

/-
Edge bound for chordal graphs.
-/
lemma edge_bound {G : SimpleGraph V} (hG : IsChordal G) :
    G.edgeFinset.card
      ≤ (G.cliqueNum).choose 2 + (Fintype.card V - G.cliqueNum) * (G.cliqueNum - 1) := by
  obtain ⟨ σ, hσ ⟩ := hG;
  rw [ forward_count ];
  convert sum_dPlus_le hσ

/-
The arithmetic core of the conditional bound, packaged over `ℚ`.
-/
lemma arith_final (cpG n omega EE : ℕ) (hpos : 1 ≤ omega) (hle : omega ≤ n)
    (h1 : cpG + omega.choose 2 + (omega - 1).choose 2 ≤ 2 + EE)
    (h2 : EE ≤ omega.choose 2 + (n - omega) * (omega - 1)) :
    (cpG : ℚ) ≤ 2 + (2 * (n : ℚ) - 1) ^ 2 / 24 := by
  -- From `h1` and `h2`, we have:
  have h3 : cpG + (omega - 1).choose 2 ≤ 2 + (n - omega) * (omega - 1) := by
    grind;
  rcases omega with ( _ | _ | omega ) <;> simp_all +decide [ Nat.choose_two_right ];
  · exact le_add_of_le_of_nonneg ( mod_cast h3 ) ( by positivity );
  · rw [ add_div', le_div_iff₀ ] <;> norm_cast;
    rw [ Int.subNatNat_eq_coe ] ; push_cast ; nlinarith only [ sq_nonneg ( 6 * ( omega + 1 ) - ( 2 * n - 1 ) : ℤ ), h3, Nat.div_mul_cancel ( show 2 ∣ ( omega + 1 ) * omega from Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.add_mod, Nat.mod_two_of_bodd ] ) ), Nat.sub_add_cancel ( by linarith : omega + 1 + 1 ≤ n ) ]

/-- **Conditional bound under wCDH.** If `G` satisfies the weak Clique-Drop Hypothesis and has
`n` vertices, then `cp(G) ≤ 2 + (2n-1)^2 / 24`. -/
theorem main_theorem [Nonempty V] {G : SimpleGraph V} (hw : wCDH G) :
    (cp G : ℚ) ≤ 2 + (2 * (Fintype.card V : ℚ) - 1) ^ 2 / 24 := by
  obtain ⟨hchordal, K, hK, hdrop⟩ := hw
  have hstep := cp_two_step hK hdrop
  have hbound := edge_bound hchordal
  exact arith_final (cp G) (Fintype.card V) G.cliqueNum G.edgeFinset.card
    (one_le_cliqueNum G) (cliqueNum_le_card G) hstep hbound

#print axioms main_theorem

end WCDH
