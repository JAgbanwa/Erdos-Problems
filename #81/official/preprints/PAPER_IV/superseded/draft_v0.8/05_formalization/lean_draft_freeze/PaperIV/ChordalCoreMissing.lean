import PaperIV.RD09RootedOrderAdapter
import PaperIV.RD09SplitEditAccount
import PaperIV.NearH1Calibration
import Mathlib.Tactic

/-!
# Missing pairs forced by clique codimension in a chordal core

This file proves the last discrete structural estimate used by the near H1
calibration.  The proof is the standard sharp PEO count, but is phrased using
the rooted elimination order already used by RD09.
-/

namespace PaperIV.ChordalCoreMissing

open Finset PaperIV.Model
open scoped symmDiff
open PaperIV.RootedEliminationOrder PaperIV.RD09RootedOrderAdapter

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every graph edge occurs exactly once as an earlier vertex together with a
later neighbour in any total rooted elimination order. -/
theorem card_graphEdges_eq_sum_laterNeighbors {P : Finset V}
    (O : Order G P) :
    (graphEdges G).card =
      ∑ v : V, (laterCoreNeighbors O (Function.Embedding.refl V) G v).card := by
  classical
  let L : V → Finset V :=
    fun v => laterCoreNeighbors O (Function.Embedding.refl V) G v
  have hcard : (Finset.univ.sigma L).card = (graphEdges G).card := by
    apply Finset.card_bij (fun q _ => s(q.1, q.2))
    · intro q hq
      have hmem : q.2 ∈ L q.1 := (Finset.mem_sigma.mp hq).2
      have hadj : G.Adj q.1 q.2 :=
        (mem_laterCoreNeighbors O (Function.Embedding.refl V)).mp hmem |>.1
      rw [mem_graphEdges, SimpleGraph.mem_edgeSet]
      exact hadj
    · intro q₁ hq₁ q₂ hq₂ heq
      have hlt₁ : O.index q₁.1 < O.index q₁.2 :=
        (mem_laterCoreNeighbors O (Function.Embedding.refl V)).mp
          (Finset.mem_sigma.mp hq₁).2 |>.2
      have hlt₂ : O.index q₂.1 < O.index q₂.2 :=
        (mem_laterCoreNeighbors O (Function.Embedding.refl V)).mp
          (Finset.mem_sigma.mp hq₂).2 |>.2
      rw [Sym2.eq, Sym2.rel_iff] at heq
      rcases heq with h | h
      · exact Sigma.ext h.1 (heq_of_eq h.2)
      · exfalso
        have : O.index q₁.1 = O.index q₂.2 := congrArg O.index h.1
        have : O.index q₁.2 = O.index q₂.1 := congrArg O.index h.2
        omega
    · intro e he
      let a := edgeEarlier O (Function.Embedding.refl V) e
      let b := edgeLater O (Function.Embedding.refl V) e
      have hb : b ∈ L a := by
        exact edgeLater_mem_laterCoreNeighbors O (Function.Embedding.refl V) he
      refine ⟨⟨a, b⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hb⟩, ?_⟩
      exact (edge_eq_oriented O (Function.Embedding.refl V) e).symm
  rw [← hcard]
  simp [L, Finset.card_sigma]

/-- When the order ends in a clique `P`, the rows indexed by `P` count
exactly the edges internal to `P`. -/
theorem sum_root_laterNeighbors_eq_choose {P : Finset V}
    (O : Order G P) (hP : G.IsClique (P : Set V)) :
    (∑ v ∈ P,
      (laterCoreNeighbors O (Function.Embedding.refl V) G v).card) =
      Nat.choose P.card 2 := by
  classical
  let L : V → Finset V :=
    fun v => laterCoreNeighbors O (Function.Embedding.refl V) G v
  have hcard : (P.sigma L).card = (PaperIV.RootVocab.rootEdges G P).card := by
    apply Finset.card_bij (fun q _ => s(q.1, q.2))
    · intro q hq
      have hq' := Finset.mem_sigma.mp hq
      have hmem : q.2 ∈ L q.1 := hq'.2
      have hadj : G.Adj q.1 q.2 :=
        (mem_laterCoreNeighbors O (Function.Embedding.refl V)).mp hmem |>.1
      apply Finset.mem_filter.mpr
      refine ⟨G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hadj), ?_⟩
      intro z hz
      simp only [Sym2.toFinset_mk_eq, Finset.mem_insert,
        Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hq'.1
      · by_contra hnot
        have hlt : O.index q.1 < O.index q.2 :=
          (mem_laterCoreNeighbors O (Function.Embedding.refl V)).mp hmem |>.2
        exact (lt_asymm hlt (outside_before_root O hnot hq'.1))
    · intro q₁ hq₁ q₂ hq₂ heq
      have hlt₁ : O.index q₁.1 < O.index q₁.2 :=
        (mem_laterCoreNeighbors O (Function.Embedding.refl V)).mp
          (Finset.mem_sigma.mp hq₁).2 |>.2
      have hlt₂ : O.index q₂.1 < O.index q₂.2 :=
        (mem_laterCoreNeighbors O (Function.Embedding.refl V)).mp
          (Finset.mem_sigma.mp hq₂).2 |>.2
      rw [Sym2.eq, Sym2.rel_iff] at heq
      rcases heq with h | h
      · exact Sigma.ext h.1 (heq_of_eq h.2)
      · exfalso
        have : O.index q₁.1 = O.index q₂.2 := congrArg O.index h.1
        have : O.index q₁.2 = O.index q₂.1 := congrArg O.index h.2
        omega
    · intro e he
      have heGraph : e ∈ graphEdges G := by
        exact (Finset.mem_filter.mp he).1
      let a := edgeEarlier O (Function.Embedding.refl V) e
      let b := edgeLater O (Function.Embedding.refl V) e
      have hab := edge_eq_oriented O (Function.Embedding.refl V) e
      have ha : a ∈ P := by
        apply (Finset.mem_filter.mp he).2
        rw [hab]
        exact Sym2.mem_toFinset.mpr (Sym2.mem_mk_left a b)
      have hb : b ∈ L a := by
        exact edgeLater_mem_laterCoreNeighbors O
          (Function.Embedding.refl V) heGraph
      refine ⟨⟨a, b⟩, Finset.mem_sigma.mpr ⟨ha, hb⟩, ?_⟩
      exact hab.symm
  calc
    (∑ v ∈ P,
        (laterCoreNeighbors O (Function.Embedding.refl V) G v).card) =
        (P.sigma L).card := by rw [Finset.card_sigma]
    _ = (PaperIV.RootVocab.rootEdges G P).card := hcard
    _ = Nat.choose P.card 2 :=
      PaperIV.RootVocab.card_rootEdges _ P hP

/-- Sharp PEO edge bound: if the terminal root is a maximum clique, every
outside row has width at most `|P|-1`, while the root rows contribute exactly
`choose(|P|,2)`. -/
theorem card_graphEdges_le_of_maximumClique {P : Finset V}
    (O : Order G P) (hP : G.IsMaximumClique P) :
    (graphEdges G).card ≤ Nat.choose P.card 2 +
      (Fintype.card V - P.card) * (P.card - 1) := by
  classical
  let L : V → Finset V :=
    fun v => laterCoreNeighbors O (Function.Embedding.refl V) G v
  have hcliqueNum : G.cliqueNum = P.card :=
    (SimpleGraph.maximumClique_card_eq_cliqueNum P hP).symm
  have hout : ∑ v ∈ PaperIV.RootVocab.outsideVertices P, (L v).card ≤
      (PaperIV.RootVocab.outsideVertices P).card * (P.card - 1) := by
    apply Finset.sum_le_card_nsmul
    intro v hv
    simpa [L, hcliqueNum] using
      card_laterCoreNeighbors_le_cliqueNum_sub_one O
        (Function.Embedding.refl V)
        (fun _ _ h => h) (fun _ _ h => h) v
  have hsplit : ∑ v : V, (L v).card =
      (∑ v ∈ P, (L v).card) +
        ∑ v ∈ PaperIV.RootVocab.outsideVertices P, (L v).card := by
    rw [← Finset.sum_union (PaperIV.RootVocab.root_disjoint_outside P)]
    rw [PaperIV.RootVocab.root_union_outside]
  rw [card_graphEdges_eq_sum_laterNeighbors O]
  rw [show (∑ v : V, (L v).card) = _ from hsplit]
  rw [show (∑ v ∈ P, (L v).card) = Nat.choose P.card 2 by
    simpa [L] using sum_root_laterNeighbors_eq_choose O hP.isClique]
  rw [PaperIV.RootVocab.card_outsideVertices] at hout
  omega

/-- Arithmetic form of the sharp PEO count.  A clique deficit of `u` vertices
forces at least `choose(u+1,2)` missing pairs. -/
theorem choose_codimension_le_complete_sub_edges {P : Finset V}
    (O : Order G P) (hP : G.IsMaximumClique P) (hPne : P.Nonempty) :
    Nat.choose (Fintype.card V - P.card + 1) 2 ≤
      Nat.choose (Fintype.card V) 2 - (graphEdges G).card := by
  have hp : 1 ≤ P.card := Finset.one_le_card.mpr hPne
  have hpk : P.card ≤ Fintype.card V := by
    simpa using Finset.card_le_univ P
  have he := card_graphEdges_le_of_maximumClique O hP
  have heQ : ((graphEdges G).card : ℚ) ≤
      (Nat.choose P.card 2 : ℕ) +
        (Fintype.card V - P.card) * (P.card - 1) := by
    exact_mod_cast he
  norm_num [Nat.cast_choose_two, Nat.cast_sub hpk,
    Nat.cast_sub hp] at heQ
  have hgoalQ :
      ((Nat.choose (Fintype.card V - P.card + 1) 2 : ℕ) : ℚ) +
          (graphEdges G).card ≤ Nat.choose (Fintype.card V) 2 := by
    norm_num [Nat.cast_choose_two, Nat.cast_sub hpk]
    nlinarith
  have hecomplete : (graphEdges G).card ≤ Nat.choose (Fintype.card V) 2 := by
    have hnonneg : (0 : ℚ) ≤
        (Nat.choose (Fintype.card V - P.card + 1) 2 : ℕ) := by positivity
    exact_mod_cast (le_trans (le_add_of_nonneg_left hnonneg) hgoalQ)
  rw [Nat.le_sub_iff_add_le hecomplete]
  exact_mod_cast hgoalQ

/-- Chordal specialization: the maximum clique itself can be prescribed as
the terminal root, so the codimension bound is unconditional once that clique
is nonempty. -/
theorem choose_codimension_le_missing_of_chordal
    (hchordal : PaperIV.IsChordal G) {P : Finset V}
    (hP : G.IsMaximumClique P) (hPne : P.Nonempty) :
    Nat.choose (Fintype.card V - P.card + 1) 2 ≤
      Nat.choose (Fintype.card V) 2 - (graphEdges G).card := by
  let O := Classical.choice (exists_order P hchordal hP.isClique)
  exact choose_codimension_le_complete_sub_edges O hP hPne

set_option maxHeartbeats 800000 in
/-- Edges of the induced core are exactly the ambient edges with both
endpoints in that core. -/
theorem card_induce_eq_card_rootEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) :
    (G.induce (C : Set V)).edgeFinset.card =
      (PaperIV.RootVocab.rootEdges G C).card := by
  classical
  let f : (C : Set V) ↪ V := Function.Embedding.subtype (fun x => x ∈ (C : Set V))
  apply Finset.card_bij (fun e _ => f.sym2Map e)
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · simpa [f, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      · intro z hz
        simp [f] at hz
        rcases hz with rfl | rfl
        · exact x.2
        · exact y.2
  · intro e₁ he₁ e₂ he₂ h
    exact f.sym2Map.injective h
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have he' := Finset.mem_filter.mp he
      have hx : x ∈ C := he'.2 (by simp)
      have hy : y ∈ C := he'.2 (by simp)
      let x' : (C : Set V) := ⟨x, hx⟩
      let y' : (C : Set V) := ⟨y, hy⟩
      refine ⟨s(x', y'), ?_, ?_⟩
      · simpa [x', y', SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] using he'.1
      · change s(x, y) = s(x, y)
        rfl

/-- The missing pairs inside a complete-split comparator core are literal edit
edges.  This is the set-theoretic bridge from the chordal codimension estimate
to the edit metric used by the near calibration. -/
theorem core_missing_le_edit
    (G S : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel S.Adj]
    (C : Finset V)
    (hS : ∀ x y, S.Adj x y ↔
      (PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C)).Adj x y) :
    Nat.choose C.card 2 - (G.induce (C : Set V)).edgeFinset.card ≤
      PaperIV.EditMetric.editDist G.edgeFinset S.edgeFinset := by
  classical
  let R := PaperIV.RootVocab.rootEdges G C
  have hRsub : R ⊆ pieceEdges C := by
    intro e he
    have he' := Finset.mem_filter.mp he
    induction e using Sym2.ind with
    | _ x y =>
      rw [mem_pieceEdges_mk]
      have hx : x ∈ C := he'.2 (by simp)
      have hy : y ∈ C := he'.2 (by simp)
      have hadj : G.Adj x y := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he'.1
      exact ⟨hx, hy, hadj.ne⟩
  have hmissingSub : pieceEdges C \ R ⊆ G.edgeFinset ∆ S.edgeFinset := by
    intro e he
    have he' := Finset.mem_sdiff.mp he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy := mem_pieceEdges_mk.mp he'.1
      have hSadj : S.Adj x y := (hS x y).mpr
        (PaperIV.SplitUniformIncidence.splitGraph_adj_inner hxy.1 hxy.2.1 hxy.2.2)
      have heS : s(x, y) ∈ S.edgeFinset :=
        S.mem_edgeFinset.mpr (S.mem_edgeSet.mpr hSadj)
      have heNotG : s(x, y) ∉ G.edgeFinset := by
        intro heG
        apply he'.2
        apply Finset.mem_filter.mpr
        refine ⟨heG, ?_⟩
        intro z hz
        simp only [Sym2.toFinset_mk_eq, Finset.mem_insert,
          Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hxy.1
        · exact hxy.2.1
      exact Finset.mem_symmDiff.mpr (Or.inr ⟨heS, heNotG⟩)
  calc
    Nat.choose C.card 2 - (G.induce (C : Set V)).edgeFinset.card =
        (pieceEdges C \ R).card := by
      rw [Finset.card_sdiff_of_subset hRsub, card_pieceEdges,
        card_induce_eq_card_rootEdges]
    _ ≤ (G.edgeFinset ∆ S.edgeFinset).card :=
      Finset.card_le_card hmissingSub
    _ = PaperIV.EditMetric.editDist G.edgeFinset S.edgeFinset := rfl

/-- A nonempty comparator core in a chordal graph contains a maximum clique
whose excluded vertices satisfy the quadratic edit bound required by the near
calibration. -/
theorem exists_core_clique_with_quadratic_edit_bound
    (G S : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel S.Adj]
    (hchordal : PaperIV.IsChordal G) (C : Finset V) (hC : C.Nonempty)
    (hS : ∀ x y, S.Adj x y ↔
      (PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C)).Adj x y) :
    ∃ P : Finset V, P ⊆ C ∧ G.IsClique (P : Set V) ∧ P.Nonempty ∧
      Nat.choose ((C \ P).card + 1) 2 ≤
      PaperIV.EditMetric.editDist G.edgeFinset S.edgeFinset := by
  classical
  letI : Fintype (C : Set V) := inferInstance
  let H := G.induce (C : Set V)
  obtain ⟨Q, hQ⟩ := SimpleGraph.maximumClique_exists (G := H)
  obtain ⟨c, hc⟩ := hC
  let c' : (C : Set V) := ⟨c, hc⟩
  have hQne : Q.Nonempty := by
    rw [← Finset.card_pos]
    have hOne : 1 ≤ Q.card := by
      simpa using hQ.maximum {c'} (by simp)
    omega
  let f : (C : Set V) ↪ V := Function.Embedding.subtype (fun x => x ∈ (C : Set V))
  let P : Finset V := Q.map f
  have hPC : P ⊆ C := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hx
    exact q.2
  have hPclique : G.IsClique (P : Set V) := by
    intro x hx y hy hxy
    obtain ⟨qx, hqx, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨qy, hqy, rfl⟩ := Finset.mem_map.mp hy
    exact hQ.isClique (by simpa using hqx) (by simpa using hqy)
      (fun h => hxy (congrArg f h))
  have hPne : P.Nonempty := by
    obtain ⟨q, hq⟩ := hQne
    exact ⟨f q, Finset.mem_map.mpr ⟨q, hq, rfl⟩⟩
  have hcodim := choose_codimension_le_missing_of_chordal
    (G := H) (PaperIV.isChordal_induce G hchordal (C : Set V)) hQ hQne
  have hedge := core_missing_le_edit G S C hS
  refine ⟨P, hPC, hPclique, hPne, ?_⟩
  have hcardP : P.card = Q.card := by simp [P]
  have hcardC : Fintype.card (C : Set V) = C.card := Fintype.card_coe C
  have hdiff : (C \ P).card = C.card - P.card :=
    Finset.card_sdiff_of_subset hPC
  have hedge' :
      Nat.choose (Fintype.card (C : Set V)) 2 - (graphEdges H).card ≤
        PaperIV.EditMetric.editDist G.edgeFinset S.edgeFinset := by
    simpa [H, PaperIV.Model.graphEdges, hcardC] using hedge
  rw [hdiff, hcardP, ← hcardC]
  exact le_trans hcodim hedge'

/-- Full numerical handoff to the RD09 constructor.  Cordality supplies the
retained clique and the preceding theorems discharge both the quadratic
missing-pair premise and the physical `m+A` edit account. -/
theorem exists_core_clique_with_calibration
    (G S : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel S.Adj]
    (hchordal : PaperIV.IsChordal G) (C : Finset V) (hC : C.Nonempty)
    (hS : ∀ x y, S.Adj x y ↔
      (PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C)).Adj x y)
    {delta residual : ℚ}
    (hn : 2 * (10 : ℚ) ^ 13 ≤ (Fintype.card V : ℚ))
    (hdelta : delta ≤ (PaperIV.NearH1Calibration.eta +
      6 * PaperIV.NearH1Calibration.eps) * (Fintype.card V : ℚ) ^ 2 +
      (Fintype.card V : ℚ) / 6 + 1 / 24)
    (hres : residual ^ 2 ≤ 24 * delta)
    (hresDef : residual = 6 * (C.card : ℚ) -
      2 * (Fintype.card V : ℚ) - 1)
    (hedit : (PaperIV.EditMetric.editDist G.edgeFinset S.edgeFinset : ℚ) ≤
      PaperIV.NearH1Calibration.eps * (Fintype.card V : ℚ) ^ 2) :
    ∃ P : Finset V, P ⊆ C ∧ G.IsClique (P : Set V) ∧ P.Nonempty ∧
      delta ≤ (61 : ℚ) / 10 * PaperIV.NearH1Calibration.eps *
        (Fintype.card V : ℚ) ^ 2 ∧
      ((C \ P).card : ℚ) ≤ 3 * (Fintype.card V : ℚ) / (2 * 10^6) ∧
      33 * (Fintype.card V : ℚ) / 100 ≤ (P.card : ℚ) ∧
      (Fintype.card V : ℚ) - 3 * P.card ≤ (P.card : ℚ) / 64 ∧
      3 * P.card - Fintype.card V ≤ (P.card : ℚ) / 64 ∧
      (1024 : ℚ) ≤ P.card ∧
      (((PaperIV.RootVocab.outsideEdges G P).card +
          PaperIV.RootVocab.missingIncidences G P : ℕ) : ℚ) ≤
        (P.card : ℚ) ^ 2 / 65536 := by
  classical
  obtain ⟨P, hPC, hPclique, hPne, hmissingNat⟩ :=
    exists_core_clique_with_quadratic_edit_bound G S hchordal C hC hS
  have hmissingQ :
      ((C \ P).card : ℚ) * (((C \ P).card : ℚ) + 1) / 2 ≤
        PaperIV.NearH1Calibration.eps * (Fintype.card V : ℚ) ^ 2 := by
    have hcast : ((Nat.choose ((C \ P).card + 1) 2 : ℕ) : ℚ) ≤
        PaperIV.EditMetric.editDist G.edgeFinset S.edgeFinset := by
      exact_mod_cast hmissingNat
    norm_num [Nat.cast_choose_two] at hcast
    nlinarith
  have ha : (P.card : ℚ) = (C.card : ℚ) - ((C \ P).card : ℚ) := by
    have hc := Finset.card_sdiff_of_subset hPC
    have hp : P.card ≤ C.card := Finset.card_le_card hPC
    rw [hc, Nat.cast_sub hp]
    ring
  have hmA0 := PaperIV.RD09SplitEditAccount.outside_add_missing_cast_le
    G S hPC hS
  have hmA :
      (((PaperIV.RootVocab.outsideEdges G P).card +
          PaperIV.RootVocab.missingIncidences G P : ℕ) : ℚ) ≤
        PaperIV.NearH1Calibration.eps * (Fintype.card V : ℚ) ^ 2 +
          ((C \ P).card : ℚ) * (Fintype.card V : ℚ) := by
    linarith
  have hcal := PaperIV.NearH1Calibration.calibration hn
    (by positivity : (0 : ℚ) ≤ ((C \ P).card : ℚ))
    hdelta hres hresDef hmissingQ ha hmA
  exact ⟨P, hPC, hPclique, hPne, hcal⟩

end PaperIV.ChordalCoreMissing
