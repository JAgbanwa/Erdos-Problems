import A4S1.IndepAllPairs

namespace FixedDefectStability
open Finset A4S1.TerminalPacking A4S1.IndepAll

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Removing a vertex of high missing degree lowers the missing matching bound. -/
theorem missing_matching_erase {s : ℕ} {S : Finset V} {x : V} (hxS : x ∈ S)
    (hxd : 2*s+3 ≤ (S.filter fun y => y ≠ x ∧ ¬G.Adj x y).card)
    (hS : ¬HasMissPairs G S (s+2)) :
    ¬HasMissPairs G (S.erase x) (s+1) := by
  rintro ⟨P,hP,hPc,hm⟩
  have hpe := card_pends_le P
  obtain ⟨y,hy,hyP⟩ : ∃ y ∈ S.filter (fun y => y ≠ x ∧ ¬G.Adj x y), y ∉ pends P := by
    by_contra hc
    push_neg at hc
    have := card_le_card (show S.filter (fun y => y ≠ x ∧ ¬G.Adj x y) ⊆ pends P from
      fun y hy => hc y hy)
    omega
  obtain ⟨hyS,hyx,hnxy⟩ := mem_filter.1 hy
  have hxP : x ∉ pends P := by
    intro hh
    obtain ⟨q,hq,h1 | h1⟩ := mem_pends.1 hh
    · have := (hm q hq).1
      rw [h1] at this
      simp at this
    · have := (hm q hq).2.1
      rw [h1] at this
      simp at this
  obtain ⟨hP2,hnot⟩ := hP.insert (Ne.symm hyx) hxP hyP
  apply hS
  refine ⟨insert (x,y) P,hP2,by rw [card_insert_of_notMem hnot,hPc],?_⟩
  intro q hq
  rcases mem_insert.1 hq with rfl | hq
  · exact ⟨hxS,hyS,hnxy⟩
  · have := hm q hq
    exact ⟨mem_of_mem_erase this.1,mem_of_mem_erase this.2.1,this.2.2⟩

/-- Quantitative strengthening of the large-core matching bound.
For the template clique on C and isolated vertices S\C, the inequality is exactly
edit_cost ≤ 2 * (e(G[S]) - choose(|S|-s,2)). No template existence is assumed. -/
theorem exists_core_repair : ∀ (s : ℕ) (S : Finset V),
    20*(s+1)^2 ≤ S.card → ¬HasMissPairs G S (s+1) →
    ∃ C ⊆ S, C.card+s=S.card ∧
      3*C.card.choose 2 ≤ (inEdges G S).card + 2*(inEdges G C).card := by
  intro s
  induction s with
  | zero =>
    intro S _ hS
    refine ⟨S,Subset.rfl,by simp,?_⟩
    rw [card_inEdges_of_isClique (isClique_of_not_hasMissPairs_one hS)]
    omega
  | succ s ih =>
    intro S hc hS
    by_cases hx : ∃ x ∈ S, 2*s+3 ≤ (S.filter fun y => y ≠ x ∧ ¬G.Adj x y).card
    · obtain ⟨x,hxS,hxd⟩ := hx
      have hno := missing_matching_erase hxS hxd hS
      have hce : (S.erase x).card+1 = S.card := card_erase_add_one hxS
      obtain ⟨C,hC,hcard,hcost⟩ := ih (S.erase x)
        (by nlinarith only [hc,hce,Nat.zero_le s]) hno
      refine ⟨C,hC.trans (erase_subset x S),by omega,?_⟩
      have := card_le_card (inEdges_mono (G := G) (erase_subset x S))
      omega
    · push_neg at hx
      have hd : ∀ x ∈ S, (S.filter fun y => y ≠ x ∧ ¬G.Adj x y).card ≤ 2*(s+1) := by
        intro x hxS
        have := hx x hxS
        omega
      have hsle : s+1 ≤ S.card := by nlinarith only [hc]
      obtain ⟨C,hC,hcard⟩ := exists_subset_card_eq (show S.card-(s+1) ≤ S.card by omega)
      have hcount : C.card+(s+1)=S.card := by omega
      have hnoC : ¬HasMissPairs G C ((s+1)+1) := fun hh => hS (hasMissPairs_mono hC hh)
      have hdC : ∀ x ∈ C, (C.filter fun y => y ≠ x ∧ ¬G.Adj x y).card ≤ 2*(s+1) := by
        intro x hxC
        exact (card_le_card (filter_subset_filter _ hC)).trans (hd x (hC hxC))
      have hlowS := eg_low (G := G) (2*(s+1)) (s+1) S hS hd
      have hlowC := eg_low (G := G) (2*(s+1)) (s+1) C hnoC hdC
      have choose_id (a : ℕ) : 2*a.choose 2+a=a*a := by
        rw [Nat.choose_two_right]
        have := Nat.div_mul_cancel (Nat.even_mul_pred_self a).two_dvd
        rcases a with _ | a
        · simp
        · simp only [Nat.add_sub_cancel] at this ⊢
          nlinarith only [this]
      have hchS := choose_id S.card
      have hchC := choose_id C.card
      refine ⟨C,hC,hcount,?_⟩
      have hlin : 13*(s+1)+4 ≤ S.card := by nlinarith only [hc]
      have hmul := Nat.mul_le_mul_left (s+1) hlin
      have hsquare : S.card*S.card = (C.card+(s+1))^2 := by rw [←hcount]; ring
      have hcountmul := congrArg (fun a : ℕ => 2*(s+1)*a) hcount
      have hdiff : 2*S.card.choose 2+(s+1)*(s+2) =
          2*C.card.choose 2+2*(s+1)*S.card := by
        nlinarith only [hchS,hchC,hsquare,hcount,hcountmul]
      nlinarith only [hdiff, hmul, hlowS, hlowC]

/-- Literal edge removals and additions needed to replace G[S] by a clique on C
and isolated vertices on S\C. -/
def coreEditCost (G : SimpleGraph V) [DecidableRel G.Adj] (S C : Finset V) : ℕ :=
  (inEdges G S \ inEdges (⊤ : SimpleGraph V) C).card +
    (inEdges (⊤ : SimpleGraph V) C \ inEdges G S).card

/-- The factor-two estimate is for actual edge edits, not an abstract loss variable. -/
theorem exists_core_repair_edits (s : ℕ) (S : Finset V)
    (hc : 20*(s+1)^2 ≤ S.card) (hS : ¬HasMissPairs G S (s+1)) :
    ∃ C ⊆ S, C.card+s=S.card ∧
      C.card.choose 2 ≤ (inEdges G S).card ∧
      coreEditCost G S C ≤ 2*((inEdges G S).card-C.card.choose 2) := by
  obtain ⟨C,hC,hcard,hbound⟩ := exists_core_repair (G := G) s S hc hS
  have htop : (inEdges (⊤ : SimpleGraph V) C).card = C.card.choose 2 :=
    card_inEdges_of_isClique (by intro a ha b hb hab; simpa using hab)
  have hinter : inEdges G S ∩ inEdges (⊤ : SimpleGraph V) C = inEdges G C := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_inter, mk_mem_inEdges]
      constructor
      · rintro ⟨⟨hab,_,_⟩,⟨_,ha,hb⟩⟩
        exact ⟨hab,ha,hb⟩
      · rintro ⟨hab,ha,hb⟩
        exact ⟨⟨hab,hC ha,hC hb⟩,⟨by simpa using hab.ne,ha,hb⟩⟩
  have hinner := card_le_card (inter_subset_right :
    inEdges G S ∩ inEdges (⊤ : SimpleGraph V) C ⊆ inEdges (⊤ : SimpleGraph V) C)
  rw [hinter,htop] at hinner
  have hnonneg : C.card.choose 2 ≤ (inEdges G S).card := by omega
  have hrem := card_sdiff_add_card_inter (inEdges G S) (inEdges (⊤ : SimpleGraph V) C)
  have hadd := card_sdiff_add_card_inter (inEdges (⊤ : SimpleGraph V) C) (inEdges G S)
  rw [hinter] at hrem
  rw [inter_comm, hinter, htop] at hadd
  refine ⟨C,hC,hcard,hnonneg,?_⟩
  unfold coreEditCost
  omega

end FixedDefectStability
#print axioms FixedDefectStability.missing_matching_erase
#print axioms FixedDefectStability.exists_core_repair
#print axioms FixedDefectStability.exists_core_repair_edits
