import CoreRepair

namespace FixedDefectStability
open Finset A4S1.TerminalPacking A4S1.IndepAll

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem choose_double (a : ℕ) : 2*a.choose 2+a=a*a := by
  rw [Nat.choose_two_right]
  have h := Nat.div_mul_cancel (Nat.even_mul_pred_self a).two_dvd
  rcases a with _ | a
  · simp
  · simp only [Nat.add_sub_cancel] at h ⊢
    nlinarith only [h]

/-- Either the repaired core can already be chosen as a clique of G, or its
excess pays a linear-in-order charge. No clique hypothesis is added. -/
theorem clique_core_or_large_excess : ∀ (s : ℕ) (S : Finset V),
    20*(s+1)^2 ≤ S.card → ¬HasMissPairs G S (s+1) →
    (∃ C ⊆ S, C.card+s=S.card ∧ G.IsClique (C : Set V)) ∨
      S.card-s + 2*(S.card-s).choose 2 ≤ 2*(inEdges G S).card := by
  intro s
  induction s with
  | zero =>
    intro S _ hS
    exact Or.inl ⟨S,Subset.rfl,by simp,isClique_of_not_hasMissPairs_one hS⟩
  | succ s ih =>
    intro S hc hS
    by_cases hx : ∃ x ∈ S, 2*s+3 ≤ (S.filter fun y => y ≠ x ∧ ¬G.Adj x y).card
    · obtain ⟨x,hxS,hxd⟩ := hx
      have hno := missing_matching_erase hxS hxd hS
      have hce : (S.erase x).card+1=S.card := card_erase_add_one hxS
      have hsmall : 20*(s+1)^2 ≤ (S.erase x).card := by
        nlinarith only [hc,hce,Nat.zero_le s]
      rcases ih (S.erase x) hsmall hno with ⟨C,hC,hcard,hcl⟩ | hlarge
      · exact Or.inl ⟨C,hC.trans (erase_subset x S),by omega,hcl⟩
      · right
        have hmono := card_le_card (inEdges_mono (G := G) (erase_subset x S))
        have heq : (S.erase x).card-s=S.card-(s+1) := by omega
        rw [heq] at hlarge
        omega
    · right
      push_neg at hx
      have hd : ∀ x ∈ S, (S.filter fun y => y ≠ x ∧ ¬G.Adj x y).card ≤ 2*(s+1) := by
        intro x hxS
        have := hx x hxS
        omega
      have hlow := eg_low (G := G) (2*(s+1)) (s+1) S hS hd
      have hsle : s+1 ≤ S.card := by nlinarith only [hc]
      have hcount : (S.card-(s+1))+(s+1)=S.card := by omega
      have hchS := choose_double S.card
      have hchC := choose_double (S.card-(s+1))
      have hsq : S.card*S.card=((S.card-(s+1))+(s+1))^2 := by rw [hcount]; ring
      have hmul := congrArg (fun a : ℕ => 2*(s+1)*a) hcount
      have hdiff : 2*S.card.choose 2+(s+1)*(s+2) =
          2*(S.card-(s+1)).choose 2+2*(s+1)*S.card := by
        nlinarith only [hchS,hchC,hsq,hcount,hmul]
      nlinarith only [hc,hlow,hdiff,hcount,Nat.zero_le (s*S.card)]

end FixedDefectStability
#print axioms FixedDefectStability.clique_core_or_large_excess
