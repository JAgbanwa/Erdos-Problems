import CoreCliqueAlternative

namespace FixedDefectStability
open Finset A4S1.TerminalPacking A4S1.IndepAll

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The endpoints of a maximal missing matching leave a literal clique. -/
theorem exists_large_clique_core (s : ℕ) (S : Finset V)
    (hS : ¬HasMissPairs G S (s+1)) :
    ∃ C ⊆ S, C.card=S.card-2*s ∧ G.IsClique (C : Set V) := by
  classical
  have hex : ∃ m, ¬HasMissPairs G S (m+1) := ⟨s,hS⟩
  let m := Nat.find hex
  have hspec : ¬HasMissPairs G S (m+1) := Nat.find_spec hex
  have hle : m ≤ s := Nat.find_min' hex hS
  have hmatch : HasMissPairs G S m := by
    rcases hm : m with _ | j
    · exact hasMissPairs_zero _
    · have hj : j < Nat.find hex := by change j < m; omega
      have hh := Nat.find_min hex hj
      push_neg at hh
      simpa [hm] using hh
  obtain ⟨P,hP,hcard,hmembers⟩ := hmatch
  let R := S \ pends P
  have hcl : G.IsClique (R : Set V) := by
    intro a ha b hb hab
    have ha' := mem_sdiff.1 ha
    have hb' := mem_sdiff.1 hb
    by_contra hn
    obtain ⟨hP',hnot⟩ := hP.insert hab ha'.2 hb'.2
    apply hspec
    refine ⟨insert (a,b) P,hP',by rw [card_insert_of_notMem hnot,hcard],?_⟩
    intro q hq
    rcases mem_insert.1 hq with rfl | hq
    · exact ⟨ha'.1,hb'.1,hn⟩
    · exact hmembers q hq
  have hRsize : S.card-2*s ≤ R.card := by
    have he := card_pends_le P
    have hc := card_sdiff_add_card_inter S (pends P)
    have hi := card_le_card (inter_subset_right : S ∩ pends P ⊆ pends P)
    change S.card-2*s ≤ (S \ pends P).card
    omega
  obtain ⟨C,hCR,hCcard⟩ := exists_subset_card_eq hRsize
  refine ⟨C,hCR.trans sdiff_subset,hCcard,?_⟩
  intro a ha b hb hab
  exact hcl (hCR ha) (hCR hb) hab

/-- A clique can replace the repaired core. If s additional vertices must move
to the exterior, their total linear charge is paid by the original excess. -/
theorem exists_clique_core_with_shift (s : ℕ) (S : Finset V)
    (hc : 20*(s+1)^2 ≤ S.card) (hS : ¬HasMissPairs G S (s+1)) :
    ∃ C ⊆ S, G.IsClique (C : Set V) ∧ ∃ r : ℕ,
      r ≤ s ∧ C.card+s+r=S.card ∧
      r*S.card ≤ 4*s*((inEdges G S).card-(S.card-s).choose 2) := by
  have hsle : 2*s ≤ S.card := by nlinarith only [hc]
  rcases clique_core_or_large_excess (G := G) s S hc hS with ⟨C,hC,hcard,hcl⟩ | hlarge
  · exact ⟨C,hC,hcl,0,by omega,by omega,by simp⟩
  · obtain ⟨C,hC,hcard,hcl⟩ := exists_large_clique_core (G := G) s S hS
    refine ⟨C,hC,hcl,s,le_rfl,by omega,?_⟩
    have he : (S.card-s).choose 2 ≤ (inEdges G S).card := by omega
    have hpaid : S.card ≤ 4*((inEdges G S).card-(S.card-s).choose 2) := by omega
    have hh := Nat.mul_le_mul_left s hpaid
    nlinarith only [hh]

end FixedDefectStability
#print axioms FixedDefectStability.exists_large_clique_core
#print axioms FixedDefectStability.exists_clique_core_with_shift
