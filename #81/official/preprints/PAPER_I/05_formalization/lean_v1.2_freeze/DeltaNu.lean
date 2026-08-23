import Mathlib

open Finset
open scoped BigOperators
open Classical

namespace DeltaNu

variable {A B : Type*}
  [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [LinearOrder A] [LinearOrder B]
variable (adj : A → B → Prop) [DecidableRel adj]

def E : Finset (A × B) := univ.filter (fun p => adj p.1 p.2)

def PA : Finset (A × A) :=
  univ.filter (fun q => q.1 < q.2 ∧ ∃ b, adj q.1 b ∧ adj q.2 b)

def PB : Finset (B × B) :=
  univ.filter (fun q => q.1 < q.2 ∧ ∃ a, adj a q.1 ∧ adj a q.2)

def IsMatching (M : Finset (A × B)) : Prop :=
  M ⊆ E adj ∧
  (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q) ∧
  (∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q)

def satA (M : Finset (A × B)) (a : A) : Prop := ∃ b, (a, b) ∈ M
def satB (M : Finset (A × B)) (b : B) : Prop := ∃ a, (a, b) ∈ M

/-- Maximal: no edge joins two unsaturated vertices (holds for maximum matchings). -/
def Maximal (M : Finset (A × B)) : Prop :=
  ∀ a b, adj a b → ¬ satA M a → ¬ satB M b → False

/-- Maximum matching number: the greatest cardinality of a matching. -/
noncomputable def nu : ℕ :=
  (univ.filter (fun M : Finset (A × B) => IsMatching adj M)).sup Finset.card

omit [DecidableEq A] [DecidableEq B] [LinearOrder A] [LinearOrder B] in
/-- Uniqueness of the A-endpoint given a B-endpoint in a matching. -/
lemma matchB_unique {M : Finset (A × B)} (hM : IsMatching adj M)
    {a1 a2 : A} {b : B} (h1 : (a1, b) ∈ M) (h2 : (a2, b) ∈ M) : a1 = a2 := by
  have := hM.2.2 (a1, b) h1 (a2, b) h2 rfl
  exact (Prod.mk.injEq _ _ _ _ ▸ this).1

omit [DecidableEq A] [DecidableEq B] [LinearOrder A] [LinearOrder B] in
/-- Uniqueness of the B-endpoint given an A-endpoint in a matching. -/
lemma matchA_unique {M : Finset (A × B)} (hM : IsMatching adj M)
    {a : A} {b1 b2 : B} (h1 : (a, b1) ∈ M) (h2 : (a, b2) ∈ M) : b1 = b2 := by
  have := hM.2.1 (a, b1) h1 (a, b2) h2 rfl
  exact (Prod.mk.injEq _ _ _ _ ▸ this).2

/-- The block-injection map `E ∖ M → PA ⊕ PB`.  For an edge `e = (a,b)`:
  * if only `b` is saturated (partner `a' = pA(b)`), send `e` to the PA-pair `{a, a'}`;
  * if only `a` is saturated (partner `b' = pB(a)`), send `e` to the PB-pair `{b, b'}`;
  * if both are saturated, route to PA (pair `{a, a'}`) when `a < a'`, else to PB
    (pair `{b, b'}`);
  * the last branch (neither saturated) is unreachable for `e ∈ E ∖ M` when `M` is
    maximal, and returns a junk value. -/
noncomputable def toPair (M : Finset (A × B)) (e : A × B) : (A × A) ⊕ (B × B) :=
  if hb : ∃ a', (a', e.2) ∈ M then
    if _ha : ∃ b', (e.1, b') ∈ M then
      if e.1 < hb.choose then Sum.inl (e.1, hb.choose)
      else Sum.inr (if h : ∃ b', (e.1, b') ∈ M then
              (if e.2 < h.choose then (e.2, h.choose) else (h.choose, e.2))
            else (e.2, e.2))
    else
      Sum.inl (if e.1 < hb.choose then (e.1, hb.choose) else (hb.choose, e.1))
  else
    if ha : ∃ b', (e.1, b') ∈ M then
      Sum.inr (if e.2 < ha.choose then (e.2, ha.choose) else (ha.choose, e.2))
    else
      Sum.inl (e.1, e.1)

/-
`toPair` maps `E ∖ M` into `PA ⊔ PB`.
-/
lemma toPair_mem (M : Finset (A × B)) (hM : IsMatching adj M) (hmax : Maximal adj M)
    {e : A × B} (he : e ∈ E adj \ M) :
    toPair M e ∈ (PA adj).disjSum (PB adj) := by
  simp +zetaDelta at *;
  by_cases hb : ∃ a', (a', e.2) ∈ M <;> simp_all +decide [ toPair ];
  · split_ifs <;> simp_all +decide [ Finset.mem_disjSum ];
    · grind +locals;
    · have := hb.choose_spec; have := ‹∃ b', ( e.1, b' ) ∈ M›.choose_spec; simp_all +decide [ IsMatching, E, PB ] ;
      grind;
    · grind +locals;
    · simp_all +decide [ PA ];
      exact ⟨ e.2, by simpa using Finset.mem_filter.mp he |>.2, by simpa using Finset.mem_filter.mp ( hM.1 hb.choose_spec ) |>.2 ⟩;
    · grind +locals;
  · split_ifs <;> simp_all +decide [ PA, PB ];
    · exact ⟨ e.1, by simpa using mem_filter.mp he |>.2, by simpa using mem_filter.mp ( hM.1 ( ‹∃ b', ( e.1, b' ) ∈ M›.choose_spec ) ) |>.2 ⟩;
    · grind +locals;
    · exact hmax _ _ ( Finset.mem_filter.mp he |>.2 ) ( by unfold satA; aesop ) ( by unfold satB; aesop )

/-
`toPair` is injective on `E ∖ M`.
-/
lemma toPair_injOn (M : Finset (A × B)) (hM : IsMatching adj M) (hmax : Maximal adj M) :
    Set.InjOn (toPair M) ↑(E adj \ M) := by
  intro e1 he1 e2 he2 h_eq;
  grind +locals

/-- Core cardinality bound for a maximal matching (proved by the block injection). -/
theorem card_E_sub_card_M_le (M : Finset (A × B))
    (hM : IsMatching adj M) (hmax : Maximal adj M) :
    (E adj).card - M.card ≤ (PA adj).card + (PB adj).card := by
  have hsub : M ⊆ E adj := hM.1
  calc (E adj).card - M.card = (E adj \ M).card := (card_sdiff_of_subset hsub).symm
    _ ≤ ((PA adj).disjSum (PB adj)).card := by
        apply Finset.card_le_card_of_injOn (toPair M)
        · intro x hx
          exact toPair_mem adj M hM hmax hx
        · exact toPair_injOn adj M hM hmax
    _ = (PA adj).card + (PB adj).card := Finset.card_disjSum _ _

/-
Main: |E| − ν ≤ |P_A| + |P_B|  (i.e. Δ := |E|−|P_A|−|P_B| ≤ ν).
-/
theorem delta_le_nu :
    (E adj).card - nu adj ≤ (PA adj).card + (PB adj).card := by
  obtain ⟨M0, hM0⟩ : ∃ M0 ∈ Finset.univ.filter (fun M : Finset (A × B) => IsMatching adj M), (Finset.univ.filter (fun M : Finset (A × B) => IsMatching adj M)).sup Finset.card = M0.card := by
    have := Finset.exists_max_image ( Finset.univ.filter fun M : Finset ( A × B ) => IsMatching adj M ) ( fun M => Finset.card M ) ⟨ ∅, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by simp +decide [ IsMatching ] ⟩ ⟩;
    obtain ⟨ M0, hM0₁, hM0₂ ⟩ := this; exact ⟨ M0, hM0₁, le_antisymm ( Finset.sup_le fun M hM => hM0₂ M hM ) ( Finset.le_sup ( f := card ) hM0₁ ) ⟩ ;
  convert card_E_sub_card_M_le adj M0 _ _;
  · exact hM0.2;
  · aesop;
  · intro a b hab hnA hnB;
    refine' hM0.2.not_gt ( lt_of_lt_of_le _ <| Finset.le_sup <| show Insert.insert ( a, b ) M0 ∈ _ from _ );
    · rw [ Finset.card_insert_of_notMem ] <;> simp_all +decide [ IsMatching ];
      exact fun h => hnA ⟨ b, h ⟩;
    · grind +locals

end DeltaNu

#print axioms DeltaNu.card_E_sub_card_M_le
#print axioms DeltaNu.delta_le_nu