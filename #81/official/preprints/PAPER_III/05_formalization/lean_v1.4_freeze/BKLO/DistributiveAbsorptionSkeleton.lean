/-
# The distributive-absorption skeleton (vehicle-independent)

`BKLO/ShellAbsorptionConfinementWall.lean` reduces the open core of AX2 §10 to a **distributive**
(`∃ R, ∀ L`) absorber: a reserved structure `R` fixed before the leftover `L`, such that `R ∪ L`
decomposes for every admissible sparse divisible `L`.  The wall shows the naive per-edge gadget
route is impossible (nothing absorbs a single edge) — the reservation must **reuse** its edges across
many potential leftovers.

This file supplies the vehicle-independent heart of the reuse: given, for each leftover edge, a
family of candidate absorbing configurations drawn from the reservation, **Hall's condition** on the
availabilities yields a system of *distinct* absorbers, and — when the chosen absorbers are pairwise
disjoint and each decomposes — their union decomposes.  It is the abstract form of the
matching step the distributive absorber needs; the vehicle then instantiates the configurations by
the project's cycle-family absorbers (`BKLO.hasAbs_fam`, `BKLO.covers_freshFam`) and the
decomposability predicate by `BKLO.TriDecomp`.

Everything here is `sorry`-free and pure `Mathlib` (the decomposability predicate is abstract).
-/
import Mathlib.Combinatorics.Hall.Basic

open Finset

namespace BKLO.DistributiveAbsorption

variable {ι β : Type*} [DecidableEq ι] [DecidableEq β]

omit [DecidableEq ι] in
/-- **Hall selection of distinct absorbers.**  If, over the active leftover set `L` (a `Fintype` of
indices), each index `i` has a family `cand i` of candidate absorbers, and Hall's condition holds —
every subfamily uses at least as many absorbers as it has indices — then there is an injective choice
`f` of a candidate for each index.  (Mathlib's finite Hall theorem, re-exposed in the absorber
vocabulary.) -/
theorem exists_injective_absorberChoice [Fintype ι] (cand : ι → Finset β)
    (hHall : ∀ S : Finset ι, S.card ≤ (S.biUnion cand).card) :
    ∃ f : ι → β, Function.Injective f ∧ ∀ i, f i ∈ cand i :=
  (Finset.all_card_le_biUnion_card_iff_exists_injective cand).1 hHall

/-- **Composition of a distinct, disjoint, decomposable selection.**  Let `Dec : Finset γ → Prop` be
any "decomposability" predicate that holds of `∅` and is closed under disjoint unions
(`Dec_empty`, `Dec_union`).  If `f : ι → Finset γ` assigns to each active index a decomposable edge
set, the assignments are pairwise disjoint, then the union over any index set is decomposable. -/
theorem dec_biUnion_of_pairwiseDisjoint {γ : Type*} [DecidableEq γ]
    {Dec : Finset γ → Prop} (hEmpty : Dec ∅)
    (hUnion : ∀ {A B : Finset γ}, Disjoint A B → Dec A → Dec B → Dec (A ∪ B))
    (L : Finset ι) (f : ι → Finset γ)
    (hdisj : (L : Set ι).Pairwise (fun i j => Disjoint (f i) (f j)))
    (hdec : ∀ i ∈ L, Dec (f i)) :
    Dec (L.biUnion f) := by
  classical
  induction L using Finset.induction with
  | empty => simpa using hEmpty
  | insert a s ha ih =>
      rw [Finset.biUnion_insert]
      have hdisj_s : (s : Set ι).Pairwise (fun i j => Disjoint (f i) (f j)) :=
        hdisj.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
      have hdec_s : ∀ i ∈ s, Dec (f i) := fun i hi => hdec i (Finset.mem_insert_of_mem hi)
      have hda : Dec (f a) := hdec a (Finset.mem_insert_self a s)
      have hds : Dec (s.biUnion f) := ih hdisj_s hdec_s
      -- `f a` is disjoint from the union over `s`
      have hdis : Disjoint (f a) (s.biUnion f) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact hdisj (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hj)
          (fun h => ha (h ▸ hj))
      exact hUnion hdis hda hds

/-- **The distributive-absorption skeleton, combined.**  With an abstract decomposability predicate
closed under disjoint union, a Hall-satisfying family of candidate absorbers, and each candidate's
edge set decomposable, there is an injective choice of a candidate per leftover index such that —
*provided the chosen absorbers are pairwise edge-disjoint* (the geometric fact the vehicle must
supply from the reservation design) — the union of the chosen absorbers over all leftover indices
decomposes. -/
theorem exists_injective_choice_dec_biUnion [Fintype ι] {γ : Type*} [DecidableEq γ]
    {Dec : Finset γ → Prop} (hEmpty : Dec ∅)
    (hUnion : ∀ {A B : Finset γ}, Disjoint A B → Dec A → Dec B → Dec (A ∪ B))
    (cand : ι → Finset β) (edgesOfCand : β → Finset γ)
    (hHall : ∀ S : Finset ι, S.card ≤ (S.biUnion cand).card)
    (hdec : ∀ i, ∀ b ∈ cand i, Dec (edgesOfCand b)) :
    ∃ f : ι → β, Function.Injective f ∧ (∀ i, f i ∈ cand i) ∧
      ( (Set.univ : Set ι).Pairwise (fun i j => Disjoint (edgesOfCand (f i)) (edgesOfCand (f j))) →
        Dec (Finset.univ.biUnion (fun i => edgesOfCand (f i))) ) := by
  classical
  obtain ⟨f, hinj, hmem⟩ := exists_injective_absorberChoice cand hHall
  refine ⟨f, hinj, hmem, fun hpair => ?_⟩
  exact dec_biUnion_of_pairwiseDisjoint hEmpty hUnion Finset.univ (fun i => edgesOfCand (f i))
    (fun i _ j _ hij => hpair (Set.mem_univ i) (Set.mem_univ j) hij)
    (fun i _ => hdec i (f i) (hmem i))

end BKLO.DistributiveAbsorption
