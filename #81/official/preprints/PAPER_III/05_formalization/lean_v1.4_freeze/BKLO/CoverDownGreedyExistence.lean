/-
# The greedy induction of BKLO Lemma 10.3 (r = 2): the accumulation core

Lemma 10.3 processes the apices `x ∈ U` in turn, choosing at each a perfect matching in the *unused*
part of the neighbourhood `N_H(x, V)` — the part not yet used by earlier apices.  Because the matching
lives in the unused part, its star-triangle edges are disjoint from everything chosen so far, so the
family is pairwise edge-disjoint and (by `BKLO.triDecomp_biUnion_starTriangles`) assembles into a
triangle decomposition.

This file proves, `sorry`-free, the **accumulation** heart of that greedy loop: from a chooser that,
for every apex and every already-used edge set `D`, returns a matching whose star-triangle edges
avoid `D` (the property Dirac supplies in the unused part), the whole sweep yields a family of
matchings whose star-triangle edge sets are pairwise disjoint.

Discharging the chooser hypothesis — that Dirac (`BKLO.perfectMatchingDirac_holds`) succeeds in the
unused neighbourhood, whose minimum degree stays `≥ |N|/2` because the `γ|V|` slack of Lemma 10.3(ii)
absorbs the `≤ γ|V|` used edges per vertex (Lemma 10.3(iii)) — is the remaining analytic step; the
combinatorial induction that turns per-step choices into a globally disjoint family is here.

Everything here is `sorry`-free.
-/
import BKLO.CoverDownGreedyAssembly

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- **The greedy accumulation of Lemma 10.3.**  Given a chooser `choose x D` returning, for every
apex `x` and every already-used edge set `D`, a matching avoiding `x` whose star-triangle edges are
disjoint from `D`, the sweep over `U` produces an assignment `Mx` whose star-triangle edge sets are
pairwise disjoint across apices. -/
theorem exists_greedy_pairwise_star {U : Finset V} (choose : V → Finset (Sym2 V) → Finset (Finset V))
    (hM : ∀ (x : V) (D : Finset (Sym2 V)), IsMatchingAvoiding (choose x D) x)
    (hdisj : ∀ (x : V) (D : Finset (Sym2 V)),
      Disjoint (famEdges (starTriangles x (choose x D))) D) :
    ∃ Mx : V → Finset (Finset V),
      (∀ x ∈ U, IsMatchingAvoiding (Mx x) x) ∧
      (U : Set V).Pairwise (fun x y =>
        Disjoint (famEdges (starTriangles x (Mx x))) (famEdges (starTriangles y (Mx y)))) := by
  classical
  refine Finset.induction_on U ⟨fun _ => ∅, by simp, by simp⟩ ?_
  intro a s ha ih
  obtain ⟨Mx, hMx, hpair⟩ := ih
  set Ds : Finset (Sym2 V) := s.biUnion (fun y => famEdges (starTriangles y (Mx y))) with hDs
  refine ⟨Function.update Mx a (choose a Ds), ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hxs
    · rw [Function.update_self]; exact hM x Ds
    · rw [Function.update_of_ne (ne_of_mem_of_not_mem hxs ha)]; exact hMx x hxs
  · -- the relation is symmetric (`Disjoint` is), so use the `insert` characterisation
    have hsymm : Symmetric (fun x y : V =>
        Disjoint (famEdges (starTriangles x (Function.update Mx a (choose a Ds) x)))
          (famEdges (starTriangles y (Function.update Mx a (choose a Ds) y)))) :=
      fun x y h => h.symm
    rw [Finset.coe_insert, Set.pairwise_insert_of_symmetric hsymm]
    refine ⟨?_, ?_⟩
    · -- pairwise on `s`: the update agrees with `Mx` there, so this is `hpair`
      intro x hx y hy hxy
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hx ha),
        Function.update_of_ne (ne_of_mem_of_not_mem hy ha)]
      exact hpair hx hy hxy
    · -- `a` vs each `b ∈ s`: `choose a Ds` avoids `Ds ⊇ famEdges (starTriangles b (Mx b))`
      intro b hb _
      rw [Function.update_self, Function.update_of_ne (ne_of_mem_of_not_mem hb ha)]
      refine (hdisj a Ds).mono_right ?_
      exact Finset.subset_biUnion_of_mem (fun y => famEdges (starTriangles y (Mx y))) hb

/-- **Greedy existence ⇒ triangle decomposition (Lemma 10.3 assembled).**  Combining the accumulation
with `BKLO.triDecomp_biUnion_starTriangles`: the greedy sweep yields an assignment whose star-triangle
union over `U` is triangle-decomposable. -/
theorem exists_greedy_triDecomp {U : Finset V} (choose : V → Finset (Sym2 V) → Finset (Finset V))
    (hM : ∀ (x : V) (D : Finset (Sym2 V)), IsMatchingAvoiding (choose x D) x)
    (hdisj : ∀ (x : V) (D : Finset (Sym2 V)),
      Disjoint (famEdges (starTriangles x (choose x D))) D) :
    ∃ Mx : V → Finset (Finset V),
      (∀ x ∈ U, IsMatchingAvoiding (Mx x) x) ∧
      TriDecomp (U.biUnion (fun x => famEdges (starTriangles x (Mx x)))) := by
  obtain ⟨Mx, hMx, hpair⟩ := exists_greedy_pairwise_star choose hM hdisj (U := U)
  exact ⟨Mx, hMx, triDecomp_biUnion_starTriangles hMx hpair⟩

end BKLO
