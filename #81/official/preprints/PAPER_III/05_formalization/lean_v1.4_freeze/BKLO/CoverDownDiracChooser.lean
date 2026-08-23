/-
# Dirac in a neighbourhood → a matching (Lemma 10.3, the per-step Dirac choice)

The per-apex step of BKLO Lemma 10.3 (r = 2) applies Hajnal–Szemerédi Theorem 10.2 — for r = 2 this
is Dirac's theorem, `BKLO.perfectMatchingDirac_holds` — to the (unused part of the) neighbourhood
graph, whose minimum degree stays `≥ |N|/2` by the `γ|V|` slack of Lemma 10.3(ii).  Dirac yields a
perfect matching, i.e. a fixed-point-free partner **involution** of the neighbourhood; the orbit
family `{a, f a}` is then a matching of `N` avoiding the apex `x`
(`BKLO.isMatchingAvoiding_involutionMatching`).

This file assembles that step, `sorry`-free: a graph on a neighbourhood `N` (even, minimum degree
`≥ |N|/2`) yields a `BKLO.IsMatchingAvoiding` matching of `N` avoiding any `x ∉ N`.  Together with
`BKLO/CoverDownGreedyExistence.lean` this is the per-step chooser; what remains of Lemma 10.3 is the
degree/budget bookkeeping keeping the unused neighbourhood's minimum degree `≥ |N|/2` (Lemma 10.3(iii)).

Everything here is `sorry`-free.
-/
import BKLO.InvolutionMatching
import BKLO.DiracMatching

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-- **Dirac gives a fixed-point-free involution of the neighbourhood.**  A graph `G` on the
neighbourhood `N` (as `{v // v ∈ N}`) with an even number of vertices and minimum degree `≥ |N|/2`
has a partner function that lifts to a fixed-point-free involution `f` of `N`. -/
theorem exists_involution_of_dirac {N : Finset V}
    (G : SimpleGraph {v // v ∈ N}) [DecidableRel G.Adj]
    (hEven : Even (Fintype.card {v // v ∈ N}))
    (hdeg : Fintype.card {v // v ∈ N} ≤ 2 * G.minDegree) :
    ∃ f : V → V, (∀ a ∈ N, f a ∈ N) ∧ (∀ a ∈ N, f (f a) = a) ∧ (∀ a ∈ N, f a ≠ a) := by
  classical
  obtain ⟨M, hM⟩ := perfectMatchingDirac_holds G hEven hdeg
  have hpartner : ∀ a : {v // v ∈ N}, ∃! b, M.Adj a b := fun a => hM.1 (hM.2 a)
  choose g hg huniq using hpartner
  have hginv : ∀ a, g (g a) = a := fun a => (huniq (g a) a (M.symm (hg a))).symm
  have hgne : ∀ a, g a ≠ a := by
    intro a h
    have hadj : G.Adj a (g a) := M.adj_sub (hg a)
    rw [h] at hadj
    exact hadj.ne rfl
  refine ⟨fun v => if h : v ∈ N then ((g ⟨v, h⟩ : {v // v ∈ N}) : V) else v, ?_, ?_, ?_⟩
  · intro a ha; simp only [dif_pos ha]; exact (g ⟨a, ha⟩).2
  · intro a ha
    simp only [dif_pos ha, dif_pos (g ⟨a, ha⟩).2]
    have h2 : (⟨((g ⟨a, ha⟩ : {v // v ∈ N}) : V), (g ⟨a, ha⟩).2⟩ : {v // v ∈ N}) = g ⟨a, ha⟩ := rfl
    rw [h2, hginv ⟨a, ha⟩]
  · intro a ha
    simp only [dif_pos ha]
    intro hcon
    exact hgne ⟨a, ha⟩ (Subtype.ext hcon)

/-- **Per-step matching from Dirac (Lemma 10.3, part A).**  A graph on an even neighbourhood `N` with
minimum degree `≥ |N|/2` yields an `BKLO.IsMatchingAvoiding` matching of `N` avoiding any `x ∉ N`. -/
theorem exists_isMatchingAvoiding_of_dirac {N : Finset V} {x : V} (hx : x ∉ N)
    (G : SimpleGraph {v // v ∈ N}) [DecidableRel G.Adj]
    (hEven : Even (Fintype.card {v // v ∈ N}))
    (hdeg : Fintype.card {v // v ∈ N} ≤ 2 * G.minDegree) :
    ∃ M : Finset (Finset V), IsMatchingAvoiding M x := by
  obtain ⟨f, hmap, hinv, hne⟩ := exists_involution_of_dirac G hEven hdeg
  exact ⟨involutionMatching N f, isMatchingAvoiding_involutionMatching hmap hinv hne hx⟩

end BKLO
