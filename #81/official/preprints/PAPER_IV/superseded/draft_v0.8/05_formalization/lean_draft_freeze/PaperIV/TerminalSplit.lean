import PaperIV.DiracEngine

/-!
# Literal terminal characterization for the copy dynamics

This is the structural (rather than numerical) terminal gate.  A terminal chordal
graph has a universal core and an independent complement.  The statement is kept
on the original vertex type; no graph isomorphism or externally supplied split
model is hidden in the conclusion.
-/

namespace PaperIV.TerminalSplit

open Finset SimpleGraph
open PaperIV.ChordalBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The stopping predicate for the class-copy dynamics. -/
def IsTerminal (H : SimpleGraph V) : Prop :=
  ∀ x y : V, IsSimplicial H x → IsSimplicial H y → ¬ H.Adj x y →
    H.neighborSet x = H.neighborSet y

/-- A split graph presented on its own vertices: the core is universal and the
outside is independent.  Universality makes the core a clique automatically. -/
def IsUniversalCoreSplit (H : SimpleGraph V) : Prop :=
  ∃ C : Set V,
    (∀ c ∈ C, ∀ w, w ≠ c → H.Adj c w) ∧
    (∀ u, u ∉ C → ∀ v, v ∉ C → ¬ H.Adj u v)

theorem simplicial_in_neighbor_or_eq (H : SimpleGraph V) (hT : IsTerminal H)
    {y s : V} (hy : IsSimplicial H y) (hs : IsSimplicial H s) :
    s ∈ H.neighborSet y ∨ H.neighborSet s = H.neighborSet y := by
  by_cases h : H.Adj y s
  · exact Or.inl ((H.mem_neighborSet y s).2 h)
  · exact Or.inr (hT s y hs hy (fun hsy => h hsy.symm))

/-- The component argument at the heart of the terminal characterization.
Outside the common neighbourhood of a nonadjacent terminal pair there is no edge. -/
theorem complement_neighbor_independent (H : SimpleGraph V)
    (hchord : PaperIV.ChordalStructure H) (hT : IsTerminal H)
    {x y : V} (hx : IsSimplicial H x) (hy : IsSimplicial H y)
    (hxy : ¬ H.Adj x y) (hC : H.neighborSet x = H.neighborSet y) :
    ∀ u v : V, u ∉ H.neighborSet x → v ∉ H.neighborSet x → ¬ H.Adj u v := by
  classical
  intro u v hu hv hadj
  set Cf : Finset V := Finset.univ.filter (fun w => w ∈ H.neighborSet x) with hCfdef
  set S : Finset V := Finset.univ.filter (fun w => w ∉ H.neighborSet x) with hSdef
  have huS : u ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hu⟩
  have hvS : v ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩
  set D : Finset V := S.filter (fun w => PaperIV.RReach H S u w) with hDdefeq
  have hDdef : ∀ w, w ∈ D ↔ (w ∈ S ∧ PaperIV.RReach H S u w) := fun w => Finset.mem_filter
  have huD : u ∈ D := (hDdef u).2 ⟨huS, Relation.ReflTransGen.refl⟩
  have hvD : v ∈ D := (hDdef v).2 ⟨hvS,
    Relation.ReflTransGen.single ⟨huS, hvS, hadj⟩⟩
  have huv_ne : u ≠ v := hadj.ne
  have hCfclique : H.IsClique (Cf : Set V) := by
    have hcoe : (Cf : Set V) = H.neighborSet x := by
      ext w; simp [hCfdef]
    rw [hcoe]; exact hx
  have hDC : ∀ d ∈ D, d ∉ Cf := by
    intro d hd
    have hdS : d ∈ S := ((hDdef d).1 hd).1
    have hnot : d ∉ H.neighborSet x := (Finset.mem_filter.1 hdS).2
    intro hdCf; exact hnot ((Finset.mem_filter.1 hdCf).2)
  have hDconn : PaperIV.RConn H D := PaperIV.rconn_component H hDdef huD
  have hsep : ∀ d ∈ D, ∀ w, H.Adj d w → w ∈ Cf ∨ w ∈ D := by
    intro d hd w hadj'
    by_cases hwC : w ∈ H.neighborSet x
    · exact Or.inl (Finset.mem_filter.2 ⟨Finset.mem_univ _, hwC⟩)
    · have hwS : w ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hwC⟩
      exact Or.inr (PaperIV.component_sep H hDdef d hd w hwS hadj')
  obtain ⟨z, hzD, hzsimp⟩ :=
    PaperIV.exists_simplicial_in_component H (PaperIV.rsh_of_chordal H hchord)
      Cf hCfclique D hDC ⟨u, huD⟩ hDconn hsep
  have hznC : z ∉ H.neighborSet x := (Finset.mem_filter.1 ((hDdef z).1 hzD).1).2
  have hzNy : z ∉ H.neighborSet y := by rw [← hC]; exact hznC
  have hNz : H.neighborSet z = H.neighborSet x := by
    rcases simplicial_in_neighbor_or_eq H hT hy hzsimp with h | h
    · exact absurd h hzNy
    · rw [h]; exact hC.symm
  obtain ⟨w0, hw0D, hw0ne⟩ : ∃ w0 ∈ D, w0 ≠ z := by
    by_cases hzu : z = u
    · exact ⟨v, hvD, by rw [hzu]; exact huv_ne.symm⟩
    · exact ⟨u, huD, fun h => hzu h.symm⟩
  obtain ⟨n, hnD, hzn⟩ :=
    PaperIV.exists_radj_of_rreach_ne H (hDconn z hzD w0 hw0D) hw0ne.symm
  have hnnC : n ∉ H.neighborSet x := (Finset.mem_filter.1 ((hDdef n).1 hnD).1).2
  have hnNz : n ∈ H.neighborSet z := (H.mem_neighborSet z n).2 hzn
  rw [hNz] at hnNz
  exact hnnC hnNz

theorem outside_neighbor_simplicial_eq (H : SimpleGraph V)
    (hchord : PaperIV.ChordalStructure H) (hT : IsTerminal H)
    {x y : V} (hx : IsSimplicial H x) (hy : IsSimplicial H y)
    (hxy : ¬ H.Adj x y) (hC : H.neighborSet x = H.neighborSet y) :
    ∀ v : V, v ∉ H.neighborSet x →
      IsSimplicial H v ∧ H.neighborSet v = H.neighborSet x := by
  intro v hv
  have hind := complement_neighbor_independent H hchord hT hx hy hxy hC
  have hsub : ∀ w, H.Adj v w → w ∈ H.neighborSet x := by
    intro w hvw
    by_contra hwC
    exact hind v w hv hwC hvw
  have hvsimp : IsSimplicial H v := by
    intro a ha b hb hab
    have haa : a ∈ H.neighborSet x := hsub a ((H.mem_neighborSet v a).1 ha)
    have hbb : b ∈ H.neighborSet x := hsub b ((H.mem_neighborSet v b).1 hb)
    exact hx haa hbb hab
  have hxnotC : x ∉ H.neighborSet x := by simp
  have hvx : ¬ H.Adj v x := hind v x hv hxnotC
  exact ⟨hvsimp, hT v x hvsimp hx hvx⟩

/-- A terminal chordal graph is literally a universal-core split graph. -/
theorem terminal_chordal_isUniversalCoreSplit (H : SimpleGraph V)
    (hchord : PaperIV.ChordalStructure H) (hT : IsTerminal H) :
    IsUniversalCoreSplit H := by
  classical
  by_cases hcomp : ∀ u v : V, u ≠ v → H.Adj u v
  · refine ⟨Set.univ, ?_, ?_⟩
    · intro u _ w hwu
      exact hcomp u w (fun h => hwu h.symm)
    · intro a ha
      exact absurd (Set.mem_univ a) ha
  · obtain ⟨x, y, hxy_ne, hxy, hx, hy⟩ :
        ∃ x y : V, x ≠ y ∧ ¬ H.Adj x y ∧ IsSimplicial H x ∧ IsSimplicial H y := by
      by_cases hconn : H.Connected
      · exact hchord.two_nonadj_simplicial hconn hcomp
      · have hne : Nonempty V := by
          rcases not_forall.1 hcomp with ⟨a, _⟩
          exact ⟨a⟩
        exact PaperIV.exists_two_nonadj_simplicial_of_not_connected H hchord hne hconn
    have hC : H.neighborSet x = H.neighborSet y := hT x y hx hy hxy
    have hind := complement_neighbor_independent H hchord hT hx hy hxy hC
    have hout := fun v (hv : v ∉ H.neighborSet x) =>
      outside_neighbor_simplicial_eq H hchord hT hx hy hxy hC v hv
    refine ⟨H.neighborSet x, ?_, ?_⟩
    · intro c hc w hwc
      by_cases hwC : w ∈ H.neighborSet x
      · exact hx hc hwC (fun h => hwc h.symm)
      · have hNw : H.neighborSet w = H.neighborSet x := (hout w hwC).2
        have hcw : c ∈ H.neighborSet w := by rw [hNw]; exact hc
        exact ((H.mem_neighborSet w c).1 hcw).symm
    · exact fun a ha b hb => hind a b ha hb

/-- Contrapositive selector: a chordal graph outside the terminal split class
has a literal nonadjacent pair of simplicial vertices with different classes. -/
theorem exists_nonterminal_simplicial_pair (H : SimpleGraph V)
    (hchord : PaperIV.ChordalStructure H) (hnonsplit : ¬ IsUniversalCoreSplit H) :
    ∃ x y : V, IsSimplicial H x ∧ IsSimplicial H y ∧ ¬ H.Adj x y ∧
      H.neighborSet x ≠ H.neighborSet y := by
  by_contra h
  push_neg at h
  apply hnonsplit
  apply terminal_chordal_isUniversalCoreSplit H hchord
  intro x y hx hy hxy
  exact h x y hx hy hxy

end PaperIV.TerminalSplit
