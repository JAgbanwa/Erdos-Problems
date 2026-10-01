import PaperIV.CopySelector
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic.Bound

/-!
# Rooted perfect-elimination orders

For a finite chordal graph and a prescribed clique `P`, this module constructs
an elimination list ending in `P`.  It then packages the list as a rooted order
and proves the nesting property used by `PaperIV.RD09L1Adapter`: along an
outside edge oriented from earlier to later, the neighbourhood inside `P` can
only grow.

The construction uses the self-contained Dirac engine already present in
Paper IV.  It does not import the external Erdős #81 formalization.
-/

namespace PaperIV.RootedEliminationOrder

open SimpleGraph PaperIV.ChordalBasics

variable {V : Type*} {G : SimpleGraph V}

/-- Suffix condition carried by a perfect-elimination list. -/
def HasCliqueSuffixes (G : SimpleGraph V) (l : List V) : Prop :=
  ∀ v rest, v :: rest <:+ l →
    G.IsClique {w | w ∈ rest ∧ G.Adj v w}

/-- A finite chordal graph has a simplicial vertex outside any proper clique. -/
theorem exists_simplicial_outside_clique [Fintype V] [DecidableEq V]
    (hchordal : PaperIV.IsChordal G) {K : Set V} (hK : G.IsClique K)
    (houtside : ∃ v : V, v ∉ K) :
    ∃ v : V, v ∉ K ∧ ChordalBasics.IsSimplicial G v := by
  classical
  let hstruct : PaperIV.ChordalStructure G :=
    PaperIV.CopySelector.chordalStructure_of_isChordal G hchordal
  by_cases hcomplete : ∀ u v : V, u ≠ v → G.Adj u v
  · obtain ⟨v, hvK⟩ := houtside
    refine ⟨v, hvK, ?_⟩
    rw [ChordalBasics.IsSimplicial]
    intro a ha b hb hab
    exact hcomplete a b hab
  · haveI : Nonempty V := ⟨Classical.choose houtside⟩
    by_cases hconn : G.Connected
    · obtain ⟨a, b, hab, hnab, ha, hb⟩ :=
        hstruct.two_nonadj_simplicial hconn hcomplete
      by_cases haK : a ∈ K
      · have hbK : b ∉ K := by
          intro hbK
          exact hnab (hK haK hbK hab)
        exact ⟨b, hbK, hb⟩
      · exact ⟨a, haK, ha⟩
    · obtain ⟨a, b, hab, hnab, ha, hb⟩ :=
        PaperIV.exists_two_nonadj_simplicial_of_not_connected G hstruct inferInstance hconn
      by_cases haK : a ∈ K
      · have hbK : b ∉ K := by
          intro hbK
          exact hnab (hK haK hbK hab)
        exact ⟨b, hbK, hb⟩
      · exact ⟨a, haK, ha⟩

/-- An arbitrary ordering of a clique satisfies every PEO suffix condition. -/
theorem clique_toList_hasCliqueSuffixes [DecidableEq V]
    {K : Finset V} (hK : G.IsClique (K : Set V)) :
    HasCliqueSuffixes G K.toList := by
  intro v rest hsuffix a ha b hb hab
  obtain ⟨pre, heq⟩ := hsuffix
  apply hK
  · have hlist : a ∈ K.toList := by
      rw [← heq]
      exact List.mem_append_right pre (List.mem_cons_of_mem v ha.1)
    exact Finset.mem_toList.mp hlist
  · have hlist : b ∈ K.toList := by
      rw [← heq]
      exact List.mem_append_right pre (List.mem_cons_of_mem v hb.1)
    exact Finset.mem_toList.mp hlist
  · exact hab

/-- Simpliciality in `G[s]` supplies the ambient clique used at one peel. -/
theorem clique_of_simplicial_induce {s : Set V} {v : V} (hv : v ∈ s)
    (hsimplicial : ChordalBasics.IsSimplicial (G.induce s) ⟨v, hv⟩) :
    G.IsClique {w | w ∈ s ∧ G.Adj v w} := by
  rw [ChordalBasics.IsSimplicial] at hsimplicial
  intro p hp q hq hpq
  have hp' : (⟨p, hp.1⟩ : s) ∈
      (G.induce s).neighborSet ⟨v, hv⟩ := hp.2
  have hq' : (⟨q, hq.1⟩ : s) ∈
      (G.induce s).neighborSet ⟨v, hv⟩ := hq.2
  exact hsimplicial hp' hq' (fun h => hpq (congrArg Subtype.val h))

/-- Peel every vertex outside `K`; the resulting list covers `s` and ends in `K`. -/
theorem elimination_list_ending_clique_aux [Fintype V] [DecidableEq V]
    (hchordal : PaperIV.IsChordal G) (K : Finset V)
    (hK : G.IsClique (K : Set V)) :
    ∀ (bound : ℕ) (s : Finset V), s.card ≤ bound → K ⊆ s →
      ∃ l : List V, l.Nodup ∧ (∀ x, x ∈ l ↔ x ∈ s) ∧
        HasCliqueSuffixes G l ∧ K.toList <:+ l := by
  classical
  intro bound
  induction bound with
  | zero =>
      intro s hs hKs
      have hcardKs : K.card ≤ s.card := Finset.card_le_card hKs
      have hEq : K = s := Finset.eq_of_subset_of_card_le hKs (by omega)
      subst s
      exact ⟨K.toList, K.nodup_toList, by simp,
        clique_toList_hasCliqueSuffixes hK, List.suffix_rfl⟩
  | succ bound ih =>
      intro s hs hKs
      by_cases hsK : s = K
      · subst s
        exact ⟨K.toList, K.nodup_toList, by simp,
          clique_toList_hasCliqueSuffixes hK, List.suffix_rfl⟩
      · have hnotSubset : ¬s ⊆ K := by
          intro hsSubset
          exact hsK (Finset.Subset.antisymm hsSubset hKs)
        obtain ⟨v, hvS, hvK⟩ := Finset.not_subset.mp hnotSubset
        let Ksub : Set ↥(s : Set V) := {z | z.val ∈ K}
        have hKsub : (G.induce (s : Set V)).IsClique Ksub := by
          intro a ha b hb hab
          exact hK ha hb (fun h => hab (Subtype.ext h))
        have houtside : ∃ z : ↥(s : Set V), z ∉ Ksub :=
          ⟨⟨v, hvS⟩, hvK⟩
        obtain ⟨w, hwKsub, hwSimplicial⟩ :=
          exists_simplicial_outside_clique
            (G := G.induce (s : Set V))
            (PaperIV.isChordal_induce G hchordal (s : Set V))
            hKsub houtside
        have hwK : w.val ∉ K := hwKsub
        have hKerased : K ⊆ s.erase w.val := by
          intro z hzK
          apply Finset.mem_erase.mpr
          refine ⟨?_, hKs hzK⟩
          intro hzw
          exact hwK (hzw ▸ hzK)
        obtain ⟨tail, htailNodup, htailMem, htailSuffix, htailEnds⟩ :=
          ih (s.erase w.val) (by
            have heraseCard := Finset.card_erase_of_mem w.2
            omega) hKerased
        have hwNotTail : w.val ∉ tail := by
          intro hwtail
          exact (Finset.mem_erase.mp ((htailMem w.val).mp hwtail)).1 rfl
        have hwClique : G.IsClique
            {z | z ∈ (s : Set V) ∧ G.Adj w.val z} :=
          clique_of_simplicial_induce w.2 hwSimplicial
        refine ⟨w.val :: tail,
          List.nodup_cons.mpr ⟨hwNotTail, htailNodup⟩, ?_, ?_, ?_⟩
        · intro z
          rw [List.mem_cons, htailMem, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨_, hz⟩)
            · exact w.2
            · exact hz
          · intro hz
            by_cases hzw : z = w.val
            · exact Or.inl hzw
            · exact Or.inr ⟨hzw, hz⟩
        · intro z rest hsuffix
          rw [List.suffix_cons_iff] at hsuffix
          rcases hsuffix with hfirst | hlater
          · obtain ⟨rfl, rfl⟩ := List.cons.inj hfirst
            intro a ha b hb hab
            exact hwClique
              ⟨(Finset.mem_erase.mp ((htailMem a).mp ha.1)).2, ha.2⟩
              ⟨(Finset.mem_erase.mp ((htailMem b).mp hb.1)).2, hb.2⟩ hab
          · exact htailSuffix z rest hlater
        · exact htailEnds.trans (List.suffix_cons w.val tail)

/-- A PEO list can be chosen to end in any prescribed clique. -/
theorem exists_elimination_list_ending_clique [Fintype V] [DecidableEq V]
    (hchordal : PaperIV.IsChordal G) (K : Finset V)
    (hK : G.IsClique (K : Set V)) :
    ∃ l : List V, l.Nodup ∧ (∀ x : V, x ∈ l) ∧
      HasCliqueSuffixes G l ∧ K.toList <:+ l := by
  classical
  obtain ⟨l, hnodup, hmem, hsuffix, hends⟩ :=
    elimination_list_ending_clique_aux hchordal K hK
      (Fintype.card V) Finset.univ Finset.card_univ.le (Finset.subset_univ K)
  exact ⟨l, hnodup, fun x => (hmem x).mpr (Finset.mem_univ x), hsuffix, hends⟩

/-- A perfect-elimination list whose final segment is the chosen root. -/
structure Order [Fintype V] [DecidableEq V] (G : SimpleGraph V) (P : Finset V) where
  list : List V
  nodup : list.Nodup
  covers : ∀ v : V, v ∈ list
  cliqueSuffixes : HasCliqueSuffixes G list
  endsInRoot : P.toList <:+ list

/-- Chordality supplies a rooted perfect-elimination order. -/
theorem exists_order [Fintype V] [DecidableEq V]
    (P : Finset V) (hchordal : PaperIV.IsChordal G)
    (hP : G.IsClique (P : Set V)) : Nonempty (Order G P) := by
  obtain ⟨l, hnodup, hcovers, hsuffixes, hends⟩ :=
    exists_elimination_list_ending_clique hchordal P hP
  exact ⟨⟨l, hnodup, hcovers, hsuffixes, hends⟩⟩

/-- Position of a vertex in the elimination list. -/
def Order.index [Fintype V] [DecidableEq V] {P : Finset V}
    (O : Order G P) (v : V) : Fin O.list.length :=
  ⟨O.list.idxOf v, List.idxOf_lt_length_of_mem (O.covers v)⟩

@[simp] theorem Order.get_index [Fintype V] [DecidableEq V] {P : Finset V}
    (O : Order G P) (v : V) : O.list.get (O.index v) = v := by
  exact List.idxOf_get (List.idxOf_lt_length_of_mem (O.covers v))

theorem Order.index_injective [Fintype V] [DecidableEq V] {P : Finset V}
    (O : Order G P) : Function.Injective O.index := by
  intro u v huv
  calc
    u = O.list.get (O.index u) := (O.get_index u).symm
    _ = O.list.get (O.index v) := congrArg O.list.get huv
    _ = v := O.get_index v

/-- Vertices later than `u` and adjacent to `u` form a clique. -/
private theorem get_mem_drop_succ {l : List V} (i j : Fin l.length) (hij : i < j) :
    l.get j ∈ l.drop (i.val + 1) := by
  apply List.mem_iff_getElem.mpr
  refine ⟨j.val - (i.val + 1), ?_, ?_⟩
  · simp only [List.length_drop]
    omega
  · simp only [List.getElem_drop]
    congr 1
    omega

theorem later_neighbors_isClique [Fintype V] [DecidableEq V] {P : Finset V}
    (O : Order G P) (u : V) :
    G.IsClique {v | O.index u < O.index v ∧ G.Adj u v} := by
  intro a ha b hb hab
  have haTail : a ∈ O.list.drop ((O.index u).val + 1) := by
    have h := get_mem_drop_succ (O.index u) (O.index a) ha.1
    rw [O.get_index] at h
    exact h
  have hbTail : b ∈ O.list.drop ((O.index u).val + 1) := by
    have h := get_mem_drop_succ (O.index u) (O.index b) hb.1
    rw [O.get_index] at h
    exact h
  have hsuffixAt :
      O.list.get (O.index u) :: O.list.drop ((O.index u).val + 1) <:+ O.list := by
    rw [List.cons_get_drop_succ]
    exact List.drop_suffix _ _
  have hadj := O.cliqueSuffixes
    (O.list.get (O.index u)) (O.list.drop ((O.index u).val + 1)) hsuffixAt
    ⟨haTail, by rw [O.get_index]; exact ha.2⟩
    ⟨hbTail, by rw [O.get_index]; exact hb.2⟩ hab
  exact hadj

/-- Every outside vertex occurs before every root vertex. -/
theorem outside_before_root [Fintype V] [DecidableEq V] {P : Finset V}
    (O : Order G P) {u x : V} (hu : u ∉ P) (hx : x ∈ P) :
    O.index u < O.index x := by
  obtain ⟨pre, hlist⟩ := O.endsInRoot
  have huNotRootList : u ∉ P.toList := by simpa using hu
  have huList : u ∈ pre ++ P.toList := by rw [hlist]; exact O.covers u
  have huPrefix : u ∈ pre := by
    rcases List.mem_append.mp huList with huPrefix | huRoot
    · exact huPrefix
    · exact (huNotRootList huRoot).elim
  have hxRootList : x ∈ P.toList := by simpa using hx
  have hnodupAppend : (pre ++ P.toList).Nodup := by rw [hlist]; exact O.nodup
  have hxNotPrefix : x ∉ pre := by
    intro hxPrefix
    exact (List.nodup_append.mp hnodupAppend).2.2 x hxPrefix x hxRootList rfl
  change O.list.idxOf u < O.list.idxOf x
  rw [← hlist, List.idxOf_append, if_pos huPrefix,
    List.idxOf_append, if_neg hxNotPrefix]
  have huIndex : pre.idxOf u < pre.length := List.idxOf_lt_length_of_mem huPrefix
  omega

/-- Along an oriented outside edge, the root neighbourhood can only grow. -/
theorem root_neighbors_mono [Fintype V] [DecidableEq V] {P : Finset V}
    (O : Order G P) {u v : V} (hu : u ∉ P) (hv : v ∉ P)
    (huvOrder : O.index u < O.index v) (huv : G.Adj u v) :
    ∀ ⦃x : V⦄, x ∈ P → G.Adj u x → G.Adj v x := by
  intro x hx hux
  have huxOrder : O.index u < O.index x := outside_before_root O hu hx
  have hvxNe : v ≠ x := by
    intro hvx
    subst x
    exact hv hx
  exact later_neighbors_isClique O u
    ⟨huvOrder, huv⟩ ⟨huxOrder, hux⟩ hvxNe

end PaperIV.RootedEliminationOrder
