import PaperIV.VertexCopyMonotone
import PaperIV.VertexCopyRank

/-!
# The compatibility gate for fine vertex copies (DV157–RD09)

`VertexCopyMonotone.exists_chordal_copy_F4_le` selects, for a chordal graph and
a nonadjacent simplicial pair, an orientation of the fine copy which stays
chordal and does not decrease the mixed fractional defect `F4 = |E| - W*`.
`VertexCopyRank` shows that the clone *class count* is not a strict rank for
arbitrary fine copies.  This module closes the gap between the two: it produces
a **selector** which simultaneously

* keeps the copy chordal,
* does not decrease `F4`,
* and strictly increases the lexicographic potential `(F4, clonePairs)`,

which is a genuine well-founded rank on the (finite) set of graphs on `V`.
Iterating the selector therefore terminates, and it terminates exactly at the
universal-core split terminal class.

The two ingredients are:

* `clonePairs_lt_of_card_cloneClass_le` — a fine copy whose *source* class is at
  least as large as its *target* class strictly increases the number of ordered
  clone pairs.  (This is the missing second lexicographic component of
  `VertexCopyRank`: the class *count* may stay put, but the pair count cannot.)
* the *dichotomy*: if the class-selected orientation happens to decrease `F4`,
  then by the symmetrization inequality `two_mul_F4_le_add` the opposite
  orientation increases `F4` **strictly**, and a strict increase of `F4` is
  itself a descent step.

Combining them gives `exists_gate_copy`, and iterating gives
`exists_terminal_symmetrizationPath`: from every chordal graph there is a finite sequence
of nonadjacent fine copies, each chordal and each not decreasing `F4`, ending in
a universal-core split graph.
-/

namespace PaperIV.VertexCopyGate

open Finset
open PaperIV.VertexCopyMonotone
open PaperIV.VertexCopyRank

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Clone classes and ordered clone pairs -/

/-- The open-neighbourhood clone class of a vertex. -/
def cloneClass (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  Finset.univ.filter fun w => G.neighborFinset w = G.neighborFinset v

/-- The number of *ordered* pairs of distinct vertices with equal open
neighbourhoods. -/
def clonePairs (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.offDiag.filter fun p : V × V =>
    G.neighborFinset p.1 = G.neighborFinset p.2).card

theorem mem_cloneClass {G : SimpleGraph V} [DecidableRel G.Adj] {v w : V} :
    w ∈ cloneClass G v ↔ G.neighborFinset w = G.neighborFinset v := by
  simp [cloneClass]

theorem self_mem_cloneClass (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    v ∈ cloneClass G v := by simp [cloneClass]

theorem one_le_card_cloneClass (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    1 ≤ (cloneClass G v).card :=
  Finset.card_pos.mpr ⟨v, self_mem_cloneClass G v⟩

theorem clonePairs_le (G : SimpleGraph V) [DecidableRel G.Adj] :
    clonePairs G ≤ Fintype.card V * Fintype.card V := by
  unfold clonePairs
  calc (Finset.univ.offDiag.filter fun p : V × V =>
          G.neighborFinset p.1 = G.neighborFinset p.2).card
      ≤ (Finset.univ.offDiag : Finset (V × V)).card := Finset.card_filter_le _ _
    _ ≤ Fintype.card V * Fintype.card V := by
        simp [Finset.offDiag_card, Finset.card_univ]

/-- **The second lexicographic component.**  A fine copy whose source class is
at least as large as its target class strictly increases the number of ordered
clone pairs. -/
theorem clonePairs_lt_of_card_cloneClass_le {G : SimpleGraph V} [DecidableRel G.Adj] {t s : V}
    (hne : t ≠ s) (hnadj : ¬ G.Adj t s)
    (hclass : G.neighborFinset t ≠ G.neighborFinset s)
    (hle : (cloneClass G t).card ≤ (cloneClass G s).card) :
    clonePairs G < clonePairs (VertexCopy.graph G t s) := by
  classical
  set G₁ := VertexCopy.graph G t s with hG₁
  have hshift : ∀ w : V, w ≠ t → G₁.neighborFinset w = shiftNbhd t s (G.neighborFinset w) :=
    fun w hw => neighborFinset_copy_of_ne G hnadj hw
  have htgt : G₁.neighborFinset t = G.neighborFinset s := VertexCopy.neighborFinset_copied G hnadj
  have hsrc : G₁.neighborFinset s = G.neighborFinset s := neighborFinset_copy_source G hne hnadj
  have hshifts : shiftNbhd t s (G.neighborFinset s) = G.neighborFinset s := by
    rw [← hshift s (Ne.symm hne), hsrc]
  set P : Finset (V × V) :=
    Finset.univ.offDiag.filter (fun p : V × V => G.neighborFinset p.1 = G.neighborFinset p.2)
    with hP
  set P₁ : Finset (V × V) :=
    Finset.univ.offDiag.filter (fun p : V × V => G₁.neighborFinset p.1 = G₁.neighborFinset p.2)
    with hP₁
  set A : Finset (V × V) := P.filter (fun p => p.1 ≠ t ∧ p.2 ≠ t) with hA
  set Cs : Finset V := cloneClass G s with hCs
  set Ct : Finset V := cloneClass G t with hCt
  have hCs_ne_t : ∀ b ∈ Cs, b ≠ t := by
    intro b hb hbt
    subst hbt
    exact hclass (mem_cloneClass.mp hb)
  -- the clone pairs of `G` avoiding the target survive the copy
  have h1 : A ⊆ P₁ := by
    intro p hp
    rw [hA, Finset.mem_filter, hP, Finset.mem_filter] at hp
    obtain ⟨⟨hdiag, heq⟩, h1t, h2t⟩ := hp
    rw [hP₁, Finset.mem_filter]
    exact ⟨hdiag, by rw [hshift _ h1t, hshift _ h2t, heq]⟩
  -- and the target becomes a clone of every member of the source class
  set T : Finset (V × V) := Cs.image (fun b => (t, b)) ∪ Cs.image (fun b => (b, t)) with hT
  have h2 : T ⊆ P₁ := by
    intro p hp
    rw [hT, Finset.mem_union] at hp
    have hkey : ∀ b ∈ Cs, G₁.neighborFinset b = G₁.neighborFinset t := by
      intro b hb
      rw [hshift b (hCs_ne_t b hb), mem_cloneClass.mp hb, hshifts, htgt]
    rcases hp with hp | hp
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
      rw [hP₁, Finset.mem_filter]
      exact ⟨Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _,
        fun h => hCs_ne_t b hb h.symm⟩, (hkey b hb).symm⟩
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
      rw [hP₁, Finset.mem_filter]
      exact ⟨Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _,
        hCs_ne_t b hb⟩, hkey b hb⟩
  have h3 : Disjoint A T := by
    rw [Finset.disjoint_left]
    intro p hpA hpT
    rw [hA, Finset.mem_filter] at hpA
    rw [hT, Finset.mem_union] at hpT
    rcases hpT with hp | hp
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
      exact hpA.2.1 rfl
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
      exact hpA.2.2 rfl
  have h4 : T.card = 2 * Cs.card := by
    rw [hT, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (by
      intro a b hab; simpa using hab), Finset.card_image_of_injective _ (by
      intro a b hab; simpa using hab)]
    · ring
    · rw [Finset.disjoint_left]
      intro p hp1 hp2
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp1
      obtain ⟨c, hc, hce⟩ := Finset.mem_image.mp hp2
      exact hCs_ne_t c hc (congrArg Prod.fst hce)
  -- the only clone pairs that can be lost are those through the target
  set D1 : Finset (V × V) := (Ct.erase t).image (fun b => (t, b)) with hD1
  set D2 : Finset (V × V) := (Ct.erase t).image (fun b => (b, t)) with hD2
  have h5 : P ⊆ A ∪ (D1 ∪ D2) := by
    intro p hp
    have hmem := hp
    rw [hP, Finset.mem_filter, Finset.mem_offDiag] at hmem
    obtain ⟨⟨-, -, hne12⟩, heq⟩ := hmem
    by_cases h1' : p.1 ≠ t
    · by_cases h2' : p.2 ≠ t
      · exact Finset.mem_union_left _ (by rw [hA, Finset.mem_filter]; exact ⟨hp, h1', h2'⟩)
      · push_neg at h2'
        refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
        rw [hD2, Finset.mem_image]
        refine ⟨p.1, Finset.mem_erase.mpr ⟨h1', ?_⟩, ?_⟩
        · rw [hCt, mem_cloneClass, heq, h2']
        · rw [← h2']
    · push_neg at h1'
      refine Finset.mem_union_right _ (Finset.mem_union_left _ ?_)
      rw [hD1, Finset.mem_image]
      refine ⟨p.2, Finset.mem_erase.mpr ⟨fun h => hne12 (h1'.trans h.symm), ?_⟩, ?_⟩
      · rw [hCt, mem_cloneClass, ← heq, h1']
      · rw [← h1']
  have hcard : (Ct.erase t).card = Ct.card - 1 :=
    Finset.card_erase_of_mem (by rw [hCt]; exact self_mem_cloneClass G t)
  have hPle : P.card ≤ A.card + 2 * (Ct.card - 1) := by
    calc P.card ≤ (A ∪ (D1 ∪ D2)).card := Finset.card_le_card h5
      _ ≤ A.card + (D1 ∪ D2).card := Finset.card_union_le _ _
      _ ≤ A.card + (D1.card + D2.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
      _ ≤ A.card + 2 * (Ct.card - 1) := by
          have e1 : D1.card ≤ Ct.card - 1 := by rw [hD1, ← hcard]; exact Finset.card_image_le
          have e2 : D2.card ≤ Ct.card - 1 := by rw [hD2, ← hcard]; exact Finset.card_image_le
          omega
  have hP₁ge : A.card + 2 * Cs.card ≤ P₁.card := by
    have hsub : A ∪ T ⊆ P₁ := Finset.union_subset h1 h2
    calc A.card + 2 * Cs.card = A.card + T.card := by rw [h4]
      _ = (A ∪ T).card := (Finset.card_union_of_disjoint h3).symm
      _ ≤ P₁.card := Finset.card_le_card hsub
  have hCt1 : 1 ≤ Ct.card := by rw [hCt]; exact one_le_card_cloneClass G t
  have hle' : Ct.card ≤ Cs.card := by rw [hCt, hCs]; exact hle
  show P.card < P₁.card
  omega

/-- For every nonadjacent pair in different clone classes, at least one of the
two fine copy orientations strictly increases the number of ordered clone
pairs. -/
theorem exists_copy_clonePairs_lt {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
    (hne : u ≠ v) (hnadj : ¬ G.Adj u v)
    (hclass : G.neighborFinset u ≠ G.neighborFinset v) :
    ∃ t s : V, ((t = u ∧ s = v) ∨ (t = v ∧ s = u)) ∧
      clonePairs G < clonePairs (VertexCopy.graph G t s) := by
  rcases le_total (cloneClass G u).card (cloneClass G v).card with h | h
  · exact ⟨u, v, Or.inl ⟨rfl, rfl⟩, clonePairs_lt_of_card_cloneClass_le hne hnadj hclass h⟩
  · exact ⟨v, u, Or.inr ⟨rfl, rfl⟩,
      clonePairs_lt_of_card_cloneClass_le (Ne.symm hne) (fun h' => hnadj h'.symm)
        (Ne.symm hclass) h⟩

/-! ### The gate: one orientation is chordal, `F4`-nondecreasing and descending -/

/-- **The compatibility gate.**  For a chordal graph and a nonadjacent pair of
simplicial vertices in different clone classes, one of the two fine copy
orientations is chordal, does not decrease the mixed fractional defect `F4`, and
strictly increases the lexicographic rank `(F4, clonePairs)`. -/
theorem exists_gate_copy {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
    (hne : u ≠ v) (hnadj : ¬ G.Adj u v)
    (hclass : G.neighborFinset u ≠ G.neighborFinset v)
    (hG : PaperIV.IsChordal G)
    (hu : PaperIV.ChordalBasics.IsSimplicial G u)
    (hv : PaperIV.ChordalBasics.IsSimplicial G v) :
    ∃ t s : V, ((t = u ∧ s = v) ∨ (t = v ∧ s = u)) ∧ t ≠ s ∧ ¬ G.Adj t s ∧
      PaperIV.ChordalBasics.IsSimplicial G s ∧
      PaperIV.IsChordal (VertexCopy.graph G t s) ∧
      F4 G ≤ F4 (VertexCopy.graph G t s) ∧
      (F4 G < F4 (VertexCopy.graph G t s) ∨
        (F4 G = F4 (VertexCopy.graph G t s) ∧
          clonePairs G < clonePairs (VertexCopy.graph G t s))) := by
  obtain ⟨t, s, hts, hrank⟩ := exists_copy_clonePairs_lt hne hnadj hclass
  obtain ⟨hne', hnadj', ht', hs'⟩ : t ≠ s ∧ ¬ G.Adj t s ∧
      PaperIV.ChordalBasics.IsSimplicial G t ∧ PaperIV.ChordalBasics.IsSimplicial G s := by
    rcases hts with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hne, hnadj, hu, hv⟩
    · exact ⟨Ne.symm hne, fun h => hnadj h.symm, hv, hu⟩
  by_cases hF4 : F4 G ≤ F4 (VertexCopy.graph G t s)
  · refine ⟨t, s, hts, hne', hnadj', hs',
      VertexCopy.isChordal_graph_of_isSimplicial G hnadj' hG hs', hF4, ?_⟩
    rcases lt_or_eq_of_le hF4 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hrank⟩
  · push_neg at hF4
    have hsum : 2 * F4 G ≤ F4 (VertexCopy.graph G t s) + F4 (VertexCopy.graph G s t) :=
      two_mul_F4_le_add hne' hnadj'
    have hstrict : F4 G < F4 (VertexCopy.graph G s t) := by linarith
    have hts' : (s = u ∧ t = v) ∨ (s = v ∧ t = u) := by
      rcases hts with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
    exact ⟨s, t, hts', Ne.symm hne', fun h => hnadj' h.symm, ht',
      VertexCopy.isChordal_graph_of_isSimplicial G (fun h => hnadj' h.symm) hG ht',
      le_of_lt hstrict, Or.inl hstrict⟩

/-! ### The instance-free potential -/

open Classical in
/-- The mixed fractional defect, with a classical decidability instance, so that
it can be used as a function of the graph alone. -/
noncomputable def F4' (G : SimpleGraph V) : ℝ := @F4 V _ _ G (Classical.decRel _)

open Classical in
/-- The ordered clone pair count, with a classical decidability instance. -/
noncomputable def clonePairs' (G : SimpleGraph V) : ℕ :=
  @clonePairs V _ _ G (Classical.decRel _)

theorem F4_congr_inst (G : SimpleGraph V) (i₁ i₂ : DecidableRel G.Adj) :
    @F4 V _ _ G i₁ = @F4 V _ _ G i₂ := by
  have h : i₁ = i₂ := Subsingleton.elim _ _
  subst h; rfl

theorem clonePairs_congr_inst (G : SimpleGraph V) (i₁ i₂ : DecidableRel G.Adj) :
    @clonePairs V _ _ G i₁ = @clonePairs V _ _ G i₂ := by
  have h : i₁ = i₂ := Subsingleton.elim _ _
  subst h; rfl

theorem F4'_eq (G : SimpleGraph V) [inst : DecidableRel G.Adj] : F4' G = F4 G :=
  F4_congr_inst G _ _

theorem clonePairs'_eq (G : SimpleGraph V) [inst : DecidableRel G.Adj] :
    clonePairs' G = clonePairs G :=
  clonePairs_congr_inst G _ _

open Classical in
/-- The number of graphs on `V` with strictly smaller defect. -/
noncomputable def smallerF4Count (G : SimpleGraph V) : ℕ :=
  (Finset.univ.filter fun H : SimpleGraph V => F4' H < F4' G).card

/-- The lexicographic potential `(F4, clonePairs)` encoded as a natural number. -/
noncomputable def potential (G : SimpleGraph V) : ℕ :=
  smallerF4Count G * (Fintype.card V * Fintype.card V + 1) + clonePairs' G

theorem clonePairs'_le (G : SimpleGraph V) :
    clonePairs' G ≤ Fintype.card V * Fintype.card V := by
  classical
  rw [clonePairs'_eq G]
  exact clonePairs_le G

theorem smallerF4Count_le (G : SimpleGraph V) :
    smallerF4Count G ≤ Fintype.card (SimpleGraph V) := by
  classical
  unfold smallerF4Count
  calc (Finset.univ.filter fun H : SimpleGraph V => F4' H < F4' G).card
      ≤ (Finset.univ : Finset (SimpleGraph V)).card := Finset.card_filter_le _ _
    _ = Fintype.card (SimpleGraph V) := Finset.card_univ

/-- The potential is bounded on the finite set of graphs on `V`. -/
theorem potential_le (G : SimpleGraph V) :
    potential G ≤ Fintype.card (SimpleGraph V) * (Fintype.card V * Fintype.card V + 1)
      + Fintype.card V * Fintype.card V :=
  Nat.add_le_add (Nat.mul_le_mul_right _ (smallerF4Count_le G)) (clonePairs'_le G)

theorem smallerF4Count_lt {G H : SimpleGraph V} (h : F4' G < F4' H) :
    smallerF4Count G < smallerF4Count H := by
  classical
  unfold smallerF4Count
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro X hX
    rw [Finset.mem_filter] at hX ⊢
    exact ⟨hX.1, lt_trans hX.2 h⟩
  · intro hsub
    have hG : G ∈ Finset.univ.filter fun X : SimpleGraph V => F4' X < F4' H :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    have := hsub hG
    rw [Finset.mem_filter] at this
    exact lt_irrefl _ this.2

theorem potential_lt_of_F4'_lt {G H : SimpleGraph V} (h : F4' G < F4' H) :
    potential G < potential H := by
  have hcount : smallerF4Count G + 1 ≤ smallerF4Count H := smallerF4Count_lt h
  have hbound : clonePairs' G ≤ Fintype.card V * Fintype.card V := clonePairs'_le G
  have hstep : smallerF4Count G * (Fintype.card V * Fintype.card V + 1)
      + (Fintype.card V * Fintype.card V + 1)
      ≤ smallerF4Count H * (Fintype.card V * Fintype.card V + 1) := by
    calc smallerF4Count G * (Fintype.card V * Fintype.card V + 1)
          + (Fintype.card V * Fintype.card V + 1)
        = (smallerF4Count G + 1) * (Fintype.card V * Fintype.card V + 1) := by ring
      _ ≤ smallerF4Count H * (Fintype.card V * Fintype.card V + 1) :=
          Nat.mul_le_mul_right _ hcount
  unfold potential
  omega

theorem potential_lt_of_F4'_eq {G H : SimpleGraph V} (h : F4' G = F4' H)
    (hlt : clonePairs' G < clonePairs' H) : potential G < potential H := by
  have hcount : smallerF4Count G = smallerF4Count H := by
    unfold smallerF4Count
    rw [h]
  unfold potential
  rw [hcount]
  omega

/-! ### Iterating the gate -/

/-- Reachability by a finite sequence of *gated* fine copies: every step copies
a simplicial source onto a distinct nonadjacent target, keeps the graph chordal,
does not decrease the mixed fractional defect `F4`, and strictly increases the
lexicographic potential. -/
inductive SymmetrizationPath : SimpleGraph V → SimpleGraph V → Prop
  | refl (G : SimpleGraph V) : SymmetrizationPath G G
  | step {G H : SimpleGraph V} {t s : V} (hne : t ≠ s) (hnadj : ¬ G.Adj t s)
      (hs : PaperIV.ChordalBasics.IsSimplicial G s)
      (hchord : PaperIV.IsChordal (VertexCopy.graph G t s))
      (hF4 : F4' G ≤ F4' (VertexCopy.graph G t s))
      (hpot : potential G < potential (VertexCopy.graph G t s))
      (h : SymmetrizationPath (VertexCopy.graph G t s) H) : SymmetrizationPath G H

/-- Along a gated copy path the mixed fractional defect never decreases. -/
theorem F4'_le_of_symmetrizationPath {G H : SimpleGraph V} (h : SymmetrizationPath G H) : F4' G ≤ F4' H := by
  induction h with
  | refl G => exact le_refl _
  | step _ _ _ _ hF4 _ _ ih => exact le_trans hF4 ih

/-- Along a gated copy path the potential never decreases. -/
theorem potential_le_of_symmetrizationPath {G H : SimpleGraph V} (h : SymmetrizationPath G H) :
    potential G ≤ potential H := by
  induction h with
  | refl G => exact le_refl _
  | step _ _ _ _ _ hpot _ ih => exact le_trans (le_of_lt hpot) ih

/-- **One gated step.**  A chordal graph outside the universal-core split
terminal class admits a fine copy which stays chordal, does not decrease the
mixed fractional defect, and strictly increases the potential. -/
theorem exists_step_of_not_terminal (G : SimpleGraph V) (hG : PaperIV.IsChordal G)
    (hterm : ¬ PaperIV.TerminalSplit.IsUniversalCoreSplit G) :
    ∃ t s : V, t ≠ s ∧ ¬ G.Adj t s ∧ PaperIV.ChordalBasics.IsSimplicial G s ∧
      PaperIV.IsChordal (VertexCopy.graph G t s) ∧
      F4' G ≤ F4' (VertexCopy.graph G t s) ∧
      potential G < potential (VertexCopy.graph G t s) := by
  classical
  obtain ⟨x, y, hx, hy, hxy, hclassSet⟩ :=
    PaperIV.TerminalSplit.exists_nonterminal_simplicial_pair G
      (PaperIV.CopySelector.chordalStructure_of_isChordal G hG) hterm
  have hne : x ≠ y := by
    intro h
    exact hclassSet (by rw [h])
  have hclass : G.neighborFinset x ≠ G.neighborFinset y := by
    intro h
    apply hclassSet
    have := congrArg (fun S : Finset V => (S : Set V)) h
    simpa only [SimpleGraph.coe_neighborFinset] using this
  obtain ⟨t, s, -, hne', hnadj', hs', hchord', hF4le, hdisj⟩ :=
    exists_gate_copy hne hxy hclass hG hx hy
  refine ⟨t, s, hne', hnadj', hs', hchord', ?_, ?_⟩
  · rw [F4'_eq G, F4'_eq (VertexCopy.graph G t s)]
    exact hF4le
  · rcases hdisj with h | ⟨heq, hrank⟩
    · refine potential_lt_of_F4'_lt ?_
      rw [F4'_eq G, F4'_eq (VertexCopy.graph G t s)]
      exact h
    · refine potential_lt_of_F4'_eq ?_ ?_
      · rw [F4'_eq G, F4'_eq (VertexCopy.graph G t s)]
        exact heq
      · rw [clonePairs'_eq G, clonePairs'_eq (VertexCopy.graph G t s)]
        exact hrank

/-- **Termination of the gated fine-copy dynamics.**  From every chordal graph
there is a finite sequence of nonadjacent fine copies with simplicial source,
each step keeping the graph chordal and not decreasing the mixed fractional
defect, which ends in a universal-core split (terminal) graph. -/
theorem exists_terminal_symmetrizationPath (G : SimpleGraph V) (hG : PaperIV.IsChordal G) :
    ∃ H : SimpleGraph V, SymmetrizationPath G H ∧ PaperIV.IsChordal H ∧
      PaperIV.TerminalSplit.IsUniversalCoreSplit H ∧ F4' G ≤ F4' H := by
  classical
  set M := Fintype.card (SimpleGraph V) * (Fintype.card V * Fintype.card V + 1)
      + Fintype.card V * Fintype.card V with hM
  have main : ∀ k : ℕ, ∀ G : SimpleGraph V, PaperIV.IsChordal G → M - potential G ≤ k →
      ∃ H : SimpleGraph V, SymmetrizationPath G H ∧ PaperIV.IsChordal H ∧
        PaperIV.TerminalSplit.IsUniversalCoreSplit H ∧ F4' G ≤ F4' H := by
    intro k
    induction k with
    | zero =>
        intro G hG hk
        by_cases hterm : PaperIV.TerminalSplit.IsUniversalCoreSplit G
        · exact ⟨G, SymmetrizationPath.refl G, hG, hterm, le_refl _⟩
        · exfalso
          obtain ⟨t, s, hne, hnadj, hs, -, -, hpot⟩ := exists_step_of_not_terminal G hG hterm
          have hb := potential_le (VertexCopy.graph G t s)
          rw [← hM] at hb
          omega
    | succ k ih =>
        intro G hG hk
        by_cases hterm : PaperIV.TerminalSplit.IsUniversalCoreSplit G
        · exact ⟨G, SymmetrizationPath.refl G, hG, hterm, le_refl _⟩
        · obtain ⟨t, s, hne, hnadj, hs, hchord', hF4le, hpot⟩ :=
            exists_step_of_not_terminal G hG hterm
          have hb := potential_le (VertexCopy.graph G t s)
          rw [← hM] at hb
          obtain ⟨H, hreach, hHchord, hHterm, hHF4⟩ :=
            ih (VertexCopy.graph G t s) hchord' (by omega)
          exact ⟨H, SymmetrizationPath.step hne hnadj hs hchord' hF4le hpot hreach, hHchord, hHterm,
            le_trans hF4le hHF4⟩
  exact main M G hG (Nat.sub_le _ _)

/-! ### Necessity of the `F4` dichotomy

The clone pair count alone cannot be the descent measure: on the literal
four-vertex chordal graph `gateG` (the single edge `2 — 3` with `0` and `1`
isolated) and its nonadjacent simplicial pair `0, 2`, *neither* orientation is
simultaneously `F4`-nondecreasing and clone-pair-increasing.  The orientation
selected by the class comparison (copy `0` onto `2`, whose source class `{0,1}`
is the larger one) strictly *decreases* `F4`, and the `F4`-nondecreasing
orientation (copy `2` onto `0`) leaves the clone pair count unchanged.  This is
exactly the configuration handled by the second branch of `exists_gate_copy`,
where `F4` increases strictly. -/

/-- The optimum of the packing LP vanishes when there are no items. -/
theorem optVal_eq_zero_of_items_empty (X : SimpleGraph V) [DecidableRel X.Adj]
    (h : PaperIV.FarRounding.items X = ∅) : optVal X = 0 := by
  obtain ⟨x, hx⟩ := exists_fracPacking_value_eq_optVal X
  rw [← hx, PaperIV.FarRounding.FracPacking.value, h, Finset.sum_empty]

section Necessity

/-- Adjacency generator of the necessity witness: the single edge `2 — 3`. -/
def gateRel : Fin 4 → Fin 4 → Prop := fun a b => a = 2 ∧ b = 3

instance : DecidableRel gateRel := fun a b => by unfold gateRel; infer_instance

/-- The single edge `2 — 3` with `0` and `1` isolated. -/
def gateG : SimpleGraph (Fin 4) := SimpleGraph.fromRel gateRel

instance : DecidableRel gateG.Adj := fun a b =>
  decidable_of_iff _ (SimpleGraph.fromRel_adj gateRel a b).symm

theorem gateG_chordal : PaperIV.IsChordal gateG :=
  isChordal_of_card_edgeFinset_le gateG (by decide)

theorem gateG_simplicial_zero : PaperIV.ChordalBasics.IsSimplicial gateG 0 := by
  have hkey : ∀ x y : Fin 4, gateG.Adj 0 x → gateG.Adj 0 y → x ≠ y → gateG.Adj x y := by decide
  intro x hx y hy hxy
  exact hkey x y hx hy hxy

theorem gateG_simplicial_two : PaperIV.ChordalBasics.IsSimplicial gateG 2 := by
  have hkey : ∀ x y : Fin 4, gateG.Adj 2 x → gateG.Adj 2 y → x ≠ y → gateG.Adj x y := by decide
  intro x hx y hy hxy
  exact hkey x y hx hy hxy

theorem gateG_nonadj : ¬ gateG.Adj 0 2 := by decide

theorem gateG_classes : gateG.neighborFinset 0 ≠ gateG.neighborFinset 2 := by decide

theorem gateG_items : PaperIV.FarRounding.items gateG = ∅ := by decide

theorem gateG_items_copy_zero :
    PaperIV.FarRounding.items (VertexCopy.graph gateG 0 2) = ∅ := by decide

theorem gateG_items_copy_two :
    PaperIV.FarRounding.items (VertexCopy.graph gateG 2 0) = ∅ := by decide

theorem F4_gateG : F4 gateG = 1 := by
  unfold F4
  rw [optVal_eq_zero_of_items_empty gateG gateG_items,
    show gateG.edgeFinset.card = 1 from by decide]
  norm_num

theorem F4_gateG_copy_zero : F4 (VertexCopy.graph gateG 0 2) = 2 := by
  unfold F4
  rw [optVal_eq_zero_of_items_empty _ gateG_items_copy_zero,
    show (VertexCopy.graph gateG 0 2).edgeFinset.card = 2 from by decide]
  norm_num

theorem F4_gateG_copy_two : F4 (VertexCopy.graph gateG 2 0) = 0 := by
  unfold F4
  rw [optVal_eq_zero_of_items_empty _ gateG_items_copy_two,
    show (VertexCopy.graph gateG 2 0).edgeFinset.card = 0 from by decide]
  norm_num

theorem gateG_clonePairs_copy_zero :
    clonePairs (VertexCopy.graph gateG 0 2) = clonePairs gateG := by decide

/-- **The clone pair count alone is not a compatible rank.**  For this chordal
graph and this nonadjacent simplicial pair, no orientation of the fine copy is
both `F4`-nondecreasing and clone-pair-increasing; the orientation supplied by
`exists_gate_copy` is the one with a strict `F4` increase. -/
theorem gate_dichotomy_necessary (t s : Fin 4) (h : (t = 0 ∧ s = 2) ∨ (t = 2 ∧ s = 0)) :
    ¬ (F4 gateG ≤ F4 (VertexCopy.graph gateG t s) ∧
      clonePairs gateG < clonePairs (VertexCopy.graph gateG t s)) := by
  rintro ⟨hF4, hrank⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [gateG_clonePairs_copy_zero] at hrank
    exact lt_irrefl _ hrank
  · rw [F4_gateG, F4_gateG_copy_two] at hF4
    norm_num at hF4

end Necessity

/-! ### The gate on the `VertexCopyRank` counterexample

On the four-vertex chordal graph `VertexCopyRank.cexG` (the path `0 — 3 — 2`
with `1` isolated) the clone *class count* is blind to the copy of `1` onto `0`
(`VertexCopyRank.cexCopy_cloneClassCount_eq`).  The ordered clone *pair* count
is blind to exactly the same orientation — and the selector of this module is
the one that rejects it: the class of the source `1` is smaller than the class
of the target `0`, so the selector copies `0` onto `1` instead, and there the
pair count jumps from `2` to `6`. -/

/-- The rejected orientation: copying `1` onto `0` leaves the clone pair count
unchanged, just as it left the clone class count unchanged. -/
theorem cex_clonePairs_copy_zero_eq :
    clonePairs (VertexCopy.graph cexG 0 1) = clonePairs cexG := by decide

/-- The selected orientation: the source class is the larger one, and the clone
pair count strictly increases. -/
theorem cex_card_cloneClass_le : (cloneClass cexG 1).card ≤ (cloneClass cexG 0).card := by decide

theorem cex_clonePairs_copy_one_lt :
    clonePairs cexG < clonePairs (VertexCopy.graph cexG 1 0) := by decide

end PaperIV.VertexCopyGate
