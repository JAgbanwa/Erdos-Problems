import PaperII.L2
import PaperII.L3
import PaperII.L4
import PaperII.L5

/-!
# Paper II — Symmetrization (ledger L6 = Theorem 5.3)

Every chordal `G` on `n` vertices reduces, by a finite sequence of admissible clone-class copies, to a
complete-split `S_{p,q}` (`p+q=n`) with `Φ_τ` nondecreasing. WF recursion on `cloneClassCount G`
(strictly decreasing by L3); each step: L5 gives a both-simplicial admissible pair, L2 a
`Φ_τ`-nondecreasing direction, L4 (A2) keeps it chordal, L3 drops the clone-class count; the process
halts at a terminal graph, which by L7 is complete-split.
-/

open scoped BigOperators

namespace PaperII

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Seam 1: nonadjacent `x,y` ⇒ the clone class of `N(x)` is disjoint from `N(y)`
(if `N(v)=N(x)` and `v ∈ N(y)` then `y ∈ N(v)=N(x)`, i.e. `x` adjacent to `y`). -/
theorem disjoint_sourceClass_nbhd (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V}
    (hxy : ¬ G.Adj x y) :
    Disjoint (sourceClass G (G.neighborFinset x)) (G.neighborFinset y) := by
  rw [Finset.disjoint_left]
  intro v hv hvy
  rw [mem_sourceClass] at hv
  have h1 : G.Adj y v := (SimpleGraph.mem_neighborFinset G y v).1 hvy
  have h2 : y ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset G v y).2 h1.symm
  rw [hv] at h2
  exact hxy ((SimpleGraph.mem_neighborFinset G x y).1 h2)

/-
Seam 2: a simplicial vertex's neighborhood (as a coerced Finset) is a clique.
-/
theorem isClique_neighborFinset_of_simplicial (G : SimpleGraph V) [DecidableRel G.Adj] {x : V}
    (hx : IsSimplicial G x) : G.IsClique (G.neighborFinset x : Set V) := by
  convert hx using 1;
  simp +decide [ IsSimplicial, SimpleGraph.coe_neighborFinset ]

/-
One reduction step: from a non-complete-split chordal `G`, produce a class-copy orientation
`A → B` that stays chordal, strictly drops the clone-class count, and does not decrease `Φ_τ`.
-/
theorem symm_step (G : SimpleGraph V) [DecidableRel G.Adj]
    (hchord : ChordalStructure G) (hnc : ¬ IsCompleteSplit G) :
    ∃ A B : Finset V,
      G.IsClique (B : Set V) ∧
      cloneClassCount (classCopy G A B) < cloneClassCount G ∧
      phiTau G ≤ phiTau (classCopy G A B) := by
  have := PaperII.exists_both_simplicial_pair G hchord hnc; obtain ⟨ x, y, hx, hy, hnadj, hne ⟩ := this;
  -- Set A := G.neighborFinset x and B := G.neighborFinset y.
  set A := G.neighborFinset x
  set B := G.neighborFinset y;
  have hAB : A ≠ B := by
    simp_all +decide [ Finset.ext_iff, SimpleGraph.neighborSet ];
    contrapose! hne; aesop;
  have hxA : x ∈ sourceClass G A := by
    -- By definition of sourceClass, we need to show that G.neighborFinset x = A.
    simp [sourceClass, A]
  have hyB : y ∈ sourceClass G B := by
    exact mem_sourceClass G B y |>.2 rfl
  have hcliqueA : G.IsClique (A : Set V) := by
    exact PaperII.isClique_neighborFinset_of_simplicial G hx
  have hcliqueB : G.IsClique (B : Set V) := by
    exact isClique_neighborFinset_of_simplicial G hy
  have hAdisj : Disjoint (sourceClass G A) B := by
    exact disjoint_sourceClass_nbhd G hnadj
  have hBdisj : Disjoint (sourceClass G B) A := by
    convert disjoint_sourceClass_nbhd G ( fun h => hnadj h.symm ) using 1;
  have hmax : phiTau G ≤ max (phiTau (classCopy G A B)) (phiTau (classCopy G B A)) := by
    apply PaperII.phiTau_le_max_classCopy G (by
    exact ⟨ x, hxA ⟩) (by
    exact ⟨ y, hyB ⟩) hAB hAdisj hBdisj;
  have hnonadjAB : ∀ v, G.neighborFinset v = A → v ∉ B := by
    exact fun v hv hvB => Finset.disjoint_left.mp hAdisj ( by rw [ mem_sourceClass ] ; exact hv ) hvB
  have hnonadjBA : ∀ v, G.neighborFinset v = B → v ∉ A := by
    exact fun v hv hvA => Finset.disjoint_left.mp hBdisj ( by rw [ mem_sourceClass ] ; exact hv ) hvA;
  cases max_choice ( phiTau ( classCopy G A B ) ) ( phiTau ( classCopy G B A ) ) <;> simp_all +decide only;
  · exact ⟨ A, B, hcliqueB, PaperII.cloneClassCount_classCopy_lt G A B ( by exact ⟨ x, hxA ⟩ ) ( by exact ⟨ y, hyB ⟩ ) hAB hnonadjAB, hmax ⟩;
  · exact ⟨ B, A, hcliqueA, PaperII.cloneClassCount_classCopy_lt G B A ⟨ y, hyB ⟩ ⟨ x, hxA ⟩ hAB.symm hnonadjBA, hmax ⟩

/-- Ledger L6 (Theorem 5.3): symmetrization to a complete-split with `Φ_τ` nondecreasing. -/
theorem symmetrization (hA2 : A2Transfer V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hchord : ChordalStructure G) :
    ∃ p q : ℕ, p + q = Fintype.card V ∧ phiTau G ≤ phiTau (completeSplit p q) := by
  classical
  by_cases h : IsCompleteSplit G
  · obtain ⟨p, q, ⟨e⟩⟩ := h
    refine ⟨p, q, ?_, ?_⟩
    · have hc := Fintype.card_congr e.toEquiv
      simp [Fintype.card_sum, Fintype.card_fin] at hc
      omega
    · have hiso := phiTau_iso G (completeSplit p q) e
      rw [hiso]
  · obtain ⟨A, B, hcliqueB, hlt, hle⟩ := symm_step G hchord h
    have hchord' : ChordalStructure (classCopy G A B) :=
      chordalStructure_classCopy hA2 G A B hchord hcliqueB
    obtain ⟨p, q, hpq, hle'⟩ := symmetrization hA2 (classCopy G A B) hchord'
    exact ⟨p, q