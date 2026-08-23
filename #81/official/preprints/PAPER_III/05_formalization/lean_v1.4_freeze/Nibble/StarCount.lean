/-
# Nibble — counting: an improving move always exists at a large uncovered star

At the Dross density `9|V| ≤ 10 δ(G)`, if a triangle packing `M` leaves a vertex `v` with a large
uncovered star and only *few* vertices carry an uncovered star comparable with that of `v`, then one
of the two moves of `Nibble/StarMoves.lean` applies, so the potential `Nibble.uncoveredPot` is not
minimal.

The counting behind this:

* almost all vertices are *cheap* (uncovered star at most `|uncoveredAt v| / 64`), by hypothesis;
* hence almost all edges are *good* (`Nibble.GoodEdgeAt`): the packing triangle covering an edge has
  a cheap third vertex, since a triangle with an expensive vertex is one of at most `|Z|·|V|`;
* hence almost every vertex sees `≥ 0.79|V|` good edges into the neighbourhood of `v`, by the
  density `δ(G) ≥ 0.9|V|`;
* if two cheap uncovered star neighbours of `v` are joined by a good edge, the short move applies;
* otherwise the good neighbourhood of one uncovered star neighbour `a₀` lands in the *matched* part
  of the star of `v`, whose partner map is injective, and the resulting set of `≥ 0.78|V|` partners
  meets the good neighbourhood of a second uncovered star neighbour `a₁` — the long move applies.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.StarMoves

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Edges and triangles at a vertex -/

/-- The edges of `G` at the vertex `z`, as hypergraph vertices. -/
def edgesAt (G : SimpleGraph V) [DecidableRel G.Adj] (z : V) : Finset (EdgeV G) :=
  Finset.univ.filter (fun E => z ∈ E.val)

theorem mem_edgesAt (G : SimpleGraph V) [DecidableRel G.Adj] {z : V} {E : EdgeV G} :
    E ∈ edgesAt G z ↔ z ∈ E.val := by
  classical
  simp [edgesAt]

theorem card_edgesAt_le (G : SimpleGraph V) [DecidableRel G.Adj] (z : V) :
    (edgesAt G z).card ≤ Fintype.card V := by
  classical
  haveI : Nonempty V := ⟨z⟩
  have hex : ∀ E ∈ edgesAt G z, ∃ w : V, ∃ h : G.Adj z w, E = edgeE G h := by
    intro E hE
    exact exists_other_endpoint G ((mem_edgesAt G).mp hE)
  choose! f hf using hex
  rw [← Finset.card_univ (α := V)]
  refine Finset.card_le_card_of_injOn f (fun E _ => Finset.mem_univ _) ?_
  intro E hE E' hE' heq
  obtain ⟨h1, he1⟩ := hf E hE
  obtain ⟨h2, he2⟩ := hf E' hE'
  have hv1 : E.val = ({z, f E} : Finset V) := by nth_rewrite 1 [he1]; rfl
  have hv2 : E'.val = ({z, f E'} : Finset V) := by nth_rewrite 1 [he2]; rfl
  exact Subtype.ext (by rw [hv1, hv2, heq])

/-- The uncovered star is at most the full star. -/
theorem unDeg_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset (EdgeV G))) (z : V) : unDeg G M z ≤ Fintype.card V := by
  classical
  refine le_trans (Finset.card_le_card ?_) (card_edgesAt_le G z)
  intro E hE
  rw [mem_uncoveredAt] at hE
  exact (mem_edgesAt G).mpr hE.1

/-- A vertex lies on at most `|V|` packing triangles. -/
theorem card_trianglesAt_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M) (z : V) :
    (M.filter (fun T => z ∈ triOf G T)).card ≤ Fintype.card V := by
  classical
  haveI : Nonempty V := ⟨z⟩
  by_cases hMz : (M.filter (fun T => z ∈ triOf G T)) = ∅
  · rw [hMz]; simp
  obtain ⟨T₀, hT₀⟩ := Finset.nonempty_of_ne_empty hMz
  have hE₀ : ∃ E : EdgeV G, E ∈ T₀ := by
    have h := (Finset.mem_filter.mp hT₀).2
    rw [triOf, Finset.mem_biUnion] at h
    obtain ⟨E, hE, -⟩ := h
    exact ⟨E, hE⟩
  haveI : Nonempty (EdgeV G) := ⟨hE₀.choose⟩
  have hex : ∀ T ∈ M.filter (fun T => z ∈ triOf G T), ∃ E : EdgeV G, E ∈ T ∧ z ∈ E.val := by
    intro T hT
    rw [Finset.mem_filter] at hT
    have := hT.2
    rw [triOf, Finset.mem_biUnion] at this
    obtain ⟨E, hE, hz⟩ := this
    exact ⟨E, hE, hz⟩
  choose! φ hφ1 hφ2 using hex
  refine le_trans (Finset.card_le_card_of_injOn φ ?_ ?_) (card_edgesAt_le G z)
  · intro T hT
    exact (mem_edgesAt G).mpr (hφ2 T hT)
  · intro T hT T' hT' heq
    have h1 := hφ1 T hT
    have h2 := hφ1 T' hT'
    rw [heq] at h1
    exact eq_of_mem_of_mem G hM (Finset.mem_filter.mp hT).1 (Finset.mem_filter.mp hT').1 h1 h2

/-! ### Expensive vertices, bad edges, bad vertices -/

open scoped Classical in
/-- The vertices whose uncovered star is more than `dd / 64`. -/
noncomputable def Zexp (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset (EdgeV G))) (dd : ℕ) : Finset V :=
  Finset.univ.filter (fun u => ¬ (64 * unDeg G M u ≤ dd))

open scoped Classical in
/-- The edges that are not good: some packing triangle covering them has an expensive vertex off
the edge. -/
noncomputable def badE (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset (EdgeV G))) (dd : ℕ) : Finset (EdgeV G) :=
  Finset.univ.filter (fun E => ¬ GoodEdgeAt G M dd E)

open scoped Classical in
/-- The vertices lying on more than `|V|/100` bad edges. -/
noncomputable def Bad (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset (EdgeV G))) (dd : ℕ) : Finset V :=
  Finset.univ.filter (fun x => Fintype.card V < 100 * ((badE G M dd).filter
    (fun E => x ∈ E.val)).card)

theorem mem_Zexp (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} {dd : ℕ} {u : V} :
    u ∈ Zexp G M dd ↔ ¬ (64 * unDeg G M u ≤ dd) := by
  classical
  simp [Zexp]

theorem cheap_of_notMem_Zexp (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} {dd : ℕ} {u : V} (h : u ∉ Zexp G M dd) :
    64 * unDeg G M u ≤ dd := by
  by_contra hc
  exact h ((mem_Zexp G).mpr hc)

/-- **Bad edges are few.**  Every bad edge lies on a packing triangle with an expensive vertex, and
each expensive vertex lies on at most `|V|` triangles. -/
theorem card_badE_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M) (dd : ℕ) :
    (badE G M dd).card ≤ 3 * ((Zexp G M dd).card * Fintype.card V) := by
  classical
  set Mbad : Finset (Finset (EdgeV G)) :=
    M.filter (fun T => ∃ z ∈ triOf G T, z ∈ Zexp G M dd) with hMbad
  have hsub : badE G M dd ⊆ Mbad.biUnion id := by
    intro E hE
    rw [badE, Finset.mem_filter] at hE
    have hnot := hE.2
    rw [GoodEdgeAt] at hnot
    push_neg at hnot
    obtain ⟨T, hT, hET, z, hz, hz1, hz2⟩ := hnot
    refine Finset.mem_biUnion.mpr ⟨T, ?_, hET⟩
    rw [hMbad, Finset.mem_filter]
    exact ⟨hT, z, hz, (mem_Zexp G).mpr (by omega)⟩
  have h1 : (Mbad.biUnion id).card ≤ ∑ T ∈ Mbad, (id T).card := Finset.card_biUnion_le
  have h2 : ∑ T ∈ Mbad, (id T).card = 3 * Mbad.card := by
    have : ∀ T ∈ Mbad, (id T).card = 3 := by
      intro T hT
      rw [hMbad, Finset.mem_filter] at hT
      exact triangleHypergraphSub_uniform G T (hM.subset hT.1)
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_comm]
  have h3 : Mbad ⊆ (Zexp G M dd).biUnion (fun z => M.filter (fun T => z ∈ triOf G T)) := by
    intro T hT
    rw [hMbad, Finset.mem_filter] at hT
    obtain ⟨hTM, z, hz, hzZ⟩ := hT
    exact Finset.mem_biUnion.mpr ⟨z, hzZ, Finset.mem_filter.mpr ⟨hTM, hz⟩⟩
  have h4 : ((Zexp G M dd).biUnion (fun z => M.filter (fun T => z ∈ triOf G T))).card
      ≤ ∑ z ∈ Zexp G M dd, (M.filter (fun T => z ∈ triOf G T)).card := Finset.card_biUnion_le
  have h5 : ∑ z ∈ Zexp G M dd, (M.filter (fun T => z ∈ triOf G T)).card
      ≤ ∑ _z ∈ Zexp G M dd, Fintype.card V :=
    Finset.sum_le_sum (fun z _ => card_trianglesAt_le G hM z)
  have h6 : ∑ _z ∈ Zexp G M dd, Fintype.card V = (Zexp G M dd).card * Fintype.card V := by
    rw [Finset.sum_const, smul_eq_mul]
  have h7 : Mbad.card ≤ (Zexp G M dd).card * Fintype.card V :=
    le_trans (Finset.card_le_card h3) (by omega)
  have h8 : (badE G M dd).card ≤ (Mbad.biUnion id).card := Finset.card_le_card hsub
  omega

/-- The bad degrees sum to twice the number of bad edges. -/
theorem sum_badDeg (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset (EdgeV G))) (dd : ℕ) :
    ∑ x : V, ((badE G M dd).filter (fun E => x ∈ E.val)).card = 2 * (badE G M dd).card := by
  classical
  have h1 : ∀ x : V, ((badE G M dd).filter (fun E => x ∈ E.val)).card
      = ∑ E ∈ badE G M dd, (if x ∈ E.val then 1 else 0) := by
    intro x; rw [Finset.card_filter]
  have h2 : ∑ x : V, ∑ E ∈ badE G M dd, (if x ∈ E.val then 1 else 0)
      = ∑ E ∈ badE G M dd, ∑ x : V, (if x ∈ E.val then 1 else 0) := Finset.sum_comm
  have h3 : ∀ E : EdgeV G, ∑ x : V, (if x ∈ E.val then 1 else 0) = 2 := by
    intro E
    have hcard : E.val.card = 2 :=
      (SimpleGraph.mem_cliqueFinset_iff.mp E.property).card_eq
    rw [← Finset.card_filter, Finset.filter_univ_mem, hcard]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), h2, Finset.sum_congr rfl (fun E _ => h3 E),
    Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Bad vertices are few.** -/
theorem card_Bad_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M) (dd : ℕ)
    (hn : 0 < Fintype.card V) :
    (Bad G M dd).card ≤ 600 * (Zexp G M dd).card := by
  classical
  set n := Fintype.card V with hn'
  set f : V → ℕ := fun x => ((badE G M dd).filter (fun E => x ∈ E.val)).card with hf
  have hsum : ∑ x : V, f x = 2 * (badE G M dd).card := sum_badDeg G M dd
  have hBad : ∀ x ∈ Bad G M dd, n < 100 * f x := by
    intro x hx
    rw [Bad, Finset.mem_filter] at hx
    exact hx.2
  have hlow : (Bad G M dd).card * n ≤ ∑ x ∈ Bad G M dd, 100 * f x := by
    calc (Bad G M dd).card * n = ∑ _x ∈ Bad G M dd, n := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ Bad G M dd, 100 * f x :=
        Finset.sum_le_sum (fun x hx => le_of_lt (hBad x hx))
  have hup : ∑ x ∈ Bad G M dd, 100 * f x ≤ 100 * ∑ x : V, f x := by
    rw [← Finset.mul_sum]
    have : ∑ x ∈ Bad G M dd, f x ≤ ∑ x : V, f x :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    omega
  have hbE := card_badE_le G hM dd
  rw [← hn'] at hbE
  have hkey : (Bad G M dd).card * n ≤ 600 * ((Zexp G M dd).card * n) := by
    have : 100 * (2 * (badE G M dd).card) ≤ 100 * (2 * (3 * ((Zexp G M dd).card * n))) := by
      omega
    omega
  have : (Bad G M dd).card * n ≤ (600 * (Zexp G M dd).card) * n := by
    calc (Bad G M dd).card * n ≤ 600 * ((Zexp G M dd).card * n) := hkey
      _ = (600 * (Zexp G M dd).card) * n := by ring
  exact Nat.le_of_mul_le_mul_right this hn

/-! ### The good neighbourhood -/

open scoped Classical in
/-- The vertices `w` adjacent both to `a` and to `v` for which the edge `aw` is good. -/
noncomputable def goodNbr (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset (EdgeV G))) (dd : ℕ) (v a : V) : Finset V :=
  (G.neighborFinset a ∩ G.neighborFinset v).filter
    (fun w => ∃ h : G.Adj a w, GoodEdgeAt G M dd (edgeE G h))

theorem goodNbr_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset (EdgeV G))) (dd : ℕ) (v a : V) :
    goodNbr G M dd v a ⊆ G.neighborFinset v := by
  classical
  intro w hw
  rw [goodNbr, Finset.mem_filter, Finset.mem_inter] at hw
  exact hw.1.2

theorem adj_of_mem_goodNbr (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} {dd : ℕ} {v a w : V} (hw : w ∈ goodNbr G M dd v a) :
    G.Adj a w := by
  classical
  rw [goodNbr, Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
  exact hw.1.1

theorem good_of_mem_goodNbr (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} {dd : ℕ} {v a w : V} (hw : w ∈ goodNbr G M dd v a)
    (h : G.Adj a w) : GoodEdgeAt G M dd (edgeE G h) := by
  classical
  rw [goodNbr, Finset.mem_filter] at hw
  obtain ⟨h', hg⟩ := hw.2
  exact hg

/-- **The good neighbourhood is large.**  At the Dross density, a vertex `a` lying on few bad edges
sees at least `0.79|V|` good edges into the neighbourhood of `v`. -/
theorem card_goodNbr_ge (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (M : Finset (Finset (EdgeV G))) (dd : ℕ) (v a : V) (ha : a ∉ Bad G M dd) :
    790 * Fintype.card V ≤ 1000 * (goodNbr G M dd v a).card := by
  classical
  set n := Fintype.card V with hn
  -- the common neighbourhood is large
  have hda : 9 * n ≤ 10 * G.degree a := le_trans hdense (by
    have := G.minDegree_le_degree a; omega)
  have hdv : 9 * n ≤ 10 * G.degree v := le_trans hdense (by
    have := G.minDegree_le_degree v; omega)
  have hunion : (G.neighborFinset a ∪ G.neighborFinset v).card ≤ n := by
    rw [hn, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  have hIE : (G.neighborFinset a ∩ G.neighborFinset v).card
      + (G.neighborFinset a ∪ G.neighborFinset v).card
      = (G.neighborFinset a).card + (G.neighborFinset v).card :=
    Finset.card_inter_add_card_union _ _
  have hdeg1 : (G.neighborFinset a).card = G.degree a := rfl
  have hdeg2 : (G.neighborFinset v).card = G.degree v := rfl
  have hcommon : 8 * n ≤ 10 * (G.neighborFinset a ∩ G.neighborFinset v).card := by
    omega
  -- the vertices dropped by the filter inject into the bad edges at `a`
  set N : Finset V := G.neighborFinset a ∩ G.neighborFinset v with hN
  set D : Finset V := N \ goodNbr G M dd v a with hD
  have hDbad : D.card ≤ ((badE G M dd).filter (fun E => a ∈ E.val)).card := by
    rcases Finset.eq_empty_or_nonempty D with hDe | ⟨w₀, hw₀⟩
    · simp [hDe]
    · have hadjof : ∀ w ∈ D, G.Adj a w := by
        intro w hw
        rw [hD, Finset.mem_sdiff] at hw
        have := hw.1
        rw [hN, Finset.mem_inter, SimpleGraph.mem_neighborFinset] at this
        exact this.1
      haveI : Nonempty (EdgeV G) := ⟨edgeE G (hadjof w₀ hw₀)⟩
      have hex : ∀ w ∈ D, ∃ E : EdgeV G, E ∈ badE G M dd ∧ a ∈ E.val ∧ w ∈ E.val := by
        intro w hw
        have hadj : G.Adj a w := hadjof w hw
        rw [hD, Finset.mem_sdiff] at hw
        refine ⟨edgeE G hadj, ?_, by simp, by simp⟩
        rw [badE, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun hg => hw.2 ?_⟩
        rw [goodNbr, Finset.mem_filter]
        exact ⟨hw.1, hadj, hg⟩
      choose! F hF1 hF2 hF3 using hex
      have hval : ∀ u ∈ D, (F u).val = ({a, u} : Finset V) := by
        intro u hu
        have hau : a ≠ u := (hadjof u hu).ne
        have h2 : ({a, u} : Finset V) ⊆ (F u).val := by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · exact hF2 _ hu
          · exact hF3 _ hu
        have hcard : (F u).val.card = 2 :=
          (SimpleGraph.mem_cliqueFinset_iff.mp (F u).property).card_eq
        have hc2 : ({a, u} : Finset V).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simp [hau]), Finset.card_singleton]
        exact (Finset.eq_of_subset_of_card_le h2 (by omega)).symm
      refine Finset.card_le_card_of_injOn F
        (fun w hw => Finset.mem_filter.mpr ⟨hF1 w hw, hF2 w hw⟩) ?_
      intro w hw w' hw' heq
      have h1 := hval w hw
      have h2 := hval w' hw'
      rw [heq, h2] at h1
      have h4 : w ∈ ({a, w'} : Finset V) := by rw [h1]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at h4
      rcases h4 with rfl | rfl
      · exact absurd rfl (hadjof w hw).ne'
      · rfl
  have hna : 100 * ((badE G M dd).filter (fun E => a ∈ E.val)).card ≤ n := by
    by_contra hc
    push_neg at hc
    exact ha (by rw [Bad, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hc⟩)
  have hsplit : (goodNbr G M dd v a).card + D.card = N.card := by
    have hsub : goodNbr G M dd v a ⊆ N := by
      intro w hw
      rw [goodNbr, Finset.mem_filter] at hw
      exact hw.1
    have hcs : D.card + (goodNbr G M dd v a).card = N.card := by
      rw [hD]; exact Finset.card_sdiff_add_card_eq_card hsub
    omega
  omega

end Nibble
