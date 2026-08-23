/-
# Nibble — an unconditional spread decomposition with *non-constant* codegree

`Nibble/DrossSpread.lean` proves the spread Dross conclusion
(`Nibble.HasSpreadFracTriangleDecomp`) unconditionally for **codegree-regular** graphs, where the
uniform triangle weighting `1/d` is already exact.  This file gives an unconditional instance in
which the codegree is *not* constant, so the uniform weighting is not exact and the weights have to
be chosen per triangle type: the **complete split graphs** `Kₙ` minus a clique, i.e. the graphs in
which one part `S` is independent and every other pair is adjacent.

* `Nibble.IsCompleteSplit` — the defining adjacency.
* `Nibble.sum_trianglesThrough_eq_commonNbrs` — the sum dictionary: summing a function of the
  vertex set of a triangle over the triangles through an edge is summing over the common
  neighbourhood of the edge.  (Reusable; the counting version is
  `Nibble.card_trianglesThrough_eq_commonNbrs`.)
* `Nibble.hasSpreadFracTriangleDecomp_of_completeSplit` — at the Dross density a complete split
  graph carries a fractional triangle decomposition with all weights at most `2/|V|`.

The decomposition is explicit: with `c = |V| - |S|` the weight is `1/(c-1)` on a triangle meeting
`S` and `(c-1-|S|)/((c-1)(c-2))` on a triangle avoiding it.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DrossSpread
import Nibble.DrossGadget

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Summing over the common neighbourhood -/

/-- **The sum dictionary.**  Summing a function of the vertex set of a triangle over the triangles
through an edge `e` is summing it over the common neighbourhood of `e`. -/
theorem sum_trianglesThrough_eq_commonNbrs (G : SimpleGraph V) [DecidableRel G.Adj] (e : EdgeV G)
    (F : Finset V → ℝ) :
    ∑ T ∈ trianglesThrough G e, F (triOf G T)
      = ∑ z ∈ commonNbrs G e, F (insert z e.val) := by
  classical
  rw [sum_trianglesThrough_eq G e F, cliqueFinset3_filter_supset_eq_image G e,
    Finset.sum_image]
  intro z hz z' hz' heq
  exact insert_commonNbrs_injOn G e (by simpa using hz) (by simpa using hz') heq

/-! ### Complete split graphs -/

/-- `G` is the **complete split graph** with independent part `S`: two distinct vertices are
adjacent unless both lie in `S`. -/
def IsCompleteSplit (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u v : V, G.Adj u v ↔ (u ≠ v ∧ ¬(u ∈ S ∧ v ∈ S))

/-- In a complete split graph the neighbourhood of a vertex of `S` is the complement of `S`. -/
theorem neighborFinset_eq_of_completeSplit {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V}
    (h : IsCompleteSplit G S) {u : V} (hu : u ∈ S) :
    G.neighborFinset u = Finset.univ \ S := by
  ext z
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff, Finset.mem_univ, true_and, h u z]
  constructor
  · rintro ⟨hne, hns⟩ hzS
    exact hns ⟨hu, hzS⟩
  · intro hzS
    exact ⟨fun hrfl => hzS (hrfl ▸ hu), fun hc => hzS hc.2⟩

/-- **The common neighbourhood of an edge with an endpoint in the independent part**: everything
outside `S` except the other endpoint. -/
theorem commonNbrs_of_completeSplit_mixed {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V}
    (hsplit : IsCompleteSplit G S) {e : EdgeV G} {p q : V} (hp : p ∈ S)
    (hpq : e.val = ({p, q} : Finset V)) :
    commonNbrs G e = (Finset.univ \ S) \ ({q} : Finset V) := by
  classical
  have hcn : ∀ z : V, z ∈ commonNbrs G e ↔ (z ∉ S ∧ z ≠ q) := by
    intro z
    constructor
    · intro hz
      rw [commonNbrs, Finset.mem_filter] at hz
      have h1 : G.Adj p z := hz.2 p (by rw [hpq]; simp)
      have h2 : G.Adj q z := hz.2 q (by rw [hpq]; simp)
      exact ⟨fun hzS => ((hsplit p z).mp h1).2 ⟨hp, hzS⟩,
        fun hzq => ((hsplit q z).mp h2).1 hzq.symm⟩
    · rintro ⟨hzS, hzq⟩
      rw [commonNbrs, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro x hx
      rw [hpq] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact (hsplit x z).mpr ⟨fun hrfl => hzS (hrfl ▸ hp), fun hc => hzS hc.2⟩
      · rw [Finset.mem_singleton] at hx'
        subst hx'
        exact (hsplit x z).mpr ⟨fun hrfl => hzq hrfl.symm, fun hc => hzS hc.2⟩
  ext z
  rw [hcn z]
  simp

/-- **The common neighbourhood of an edge inside the complete part**: everything but the edge. -/
theorem commonNbrs_of_completeSplit_pure {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V}
    (hsplit : IsCompleteSplit G S) {e : EdgeV G} {u v : V} (hu : u ∉ S) (hv : v ∉ S)
    (hval : e.val = ({u, v} : Finset V)) :
    commonNbrs G e = Finset.univ \ e.val := by
  classical
  have hcn : ∀ z : V, z ∈ commonNbrs G e ↔ (z ≠ u ∧ z ≠ v) := by
    intro z
    constructor
    · intro hz
      rw [commonNbrs, Finset.mem_filter] at hz
      have h1 : G.Adj u z := hz.2 u (by rw [hval]; simp)
      have h2 : G.Adj v z := hz.2 v (by rw [hval]; simp)
      exact ⟨fun hrfl => h1.ne hrfl.symm, fun hrfl => h2.ne hrfl.symm⟩
    · rintro ⟨hzu, hzv⟩
      rw [commonNbrs, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro x hx
      rw [hval] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact (hsplit x z).mpr ⟨fun hrfl => hzu hrfl.symm, fun hc => hu hc.1⟩
      · rw [Finset.mem_singleton] at hx'
        subst hx'
        exact (hsplit x z).mpr ⟨fun hrfl => hzv hrfl.symm, fun hc => hv hc.1⟩
  ext z
  rw [hcn z, hval]
  simp

/-- **At the Dross density a complete split graph has a small independent part.** -/
theorem card_le_of_completeSplit_dense {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V}
    (h : IsCompleteSplit G S) (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) :
    10 * S.card ≤ Fintype.card V := by
  rcases Finset.eq_empty_or_nonempty S with rfl | ⟨u, hu⟩
  · simp
  · have hdeg : G.degree u = Fintype.card V - S.card := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_eq_of_completeSplit h hu,
        Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have hmin : G.minDegree ≤ G.degree u := G.minDegree_le_degree u
    have hsle : S.card ≤ Fintype.card V := Finset.card_le_univ S
    omega

/-- **Complete split graphs at the Dross density carry a `2`-spread fractional triangle
decomposition.**  The codegree is not constant here — an edge inside the complete part lies in
`|V| - 2` triangles, an edge meeting `S` in only `|V| - |S| - 1` — so the uniform weighting is not
exact; the two triangle types get the weights `(c-1-|S|)/((c-1)(c-2))` and `1/(c-1)`, where
`c = |V| - |S|`. -/
theorem hasSpreadFracTriangleDecomp_of_completeSplit (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} (hsplit : IsCompleteSplit G S)
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) :
    HasSpreadFracTriangleDecomp G 2 := by
  classical
  by_cases hne : Nonempty V
  swap
  · exact exists_decomp_of_not_nonempty G hne _
  obtain ⟨v₀⟩ := hne
  have hten : 10 ≤ Fintype.card V := ten_le_card_of_dense G hdense v₀
  have hs10 : 10 * S.card ≤ Fintype.card V := card_le_of_completeSplit_dense hsplit hdense
  -- notation
  set n : ℕ := Fintype.card V with hn
  set s : ℕ := S.card with hsdef
  have hsn : 2 * s + 4 ≤ n := by omega
  have hcpos : (0 : ℝ) < (n : ℝ) - (s : ℝ) - 2 := by
    have : ((2 * s + 4 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsn
    push_cast at this
    linarith only [this]
  have hc1 : (0 : ℝ) < (n : ℝ) - (s : ℝ) - 1 := by linarith only [hcpos]
  set b : ℝ := 1 / ((n : ℝ) - (s : ℝ) - 1) with hb
  set a : ℝ := ((n : ℝ) - (s : ℝ) - 1 - (s : ℝ)) /
    (((n : ℝ) - (s : ℝ) - 1) * ((n : ℝ) - (s : ℝ) - 2)) with ha
  have hanum : (0 : ℝ) ≤ (n : ℝ) - (s : ℝ) - 1 - (s : ℝ) := by
    have : ((2 * s + 4 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsn
    push_cast at this
    linarith only [this]
  have hbpos : 0 < b := by rw [hb]; positivity
  have hanonneg : 0 ≤ a := by
    rw [ha]
    apply div_nonneg hanum
    positivity
  -- the weight function
  refine ⟨fun T => if ((triOf G T) ∩ S).Nonempty then b else a, ⟨fun T _ => ?_, fun e => ?_⟩,
    fun T _ => ?_⟩
  · dsimp only
    split <;> [exact le_of_lt hbpos; exact hanonneg]
  · -- the coverage of an edge
    obtain ⟨u, v, huv, hadj, hval⟩ := exists_pair_of_edgeV G e
    have hnot : ¬ (u ∈ S ∧ v ∈ S) := ((hsplit u v).mp hadj).2
    have hsum := sum_trianglesThrough_eq_commonNbrs G e
      (fun t => if (t ∩ S).Nonempty then b else a)
    dsimp only at hsum ⊢
    rw [hsum]
    -- a helper for the case where one endpoint lies in `S`
    have hmixed : ∀ p q : V, p ∈ S → q ∉ S → e.val = ({p, q} : Finset V) →
        ∑ z ∈ commonNbrs G e, (if ((insert z e.val) ∩ S).Nonempty then b else a) = 1 := by
      intro p q hp hq hpq
      have hcneq := commonNbrs_of_completeSplit_mixed hsplit hp hpq
      have hconst : ∀ z ∈ commonNbrs G e,
          (if ((insert z e.val) ∩ S).Nonempty then b else a) = b := by
        intro z _
        rw [if_pos]
        exact ⟨p, Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem (by rw [hpq]; simp), hp⟩⟩
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcneq]
      have hqmem : ({q} : Finset V) ⊆ Finset.univ \ S := by
        intro x hx
        rw [Finset.mem_singleton] at hx
        subst hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hq⟩
      have hcard : ((Finset.univ \ S) \ ({q} : Finset V)).card = n - s - 1 := by
        rw [Finset.card_sdiff_of_subset hqmem,
          Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
          Finset.card_singleton]
      rw [hcard, nsmul_eq_mul, hb]
      have hcast : ((n - s - 1 : ℕ) : ℝ) = (n : ℝ) - (s : ℝ) - 1 := by
        have h2 : (n - s - 1 : ℕ) + (s + 1) = n := by omega
        have h3 := congrArg (fun k : ℕ => (k : ℝ)) h2
        push_cast at h3
        linarith only [h3]
      rw [hcast, mul_one_div, div_self (ne_of_gt hc1)]
    by_cases hu : u ∈ S
    · exact hmixed u v hu (fun hv => hnot ⟨hu, hv⟩) hval
    · by_cases hv : v ∈ S
      · exact hmixed v u hv hu (by rw [hval, Finset.pair_comm])
      · -- both endpoints outside `S`
        have hcneq := commonNbrs_of_completeSplit_pure hsplit hu hv hval
        have hiff : ∀ z : V, ((insert z e.val) ∩ S).Nonempty ↔ z ∈ S := by
          intro z
          constructor
          · rintro ⟨w, hw⟩
            rw [Finset.mem_inter, Finset.mem_insert, hval] at hw
            rcases hw.1 with rfl | hw'
            · exact hw.2
            · rcases Finset.mem_insert.mp hw' with rfl | hw''
              · exact absurd hw.2 hu
              · rw [Finset.mem_singleton] at hw''
                subst hw''
                exact absurd hw.2 hv
          · intro hz
            exact ⟨z, Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, hz⟩⟩
        have hfun : ∀ z ∈ commonNbrs G e,
            (if ((insert z e.val) ∩ S).Nonempty then b else a) = (if z ∈ S then b else a) := by
          intro z _
          by_cases hz : z ∈ S
          · rw [if_pos ((hiff z).mpr hz), if_pos hz]
          · rw [if_neg (fun hc => hz ((hiff z).mp hc)), if_neg hz]
        rw [Finset.sum_congr rfl hfun, hcneq, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
        -- the two counts
        have hSsub : S ⊆ Finset.univ \ e.val := by
          intro x hx
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [hval]
          intro hxe
          rcases Finset.mem_insert.mp hxe with rfl | hxe'
          · exact hu hx
          · rw [Finset.mem_singleton] at hxe'
            subst hxe'
            exact hv hx
        have h1 : ((Finset.univ \ e.val).filter (fun z => z ∈ S)) = S := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
          exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_sdiff.mp (hSsub h)).2, h⟩⟩
        have hevalsub : e.val ⊆ Finset.univ \ S := by
          intro x hx
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [hval] at hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact hu
          · rw [Finset.mem_singleton] at hx'
            subst hx'
            exact hv
        have h2 : ((Finset.univ \ e.val).filter (fun z => ¬ z ∈ S))
            = (Finset.univ \ S) \ e.val := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
          tauto
        have hecard : (e.val).card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp e.property).card_eq
        have hc2 : ((Finset.univ \ S) \ e.val).card = n - s - 2 := by
          rw [Finset.card_sdiff_of_subset hevalsub,
            Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hecard]
        rw [h1, h2, hc2, nsmul_eq_mul, nsmul_eq_mul]
        have hcast2 : ((n - s - 2 : ℕ) : ℝ) = (n : ℝ) - (s : ℝ) - 2 := by
          have h2' : (n - s - 2 : ℕ) + (s + 2) = n := by omega
          have h3 := congrArg (fun k : ℕ => (k : ℝ)) h2'
          push_cast at h3
          linarith only [h3]
        rw [hcast2, hb, ha]
        field_simp
        ring
  · -- the spread bound
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hten
      linarith only [this]
    have hbound_b : b ≤ 2 / (n : ℝ) := by
      rw [hb, div_le_div_iff₀ hc1 hnpos]
      have : ((2 * s + 4 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsn
      push_cast at this
      linarith only [this]
    have hbound_a : a ≤ 2 / (n : ℝ) := by
      have hle : a ≤ 1 / ((n : ℝ) - (s : ℝ) - 2) := by
        rw [ha, div_le_div_iff₀ (by positivity) hcpos]
        nlinarith only [hcpos]
      refine hle.trans ?_
      rw [div_le_div_iff₀ hcpos hnpos]
      have : ((2 * s + 4 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsn
      push_cast at this
      linarith only [this]
    dsimp only
    split <;> [exact hbound_b; exact hbound_a]


/-! ### The codegree is genuinely non-constant -/

/-- **A complete split graph with at least two independent and two complete vertices has
non-constant codegree**: an edge inside the complete part lies in `|V| - 2` triangles, an edge
meeting `S` in only `|V| - |S| - 1`.  So this family is not covered by the codegree-regular case
`Nibble.hasSpreadFracTriangleDecomp_of_codegree_const`. -/
theorem exists_codegree_ne_of_completeSplit (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} (hsplit : IsCompleteSplit G S) (hS : 2 ≤ S.card)
    (hC : 2 ≤ (Finset.univ \ S).card) :
    ∃ e e' : EdgeV G, (commonNbrs G e).card ≠ (commonNbrs G e').card := by
  classical
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ \ S).card)
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have huS : u ∉ S := (Finset.mem_sdiff.mp hu).2
  have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
  have hadj : G.Adj u v := (hsplit u v).mpr ⟨huv, fun hc => huS hc.1⟩
  have hadj' : G.Adj p u := (hsplit p u).mpr ⟨fun hrfl => huS (hrfl ▸ hp), fun hc => huS hc.2⟩
  refine ⟨⟨{u, v}, pair_mem_cliqueFinset_two G hadj⟩,
    ⟨{p, u}, pair_mem_cliqueFinset_two G hadj'⟩, ?_⟩
  have hcard1 : (commonNbrs G ⟨{u, v}, pair_mem_cliqueFinset_two G hadj⟩).card
      = Fintype.card V - 2 := by
    rw [commonNbrs_of_completeSplit_pure hsplit huS hvS rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_insert_of_notMem (by simp [huv]), Finset.card_singleton]
  have husub : ({u} : Finset V) ⊆ Finset.univ \ S := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, huS⟩
  have hcard2 : (commonNbrs G ⟨{p, u}, pair_mem_cliqueFinset_two G hadj'⟩).card
      = Fintype.card V - S.card - 1 := by
    rw [commonNbrs_of_completeSplit_mixed hsplit hp rfl, Finset.card_sdiff_of_subset husub,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Finset.card_singleton]
  have hsle : S.card ≤ Fintype.card V := Finset.card_le_univ S
  have hcs : (Finset.univ \ S).card = Fintype.card V - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  rw [hcard1, hcard2]
  omega

end Nibble
