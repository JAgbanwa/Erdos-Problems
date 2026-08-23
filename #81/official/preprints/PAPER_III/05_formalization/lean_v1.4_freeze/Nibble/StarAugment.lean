/-
# Nibble — an improving move always exists at a large uncovered star

The core step: at the Dross density `9|V| ≤ 10 δ(G)`, if the triangle packing `M` leaves a vertex
`v` with an uncovered star of size `d ≥ 4000`, and at most `d / 10⁶` vertices carry an uncovered
star bigger than `d / 64`, then the potential `Nibble.uncoveredPot` can be strictly decreased.

Consequently a potential-minimal packing has *every* uncovered star small — the per-vertex bound
with no `1/10` wall.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.StarCount

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The improving move.**  At the Dross density, a packing whose uncovered star at `v` is large
while few vertices have a comparable uncovered star is not potential-minimal. -/
theorem exists_pot_decrease (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree)
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M) (v : V)
    (hbig : 4000 ≤ unDeg G M v)
    (hZ : 1000000 * (Zexp G M (unDeg G M v)).card ≤ unDeg G M v) :
    ∃ M' : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M' ∧
      uncoveredPot G M' < uncoveredPot G M := by
  classical
  set n := Fintype.card V with hn
  set d := unDeg G M v with hd
  set Z := Zexp G M d with hZdef
  set B := Bad G M d with hBdef
  have hdn : d ≤ n := unDeg_le_card G M v
  have hn0 : 0 < n := by omega
  have hBcard : B.card ≤ 600 * Z.card := card_Bad_le G hM d hn0
  set A := unNbr G M v with hAdef
  have hAcard : A.card = d := card_unNbr G M v
  have hAsub : A ⊆ G.neighborFinset v := by
    intro a ha
    obtain ⟨hadj, -⟩ := (mem_unNbr G).mp ha
    exact SimpleGraph.mem_neighborFinset G v a |>.mpr hadj
  set W : Finset V := G.neighborFinset v \ A with hWdef
  set Agood : Finset V := A \ (Z ∪ B) with hAgooddef
  -- `Agood` is almost all of `A`
  have hAgoodcard : d ≤ Agood.card + 601 * Z.card := by
    have hsub : A ⊆ Agood ∪ (Z ∪ B) := by
      intro a ha
      by_cases hzb : a ∈ Z ∪ B
      · exact Finset.mem_union_right _ hzb
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha, hzb⟩)
    have h1 : A.card ≤ Agood.card + (Z ∪ B).card :=
      le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have h2 : (Z ∪ B).card ≤ Z.card + B.card := Finset.card_union_le _ _
    omega
  have hZsmall : 1000000 * Z.card ≤ d := hZ
  have hAgood2 : 2 ≤ Agood.card := by omega
  -- basic facts about the uncovered star
  have hAmem : ∀ a ∈ A, ∃ h : G.Adj v a, UncE G M (edgeE G h) := by
    intro a ha
    exact (mem_unNbr G).mp ha
  have hAgoodA : Agood ⊆ A := Finset.sdiff_subset
  have hcheapAgood : ∀ a ∈ Agood, 64 * unDeg G M a ≤ d := by
    intro a ha
    rw [hAgooddef, Finset.mem_sdiff] at ha
    exact cheap_of_notMem_Zexp G (fun hz => ha.2 (Finset.mem_union_left _ hz))
  have hBadAgood : ∀ a ∈ Agood, a ∉ Bad G M d := by
    intro a ha hbad
    rw [hAgooddef, Finset.mem_sdiff] at ha
    exact ha.2 (Finset.mem_union_right _ hbad)
  by_cases hcase : ∃ a₀ ∈ Agood, ∃ a₁ ∈ Agood, a₁ ∈ goodNbr G M d v a₀
  · -- **the short move**
    obtain ⟨a₀, ha₀, a₁, ha₁, hmem⟩ := hcase
    have hadj : G.Adj a₀ a₁ := adj_of_mem_goodNbr G hmem
    have hgood : GoodEdgeAt G M d (edgeE G hadj) := good_of_mem_goodNbr G hmem hadj
    obtain ⟨hva₀, hu0⟩ := hAmem a₀ (hAgoodA ha₀)
    obtain ⟨hva₁, hu1⟩ := hAmem a₁ (hAgoodA ha₁)
    exact exchange_short G hM hva₀ hva₁ hadj hu0 hu1 hgood (hcheapAgood a₀ ha₀)
      (hcheapAgood a₁ ha₁) hbig
  · -- **the long move**
    push_neg at hcase
    -- the partner of a matched star neighbour
    haveI : Nonempty V := ⟨v⟩
    have hpartner : ∀ u ∈ W, ∃ w : V, w ∈ W ∧ w ≠ u ∧ ∃ (hvu : G.Adj v u) (huw : G.Adj u w)
        (hvw : G.Adj v w), triE G hvu huw hvw ∈ M := by
      intro u hu
      rw [hWdef, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hu
      obtain ⟨hvu, hnA⟩ := hu
      have hcov : ¬ UncE G M (edgeE G hvu) := fun h => hnA ((mem_unNbr G).mpr ⟨hvu, h⟩)
      simp only [UncE, not_forall, not_not] at hcov
      obtain ⟨T, hT, hmem⟩ := hcov
      obtain ⟨w, huw, hvw, hwv, hwu, hTeq⟩ := exists_third_vertex G hvu (hM.subset hT) hmem
      refine ⟨w, ?_, hwu, hvu, huw, hvw, hTeq ▸ hT⟩
      rw [hWdef, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
      refine ⟨hvw, fun hwA => ?_⟩
      obtain ⟨hvw', hunc⟩ := (mem_unNbr G).mp hwA
      have hmem' : edgeE G hvw ∈ T := by rw [hTeq, mem_triE]; exact Or.inr (Or.inr rfl)
      exact hunc T hT hmem'
    choose! prt hprtW hprtne hprt using hpartner
    have hWv : ∀ u ∈ W, G.Adj v u := by
      intro u hu
      rw [hWdef, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hu
      exact hu.1
    have hprtinj : ∀ u ∈ W, ∀ u' ∈ W, prt u = prt u' → u = u' := by
      intro u hu u' hu' heq
      obtain ⟨hvu, huw, hvw, hT⟩ := hprt u hu
      obtain ⟨hvu', hu'w', hvw', hT'⟩ := hprt u' hu'
      have hE : edgeE G hvw = edgeE G hvw' := by
        apply Subtype.ext
        show ({v, prt u} : Finset V) = {v, prt u'}
        rw [heq]
      have hmem : edgeE G hvw ∈ triE G hvu huw hvw := by
        rw [mem_triE]; exact Or.inr (Or.inr rfl)
      have hmem' : edgeE G hvw' ∈ triE G hvu' hu'w' hvw' := by
        rw [mem_triE]; exact Or.inr (Or.inr rfl)
      have hTT : triE G hvu huw hvw = triE G hvu' hu'w' hvw' :=
        eq_of_mem_of_mem G hM hT hT' hmem (hE ▸ hmem')
      have hvumem : edgeE G hvu ∈ triE G hvu' hu'w' hvw' := by
        rw [← hTT, mem_triE]; exact Or.inl rfl
      rw [mem_triE] at hvumem
      have hvne : ∀ t ∈ W, v ≠ t := fun t ht => (hWv t ht).ne
      rcases hvumem with h | h | h
      · have hpair := (edgeE_eq_iff G hvu hvu').mp h
        have hmemu : u ∈ ({v, u'} : Finset V) := by rw [← hpair]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmemu
        rcases hmemu with rfl | rfl
        · exact absurd rfl hvu.ne'
        · rfl
      · have hpair := (edgeE_eq_iff G hvu hu'w').mp h
        have hmemv : v ∈ ({u', prt u'} : Finset V) := by rw [← hpair]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmemv
        rcases hmemv with h1 | h1
        · exact absurd h1 (hvne u' hu')
        · exact absurd h1 (hvne (prt u') (hprtW u' hu'))
      · have hpair := (edgeE_eq_iff G hvu hvw').mp h
        have hmemu : u ∈ ({v, prt u'} : Finset V) := by rw [← hpair]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmemu
        rcases hmemu with h1 | h1
        · exact absurd h1 hvu.ne'
        · exact absurd (heq.trans h1.symm) (hprtne u hu)
    -- pick two uncovered star neighbours
    obtain ⟨a₀, ha₀, a₁, ha₁, ha₀a₁⟩ := Finset.one_lt_card.mp (by omega : 1 < Agood.card)
    set U₀ : Finset V := goodNbr G M d v a₀ with hU₀
    set U₁ : Finset V := goodNbr G M d v a₁ with hU₁
    have hU₀card : 790 * n ≤ 1000 * U₀.card :=
      card_goodNbr_ge G hdense M d v a₀ (hBadAgood a₀ ha₀)
    have hU₁card : 790 * n ≤ 1000 * U₁.card :=
      card_goodNbr_ge G hdense M d v a₁ (hBadAgood a₁ ha₁)
    -- `U₀` avoids the good part of the uncovered star, hence lands in the matched part
    have hU₀W : U₀.card ≤ (U₀ ∩ W).card + 601 * Z.card := by
      have hsub : U₀ ⊆ (U₀ ∩ W) ∪ (Z ∪ B) := by
        intro w hw
        by_cases hwW : w ∈ W
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hw, hwW⟩)
        · -- `w` is a neighbour of `v` not in `W`, hence in `A`
          have hwv : w ∈ G.neighborFinset v := goodNbr_subset G M d v a₀ hw
          have hwA : w ∈ A := by
            by_contra hc
            exact hwW (Finset.mem_sdiff.mpr ⟨hwv, hc⟩)
          have hwnot : w ∉ Agood := fun hg => hcase a₀ ha₀ w hg hw
          rw [hAgooddef, Finset.mem_sdiff] at hwnot
          push_neg at hwnot
          exact Finset.mem_union_right _ (hwnot hwA)
      have h1 : U₀.card ≤ (U₀ ∩ W).card + (Z ∪ B).card :=
        le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
      have h2 : (Z ∪ B).card ≤ Z.card + B.card := Finset.card_union_le _ _
      omega
    -- discard the few vertices whose partner is expensive
    set X : Finset V := (U₀ ∩ W).filter (fun w => w ∉ Z ∧ prt w ∉ Z) with hXdef
    have hXcard : (U₀ ∩ W).card ≤ X.card + 2 * Z.card := by
      set Y' : Finset V := (U₀ ∩ W).filter (fun w => ¬ (w ∉ Z ∧ prt w ∉ Z)) with hY'
      have hsplit : X.card + Y'.card = (U₀ ∩ W).card := by
        rw [hXdef, hY']
        exact Finset.card_filter_add_card_filter_not _
      have hY'card : Y'.card ≤ 2 * Z.card := by
        have hsub : Y' ⊆ Z ∪ ((U₀ ∩ W).filter (fun w => prt w ∈ Z)) := by
          intro w hw
          rw [hY', Finset.mem_filter] at hw
          push_neg at hw
          by_cases hwZ : w ∈ Z
          · exact Finset.mem_union_left _ hwZ
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw.1, hw.2 hwZ⟩)
        have hinj : ((U₀ ∩ W).filter (fun w => prt w ∈ Z)).card ≤ Z.card := by
          refine Finset.card_le_card_of_injOn prt ?_ ?_
          · intro w hw
            exact (Finset.mem_filter.mp hw).2
          · intro w hw w' hw' heq
            have hwW : w ∈ W := (Finset.mem_inter.mp (Finset.mem_filter.mp hw).1).2
            have hw'W : w' ∈ W := (Finset.mem_inter.mp (Finset.mem_filter.mp hw').1).2
            exact hprtinj w hwW w' hw'W heq
        have := Finset.card_le_card hsub
        have h2 := Finset.card_union_le Z ((U₀ ∩ W).filter (fun w => prt w ∈ Z))
        omega
      omega
    -- the partners of `X`
    set Y : Finset V := X.image prt with hYdef
    have hXW : X ⊆ W := by
      intro w hw
      exact (Finset.mem_inter.mp (Finset.mem_filter.mp hw).1).2
    have hYcard : Y.card = X.card := by
      rw [hYdef]
      refine Finset.card_image_of_injOn ?_
      intro w hw w' hw' heq
      exact hprtinj w (hXW hw) w' (hXW hw') heq
    have hYsub : Y ⊆ G.neighborFinset v := by
      intro w hw
      rw [hYdef, Finset.mem_image] at hw
      obtain ⟨u, hu, rfl⟩ := hw
      have := hprtW u (hXW hu)
      rw [hWdef, Finset.mem_sdiff] at this
      exact this.1
    have hU₁sub : U₁ ⊆ G.neighborFinset v := goodNbr_subset G M d v a₁
    have hNv : (G.neighborFinset v).card ≤ n := by
      rw [hn, ← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    -- the two large sets in the neighbourhood of `v` must meet
    have hmeet : (Y ∩ U₁).Nonempty := by
      rw [← Finset.card_pos]
      have hun : (Y ∪ U₁).card ≤ n := le_trans (Finset.card_le_card
        (Finset.union_subset hYsub hU₁sub)) hNv
      have hIE : (Y ∩ U₁).card + (Y ∪ U₁).card = Y.card + U₁.card :=
        Finset.card_inter_add_card_union _ _
      omega
    obtain ⟨y₁, hy₁⟩ := hmeet
    rw [Finset.mem_inter] at hy₁
    obtain ⟨hy₁Y, hy₁U₁⟩ := hy₁
    rw [hYdef, Finset.mem_image] at hy₁Y
    obtain ⟨x₁, hx₁X, rfl⟩ := hy₁Y
    have hx₁W : x₁ ∈ W := hXW hx₁X
    -- assemble the data of the long move
    obtain ⟨hva₀, hu0⟩ := hAmem a₀ (hAgoodA ha₀)
    obtain ⟨hva₁, hu1⟩ := hAmem a₁ (hAgoodA ha₁)
    obtain ⟨hvx, hxy', hvy', hT0'⟩ := hprt x₁ hx₁W
    have hax : G.Adj a₀ x₁ := adj_of_mem_goodNbr G (Finset.mem_of_mem_inter_left
      (Finset.mem_filter.mp hx₁X).1)
    have ha₁y₁ : G.Adj a₁ (prt x₁) := adj_of_mem_goodNbr G hy₁U₁
    have hya : G.Adj (prt x₁) a₁ := ha₁y₁.symm
    have hg1 : GoodEdgeAt G M d (edgeE G hax) :=
      good_of_mem_goodNbr G (Finset.mem_of_mem_inter_left (Finset.mem_filter.mp hx₁X).1) hax
    have hg2 : GoodEdgeAt G M d (edgeE G hya) := by
      have h := good_of_mem_goodNbr G hy₁U₁ ha₁y₁
      rwa [← edgeE_comm G ha₁y₁] at h
    -- distinctness
    have hAW : ∀ a ∈ A, ∀ w ∈ W, a ≠ w := by
      intro a ha w hw
      rintro rfl
      rw [hWdef, Finset.mem_sdiff] at hw
      exact hw.2 ha
    have hy₁W : prt x₁ ∈ W := hprtW x₁ hx₁W
    have ha₀y : a₀ ≠ prt x₁ := hAW a₀ (hAgoodA ha₀) (prt x₁) hy₁W
    have ha₁x : a₁ ≠ x₁ := hAW a₁ (hAgoodA ha₁) x₁ hx₁W
    -- cheapness of the four vertices
    have hcx : 64 * unDeg G M x₁ ≤ d := by
      refine cheap_of_notMem_Zexp G ?_
      have := (Finset.mem_filter.mp hx₁X).2
      exact this.1
    have hcy : 64 * unDeg G M (prt x₁) ≤ d := by
      refine cheap_of_notMem_Zexp G ?_
      exact (Finset.mem_filter.mp hx₁X).2.2
    exact exchange_long G hM hva₀ hva₁ hvx hvy' hax hya hxy' ha₀a₁ ha₀y ha₁x hu0 hu1 hT0' hg1 hg2
      (hcheapAgood a₀ ha₀) (hcheapAgood a₁ ha₁) hcx hcy hbig

end Nibble
