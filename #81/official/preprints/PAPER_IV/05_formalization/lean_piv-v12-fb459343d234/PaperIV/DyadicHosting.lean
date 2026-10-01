import PaperIV.GalvinRectangle
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Sym.Sym2

/-!
# E4, part B — covering all core pairs with bipartite Galvin layers

**Theorem (`dyadic_list_colouring`).**  Let `S` be a set of `a` vertices and let every
pair `uv ⊆ S` carry a list `L(uv)` with `|L(uv)| ≥ 3⌈a/2⌉ − 2`.  Then the complete graph on
`S` has a proper list edge colouring from `L`.

Only Galvin's theorem for complete bipartite graphs is used (`GalvinRect.galvin_grid`,
proved from scratch in this project).  Häggkvist–Janssen is **not** used.

## The layer scheme: finest layer first

Split `S = S₁ ⊔ S₂` with `|S₁| = ⌈a/2⌉`, `|S₂| = ⌊a/2⌋`, and recurse.  Unfolding the
recursion gives `⌈log₂ a⌉` bipartite layers; the layer joining the two halves of a block
of size `s` is a disjoint union of complete bipartite graphs `K_{⌈s/2⌉,⌊s/2⌋}` and is
coloured **after** both halves.  At that moment each endpoint has used at most
`⌈s/2⌉ − 1` colours, so the reduced list of a cross pair has at least
`|L| − 2(⌈s/2⌉ − 1)` colours, and Galvin needs `⌈s/2⌉`.  Hence the list condition of the
layer at block size `s` is `|L| ≥ 3⌈s/2⌉ − 2`, and the binding layer is the last one
(`s = a`): `|L| ≥ 3⌈a/2⌉ − 2`.

The naive scheme of the task statement orders the layers the other way (coarsest first);
then the finest layers are coloured last, when almost `a` colours are spent at each
endpoint, and the requirement degenerates to `≈ 2a`.  Reversing the order costs nothing and
brings it down to `≈ 3a/2`.
-/

namespace PaperIV.DyadicHosting

open Finset PaperIV.GalvinRect

variable {V : Type*} [DecidableEq V] {Col : Type*} [DecidableEq Col] [Nonempty Col]

/-- A proper list edge colouring of the complete graph on `S`, written as a symmetric
function of the two endpoints. -/
def IsProperListColouring (S : Finset V) (L : Sym2 V → Finset Col) (c : V → V → Col) :
    Prop :=
  (∀ u ∈ S, ∀ v ∈ S, u ≠ v → c u v = c v u ∧ c u v ∈ L s(u, v)) ∧
    (∀ u ∈ S, ∀ v ∈ S, ∀ w ∈ S, u ≠ v → u ≠ w → v ≠ w → c u v ≠ c u w)

/-- **One Galvin layer**: `K_{S₁,S₂}` with lists of size at least `max(|S₁|,|S₂|)`. -/
theorem bipartite_layer (S1 S2 : Finset V) (L : V → V → Finset Col)
    (hL : ∀ u ∈ S1, ∀ v ∈ S2, max S1.card S2.card ≤ (L u v).card) :
    ∃ g : V → V → Col, (∀ u ∈ S1, ∀ v ∈ S2, g u v ∈ L u v) ∧
      (∀ u ∈ S1, ∀ v ∈ S2, ∀ v' ∈ S2, v ≠ v' → g u v ≠ g u v') ∧
      (∀ u ∈ S1, ∀ u' ∈ S1, ∀ v ∈ S2, u ≠ u' → g u v ≠ g u' v) := by
  classical
  obtain ⟨f, hfL, hrow, hcol⟩ := galvin_grid (R := S1) (C := S2) (max S1.card S2.card)
    (by simp) (by simp) (fun s => L s.1 s.2) (fun s => hL s.1 s.1.2 s.2 s.2.2)
  refine ⟨fun u v => if h : u ∈ S1 ∧ v ∈ S2 then f (⟨u, h.1⟩, ⟨v, h.2⟩)
    else Classical.arbitrary Col, ?_, ?_, ?_⟩
  · intro u hu v hv
    simp only [hu, hv, and_self, dite_true]
    exact hfL _
  · intro u hu v hv v' hv' hvv'
    simp only [hu, hv, hv', and_self, dite_true]
    exact hrow _ _ (fun h => hvv' (congrArg (fun p => (p.2 : V)) h)) rfl
  · intro u hu u' hu' v hv huu'
    simp only [hu, hu', hv, and_self, dite_true]
    exact hcol _ _ (fun h => huu' (congrArg (fun p => (p.1 : V)) h)) rfl

/-- **Part B: the dyadic layer scheme.**  Lists of size `3⌈a/2⌉ − 2` suffice to colour
every pair of an `a`-set, using only Galvin's theorem on complete bipartite layers. -/
theorem dyadic_list_colouring :
    ∀ (S : Finset V) (L : Sym2 V → Finset Col),
      (∀ u ∈ S, ∀ v ∈ S, u ≠ v → 3 * ((S.card + 1) / 2) ≤ (L s(u, v)).card + 2) →
        ∃ c : V → V → Col, IsProperListColouring S L c := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  intro L hL
  rcases Nat.lt_or_ge S.card 2 with hsmall | hbig
  · refine ⟨fun _ _ => Classical.arbitrary Col, ?_, ?_⟩
    · intro u hu v hv huv
      exact absurd (Finset.card_le_one.1 (by omega) u hu v hv) huv
    · intro u hu v hv w hw huv
      exact absurd (Finset.card_le_one.1 (by omega) u hu v hv) huv
  obtain ⟨S1, hS1S, hS1c⟩ := Finset.exists_subset_card_eq (s := S) (n := (S.card + 1) / 2)
    (by omega)
  set S2 := S \ S1 with hS2
  have hS2c : S2.card = S.card - (S.card + 1) / 2 := by
    rw [hS2, card_sdiff_of_subset hS1S, hS1c]
  have hS1lt : S1 ⊂ S := by
    refine ⟨hS1S, fun h => ?_⟩
    have := card_le_card h
    omega
  have hS2lt : S2 ⊂ S := by
    refine ⟨sdiff_subset, fun h => ?_⟩
    have := card_le_card h
    omega
  have hdisj : ∀ x, x ∈ S1 → x ∉ S2 := fun x hx h => (mem_sdiff.1 h).2 hx
  have hcover : ∀ x ∈ S, x ∈ S1 ∨ x ∈ S2 := fun x hx => by
    by_cases h : x ∈ S1
    · exact Or.inl h
    · exact Or.inr (mem_sdiff.2 ⟨hx, h⟩)
  obtain ⟨c1, hc1s, hc1p⟩ := ih S1 hS1lt L (fun u hu v hv huv => by
    have := hL u (hS1S hu) v (hS1S hv) huv
    have : (S1.card + 1) / 2 ≤ (S.card + 1) / 2 := by omega
    omega)
  obtain ⟨c2, hc2s, hc2p⟩ := ih S2 hS2lt L (fun u hu v hv huv => by
    have := hL u (hS2lt.1 hu) v (hS2lt.1 hv) huv
    have : (S2.card + 1) / 2 ≤ (S.card + 1) / 2 := by omega
    omega)
  -- the reduced lists of the last layer
  let L' : V → V → Finset Col := fun u v =>
    (L s(u, v) \ (S1.erase u).image (c1 u)) \ (S2.erase v).image (c2 v)
  have hL' : ∀ u ∈ S1, ∀ v ∈ S2, max S1.card S2.card ≤ (L' u v).card := by
    intro u hu v hv
    have h0 := hL u (hS1S hu) v (hS2lt.1 hv) (fun h => hdisj u hu (h ▸ hv))
    have h1 : ((S1.erase u).image (c1 u)).card ≤ S1.card - 1 := by
      rw [← card_erase_of_mem hu]; exact card_image_le
    have h2 : ((S2.erase v).image (c2 v)).card ≤ S2.card - 1 := by
      rw [← card_erase_of_mem hv]; exact card_image_le
    have h3 := le_card_sdiff ((S1.erase u).image (c1 u)) (L s(u, v))
    have h4 := le_card_sdiff ((S2.erase v).image (c2 v))
      (L s(u, v) \ (S1.erase u).image (c1 u))
    have h5 : 1 ≤ S1.card := by
      exact card_pos.2 ⟨u, hu⟩
    have h6 : 1 ≤ S2.card := card_pos.2 ⟨v, hv⟩
    show max S1.card S2.card ≤ ((L s(u, v) \ (S1.erase u).image (c1 u)) \
      (S2.erase v).image (c2 v)).card
    rw [max_le_iff]
    omega
  obtain ⟨g, hgL, hgrow, hgcol⟩ := bipartite_layer S1 S2 L' hL'
  have hgL1 : ∀ u ∈ S1, ∀ v ∈ S2, g u v ∈ L s(u, v) := fun u hu v hv =>
    (mem_sdiff.1 (mem_sdiff.1 (hgL u hu v hv)).1).1
  have hgA : ∀ u ∈ S1, ∀ v ∈ S2, ∀ w ∈ S1, w ≠ u → g u v ≠ c1 u w := by
    intro u hu v hv w hw hwu h
    have := (mem_sdiff.1 (mem_sdiff.1 (hgL u hu v hv)).1).2
    exact this (mem_image.2 ⟨w, mem_erase.2 ⟨hwu, hw⟩, h.symm⟩)
  have hgB : ∀ u ∈ S1, ∀ v ∈ S2, ∀ w ∈ S2, w ≠ v → g u v ≠ c2 v w := by
    intro u hu v hv w hw hwv h
    have := (mem_sdiff.1 (hgL u hu v hv)).2
    exact this (mem_image.2 ⟨w, mem_erase.2 ⟨hwv, hw⟩, h.symm⟩)
  refine ⟨fun u v => if u ∈ S1 ∧ v ∈ S1 then c1 u v else if u ∈ S2 ∧ v ∈ S2 then c2 u v
    else if u ∈ S1 then g u v else g v u, ?_, ?_⟩
  · intro u hu v hv huv
    rcases hcover u hu with hu1 | hu2 <;> rcases hcover v hv with hv1 | hv2
    · simp only [hu1, hv1, and_self, if_true]
      exact hc1s u hu1 v hv1 huv
    · have hu2 : u ∉ S2 := hdisj u hu1
      have hv1 : v ∉ S1 := fun h => hdisj v h hv2
      simp only [hu1, hv1, hu2, hv2, and_false, false_and, if_false, if_true]
      exact ⟨trivial, hgL1 u hu1 v hv2⟩
    · have hu1 : u ∉ S1 := fun h => hdisj u h hu2
      have hv2 : v ∉ S2 := hdisj v hv1
      simp only [hu1, hv1, hu2, hv2, and_false, false_and, if_false, if_true]
      exact ⟨trivial, Sym2.eq_swap ▸ hgL1 v hv1 u hu2⟩
    · have hu1 : u ∉ S1 := fun h => hdisj u h hu2
      have hv1 : v ∉ S1 := fun h => hdisj v h hv2
      simp only [hu1, hv1, hu2, hv2, and_self, if_false, if_true]
      exact hc2s u hu2 v hv2 huv
  · intro u hu v hv w hw huv huw hvw
    rcases hcover u hu with hu1 | hu2
    · have hu2 : u ∉ S2 := hdisj u hu1
      rcases hcover v hv with hv1 | hv2 <;> rcases hcover w hw with hw1 | hw2
      · simp only [hu1, hv1, hw1, and_self, if_true]
        exact hc1p u hu1 v hv1 w hw1 huv huw hvw
      · have hw1 : w ∉ S1 := fun h => hdisj w h hw2
        simp only [hu1, hv1, hw1, hu2, hw2, and_self, and_false, false_and, if_true, if_false]
        exact fun h => hgA u hu1 w hw2 v hv1 (Ne.symm huv) h.symm
      · have hv1 : v ∉ S1 := fun h => hdisj v h hv2
        simp only [hu1, hv1, hw1, hu2, hv2, and_self, and_false, false_and, if_true, if_false]
        exact hgA u hu1 v hv2 w hw1 (Ne.symm huw)
      · have hv1 : v ∉ S1 := fun h => hdisj v h hv2
        have hw1 : w ∉ S1 := fun h => hdisj w h hw2
        simp only [hu1, hv1, hw1, hu2, and_false, false_and, if_true, if_false]
        exact hgrow u hu1 v hv2 w hw2 hvw
    · have hu1 : u ∉ S1 := fun h => hdisj u h hu2
      rcases hcover v hv with hv1 | hv2 <;> rcases hcover w hw with hw1 | hw2
      · have hv2 : v ∉ S2 := hdisj v hv1
        have hw2 : w ∉ S2 := hdisj w hw1
        simp only [hu1, hv2, hw2, and_false, false_and, if_false]
        exact hgcol v hv1 w hw1 u hu2 hvw
      · have hv2 : v ∉ S2 := hdisj v hv1
        have hw1 : w ∉ S1 := fun h => hdisj w h hw2
        simp only [hu1, hu2, hv2, hw2, hw1, and_self, and_false, false_and, if_true, if_false]
        exact hgB v hv1 u hu2 w hw2 (Ne.symm huw)
      · have hv1 : v ∉ S1 := fun h => hdisj v h hv2
        have hw2 : w ∉ S2 := hdisj w hw1
        simp only [hu1, hu2, hv1, hv2, hw2, and_self, and_false, false_and, if_true, if_false]
        exact fun h => hgB w hw1 u hu2 v hv2 (Ne.symm huv) h.symm
      · have hv1 : v ∉ S1 := fun h => hdisj v h hv2
        have hw1 : w ∉ S1 := fun h => hdisj w h hw2
        simp only [hu1, hu2, hv2, hw2, and_self, false_and, if_true, if_false]
        exact hc2p u hu2 v hv2 w hw2 huv huw hvw

end PaperIV.DyadicHosting
