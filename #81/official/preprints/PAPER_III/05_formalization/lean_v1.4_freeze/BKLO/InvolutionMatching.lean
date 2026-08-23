/-
# From a fixed-point-free involution to a matching (Dirac → the star bricks)

BKLO Lemma 10.3 (for `r = 2`) chooses, at each apex `x`, a **perfect matching** of the neighbourhood
`N_H(x, V)`.  Dirac's theorem — our `BKLO.perfectMatchingDirac_holds` — produces such a matching as a
partner **involution** `f` (each vertex paired with a unique neighbour, `f (f a) = a`, `f a ≠ a`), as
consumed e.g. in `BKLO/ClassPairing.lean`.

This file converts that involution into the `Finset (Finset V)` matching vocabulary of
`BKLO/StarMatchingTriangles.lean`: the orbit family `{a, f a}` for `a ∈ S` is a matching
(`BKLO.IsMatchingAvoiding`) of `S`, avoiding any vertex outside `S`.  It is the bridge that lets the
greedy loop of Lemma 10.3 feed Dirac's output straight into `BKLO.starTriangles`.

Everything here is `sorry`-free.
-/
import BKLO.StarMatchingTriangles

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- The matching induced by a partner function `f` on `S`: the orbit `{a, f a}` for each `a ∈ S`. -/
def involutionMatching (S : Finset V) (f : V → V) : Finset (Finset V) :=
  S.image (fun a => {a, f a})

/-- **A fixed-point-free involution on `S` gives a matching of `S`, avoiding any `x ∉ S`.** -/
theorem isMatchingAvoiding_involutionMatching {S : Finset V} {f : V → V} {x : V}
    (hmap : ∀ a ∈ S, f a ∈ S) (hinv : ∀ a ∈ S, f (f a) = a) (hne : ∀ a ∈ S, f a ≠ a)
    (hx : x ∉ S) : IsMatchingAvoiding (involutionMatching S f) x := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- every orbit is a 2-element set
    intro e he
    rw [involutionMatching, Finset.mem_image] at he
    obtain ⟨a, ha, rfl⟩ := he
    rw [Finset.card_pair (hne a ha).symm]
  · -- distinct orbits are disjoint
    intro e he f' hf' hef
    rw [Finset.mem_coe, involutionMatching, Finset.mem_image] at he hf'
    obtain ⟨a, ha, rfl⟩ := he
    obtain ⟨b, hb, rfl⟩ := hf'
    refine Finset.disjoint_left.2 fun c hc hc' => hef ?_
    -- the orbit `{w, f w}` of any `w ∈ {z, f z}` is `{z, f z}` itself
    have key : ∀ z ∈ S, ∀ w, w ∈ ({z, f z} : Finset V) → ({w, f w} : Finset V) = {z, f z} := by
      intro z hz w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · rfl
      · rw [Finset.mem_singleton] at hw
        subst hw
        rw [hinv z hz]; exact Finset.pair_comm _ _
    -- so `{a, f a} = {c, f c} = {b, f b}`
    rw [← key a ha c hc]
    exact key b hb c hc'
  · -- the orbits avoid `x`
    intro e he
    rw [involutionMatching, Finset.mem_image] at he
    obtain ⟨a, ha, rfl⟩ := he
    rw [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨fun h => hx (h ▸ ha), fun h => hx (h ▸ hmap a ha)⟩

end BKLO
