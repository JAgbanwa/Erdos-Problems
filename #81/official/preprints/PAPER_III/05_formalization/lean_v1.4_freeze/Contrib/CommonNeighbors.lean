/-
# A2 — Common-neighbourhood lower bound from minimum degree (SimpleGraph, idiomatic)

Re-statement, in Mathlib's `SimpleGraph` API, of the common-neighbourhood bound used in the dense
regime (originally `BKLO.HostGraph.card_commonNbrs_host`, entangled with the bespoke
`Finset (Sym2 V)` representation).  Here it is stated and proved purely over `SimpleGraph`:

> if every vertex of a set `W` has degree at least `d`, then the set of common neighbours of `W`
> has at least `n − |W|·(n − d)` elements.

The proof is a union bound: the complement of the common neighbourhood is covered by the
non-neighbourhoods of the members of `W`, each of size `n − deg w ≤ n − d`.
-/
import Mathlib

open Finset

namespace Contrib

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The common neighbours of a finite set `W`: vertices adjacent to every member of `W`. -/
def commonNbrs (W : Finset V) : Finset V :=
  Finset.univ.filter (fun v => ∀ w ∈ W, G.Adj w v)

/-- The number of non-neighbours of a vertex `w` is `n − deg w`. -/
theorem card_nonNeighbors (w : V) :
    (Finset.univ.filter (fun v => ¬ G.Adj w v)).card = Fintype.card V - G.degree w := by
  classical
  have hpair := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset V)) (p := fun v => G.Adj w v)
  have hAdj : (Finset.univ.filter (fun v => G.Adj w v)) = G.neighborFinset w := by
    ext v; simp [SimpleGraph.mem_neighborFinset]
  have hdeg : (Finset.univ.filter (fun v => G.Adj w v)).card = G.degree w := by
    rw [hAdj]; rfl
  rw [Finset.card_univ] at hpair
  omega

/-- **Common-neighbourhood lower bound from minimum degree.**  If every vertex of `W` has degree at
least `d`, the common neighbourhood of `W` has at least `n − |W|·(n − d)` vertices. -/
theorem card_commonNbrs_ge (W : Finset V) (d : ℕ)
    (hd : ∀ w ∈ W, d ≤ G.degree w) :
    Fintype.card V - W.card * (Fintype.card V - d) ≤ (commonNbrs G W).card := by
  classical
  set n := Fintype.card V with hn
  -- the complement of the common neighbourhood is covered by the non-neighbourhoods of `w ∈ W`
  have hbad : (Finset.univ \ commonNbrs G W)
      ⊆ W.biUnion (fun w => Finset.univ.filter (fun v => ¬ G.Adj w v)) := by
    intro v hv
    rw [Finset.mem_sdiff, commonNbrs, Finset.mem_filter] at hv
    push_neg at hv
    obtain ⟨w, hw, hadj⟩ := hv.2 (Finset.mem_univ v)
    exact Finset.mem_biUnion.2 ⟨w, hw, Finset.mem_filter.2 ⟨Finset.mem_univ v, hadj⟩⟩
  -- each non-neighbourhood has size `n − deg w ≤ n − d`
  have hcardw : ∀ w ∈ W, (Finset.univ.filter (fun v => ¬ G.Adj w v)).card ≤ n - d := by
    intro w hw
    rw [card_nonNeighbors]
    exact Nat.sub_le_sub_left (hd w hw) n
  -- union bound on the complement
  have hbadcard : (Finset.univ \ commonNbrs G W).card ≤ W.card * (n - d) := by
    calc (Finset.univ \ commonNbrs G W).card
        ≤ (W.biUnion (fun w => Finset.univ.filter (fun v => ¬ G.Adj w v))).card :=
          Finset.card_le_card hbad
      _ ≤ ∑ w ∈ W, (Finset.univ.filter (fun v => ¬ G.Adj w v)).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ W, (n - d) := Finset.sum_le_sum hcardw
      _ = W.card * (n - d) := by rw [Finset.sum_const, smul_eq_mul]
  -- convert complement bound to a lower bound on the common neighbourhood
  have hc : (Finset.univ \ commonNbrs G W).card = n - (commonNbrs G W).card := by
    rw [Finset.card_univ_diff]
  have hle : (commonNbrs G W).card ≤ n := by
    rw [hn]; exact Finset.card_le_univ _
  omega

/-- **Dense specialisation.**  If `|W| ≤ k` and every vertex of `W` has degree at least `n − c`,
then `W` has at least `n − k·c` common neighbours. -/
theorem card_commonNbrs_ge_dense (W : Finset V) (k c : ℕ)
    (hk : W.card ≤ k) (hd : ∀ w ∈ W, Fintype.card V - c ≤ G.degree w) :
    Fintype.card V - k * c ≤ (commonNbrs G W).card := by
  have hmain := card_commonNbrs_ge G W (Fintype.card V - c) hd
  have hcc : Fintype.card V - (Fintype.card V - c) ≤ c := by omega
  calc Fintype.card V - k * c
      ≤ Fintype.card V - W.card * (Fintype.card V - (Fintype.card V - c)) := by
        apply Nat.sub_le_sub_left
        calc W.card * (Fintype.card V - (Fintype.card V - c))
            ≤ W.card * c := Nat.mul_le_mul_left _ hcc
          _ ≤ k * c := Nat.mul_le_mul_right _ hk
    _ ≤ (commonNbrs G W).card := hmain

end Contrib
