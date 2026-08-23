/-
# Yuster Y1c-ii — counting the capturing vertices (Szemerédi + averaging reconstruction)

Standalone, Mathlib-only. The counting half of Y1c, reconstructed from a double-counting identity plus
an averaging (Markov-type) bound — no external paper needed. A vertex `v` *captures* a part `s` if its
neighbourhood contains an `ε`-fraction of `s` (`ε|s| ≤ |s ∩ N(v)|`). The identity
`∑_v |s ∩ N(v)| = ∑_{u∈s} deg(u)` (each pair `(v,u)` with `u ∈ s ∩ N(v)` corresponds to `v ∈ N(u)` by
symmetry) drives an averaging bound on how many vertices capture `s`.

Combined with `triangleHypergraph_degree_lower_of_capture` (Y1c-i), this lower-bounds the triangle
degree of most vertices. (The residual — handling the small non-capturing exceptional set to reach
`NearlyRegular` for ALL vertices — is the Haxell–Rödl design choice this reconstruction leaves open.)

* `sum_card_inter_neighbor` — the double-counting identity.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Bound

open Finset SimpleGraph

namespace Nibble.Yuster

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Double-counting identity.** Summing over all vertices the number of neighbours in `s` counts,
for each `u ∈ s`, its degree: `∑_v |s ∩ N(v)| = ∑_{u∈s} deg(u)`. Each incidence `(v, u)` with
`u ∈ s ∩ N(v)` corresponds by symmetry to `v ∈ N(u)`. -/
theorem sum_card_inter_neighbor (s : Finset V) :
    ∑ v : V, (s ∩ G.neighborFinset v).card = ∑ u ∈ s, G.degree u := by
  have key : ∀ v : V, (s ∩ G.neighborFinset v).card
      = ∑ u ∈ s, (if v ∈ G.neighborFinset u then 1 else 0) := by
    intro v
    rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    refine if_congr ?_ rfl rfl
    simp only [SimpleGraph.mem_neighborFinset]
    exact G.adj_comm v u
  simp_rw [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one,
    G.card_neighborFinset_eq_degree]

/-- **Averaging lower bound on the capturing set.** Let `Cap` be the set of `s`-capturing vertices
(`ε|s| ≤ |s ∩ N(v)|`). Since each vertex contributes `≤ |s|` to `∑_v |s ∩ N(v)|` if capturing and
`< ε|s|` otherwise, the identity `∑_v |s ∩ N(v)| = ∑_{u∈s} deg(u)` forces
`∑_{u∈s} deg(u) − ε|s|·|V| ≤ (1-ε)·|s|·|Cap|` — a positive lower bound on `|Cap|` when `s` is
well-connected. -/
theorem card_capturing_lower {ε : ℝ} (s : Finset V) :
    (∑ u ∈ s, (G.degree u : ℝ)) - ε * (s.card : ℝ) * (Fintype.card V : ℝ)
      ≤ (1 - ε) * (s.card : ℝ) *
          ((Finset.univ.filter
            (fun v => ε * (s.card : ℝ) ≤ ((s ∩ G.neighborFinset v).card : ℝ))).card : ℝ) := by
  classical
  set p : V → Prop := fun v => ε * (s.card : ℝ) ≤ ((s ∩ G.neighborFinset v).card : ℝ) with hp
  set Cap := Finset.univ.filter p with hCap
  have hid : (∑ v : V, ((s ∩ G.neighborFinset v).card : ℝ)) = ∑ u ∈ s, (G.degree u : ℝ) := by
    exact_mod_cast sum_card_inter_neighbor G s
  have hsplit : (∑ v : V, ((s ∩ G.neighborFinset v).card : ℝ))
      = (∑ v ∈ Cap, ((s ∩ G.neighborFinset v).card : ℝ))
        + (∑ v ∈ Finset.univ.filter (fun v => ¬ p v), ((s ∩ G.neighborFinset v).card : ℝ)) := by
    rw [hCap]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ p
      (fun v => ((s ∩ G.neighborFinset v).card : ℝ))).symm
  have hCapub : (∑ v ∈ Cap, ((s ∩ G.neighborFinset v).card : ℝ)) ≤ (s.card : ℝ) * (Cap.card : ℝ) := by
    calc (∑ v ∈ Cap, ((s ∩ G.neighborFinset v).card : ℝ))
        ≤ ∑ _v ∈ Cap, (s.card : ℝ) :=
          Finset.sum_le_sum (fun v _ => by exact_mod_cast Finset.card_le_card Finset.inter_subset_left)
      _ = (s.card : ℝ) * (Cap.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hNotub : (∑ v ∈ Finset.univ.filter (fun v => ¬ p v), ((s ∩ G.neighborFinset v).card : ℝ))
      ≤ ε * (s.card : ℝ) * ((Finset.univ.filter (fun v => ¬ p v)).card : ℝ) := by
    calc (∑ v ∈ Finset.univ.filter (fun v => ¬ p v), ((s ∩ G.neighborFinset v).card : ℝ))
        ≤ ∑ _v ∈ Finset.univ.filter (fun v => ¬ p v), (ε * (s.card : ℝ)) :=
          Finset.sum_le_sum (fun v hv => by
            rw [Finset.mem_filter] at hv
            simp only [hp, not_le] at hv
            exact hv.2.le)
      _ = ε * (s.card : ℝ) * ((Finset.univ.filter (fun v => ¬ p v)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hnotcard : ((Finset.univ.filter (fun v => ¬ p v)).card : ℝ)
      = (Fintype.card V : ℝ) - (Cap.card : ℝ) := by
    have hset : Finset.univ.filter (fun v => ¬ p v) = Finset.univ \ Cap := by
      rw [Finset.filter_not, hCap]
    rw [hset, Finset.card_sdiff, Finset.inter_univ,
      Nat.cast_sub (Finset.card_le_card (Finset.subset_univ _)), Finset.card_univ]
  rw [hid] at hsplit
  rw [hnotcard] at hNotub
  have hAB : (∑ u ∈ s, (G.degree u : ℝ))
      ≤ (s.card : ℝ) * (Cap.card : ℝ)
        + ε * (s.card : ℝ) * ((Fintype.card V : ℝ) - (Cap.card : ℝ)) := by
    rw [hsplit]; linarith only [hCapub, hNotub]
  have he1 : ε * (s.card : ℝ) * ((Fintype.card V : ℝ) - (Cap.card : ℝ))
      = ε * (s.card : ℝ) * (Fintype.card V : ℝ) - ε * (s.card : ℝ) * (Cap.card : ℝ) := by ring
  have he2 : (1 - ε) * (s.card : ℝ) * (Cap.card : ℝ)
      = (s.card : ℝ) * (Cap.card : ℝ) - ε * (s.card : ℝ) * (Cap.card : ℝ) := by ring
  rw [he1] at hAB
  rw [he2]
  linarith only [hAB]

end Nibble.Yuster
