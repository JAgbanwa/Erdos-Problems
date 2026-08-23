/-
  ROUTE B (local exploration) — general finite max-flow / min-cut, from scratch.

  Mathlib has no MFMC. Here we lay the reusable layer: finite network, flow (skew-symmetric,
  capacity-bounded, conserved at internal nodes), value, cut, cut capacity.

  What is PROVED here (gate-clean): **weak duality** — for ANY flow `f` and ANY s–t cut `S`,
  `value f ≤ capacity S`. This is the easy (and reusable) half of max-flow/min-cut, via the
  cut-flow identity `value f = Σ_{u∈S, v∉S} f u v` (skew symmetry kills the S×S diagonal, and
  internal conservation kills every term but the source).

  The remaining `sorry` (`maxflow_eq_mincut`) is the HARD direction (existence of a flow meeting
  a cut — augmenting paths / integrality), i.e. exactly the infrastructure Route A/C also need.
-/
import Mathlib

namespace Ax2.RouteB

open Finset

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- A finite s–t network: capacities (assumed nonnegative) with distinct source and sink. -/
structure Network (N : Type*) [Fintype N] [DecidableEq N] where
  cap : N → N → ℝ
  capNonneg : ∀ u v, 0 ≤ cap u v
  s : N
  t : N
  st : s ≠ t

/-- A feasible flow on a network. -/
structure Flow (Net : Network N) where
  f : N → N → ℝ
  skew : ∀ u v, f u v = - f v u
  capacitated : ∀ u v, f u v ≤ Net.cap u v
  conserved : ∀ u, u ≠ Net.s → u ≠ Net.t → ∑ v, f u v = 0

/-- The value of a flow: net flow out of the source. -/
def Flow.value {Net : Network N} (F : Flow Net) : ℝ := ∑ v, F.f Net.s v

/-- An s–t cut: a set of nodes containing the source but not the sink. -/
structure Cut (Net : Network N) where
  S : Finset N
  hs : Net.s ∈ S
  ht : Net.t ∉ S

/-- The capacity of a cut: total capacity of edges leaving `S`. -/
def Cut.capacity {Net : Network N} (C : Cut Net) : ℝ :=
  ∑ u ∈ C.S, ∑ v ∈ (Finset.univ \ C.S), Net.cap u v

/-- The flow across a cut equals the value of the flow. -/
lemma Flow.value_eq_flow_across {Net : Network N} (F : Flow Net) (C : Cut Net) :
    F.value = ∑ u ∈ C.S, ∑ v ∈ (Finset.univ \ C.S), F.f u v := by
  -- Σ_{u∈S} Σ_{v∈univ} f u v  =  value (only s contributes; internal nodes conserved, t∉S)
  have hfull : ∑ u ∈ C.S, ∑ v, F.f u v = F.value := by
    rw [Finset.sum_eq_single Net.s]
    · rfl
    · intro u huS hune
      exact F.conserved u hune (by rintro rfl; exact C.ht huS)
    · intro h; exact absurd C.hs h
  -- split the inner full sum over v into v∈S and v∉S
  have hsplit : ∀ u, ∑ v, F.f u v
      = (∑ v ∈ C.S, F.f u v) + ∑ v ∈ (Finset.univ \ C.S), F.f u v := by
    intro u
    rw [← Finset.sum_add_sum_compl C.S (F.f u), Finset.compl_eq_univ_sdiff]
  -- the S×S block vanishes by skew symmetry: D = -D ⇒ D = 0
  have hdiag : ∑ u ∈ C.S, ∑ v ∈ C.S, F.f u v = 0 := by
    have e1 : ∑ u ∈ C.S, ∑ v ∈ C.S, F.f u v
            = ∑ u ∈ C.S, ∑ v ∈ C.S, (- F.f v u) := by
      apply Finset.sum_congr rfl; intro u _
      apply Finset.sum_congr rfl; intro v _
      exact F.skew u v
    have e2 : ∑ u ∈ C.S, ∑ v ∈ C.S, (- F.f v u)
            = - ∑ u ∈ C.S, ∑ v ∈ C.S, F.f v u := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro u _
      rw [Finset.sum_neg_distrib]
    have e3 : ∑ u ∈ C.S, ∑ v ∈ C.S, F.f v u
            = ∑ u ∈ C.S, ∑ v ∈ C.S, F.f u v := Finset.sum_comm
    linarith [e1, e2, e3]
  calc F.value = ∑ u ∈ C.S, ∑ v, F.f u v := hfull.symm
    _ = ∑ u ∈ C.S, ((∑ v ∈ C.S, F.f u v) + ∑ v ∈ (Finset.univ \ C.S), F.f u v) := by
          apply Finset.sum_congr rfl; intro u _; rw [hsplit u]
    _ = (∑ u ∈ C.S, ∑ v ∈ C.S, F.f u v)
          + ∑ u ∈ C.S, ∑ v ∈ (Finset.univ \ C.S), F.f u v := by rw [Finset.sum_add_distrib]
    _ = ∑ u ∈ C.S, ∑ v ∈ (Finset.univ \ C.S), F.f u v := by rw [hdiag]; ring

/-- **Weak duality (PROVED).** Every flow value is bounded by every cut capacity. -/
theorem value_le_capacity {Net : Network N} (F : Flow Net) (C : Cut Net) :
    F.value ≤ C.capacity := by
  rw [F.value_eq_flow_across C]
  unfold Cut.capacity
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  exact F.capacitated u v

-- Strong duality (max flow = min cut) is developed in `Ax2.Explore.MFMC`
-- (`maxflow_eq_mincut`), via the residual-reachable saturated cut.

end Ax2.RouteB
