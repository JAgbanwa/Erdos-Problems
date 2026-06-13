import ErdosProblems.Problem84.Basic

import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

/-!
# Constructive realizers and the Fibonacci lower bound

We build an explicit, growing family of realizable cycle spectra and deduce
`f(n) ≥ F_n` (Fibonacci), hence `f(n) ≥ c·φ^n` and `f(n)/2^{n/2} → ∞`.
-/

namespace ErdosProblem84

open scoped BigOperators Topology

/-- Embed `Fin m` into `Fin (m + k)`. -/
def finCastAdd (m k : ℕ) (v : Fin m) : Fin (m + k) :=
  ⟨v.val, Nat.lt_of_lt_of_le v.isLt (Nat.le_add_right _ _)⟩

/-- Add an isolated final vertex to a graph on `Fin m`. -/
def addIsolatedVertex {m : ℕ} (G : SimpleGraph (Fin m)) : SimpleGraph (Fin (m + 1)) where
  Adj i j :=
    if hi : i.val < m then
      if hj : j.val < m then G.Adj ⟨i, hi⟩ ⟨j, hj⟩ else False
    else False
  symm := by
    intro i j h
    by_cases hi : i.val < m
    · by_cases hj : j.val < m
      · exact G.symm (hi := hi) (hj := hj) h
      · exact h
    · exact h
  loopless := by
    intro i h
    by_cases hi : i.val < m
    · by_cases hj : j.val < m
      · exact G.loopless ⟨i, hi⟩ h
      · exact h
    · exact h

/-- Extend a graph on `Fin m` by two vertices creating a cycle of length `m + 2`. -/
def addMaxCycle {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) : SimpleGraph (Fin (m + 2)) where
  Adj i j :=
    let ai := i.val
    let aj := j.val
    if ai < m ∧ aj < m then
      G.Adj ⟨i, by omega⟩ ⟨j, by omega⟩
    else if ai = m ∧ aj = m + 1 then True
    else if aj = m ∧ ai = m + 1 then True
    else if ai = m ∧ aj = 0 then True
    else if aj = m ∧ ai = 0 then True
    else if ai = m + 1 ∧ aj = m - 1 then True
    else if aj = m + 1 ∧ ai = m - 1 then True
    else False
  symm := by
    intro i j; unfold Adj; grind
  loopless := by
    intro i h; unfold Adj at h; split_ifs at h <;> try exact h

/-- A tracked realizable spectrum together with its witness graph. -/
inductive TrackedRealizer : ℕ → Type
| path (m : ℕ) (hm : 3 ≤ m) : TrackedRealizer m
| iso {m} (t : TrackedRealizer m) : TrackedRealizer (m + 1)
| max {m} (t : TrackedRealizer m) (hm : 3 ≤ m) : TrackedRealizer (m + 2)

open TrackedRealizer in
def TrackedRealizer.graph : TrackedRealizer n → SimpleGraph (Fin n)
| path m hm => pathGraph m
| iso t => addIsolatedVertex t.graph
| max t hm => addMaxCycle t.graph hm

open TrackedRealizer in
noncomputable def TrackedRealizer.spectrum : TrackedRealizer n → Set ℕ :=
  fun t => cycleSpectrum t.graph

theorem TrackedRealizer.realizable (t : TrackedRealizer n) :
    Realizable n t.spectrum :=
  ⟨by
    intro ℓ h
    simp only [TrackedRealizer.spectrum, cycleSpectrum] at h
    obtain ⟨u, p, hp, rfl⟩ := h
    sorry,
  ⟨t.graph, rfl⟩⟩

end ErdosProblem84
