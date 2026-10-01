/-
The edit route: no induced cycle of length ≥ 4 ⇒ chordal (every cycle of length ≥ 4 has a chord).

A chordless cycle `c` of length `L ≥ 4` gives an induced embedding `cycleGraph L ↪g G`, `i ↦ c.getVert i`. It is
injective by `IsCycle.getVert_injOn'`. Consecutive vertices are adjacent by `adj_getVert_succ`, and any other
adjacency would be a chord, since `toSubgraph_adj_iff` says that the edges of `c` are exactly the consecutive
pairs. This is the direction needed to read the Alon–Shapira edit-closeness (`AlonShapira.IsChordal`, "no induced
`C_k`, `k ≥ 4`") as closeness to `SimpleGraph.IsChordal` of `PaperIV/ChordalStructure.lean`.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
import PaperIV.EditRouteLemmaK
import PaperIV.ChordalStructure
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace PaperIV.EditRoute

open SimpleGraph

/-- **No induced long cycle ⇒ chordal.** -/
theorem isChordal_of_noInducedCycle {V : Type*} (G : SimpleGraph V)
    (h : ∀ k : ℕ, 4 ≤ k → IsEmpty (SimpleGraph.cycleGraph k ↪g G)) : G.IsChordal := by
  intro v c hc hlen
  by_contra hno
  push_neg at hno
  set L := c.length with hL
  have hL2 : 2 ≤ L := by omega
  let φ : Fin L → V := fun i => c.getVert i.val
  have hinj : Function.Injective φ := by
    intro i j hij
    have hi : i.val ∈ {i | i ≤ c.length - 1} := by simp only [Set.mem_setOf_eq]; omega
    have hj : j.val ∈ {i | i ≤ c.length - 1} := by simp only [Set.mem_setOf_eq]; omega
    exact Fin.ext (hc.getVert_injOn' hi hj hij)
  have hlastv : c.getVert L = c.getVert 0 := by rw [c.getVert_length, c.getVert_zero]
  have hsucc : ∀ m : ℕ, m < L → c.getVert (m + 1) = c.getVert ((m + 1) % L) := by
    intro m hm
    rcases Nat.lt_or_ge (m + 1) L with h' | h'
    · rw [Nat.mod_eq_of_lt h']
    · have hm1 : m + 1 = L := by omega
      rw [hm1, Nat.mod_self, hlastv]
  have hiff : ∀ i j : Fin L, G.Adj (φ i) (φ j) ↔ (cycleGraph L).Adj i j := by
    intro i j
    rw [cycleGraph_adj_iff_mod hL2]
    constructor
    · intro hadj
      have hmem := hno _ _ (c.getVert_mem_support _) (c.getVert_mem_support _) hadj
      rw [← Walk.adj_toSubgraph_iff_mem_edges, Walk.toSubgraph_adj_iff] at hmem
      obtain ⟨m, hm, hmL⟩ := hmem
      rw [hsucc m hmL] at hm
      have hmL' : (m + 1) % L < L := Nat.mod_lt _ (by omega)
      rcases Sym2.eq_iff.mp hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have e1 : (⟨m, hmL⟩ : Fin L) = i := hinj (show φ ⟨m, hmL⟩ = φ i from h1)
        have e2 : (⟨(m + 1) % L, hmL'⟩ : Fin L) = j := hinj (show φ ⟨(m + 1) % L, hmL'⟩ = φ j from h2)
        left
        rw [← e1, ← e2]
      · have e1 : (⟨m, hmL⟩ : Fin L) = j := hinj (show φ ⟨m, hmL⟩ = φ j from h1)
        have e2 : (⟨(m + 1) % L, hmL'⟩ : Fin L) = i := hinj (show φ ⟨(m + 1) % L, hmL'⟩ = φ i from h2)
        right
        rw [← e1, ← e2]
    · rintro (h1 | h1)
      · have hadj := c.adj_getVert_succ (i := i.val) i.isLt
        rw [hsucc i.val i.isLt, h1] at hadj
        exact hadj
      · have hadj := c.adj_getVert_succ (i := j.val) j.isLt
        rw [hsucc j.val j.isLt, h1] at hadj
        exact hadj.symm
  exact (h L hlen).false ⟨⟨φ, hinj⟩, fun {a b} => hiff a b⟩

end PaperIV.EditRoute
