module

public import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Ends.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

/-!
# Alon–Shapira: basic definitions

Graph families, induced-`𝓕`-freeness, edit distance, `ε`-farness, induced copies, and the
statement `Lemma42 𝓕` of Lemma 4.2 of Alon–Shapira.
-/

@[expose] public section

open SimpleGraph

open scoped Classical

namespace AlonShapira

/-- A (possibly infinite) family of finite graphs: `𝓕 k` is the set of its members on `k`
vertices (vertex set `Fin k`). -/
abbrev GraphFamily := ∀ k : ℕ, Set (SimpleGraph (Fin k))

/-- `G` is *induced `𝓕`-free*: no member of `𝓕` embeds into `G` as an induced subgraph. -/
def IndFree (𝓕 : GraphFamily) {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ k, ∀ H ∈ 𝓕 k, IsEmpty (H ↪g G)

/-- Edit distance between two graphs on the same vertex set: the number of pairs that are an
edge in exactly one of them (edges to add or remove to go from `G` to `G'`). -/
noncomputable def editDist {n : ℕ} (G G' : SimpleGraph (Fin n)) : ℕ :=
  (symmDiff G.edgeFinset G'.edgeFinset).card

/-- `G` (on `n` vertices) is `ε`-far from being induced `𝓕`-free: one has to add/delete at least
`ε n²` edges to turn `G` into an induced `𝓕`-free graph. -/
def FarFromIndFree (𝓕 : GraphFamily) (ε : ℝ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ G' : SimpleGraph (Fin n), IndFree 𝓕 G' → ε * (n : ℝ) ^ 2 ≤ editDist G G'

/-- Number of (labelled) induced copies of `H` in `G`, i.e. of induced embeddings `H ↪g G`. -/
noncomputable def indCopies {k n : ℕ} (H : SimpleGraph (Fin k)) (G : SimpleGraph (Fin n)) : ℕ :=
  Fintype.card (H ↪g G)

/-- **Statement of Lemma 4.2 (Alon–Shapira)** for the family `𝓕`: there are functions
`N`, `f` and `δ` with `δ ε > 0` such that every graph on `n ≥ N ε` vertices which is `ε`-far
from being induced `𝓕`-free contains at least `δ ε · n^k` induced copies of some `H ∈ 𝓕` with
`k ≤ f ε` vertices. -/
def Lemma42 (𝓕 : GraphFamily) : Prop :=
  ∃ N : ℝ → ℕ, ∃ f : ℝ → ℕ, ∃ δ : ℝ → ℝ,
    ∀ ε > 0, 0 < δ ε ∧
      ∀ n ≥ N ε, ∀ G : SimpleGraph (Fin n), FarFromIndFree 𝓕 ε G →
        ∃ k ≤ f ε, ∃ H ∈ 𝓕 k, δ ε * (n : ℝ) ^ k ≤ indCopies H G

end AlonShapira
