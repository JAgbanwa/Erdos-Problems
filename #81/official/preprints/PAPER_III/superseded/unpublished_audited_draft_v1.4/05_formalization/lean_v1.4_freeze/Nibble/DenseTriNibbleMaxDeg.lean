/-
# Nibble — the DENSE MAX-DEGREE triangle nibble

Target of this file: the *per-vertex* (maximum-degree) leftover form of the dense approximate
triangle decomposition.

  For every `η > 0` there is `n₀` such that every graph `G` on at least `n₀` vertices with
  `δ(G) ≥ (9/10)|V|` carries a family `P` of pairwise edge-disjoint triangles such that **every**
  vertex `v` is incident to at most `η|V|` edges of `G` left uncovered by `P`:

    `((G.edgeFinset \ P.biUnion triEdges).filter (fun e => v ∈ e)).card ≤ η * |V|`.

The density hypothesis `9|V| ≤ 10 δ(G)` is essential: the density-free max-degree form is false
(the `K₄`-book obstruction), and it is used throughout the chain below.

## Provenance

The packing engine named in the task, `Nibble.nibbleTheoremMost_holds`, does **not** exist in this
development: the interface `NibbleTheoremMost` it would inhabit is *refuted* here by the star
witness (`Nibble.not_nibbleTheoremMost`, `Nibble.not_adaptiveOracleExists` in
`Nibble/AdaptiveAssembly.lean`), and the declaration is retained only inside a block comment.  The
corrected, ceiling-carrying engine `Nibble.nibbleTheoremMostCeil_holds` is what the development
actually runs, and it is what feeds the dense chain used here:
`nibbleTheoremMostCeil_holds → Nibble.exists_matching_of_spread → Nibble.spreadTriangleRounding →
Nibble.denseGlobalSmallLeftover_final`.

The max-degree upgrade itself is the global-potential argument already carried out in the library:
`Nibble.denseTriangleNibbleDeg_all` minimises the star potential `∑_v |uncoveredAt G M v|²` over all
packings, bounds it by the *total*-leftover packing coming from
`Nibble.denseGlobalSmallLeftover_final`, and uses `Nibble.exists_pot_decrease` (the dense-regime
star-augmentation move, which is where `δ(G) ≥ (9/10)|V|` is consumed) to rule out any vertex with
uncovered star bigger than `β|V|`.  What is added here is the packaging: the ceiling in
`Nibble.dense_approx_deg_bounded_all` is removed by running that theorem at `β = η/2` and taking
`n₀ ≥ 2/η`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DenseTriangleNibbleDegAll

open Finset SimpleGraph

namespace Nibble

/-- The edge set of a triangle (indeed of any finite vertex set), as unordered pairs.
Alias for `Nibble.edgesOf`, matching the name used in the statement of the dense max-degree
triangle nibble. -/
abbrev triEdges {V : Type*} [DecidableEq V] (t : Finset V) : Finset (Sym2 V) := edgesOf t

/-- **The dense max-degree triangle nibble.**

For every `η > 0` there is an `n₀` such that every graph `G` on at least `n₀` vertices whose minimum
degree satisfies `δ(G) ≥ (9/10)|V|` admits a family `P` of pairwise edge-disjoint triangles for
which every single vertex `v` lies on at most `η|V|` uncovered edges:

`((G.edgeFinset \ P.biUnion triEdges).filter (fun e => v ∈ e)).card ≤ η * |V|`.

This is the per-vertex (maximum-degree) leftover form; the density hypothesis is what makes it
true. -/
theorem denseTriNibbleMaxDeg_holds (η : ℝ) (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ P : Finset (Finset V),
        (∀ t ∈ P, G.IsNClique 3 t) ∧
        (P : Set (Finset V)).Pairwise (fun s t => Disjoint (triEdges s) (triEdges t)) ∧
        ∀ v : V,
          (((G.edgeFinset \ (P.biUnion triEdges)).filter (fun e => v ∈ e)).card : ℝ)
            ≤ η * (Fintype.card V : ℝ) := by
  classical
  obtain ⟨n₀, hmain⟩ := dense_approx_deg_bounded_all (η / 2) (by positivity)
  refine ⟨max n₀ ⌈2 / η⌉₊, ?_⟩
  intro V _ _ G _ hV hdense
  obtain ⟨P, L, htri, hdisj, hL, -, hdeg⟩ :=
    hmain G (le_trans (le_max_left _ _) hV) hdense
  refine ⟨P, htri, hdisj, ?_⟩
  intro v
  -- `n` is large enough that `(η/2)·n + 1 ≤ η·n`
  have hn : (2 : ℝ) / η ≤ (Fintype.card V : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast le_trans (le_max_right n₀ _) hV
  have hstep : (η / 2) * (Fintype.card V : ℝ) + 1 ≤ η * (Fintype.card V : ℝ) := by
    have h2 : (2 : ℝ) ≤ η * (Fintype.card V : ℝ) := by
      rw [div_le_iff₀ hη] at hn; linarith
    linarith
  have hceil : (⌈(η / 2) * (Fintype.card V : ℝ)⌉₊ : ℝ) ≤ η * (Fintype.card V : ℝ) := by
    refine le_trans (le_of_lt (Nat.ceil_lt_add_one (by positivity))) hstep
  calc (((G.edgeFinset \ (P.biUnion triEdges)).filter (fun e => v ∈ e)).card : ℝ)
      = ((L.filter (fun e => v ∈ e)).card : ℝ) := by rw [hL]
    _ ≤ (⌈(η / 2) * (Fintype.card V : ℝ)⌉₊ : ℝ) := by exact_mod_cast hdeg v
    _ ≤ η * (Fintype.card V : ℝ) := hceil

end Nibble
