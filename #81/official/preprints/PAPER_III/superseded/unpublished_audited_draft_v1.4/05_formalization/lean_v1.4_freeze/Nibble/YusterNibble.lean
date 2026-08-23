/-
# Nibble — Yuster Y5 : apply the nibble theorem to the triangle hypergraph

Standalone, Mathlib-only. Instantiates `NibbleTheorem` (the T3 interface) at `r = 3` for triangle
packing: a `3`-uniform, near-regular, low-codegree hypergraph on a vertex type `W` has a matching
covering a `(1-β)` fraction of `|W|/3`. Applied with `W = the edges of G` this yields a triangle
packing of size `≥ (1-β)·|E(G)|/3` — the hard direction of `ν₃*−ν₃ = o(n²)`.

IMPORTANT ENCODING NOTE: the nibble's bound `|M| ≥ (1-β)·(Fintype.card W)/r` uses the FULL vertex-type
cardinality, and `NearlyRegular` requires every vertex active. So the triangle hypergraph must live on
the vertex type `W = edges of G` (`Fintype.card W = |E(G)|`), NOT on `Finset V` (`2^{|V|}` vertices,
most inactive). `Nibble.YusterE.triangleHypergraphE` (over `Finset V`) must be transported to the edge
subtype before this lemma applies; that transport + the `ν₃` connection are the remaining Y5 work.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Regular
import Nibble.Interface
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.Bound

open Hypergraph

namespace Nibble.YusterE

/-- **Y5 — apply `NibbleTheorem` at `r = 3`.** For any target `β > 0` there is a near-regularity
tolerance `μ > 0` such that every `3`-uniform, `(1±μ)`-near-`d`-regular, codegree-`≤ μd` hypergraph
on a finite vertex type `W` has a matching covering `≥ (1-β)·(|W|/3)` — a near-perfect triangle
packing. (Apply with `W = E(G)`.) -/
theorem exists_near_perfect_triangle_matching (hNibble : NibbleTheorem) {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (d : ℝ),
      0 < d → d₀ ≤ d → IsUniform H 3 → NearlyRegular H d μ → CodegreeBounded H (μ * d) →
      ∃ M : Finset (Finset W), IsMatching H M ∧
        (1 - β) * ((Fintype.card W : ℝ) / 3) ≤ (M.card : ℝ) :=
  hNibble 3 (by norm_num) β hβ

end Nibble.YusterE
