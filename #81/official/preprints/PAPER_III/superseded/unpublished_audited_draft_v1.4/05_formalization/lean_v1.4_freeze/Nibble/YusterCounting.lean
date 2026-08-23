/-
# Yuster Y3: lower bounds for degrees in the triangle hypergraph

This file identifies triangles through a fixed vertex with graph edges inside its
neighbourhood, and derives the required lower bound from a dense uniform pair.
-/
import Nibble.Yuster
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Bound

open Hypergraph SimpleGraph

namespace Nibble.Yuster

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph edges whose two endpoints lie in `s`, represented as two-element finsets. -/
def edgesInside (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) : Finset (Finset V) :=
  (s.powersetCard 2).filter fun e => G.IsClique (e : Set V)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Triangles through `v` are in bijection with edges of `G` inside the neighbourhood of `v`. -/
theorem triangleHypergraph_degree_eq_edgesInside (v : V) :
    degree (triangleHypergraph G) v = (edgesInside G (G.neighborFinset v)).card := by
  rw [Hypergraph.degree, triangleHypergraph, edgesInside]
  refine Finset.card_bij (fun e _ => e.erase v) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ha
    obtain ⟨hclique, hv⟩ := ha
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    have hsub : a.erase v ⊆ G.neighborFinset v := by
      intro x hx
      have hax : x ∈ a := Finset.mem_of_mem_erase hx
      have hxv : x ≠ v := Finset.ne_of_mem_erase hx
      rw [SimpleGraph.mem_neighborFinset]
      exact hclique.isClique (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hax) (fun h => hxv h.symm)
    have hcard : (a.erase v).card = 2 := by rw [Finset.card_erase_of_mem hv, hclique.card_eq]
    refine ⟨⟨hsub, hcard⟩, ?_⟩
    intro x hx y hy hxy
    have hx' : x ∈ a := Finset.mem_of_mem_erase hx
    have hy' : y ∈ a := Finset.mem_of_mem_erase hy
    exact hclique.isClique (Finset.mem_coe.mpr hx') (Finset.mem_coe.mpr hy') hxy
  · intro a₁ ha₁ a₂ ha₂ hef
    simp only [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ha₁ ha₂
    obtain ⟨_, hv₁⟩ := ha₁
    obtain ⟨_, hv₂⟩ := ha₂
    simp only at hef
    have : insert v (a₁.erase v) = insert v (a₂.erase v) := congrArg _ hef
    rwa [Finset.insert_erase hv₁, Finset.insert_erase hv₂] at this
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hb
    have hsub := hb.1
    have hvnotin : v ∉ b := by
      intro hvb
      have : v ∈ G.neighborFinset v := hsub.1 hvb
      rw [SimpleGraph.mem_neighborFinset] at this
      simp_all
    refine ⟨insert v b, ?_, ?_⟩
    · simp only [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff]
      obtain ⟨hsub', hcard⟩ := hsub
      have hbclique : G.IsClique (↑b) := hb.2
      refine ⟨?_, Finset.mem_insert_self v b⟩
      have h : G.IsNClique 3 (insert v b) := by
        constructor
        · intro x hx y hy hxy
          simp only [Finset.mem_coe, Finset.mem_insert] at hx hy
          rcases hx with rfl | hxb
          · rcases hy with rfl | hyb
            · contradiction
            · rw [← SimpleGraph.mem_neighborFinset]; exact hsub' hyb
          · rcases hy with rfl | hyb
            · rw [SimpleGraph.adj_comm, ← SimpleGraph.mem_neighborFinset]; exact hsub' hxb
            · exact hbclique (Finset.mem_coe.mpr hxb) (Finset.mem_coe.mpr hyb) hxy
        · simp [hvnotin, hcard]
      exact h
    · exact Finset.erase_insert hvnotin

/-- Interedges of two disjoint subsets inject into the edges inside any common ambient set. -/
theorem card_interedges_le_edgesInside {s t w : Finset V}
    (hst : Disjoint s t) (hsw : s ⊆ w) (htw : t ⊆ w) :
    (G.interedges s t).card ≤ (edgesInside G w).card := by
  apply Finset.card_le_card_of_injOn (f := fun p => {p.1, p.2})
  · -- MapsTo: show that each interedge maps to an edge inside w
    intro p hp
    rw [Finset.mem_coe] at hp ⊢
    simp only [edgesInside, Finset.mem_filter, Finset.mem_powersetCard]
    -- p ∈ G.interedges s t means p.1 ∈ s, p.2 ∈ t, and G.Adj p.1 p.2
    change p ∈ Finset.filter (fun p => G.Adj p.1 p.2) (s ×ˢ t) at hp
    simp only [Finset.mem_filter] at hp
    rcases hp with ⟨hp_mem, hp_adj⟩
    simp only [Finset.mem_product] at hp_mem
    rcases hp_mem with ⟨hps, hpt⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · -- {p.1, p.2} ⊆ w
      intro x hx
      simp at hx
      rcases hx with rfl | rfl <;> [exact hsw hps; exact htw hpt]
    · -- {p.1, p.2}.card = 2
      rw [Finset.card_pair]
      intro h
      have : p.2 ∈ s := h.symm ▸ hps
      exact Finset.disjoint_left.mp hst this hpt
    · -- G.IsClique {p.1, p.2}
      rw [SimpleGraph.isClique_iff]
      intro a ha b hb hab
      simp at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all [SimpleGraph.Adj.symm]
  · -- InjOn: show that {p.1, p.2} is injective on interedges
    intro p₁ hp₁ p₂ hp₂ heq
    -- Both pairs are in interedges, so p.1 ∈ s and p.2 ∈ t
    change p₁ ∈ Finset.filter (fun p => G.Adj p.1 p.2) (s ×ˢ t) at hp₁
    change p₂ ∈ Finset.filter (fun p => G.Adj p.1 p.2) (s ×ˢ t) at hp₂
    simp only [Finset.mem_filter, Finset.mem_product] at hp₁ hp₂
    rcases hp₁ with ⟨⟨h₁s, h₁t⟩, _⟩
    rcases hp₂ with ⟨⟨h₂s, h₂t⟩, _⟩
    -- heq : {p₁.1, p₁.2} = {p₂.1, p₂.2}
    simp only at heq
    have hp11 : p₁.1 ∈ ({p₂.1, p₂.2} : Finset V) := by rw [← heq]; exact Finset.mem_insert_self _ _
    have hp12 : p₁.2 ∈ ({p₂.1, p₂.2} : Finset V) := by rw [← heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    -- From hp11: p₁.1 = p₂.1 or p₁.1 = p₂.2
    -- But p₁.1 ∈ s, p₂.2 ∈ t, and s ⊓ t = ∅, so p₁.1 ≠ p₂.2
    simp at hp11 hp12
    have h11 : p₁.1 = p₂.1 ∨ p₁.1 = p₂.2 := hp11
    have h12 : p₁.2 = p₂.1 ∨ p₁.2 = p₂.2 := hp12
    rcases h11 with h11a | h11b <;> rcases h12 with h12a | h12b
    · -- p₁.1 = p₂.1 and p₁.2 = p₂.1: contradicts disjointness (p₁.2 ∈ t and p₂.1 ∈ s)
      exfalso
      have : p₁.2 ∈ s := h12a ▸ h₂s
      exact Finset.disjoint_left.mp hst this h₁t
    · -- p₁.1 = p₂.1 and p₁.2 = p₂.2: valid
      exact Prod.ext h11a h12b
    · -- p₁.1 = p₂.2 and p₁.2 = p₂.1: contradicts disjointness
      exfalso
      have : p₁.1 ∈ t := h11b ▸ h₂t
      exact Finset.disjoint_left.mp hst h₁s this
    · -- p₁.1 = p₂.2 and p₁.2 = p₂.2: contradicts disjointness
      exfalso
      have : p₁.1 ∈ t := h11b ▸ h₂t
      exact Finset.disjoint_left.mp hst h₁s this

/-- A `2ε`-dense pair has at least `ε |s| |t|` interedges.
Uniformity supplies the positivity of `ε`; no further consequence of uniformity is needed here. -/
theorem uniform_dense_pair_interedges_lower {ε : ℝ} {s t : Finset V}
    (hunif : G.IsUniform ε s t) (hdense : 2 * ε ≤ (G.edgeDensity s t : ℝ)) :
    ε * (s.card : ℝ) * (t.card : ℝ) ≤ (G.interedges s t).card := by
  have edgeDensity_def : G.edgeDensity s t = (G.interedges s t).card / (s.card * t.card : ℕ) := by
    simp [SimpleGraph.edgeDensity, Rel.edgeDensity, SimpleGraph.interedges, Rel.interedges]
  rw [edgeDensity_def] at hdense
  simp only [Rat.cast_div, Rat.cast_natCast] at hdense
  have hdense' : 2 * ε ≤ ↑(G.interedges s t).card / ((s.card : ℝ) * t.card) := by
    convert hdense using 2
    norm_cast
  by_cases h : (s.card : ℝ) * t.card = 0
  · have : ε * ↑s.card * ↑t.card = 0 := by linear_combination h * ε
    simp [this]
  · have hpos : 0 < (s.card : ℝ) * t.card := lt_of_le_of_ne (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Ne.symm h)
    have := (le_div_iff₀ hpos).mp hdense'
    have hε_neg : ε < 0 → ε * ↑s.card * ↑t.card ≤ ↑(G.interedges s t).card := by
      intro hε
      have : ε * ↑s.card * ↑t.card < 0 := by nlinarith only [hpos, hε]
      linarith [show (0 : ℝ) ≤ (G.interedges s t).card by exact Nat.cast_nonneg _]
    by_cases hε : ε < 0
    · exact hε_neg hε
    · push_neg at hε
      linarith [mul_nonneg hε (mul_nonneg (Nat.cast_nonneg (s.card)) (Nat.cast_nonneg (t.card)))]

/-- **Y3 degree lower bound.** A disjoint `2ε`-dense uniform pair inside the neighbourhood of `v`
provides that many distinct triangles through `v`. -/
theorem triangleHypergraph_degree_lower_of_uniform_pair {ε : ℝ} {v : V} {s t : Finset V}
    (hunif : G.IsUniform ε s t) (hdense : 2 * ε ≤ (G.edgeDensity s t : ℝ))
    (hst : Disjoint s t) (hsv : s ⊆ G.neighborFinset v)
    (htv : t ⊆ G.neighborFinset v) :
    ε * (s.card : ℝ) * (t.card : ℝ) ≤ degree (triangleHypergraph G) v := by
  rw [triangleHypergraph_degree_eq_edgesInside]
  exact (uniform_dense_pair_interedges_lower G hunif hdense).trans
    (Nat.cast_le.mpr (card_interedges_le_edgesInside G hst hsv htv))

end Nibble.Yuster
