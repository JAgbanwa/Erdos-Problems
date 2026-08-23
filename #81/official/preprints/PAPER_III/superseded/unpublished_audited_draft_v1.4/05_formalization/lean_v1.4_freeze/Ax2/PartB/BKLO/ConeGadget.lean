/-
  Part B (Phase 2) — the general cone gadget.

  `ReservedSplitParts.triDecomposable_doubleCone` says that the double cone over a *six*-cycle,
  together with the six-cycle, is triangle-decomposable.  The absorber has to handle cycles of
  arbitrary length, so this file proves the general statement, in the form in which it is really
  used: a cone over a *matching*.

  The union of two perfect matchings `M₁`, `M₂` of a common vertex set is exactly a disjoint union
  of cycles (for a single cycle: its odd and its even edges).  Coning `M₁` from an apex `w` and
  `M₂` from a second apex `u` covers

      (edges of `M₁` and `M₂`)  ∪  (all spokes from `w` and from `u`),

  and the two cones together form an edge-disjoint triangle family.  Specialised to the two
  alternating matchings of a `2m`-cycle this is exactly "the double cone over a `2m`-cycle,
  together with the cycle, is triangle-decomposable", i.e. the general form of
  `triDecomposable_doubleCone` (which is the case `2m = 6`).

  Main results:

  * `coveredEdges_pairConeTris` — the covered-edge formula for one cone;
  * `edgeDisjoint_pairConeTris_union` — the two cones form an edge-disjoint family;
  * `triDecomposable_pairCones` — the resulting decomposability statement.
-/
import Ax2.PartB.BKLO.ReservedSplitParts

namespace Ax2.BKLO

open SimpleGraph Finset Ax2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The triangles of the cone with apex `w` over the list of pairs `M`. -/
def pairConeTris (w : V) (M : List (V × V)) : Finset (Finset V) :=
  (M.map (fun p => ({w, p.1, p.2} : Finset V))).toFinset

/-- The edges of the matching `M`. -/
def pairEdges (M : List (V × V)) : Finset (Sym2 V) :=
  (M.map (fun p => s(p.1, p.2))).toFinset

/-- The spokes from `w` to the vertices covered by `M`. -/
def spokeEdges (w : V) (M : List (V × V)) : Finset (Sym2 V) :=
  (M.flatMap (fun p => [s(w, p.1), s(w, p.2)])).toFinset

/-- The pairs of `M` are pairwise vertex-disjoint, and each pair consists of two distinct
vertices. -/
def MatchingPairs (M : List (V × V)) : Prop :=
  (∀ p ∈ M, p.1 ≠ p.2) ∧
    M.Pairwise (fun p q => p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2)

omit [Fintype V] in
@[simp] theorem pairConeTris_nil (w : V) : pairConeTris w ([] : List (V × V)) = ∅ := rfl

omit [Fintype V] in
@[simp] theorem pairConeTris_cons (w : V) (p : V × V) (M : List (V × V)) :
    pairConeTris w (p :: M) = insert ({w, p.1, p.2} : Finset V) (pairConeTris w M) := by
  simp [pairConeTris]

omit [Fintype V] in
theorem mem_pairConeTris {w : V} {M : List (V × V)} {t : Finset V} :
    t ∈ pairConeTris w M ↔ ∃ p ∈ M, t = ({w, p.1, p.2} : Finset V) := by
  simp [pairConeTris, eq_comm]

omit [Fintype V] in
/-- **The edges covered by a cone over a matching**: the matching edges and the spokes. -/
theorem coveredEdges_pairConeTris (w : V) (M : List (V × V))
    (hw : ∀ p ∈ M, w ≠ p.1 ∧ w ≠ p.2) (hM : ∀ p ∈ M, p.1 ≠ p.2) :
    coveredEdges (pairConeTris w M) = pairEdges M ∪ spokeEdges w M := by
  induction M with
  | nil => simp [coveredEdges, pairEdges, spokeEdges]
  | cons p M ih =>
      have hp := hw p (by simp)
      have hp' := hM p (by simp)
      rw [pairConeTris_cons, coveredEdges, Finset.biUnion_insert, ← coveredEdges,
        ih (fun q hq => hw q (by simp [hq])) (fun q hq => hM q (by simp [hq])),
        triEdges_triple hp.1 hp.2 hp']
      ext e
      simp only [pairEdges, spokeEdges, List.map_cons, List.toFinset_cons, List.flatMap_cons,
        List.toFinset_append, Finset.mem_union, Finset.mem_insert, List.mem_toFinset,
        Finset.mem_singleton, List.not_mem_nil, or_false]
      tauto

omit [Fintype V] in
/-- Two cone triangles over disjoint pairs meet in the apex only. -/
theorem triEdges_disjoint_pairCone {w : V} {p q : V × V}
    (h : p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) :
    Disjoint (triEdges ({w, p.1, p.2} : Finset V)) (triEdges ({w, q.1, q.2} : Finset V)) := by
  refine triEdges_disjoint_of_card_inter_le_one ?_
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  rcases hx1 with rfl | rfl | rfl <;> rcases hy1 with rfl | rfl | rfl <;>
    simp_all [eq_comm]

omit [Fintype V] in
/-- Two cone triangles with different apexes over pairs meeting in at most one vertex have
disjoint edge sets. -/
theorem triEdges_disjoint_pairCone_cross {w u : V} {p q : V × V} (hwu : w ≠ u)
    (hwq : w ≠ q.1 ∧ w ≠ q.2) (hup : u ≠ p.1 ∧ u ≠ p.2)
    (hcross : (({p.1, p.2} : Finset V) ∩ ({q.1, q.2} : Finset V)).card ≤ 1) :
    Disjoint (triEdges ({w, p.1, p.2} : Finset V)) (triEdges ({u, q.1, q.2} : Finset V)) := by
  refine triEdges_disjoint_of_card_inter_le_one ?_
  have hsub : ({w, p.1, p.2} : Finset V) ∩ ({u, q.1, q.2} : Finset V) ⊆
      ({p.1, p.2} : Finset V) ∩ ({q.1, q.2} : Finset V) := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hwq1, hwq2⟩ := hwq
    obtain ⟨hup1, hup2⟩ := hup
    rcases hx1 with rfl | h | h <;> rcases hx2 with rfl | h' | h' <;> simp_all
  exact le_trans (Finset.card_le_card hsub) hcross

omit [Fintype V] in
/-- **The two cones form an edge-disjoint triangle family.** -/
theorem edgeDisjoint_pairConeTris_union {w u : V} {M₁ M₂ : List (V × V)} (hwu : w ≠ u)
    (hw₂ : ∀ q ∈ M₂, w ≠ q.1 ∧ w ≠ q.2) (hu₁ : ∀ p ∈ M₁, u ≠ p.1 ∧ u ≠ p.2)
    (hM₁ : MatchingPairs M₁) (hM₂ : MatchingPairs M₂)
    (hcross : ∀ p ∈ M₁, ∀ q ∈ M₂,
      (({p.1, p.2} : Finset V) ∩ ({q.1, q.2} : Finset V)).card ≤ 1) :
    EdgeDisjoint (pairConeTris w M₁ ∪ pairConeTris u M₂) := by
  have hsymm : Symmetric (fun p q : V × V => p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) := by
    rintro p q ⟨h1, h2, h3, h4⟩
    exact ⟨h1.symm, h3.symm, h2.symm, h4.symm⟩
  intro t₁ ht₁ t₂ ht₂ hne
  rcases Finset.mem_union.mp ht₁ with h₁ | h₁ <;> rcases Finset.mem_union.mp ht₂ with h₂ | h₂
  · obtain ⟨p, hp, rfl⟩ := mem_pairConeTris.mp h₁
    obtain ⟨q, hq, rfl⟩ := mem_pairConeTris.mp h₂
    have hpq : p ≠ q := by rintro rfl; exact hne rfl
    exact triEdges_disjoint_pairCone (List.Pairwise.forall hsymm hM₁.2 hp hq hpq)
  · obtain ⟨p, hp, rfl⟩ := mem_pairConeTris.mp h₁
    obtain ⟨q, hq, rfl⟩ := mem_pairConeTris.mp h₂
    exact triEdges_disjoint_pairCone_cross hwu (hw₂ q hq) (hu₁ p hp) (hcross p hp q hq)
  · obtain ⟨p, hp, rfl⟩ := mem_pairConeTris.mp h₁
    obtain ⟨q, hq, rfl⟩ := mem_pairConeTris.mp h₂
    exact (triEdges_disjoint_pairCone_cross hwu (hw₂ p hp) (hu₁ q hq) (hcross q hq p hp)).symm
  · obtain ⟨p, hp, rfl⟩ := mem_pairConeTris.mp h₁
    obtain ⟨q, hq, rfl⟩ := mem_pairConeTris.mp h₂
    have hpq : p ≠ q := by rintro rfl; exact hne rfl
    exact triEdges_disjoint_pairCone (List.Pairwise.forall hsymm hM₂.2 hp hq hpq)

omit [Fintype V] in
/-- **The general cone gadget.**  Cone the matching `M₁` from the apex `w` and the matching `M₂`
from a second apex `u`.  If the pairs inside each matching are vertex-disjoint, the pairs of the
two matchings meet in at most one vertex, the apexes avoid all these vertices and each cone
triangle is a triangle of `G`, then

  `(edges of M₁) ∪ (edges of M₂) ∪ (spokes from w) ∪ (spokes from u)`

is triangle-decomposable.  For the two alternating matchings of a `2m`-cycle this is the double
cone over that cycle together with the cycle itself, i.e. the general form of
`triDecomposable_doubleCone`. -/
theorem triDecomposable_pairCones (G : SimpleGraph V) [DecidableRel G.Adj] {w u : V}
    {M₁ M₂ : List (V × V)} (hwu : w ≠ u)
    (hw₁ : ∀ p ∈ M₁, w ≠ p.1 ∧ w ≠ p.2) (hw₂ : ∀ q ∈ M₂, w ≠ q.1 ∧ w ≠ q.2)
    (hu₁ : ∀ p ∈ M₁, u ≠ p.1 ∧ u ≠ p.2) (hu₂ : ∀ q ∈ M₂, u ≠ q.1 ∧ u ≠ q.2)
    (hM₁ : MatchingPairs M₁) (hM₂ : MatchingPairs M₂)
    (hcross : ∀ p ∈ M₁, ∀ q ∈ M₂,
      (({p.1, p.2} : Finset V) ∩ ({q.1, q.2} : Finset V)).card ≤ 1)
    (hcl₁ : ∀ p ∈ M₁, G.IsNClique 3 ({w, p.1, p.2} : Finset V))
    (hcl₂ : ∀ q ∈ M₂, G.IsNClique 3 ({u, q.1, q.2} : Finset V)) :
    TriDecomposable G
      ((pairEdges M₁ ∪ spokeEdges w M₁) ∪ (pairEdges M₂ ∪ spokeEdges u M₂)) := by
  have hcov : coveredEdges (pairConeTris w M₁ ∪ pairConeTris u M₂) =
      (pairEdges M₁ ∪ spokeEdges w M₁) ∪ (pairEdges M₂ ∪ spokeEdges u M₂) := by
    rw [coveredEdges, Finset.union_biUnion, ← coveredEdges, ← coveredEdges,
      coveredEdges_pairConeTris w M₁ hw₁ hM₁.1, coveredEdges_pairConeTris u M₂ hu₂ hM₂.1]
  have hcl : ∀ t ∈ pairConeTris w M₁ ∪ pairConeTris u M₂, G.IsNClique 3 t := by
    intro t ht
    rcases Finset.mem_union.mp ht with h | h
    · obtain ⟨p, hp, rfl⟩ := mem_pairConeTris.mp h
      exact hcl₁ p hp
    · obtain ⟨q, hq, rfl⟩ := mem_pairConeTris.mp h
      exact hcl₂ q hq
  have hd := edgeDisjoint_pairConeTris_union hwu hw₂ hu₁ hM₁ hM₂ hcross
  exact hcov ▸ TriDecomposable.of_family G hcl hd

omit [Fintype V] in
/-- Rearranging the four pieces of a two-cone cover into "spokes" and "matching edges". -/
theorem cone_union_rearrange (A B C D : Finset (Sym2 V)) :
    (A ∪ B) ∪ (C ∪ D) = (B ∪ D) ∪ (A ∪ C) := by
  ext e
  simp only [Finset.mem_union]
  tauto

omit [Fintype V] in
/-- **Absorbing an arbitrary even cycle by transforming it into an absorbable one.**  The general
form of `localAbsorbable_sixCycle_of_doubleCone`: if the reserved family `B` absorbs the cycle
`C'` presented by the matchings `N₁, N₂`, and the cycle `C` presented by `M₁, M₂` spans the same
spokes (`hspokes`, the analogue of the equality of double cones), then `B` enlarged by the spokes
and by `C'` absorbs `C`.  Instance of `localAbsorbable_transformer` with the transformer
`triDecomposable_pairCones` applied to both presentations. -/
theorem localAbsorbable_cycle_of_pairCones (G : SimpleGraph V) [DecidableRel G.Adj] {w u : V}
    {M₁ M₂ N₁ N₂ : List (V × V)} {B : Finset (Finset V)}
    (hB : ∀ t ∈ B, G.IsNClique 3 t) (hBd : EdgeDisjoint B)
    (habs : LocalAbsorbable G B (pairEdges N₁ ∪ pairEdges N₂)) (hwu : w ≠ u)
    (hwM₁ : ∀ p ∈ M₁, w ≠ p.1 ∧ w ≠ p.2) (hwM₂ : ∀ q ∈ M₂, w ≠ q.1 ∧ w ≠ q.2)
    (huM₁ : ∀ p ∈ M₁, u ≠ p.1 ∧ u ≠ p.2) (huM₂ : ∀ q ∈ M₂, u ≠ q.1 ∧ u ≠ q.2)
    (hM₁ : MatchingPairs M₁) (hM₂ : MatchingPairs M₂)
    (hcrossM : ∀ p ∈ M₁, ∀ q ∈ M₂,
      (({p.1, p.2} : Finset V) ∩ ({q.1, q.2} : Finset V)).card ≤ 1)
    (hclM₁ : ∀ p ∈ M₁, G.IsNClique 3 ({w, p.1, p.2} : Finset V))
    (hclM₂ : ∀ q ∈ M₂, G.IsNClique 3 ({u, q.1, q.2} : Finset V))
    (hwN₁ : ∀ p ∈ N₁, w ≠ p.1 ∧ w ≠ p.2) (hwN₂ : ∀ q ∈ N₂, w ≠ q.1 ∧ w ≠ q.2)
    (huN₁ : ∀ p ∈ N₁, u ≠ p.1 ∧ u ≠ p.2) (huN₂ : ∀ q ∈ N₂, u ≠ q.1 ∧ u ≠ q.2)
    (hN₁ : MatchingPairs N₁) (hN₂ : MatchingPairs N₂)
    (hcrossN : ∀ p ∈ N₁, ∀ q ∈ N₂,
      (({p.1, p.2} : Finset V) ∩ ({q.1, q.2} : Finset V)).card ≤ 1)
    (hclN₁ : ∀ p ∈ N₁, G.IsNClique 3 ({w, p.1, p.2} : Finset V))
    (hclN₂ : ∀ q ∈ N₂, G.IsNClique 3 ({u, q.1, q.2} : Finset V))
    (hspokes : spokeEdges w N₁ ∪ spokeEdges u N₂ = spokeEdges w M₁ ∪ spokeEdges u M₂)
    (hd1 : Disjoint (coveredEdges B ∪ (pairEdges N₁ ∪ pairEdges N₂))
      ((spokeEdges w M₁ ∪ spokeEdges u M₂) ∪ (pairEdges M₁ ∪ pairEdges M₂)))
    (hd2 : Disjoint (coveredEdges B)
      ((spokeEdges w M₁ ∪ spokeEdges u M₂) ∪ (pairEdges N₁ ∪ pairEdges N₂))) :
    ∃ B' : Finset (Finset V), (∀ t ∈ B', G.IsNClique 3 t) ∧ EdgeDisjoint B' ∧
      coveredEdges B' = coveredEdges B ∪
        ((spokeEdges w M₁ ∪ spokeEdges u M₂) ∪ (pairEdges N₁ ∪ pairEdges N₂)) ∧
      LocalAbsorbable G B' (pairEdges M₁ ∪ pairEdges M₂) := by
  have hconeM := triDecomposable_pairCones G hwu hwM₁ hwM₂ huM₁ huM₂ hM₁ hM₂ hcrossM hclM₁ hclM₂
  have hconeN := triDecomposable_pairCones G hwu hwN₁ hwN₂ huN₁ huN₂ hN₁ hN₂ hcrossN hclN₁ hclN₂
  rw [cone_union_rearrange] at hconeM hconeN
  rw [hspokes] at hconeN
  exact localAbsorbable_transformer G hB hBd habs hconeM hconeN hd1 hd2

/-! ### Non-vacuity: the double cone over an eight-cycle -/

set_option maxRecDepth 4000 in
/-- **The gadget goes beyond the six-cycle case.**  In `K₁₀` the eight-cycle `0-1-2-⋯-7-0`,
presented by its two alternating matchings, together with the sixteen spokes from the two apexes
`8` and `9`, carries an edge-disjoint triangle decomposition (24 edges, 8
triangles).  This is the instance `triDecomposable_doubleCone` could not provide. -/
theorem triDecomposable_eightCycle_doubleCone :
    TriDecomposable (⊤ : SimpleGraph (Fin 10))
      ((pairEdges [((0 : Fin 10), (1 : Fin 10)), (2, 3), (4, 5), (6, 7)] ∪
          spokeEdges 8 [((0 : Fin 10), (1 : Fin 10)), (2, 3), (4, 5), (6, 7)]) ∪
        (pairEdges [((1 : Fin 10), (2 : Fin 10)), (3, 4), (5, 6), (7, 0)] ∪
          spokeEdges 9 [((1 : Fin 10), (2 : Fin 10)), (3, 4), (5, 6), (7, 0)])) := by
  refine triDecomposable_pairCones _ (by decide) (by decide) (by decide) (by decide) (by decide)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) ?_ ?_
  · intro p hp
    fin_cases hp <;> exact SimpleGraph.is3Clique_triple_iff.2 (by decide)
  · intro q hq
    fin_cases hq <;> exact SimpleGraph.is3Clique_triple_iff.2 (by decide)

end Ax2.BKLO
