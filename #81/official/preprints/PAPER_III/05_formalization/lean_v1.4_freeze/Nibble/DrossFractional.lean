/-
# Nibble — the global fractional input that would unlock `c < 1/5`

`Nibble.beats_half_of_leftoverConst` shows that a *single* leftover constant `c < 1/5` at the Dross
density already beats the unconditional per-vertex wall `1/2`.  The counting route of this library
certifies `c = 0.3362` (`Nibble.denseGlobalLeftoverConst_1681_over_5000`), and that constant is the
exact optimum of the linear-programming relaxation of its three counting inputs
(`Nibble.master_linear_threshold`) — no reweighting of the same count can reach `1/5`.  This is not
an artefact of the particular count: a maximal packing may leave a triangle-free graph, so Mantel
caps *any* argument that only sees maximality at `c = 1/2`, and the second-order swaps of
`Nibble.DenseTriangleNibbleDegProof` are capped at `c = 1/4` by a leftover consisting of two
disjoint balanced complete bipartite graphs inside a near-complete `G` — it is triangle-free and
admits none of the improving swaps.  Crossing `1/5` therefore requires a *global* input.

This file isolates that input, in the exact two-step form in which it is available in the
literature, and machine-checks that the two steps together close the target.

* `Nibble.IsFracTriangleDecomp` — a **fractional triangle decomposition** of `G`: nonnegative
  weights on the triangles with every edge receiving total weight `1`.
* `Nibble.DrossFractional` — **Dross's theorem** (F. Dross, *Fractional triangle decompositions in
  graphs with large minimum degree*, SIAM J. Discrete Math. **30** (2016), Thm 5): every graph with
  `δ(G) ≥ (9/10)|V|` has a fractional triangle decomposition.  This is exactly the density at which
  the residual `Nibble.DenseGlobalLeftoverConst` is posed.
* `Nibble.FracRoundingToPacking` — the **rounding** step (Frankl–Rödl / Haxell–Rödl nibble): a graph
  carrying a fractional triangle decomposition has, for large `|V|`, an integral triangle packing
  leaving `o(|V|²)` uncovered incidences.
* `Nibble.denseGlobalSmallLeftover_of_dross_of_rounding`,
  `Nibble.leftoverConst_below_fifth_of_dross_of_rounding`,
  `Nibble.beats_half_of_dross_of_rounding` — the machine-checked chain

  `DrossFractional → FracRoundingToPacking → DenseGlobalSmallLeftover`
  `→ (∃ c < 1/5, DenseGlobalLeftoverConst c) → (∃ β < 1/2, per-vertex star bound β|V|)`,

  i.e. the two displayed global statements are *precisely* what is missing between the proved
  `0.3362` and the target `1/5`.

To certify that `Nibble.IsFracTriangleDecomp` says what it should, the file also proves it
non-vacuous and correct on examples:

* `Nibble.exists_triangle_of_fracDecomp` — under a fractional decomposition every edge lies in a
  triangle (so the definition has real content);
* `Nibble.isFracTriangleDecomp_top` — the **complete graph** on `n ≥ 3` vertices carries the
  fractional (indeed integral, up to scaling) decomposition `w ≡ 1/(n − 2)`, via
  `Nibble.card_triangles_through_edge_top`: every edge of `Kₙ` lies in exactly `n − 2` triangles.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DenseGlobalLeftoverSharp

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Fractional triangle decompositions -/

/-- The triangles of `G` through a given edge, as hyperedges of the edge-type triangle
hypergraph. -/
noncomputable def trianglesThrough (G : SimpleGraph V) [DecidableRel G.Adj] (e : EdgeV G) :
    Finset (Finset (EdgeV G)) :=
  (triangleHypergraphSub G).filter (fun T => e ∈ T)

/-- **A fractional triangle decomposition** of `G`: nonnegative weights on the triangles of `G`
under which every edge of `G` carries total weight exactly `1`. -/
def IsFracTriangleDecomp (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset (EdgeV G) → ℝ) : Prop :=
  (∀ T ∈ triangleHypergraphSub G, 0 ≤ w T) ∧
    ∀ e : EdgeV G, ∑ T ∈ trianglesThrough G e, w T = 1

/-- `G` **has** a fractional triangle decomposition. -/
def HasFracTriangleDecomp (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ w : Finset (EdgeV G) → ℝ, IsFracTriangleDecomp G w

/-- **The definition has content**: if `G` carries a fractional triangle decomposition then every
edge of `G` lies in a triangle. -/
theorem exists_triangle_of_fracDecomp (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : HasFracTriangleDecomp G) (e : EdgeV G) :
    ∃ T ∈ triangleHypergraphSub G, e ∈ T := by
  obtain ⟨w, -, hsum⟩ := h
  by_contra hcon
  push_neg at hcon
  have hempty : trianglesThrough G e = ∅ := by
    rw [trianglesThrough, Finset.filter_eq_empty_iff]
    exact fun T hT => hcon T hT
  have := hsum e
  rw [hempty, Finset.sum_empty] at this
  exact absurd this (by norm_num)

/-! ### The triangles through an edge -/

/-- The triangles of `G` through the edge `e`, transported to vertex sets: the `3`-cliques
containing the two endpoints of `e`. -/
theorem card_trianglesThrough_eq (G : SimpleGraph V) [DecidableRel G.Adj] (e : EdgeV G) :
    (trianglesThrough G e).card
      = ((G.cliqueFinset 3).filter (fun t => e.val ⊆ t)).card := by
  classical
  have hecard : (e.val).card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp e.property).card_eq
  refine (Finset.card_bij'
    (fun t _ => (t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2))
    (fun T _ => triOf G T) ?_ ?_ ?_ ?_).symm
  · intro t ht
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
    rw [trianglesThrough, Finset.mem_filter]
    refine ⟨(mem_triangleHypergraphSub_iff G).mpr ⟨t, ht.1, rfl⟩, ?_⟩
    rw [Finset.mem_subtype, Finset.mem_powersetCard]
    exact ⟨ht.2, hecard⟩
  · intro T hT
    rw [trianglesThrough, Finset.mem_filter] at hT
    obtain ⟨t, ht, rfl⟩ := (mem_triangleHypergraphSub_iff G).mp hT.1
    show triOf G _ ∈ _
    rw [triOf_subtype G ht, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff]
    refine ⟨ht, ?_⟩
    have := hT.2
    rw [Finset.mem_subtype, Finset.mem_powersetCard] at this
    exact this.1
  · intro t ht
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
    exact triOf_subtype G ht.1
  · intro T hT
    rw [trianglesThrough, Finset.mem_filter] at hT
    obtain ⟨t, ht, rfl⟩ := (mem_triangleHypergraphSub_iff G).mp hT.1
    show ((triOf G _).powersetCard 2).subtype (· ∈ G.cliqueFinset 2) = _
    rw [triOf_subtype G ht]

/-! ### Non-vacuity: the complete graph -/

/-- **Every edge of the complete graph lies in exactly `|V| - 2` triangles.** -/
theorem card_triangles_through_edge_top (e : EdgeV (⊤ : SimpleGraph V)) :
    (trianglesThrough (⊤ : SimpleGraph V) e).card = Fintype.card V - 2 := by
  classical
  have hecard : (e.val).card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp e.property).card_eq
  rw [card_trianglesThrough_eq]
  have hset : ((⊤ : SimpleGraph V).cliqueFinset 3).filter (fun t => e.val ⊆ t)
      = (Finset.univ \ e.val).image (fun z => insert z e.val) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_sdiff, Finset.mem_univ, true_and,
      SimpleGraph.mem_cliqueFinset_iff]
    constructor
    · rintro ⟨ht, hsub⟩
      have hcard : (t \ e.val).card = 1 := by
        rw [Finset.card_sdiff_of_subset hsub, ht.card_eq, hecard]
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
      have hzt : z ∈ t \ e.val := by rw [hz]; exact Finset.mem_singleton_self z
      rw [Finset.mem_sdiff] at hzt
      refine ⟨z, hzt.2, ?_⟩
      have hsubset : insert z e.val ⊆ t := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hzt.1
        · exact hsub hx
      have hcard3 : t.card ≤ (insert z e.val).card := by
        rw [ht.card_eq, Finset.card_insert_of_notMem hzt.2, hecard]
      exact Finset.eq_of_subset_of_card_le hsubset hcard3
    · rintro ⟨z, hz, rfl⟩
      have hcard : (insert z e.val).card = 3 := by
        rw [Finset.card_insert_of_notMem hz, hecard]
      exact ⟨⟨fun a _ b _ hab => hab, hcard⟩, Finset.subset_insert _ _⟩
  have hinj : Set.InjOn (fun z => insert z e.val) (Finset.univ \ e.val : Finset V) := by
    intro z hz z' hz' heq
    rw [Finset.mem_coe, Finset.mem_sdiff] at hz hz'
    have hmem : z ∈ insert z' e.val := by
      have : z ∈ insert z e.val := Finset.mem_insert_self z _
      simpa [heq] using this
    rcases Finset.mem_insert.mp hmem with h | h
    · exact h
    · exact absurd h hz.2
  rw [hset, Finset.card_image_of_injOn hinj, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, hecard]

/-- **The complete graph carries a fractional triangle decomposition**: the uniform weight
`1/(|V| - 2)`.  In particular `Nibble.IsFracTriangleDecomp` is satisfiable, and satisfied by exactly
the graphs one expects. -/
theorem isFracTriangleDecomp_top (hV : 3 ≤ Fintype.card V) :
    IsFracTriangleDecomp (⊤ : SimpleGraph V)
      (fun _ => 1 / ((Fintype.card V : ℝ) - 2)) := by
  have h2 : (0 : ℝ) < (Fintype.card V : ℝ) - 2 := by
    have : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV
    linarith
  refine ⟨fun T _ => by positivity, fun e => ?_⟩
  rw [Finset.sum_const, card_triangles_through_edge_top e, nsmul_eq_mul]
  have hcast : ((Fintype.card V - 2 : ℕ) : ℝ) = (Fintype.card V : ℝ) - 2 := by
    have : (2 : ℕ) ≤ Fintype.card V := by omega
    push_cast [this]
    ring
  rw [hcast]
  field_simp

/-- **The complete graph has a fractional triangle decomposition.** -/
theorem hasFracTriangleDecomp_top (hV : 3 ≤ Fintype.card V) :
    HasFracTriangleDecomp (⊤ : SimpleGraph V) :=
  ⟨_, isFracTriangleDecomp_top hV⟩

/-! ### The two missing global statements -/

/-- **Dross's theorem** (SIAM J. Discrete Math. **30** (2016), Thm 5), at the density used
throughout this library: every graph with `9|V| ≤ 10 δ(G)` admits a fractional triangle
decomposition.  Not proved here: this is the global input. -/
def DrossFractional : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    9 * Fintype.card V ≤ 10 * G.minDegree → HasFracTriangleDecomp G

/-- **The rounding step** (Frankl–Rödl / Haxell–Rödl nibble): a graph carrying a fractional triangle
decomposition has, once `|V|` is large, an integral triangle packing whose uncovered incidence count
is at most `ε|V|²`.  Not proved here: this is the second global input. -/
def FracRoundingToPacking : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → HasFracTriangleDecomp G →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        (uncoveredTot G M : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-! ### The machine-checked chain to the target -/

/-- **Dross + rounding give the `o(|V|²)` residual.** -/
theorem denseGlobalSmallLeftover_of_dross_of_rounding (hdross : DrossFractional)
    (hround : FracRoundingToPacking) : DenseGlobalSmallLeftover := by
  intro ε hε
  obtain ⟨n₀, hmain⟩ := hround ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV hdense
  exact hmain G hV (hdross G hdense)

/-- **Dross + rounding cross the `1/5` wall.**  This is the target
`∃ c < 1/5, DenseGlobalLeftoverConst c`. -/
theorem leftoverConst_below_fifth_of_dross_of_rounding (hdross : DrossFractional)
    (hround : FracRoundingToPacking) :
    ∃ c : ℝ, c < 1 / 5 ∧ DenseGlobalLeftoverConst c := by
  refine ⟨1 / 10, by norm_num, ?_⟩
  exact denseGlobalLeftoverConst_of_smallLeftover
    (denseGlobalSmallLeftover_of_dross_of_rounding hdross hround) (by norm_num)

/-- **Dross + rounding beat the unconditional `1/2` wall** for the per-vertex uncovered star. -/
theorem beats_half_of_dross_of_rounding (hdross : DrossFractional)
    (hround : FracRoundingToPacking) :
    ∃ β : ℝ, β < 1 / 2 ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
        ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
          ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) := by
  refine beats_half_of_leftoverConst (by norm_num : (0:ℝ) ≤ 1 / 10) (by norm_num) ?_
  exact denseGlobalLeftoverConst_of_smallLeftover
    (denseGlobalSmallLeftover_of_dross_of_rounding hdross hround) (by norm_num)

/-- **Dross + rounding give the full `1/10` per-vertex bound**, i.e. the residual
`Nibble.DenseTriangleNibbleDeg` for every `β > 1/10`. -/
theorem denseTriangleNibbleDeg_of_dross_of_rounding (hdross : DrossFractional)
    (hround : FracRoundingToPacking) {β : ℝ} (hβ : 1 / 10 < β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) :=
  denseTriangleNibbleDeg_of_tenth_lt_of_const
    (denseGlobalSmallLeftover_of_dross_of_rounding hdross hround) hβ

end Nibble
