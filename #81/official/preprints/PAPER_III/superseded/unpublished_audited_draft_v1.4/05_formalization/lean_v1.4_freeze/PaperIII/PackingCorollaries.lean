import PaperIII.E_5

/-!
# Paper III — Packing-native corollaries

This module records the packing formulations underlying §5.1 and §5.2.
-/

namespace PaperIII

open SplitGraph Finset

set_option maxHeartbeats 800000

/-- The edges of the color class `c` whose two endpoints lie in the neighborhood of `i`. -/
def factorEdges (G : SplitGraph) (φ : Sym2 (Fin G.p) → ℕ)
    (c : Fin (rp G.p)) (i : Fin G.q) : Finset (Sym2 (Fin G.p)) :=
  (⊤ : SimpleGraph (Fin G.p)).edgeFinset.filter
    fun e => φ e = c.1 ∧ ∀ v ∈ e, v ∈ G.N i

/-- The KKI triangle obtained by adjoining the independent vertex `i` to a clique edge. -/
def factorTriangle (G : SplitGraph) (i : Fin G.q)
    (e : Sym2 (Fin G.p)) : Finset G.V :=
  insert (Sum.inr i) (e.toFinset.image Sum.inl)

/-- The family of KKI triangles arising from an injective assignment of factors to
independent vertices. -/
def factorAssignmentPacking (G : SplitGraph) (φ : Sym2 (Fin G.p) → ℕ)
    (σ : Fin (rp G.p) ↪ Fin G.q) : Finset (Finset G.V) :=
  Finset.univ.biUnion fun c =>
    (factorEdges G φ c (σ c)).image (factorTriangle G (σ c))

/-- A proper factor coloring and an injective assignment of its factors produce a triangle
packing. -/
lemma factorAssignmentPacking_isPacking (G : SplitGraph)
    (φ : Sym2 (Fin G.p) → ℕ)
    (hproper : ∀ e ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset,
      ∀ f ∈ (⊤ : SimpleGraph (Fin G.p)).edgeFinset,
        e ≠ f → (∃ v, v ∈ e ∧ v ∈ f) → φ e ≠ φ f)
    (σ : Fin (rp G.p) ↪ Fin G.q) :
    IsTrianglePacking G.graph (factorAssignmentPacking G φ σ) := by
  constructor
  · unfold factorAssignmentPacking
    simp +decide [*, SimpleGraph.isNClique_iff]
    rintro t c e he rfl
    unfold factorEdges factorTriangle at *
    simp_all +decide [SimpleGraph.isClique_iff, Finset.card_image_of_injective,
      Function.Injective]
    rcases e with ⟨a, b⟩
    simp_all +decide [SimpleGraph.adj_comm]
    simp_all +decide [Sym2.toFinset, Set.Pairwise]
    simp_all +decide [SplitGraph.graph, SplitGraph.Adj]
    simp +decide [Sym2.toMultiset, he.1]
  · intro t₁ ht₁ t₂ ht₂ hne
    obtain ⟨c₁, e₁, hc₁, he₁⟩ :
        ∃ c₁ : Fin (rp G.p), ∃ e₁ : Sym2 (Fin G.p),
          t₁ = factorTriangle G (σ c₁) e₁ ∧ e₁ ∈ factorEdges G φ c₁ (σ c₁) := by
      unfold factorAssignmentPacking at ht₁
      aesop
    obtain ⟨c₂, e₂, hc₂, he₂⟩ :
        ∃ c₂ : Fin (rp G.p), ∃ e₂ : Sym2 (Fin G.p),
          t₂ = factorTriangle G (σ c₂) e₂ ∧ e₂ ∈ factorEdges G φ c₂ (σ c₂) := by
      unfold factorAssignmentPacking at ht₂
      aesop
    by_cases h : c₁ = c₂ <;> simp_all +decide [factorEdges]
    · have h_no_common_vertices : ∀ v : Fin G.p, v ∈ e₁ → v ∈ e₂ → False := by
        grind
      unfold factorTriangle
      simp +decide [Finset.ext_iff]
      exact fun v hv w hw hvw => h_no_common_vertices v hv (hvw ▸ hw)
    · by_cases h' : e₁ = e₂ <;> simp_all +decide [factorTriangle]
      · exact False.elim <| h <| Fin.ext he₁.1.symm
      · contrapose! hproper
        obtain ⟨x, hx⟩ := Finset.one_lt_card.mp hproper
        cases e₁
        cases e₂
        aesop

/-- The number of triangles in a factor-assignment packing is the sum of the assigned
factor-edge counts. -/
lemma card_factorAssignmentPacking (G : SplitGraph)
    (φ : Sym2 (Fin G.p) → ℕ)
    (σ : Fin (rp G.p) ↪ Fin G.q) :
    (factorAssignmentPacking G φ σ).card =
      ∑ c : Fin (rp G.p), (factorEdges G φ c (σ c)).card := by
  convert Finset.card_biUnion _
  · rw [Finset.card_image_of_injOn]
    intro e₁ he₁ e₂ he₂ h_eq
    unfold factorTriangle at h_eq
    simp_all +decide [Finset.ext_iff, Sym2.ext_iff]
  · intro c hc d hd hcd
    simp_all +decide [Finset.disjoint_left, factorTriangle]
    intro a ha x hx H
    replace H := Finset.ext_iff.mp H (Sum.inr (σ d))
    simp_all +decide

/-- **§5.1, packing-native max-over-assignments.** Every injective assignment of the
round-robin factors to independent vertices gives at most `nu3'` KKI triangles. -/
theorem factorization_assignment_packing (G : SplitGraph) :
    ∀ σ : Fin (rp G.p) ↪ Fin G.q,
      (∑ j, (factorEdges G (Classical.choose (complete_graph_edge_coloring G.p))
        j (σ j)).card : ℝ) ≤ G.nu3' := by
  intro σ
  have hpack : IsTrianglePacking G.graph
      (factorAssignmentPacking G
        (Classical.choose (complete_graph_edge_coloring G.p)) σ) :=
    factorAssignmentPacking_isPacking G _
      (Classical.choose_spec (complete_graph_edge_coloring G.p)).2 σ
  have hcard : (factorAssignmentPacking G
      (Classical.choose (complete_graph_edge_coloring G.p)) σ).card ≤ G.nu3' := by
    exact le_csSup
      ⟨Finset.univ.card, fun k hk => by
        obtain ⟨T, hT, rfl⟩ := hk
        exact Finset.card_le_univ T⟩
      ⟨_, hpack, rfl⟩
  rw [card_factorAssignmentPacking] at hcard
  exact_mod_cast hcard

/-- **§5.2, packing-native double factorization.** The ordinary factor contribution plus
the doubled-factor dispersion contribution is bounded by the maximum triangle packing. -/
theorem double_factorization_packing (G : SplitGraph)
    (hrp : rp G.p ≤ G.q) (hq2 : 2 ≤ G.q) :
    (1 / (G.q : ℝ)) * ∑ i, ((G.d i).choose 2 : ℝ)
      + ((G.doubledFactors : ℝ) / (rp G.p : ℝ)) * (G.dispersionV : ℝ)
        / ((G.q : ℝ) * ((G.q : ℝ) - 1)) ≤ (G.nu3' : ℝ) := by
  exact double_factor_nu_bound G hrp hq2

end PaperIII
