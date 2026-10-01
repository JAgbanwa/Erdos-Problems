import PaperIV.VertexCopyTransport
import PaperIV.VertexCopySelector

/-!
# Symmetrization monotonicity of the mixed fractional defect (DV157–RD09)

For a finite graph `G` write

* `optVal G` for the optimum value `W*` of the literal mixed `K₃/K₄` fractional
  packing LP of `PaperIV.FarRounding` (it exists by
  `FarRoundingRealLP.exists_realOptimal`);
* `F4 G = |E(G)| - W*(G)` for the mixed fractional defect.

Let `u ≠ v` be nonadjacent in `G`.  The two *fine copy* orientations are
`VertexCopy.graph G u v` (copy `v` onto `u`) and `VertexCopy.graph G v u`.
The main results are:

* `optVal_copy_add_le` : `W*(G₁) + W*(G₂) ≤ 2 W*(G)`, proved by exhibiting the
  literal feasible packing of `G` obtained by averaging the two transported
  optimal packings (`VertexCopyTransport.transportWeight`);
* `card_edgeFinset_copy_add` : `|E(G₁)| + |E(G₂)| = 2|E(G)|`;
* `two_mul_F4_le_add` : `2 F4(G) ≤ F4(G₁) + F4(G₂)`, hence
  `F4_le_max` : at least one orientation does not decrease the defect.

Combining with chordality preservation for a simplicial source
(`VertexCopy.isChordal_graph_of_isSimplicial`) gives
`exists_chordal_copy_F4_le`, the symmetrization step actually required by the
fine copy path: for a chordal `G` and a nonadjacent simplicial pair, one of
the two one-vertex copies is chordal and has defect at least that of `G`.

Nothing here is assumed: both orientations are literal graphs, and the
inequality is witnessed by an explicit fractional packing.
-/

namespace PaperIV.VertexCopyMonotone

open Finset
open PaperIV.FarRounding
open PaperIV.VertexCopyTransport

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The LP optimum and the defect -/

/-- The optimal value `W*` of the mixed `K₃/K₄` fractional packing LP. -/
noncomputable def optVal (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (Classical.choose (FarRoundingRealLP.exists_realOptimal G)).value

theorem le_optVal {G : SimpleGraph V} [DecidableRel G.Adj] (x : FracPacking G ℝ) :
    x.value ≤ optVal G :=
  Classical.choose_spec (FarRoundingRealLP.exists_realOptimal G) x

theorem exists_fracPacking_value_eq_optVal (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ x : FracPacking G ℝ, x.value = optVal G :=
  ⟨Classical.choose (FarRoundingRealLP.exists_realOptimal G), rfl⟩

/-- The mixed fractional defect `F4 = |E| - W*`. -/
noncomputable def F4 (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (G.edgeFinset.card : ℝ) - optVal G

/-! ### The averaged transported packing -/

variable (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)

/-- The average of the two transported weights, one per copy orientation. -/
noncomputable def symmWeight (x₁ : FracPacking (VertexCopy.graph G u v) ℝ)
    (x₂ : FracPacking (VertexCopy.graph G v u) ℝ) : Finset V → ℝ := fun L =>
  (transportWeight G u v x₁ L + transportWeight G v u x₂ L) / 2

variable {G u v}

theorem loadAt_symmWeight (x₁ : FracPacking (VertexCopy.graph G u v) ℝ)
    (x₂ : FracPacking (VertexCopy.graph G v u) ℝ) (e : Sym2 V) :
    loadAt G (symmWeight G u v x₁ x₂) e
      = (loadAt G (transportWeight G u v x₁) e
          + loadAt G (transportWeight G v u x₂) e) / 2 := by
  unfold loadAt symmWeight
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun K _ => ?_
  split_ifs <;> ring

/-- The two copy orientations never load one edge more than twice in total. -/
theorem loads_add_le_two (hne : u ≠ v) (hnadj : ¬ G.Adj u v)
    (x₁ : FracPacking (VertexCopy.graph G u v) ℝ)
    (x₂ : FracPacking (VertexCopy.graph G v u) ℝ) {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    loadAt G (transportWeight G u v x₁) e + loadAt G (transportWeight G v u x₂) e ≤ 2 := by
  have hnadj' : ¬ G.Adj v u := fun h => hnadj h.symm
  by_cases hu : u ∈ e
  · have hv : v ∉ e := by
      intro hv
      obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hu
      have hadj : G.Adj u w := by
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rcases Sym2.mem_iff.mp hv with h | h
      · exact hne h.symm
      · exact hnadj (h ▸ hadj)
    rw [loadAt_transport_eq_zero x₁ hu]
    have := loadAt_transport_le_two hnadj' x₂ he
    linarith
  · by_cases hv : v ∈ e
    · rw [loadAt_transport_eq_zero x₂ hv]
      have := loadAt_transport_le_two hnadj x₁ he
      linarith
    · have h₁ := loadAt_transport_le_one hnadj x₁ he hu hv
      have h₂ := loadAt_transport_le_one hnadj' x₂ he hv hu
      linarith

/-- The literal averaged fractional packing of `G`. -/
noncomputable def symmPacking (hne : u ≠ v) (hnadj : ¬ G.Adj u v)
    (x₁ : FracPacking (VertexCopy.graph G u v) ℝ)
    (x₂ : FracPacking (VertexCopy.graph G v u) ℝ) : FracPacking G ℝ where
  weight := symmWeight G u v x₁ x₂
  weight_nonneg L := by
    have h₁ := transportWeight_nonneg x₁ L
    have h₂ := transportWeight_nonneg x₂ L
    unfold symmWeight
    linarith
  capacity e he := by
    have h := loads_add_le_two hne hnadj x₁ x₂ he
    have := loadAt_symmWeight x₁ x₂ e
    unfold loadAt at this
    rw [this]
    unfold loadAt at h
    linarith

theorem symmPacking_value (hne : u ≠ v) (hnadj : ¬ G.Adj u v)
    (x₁ : FracPacking (VertexCopy.graph G u v) ℝ)
    (x₂ : FracPacking (VertexCopy.graph G v u) ℝ) :
    (symmPacking hne hnadj x₁ x₂).value = (x₁.value + x₂.value) / 2 := by
  have hnadj' : ¬ G.Adj v u := fun h => hnadj h.symm
  have h₁ := transport_value hne hnadj x₁
  have h₂ := transport_value (Ne.symm hne) hnadj' x₂
  have hsplit : ∑ L ∈ items G, gainF ℝ L * symmWeight G u v x₁ x₂ L
      = (∑ L ∈ items G, gainF ℝ L * transportWeight G u v x₁ L
          + ∑ L ∈ items G, gainF ℝ L * transportWeight G v u x₂ L) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun K _ => ?_
    unfold symmWeight
    ring
  show ∑ L ∈ items G, gainF ℝ L * symmWeight G u v x₁ x₂ L = _
  rw [hsplit, h₁, h₂]

/-! ### The symmetrization inequality for the LP optimum -/

/-- **Concavity of the mixed LP optimum under one fine copy.**  The two copy
orientations of a nonadjacent pair cannot have more total fractional value than
twice the original graph. -/
theorem optVal_copy_add_le (hne : u ≠ v) (hnadj : ¬ G.Adj u v) :
    optVal (VertexCopy.graph G u v) + optVal (VertexCopy.graph G v u) ≤ 2 * optVal G := by
  obtain ⟨x₁, hx₁⟩ := exists_fracPacking_value_eq_optVal (VertexCopy.graph G u v)
  obtain ⟨x₂, hx₂⟩ := exists_fracPacking_value_eq_optVal (VertexCopy.graph G v u)
  have h := le_optVal (symmPacking hne hnadj x₁ x₂)
  rw [symmPacking_value hne hnadj x₁ x₂, hx₁, hx₂] at h
  linarith

/-! ### The edge ledger of the two orientations -/

theorem card_edgeFinset_copy_add_degree (hnadj : ¬ G.Adj u v) :
    (VertexCopy.graph G u v).edgeFinset.card + G.degree u
      = G.edgeFinset.card + G.degree v := by
  have hfilter : (VertexCopy.graph G u v).edgeFinset.filter (fun e => ¬ u ∈ e)
      = G.edgeFinset.filter (fun e => ¬ u ∈ e) := by
    ext e
    simp only [Finset.mem_filter, and_congr_left_iff]
    intro hu
    exact mem_edgeFinset_copy_iff_of_not_mem hu
  have hdeg : (VertexCopy.graph G u v).degree u = G.degree v := by
    unfold SimpleGraph.degree
    rw [VertexCopy.neighborFinset_copied G hnadj]
  have hH := Finset.card_filter_add_card_filter_not
    (s := (VertexCopy.graph G u v).edgeFinset) (fun e => u ∈ e)
  have hG := Finset.card_filter_add_card_filter_not (s := G.edgeFinset) (fun e => u ∈ e)
  have hincH : ((VertexCopy.graph G u v).edgeFinset.filter (fun e => u ∈ e)).card
      = (VertexCopy.graph G u v).degree u := by
    rw [← SimpleGraph.incidenceFinset_eq_filter, SimpleGraph.card_incidenceFinset_eq_degree]
  have hincG : (G.edgeFinset.filter (fun e => u ∈ e)).card = G.degree u := by
    rw [← SimpleGraph.incidenceFinset_eq_filter, SimpleGraph.card_incidenceFinset_eq_degree]
  rw [hincH, hdeg] at hH
  rw [hincG] at hG
  rw [hfilter] at hH
  omega

/-- The copy is edge-balanced: the two orientations average the edge count. -/
theorem card_edgeFinset_copy_add (hnadj : ¬ G.Adj u v) :
    (VertexCopy.graph G u v).edgeFinset.card + (VertexCopy.graph G v u).edgeFinset.card
      = 2 * G.edgeFinset.card := by
  have h₁ := card_edgeFinset_copy_add_degree (G := G) (u := u) (v := v) hnadj
  have h₂ := card_edgeFinset_copy_add_degree (G := G) (u := v) (v := u) (fun h => hnadj h.symm)
  omega

/-! ### Monotonicity of the defect -/

/-- **Symmetrization monotonicity of the mixed fractional defect.**  The two
fine copy orientations of a nonadjacent pair have, on average, at least the
defect of `G`. -/
theorem two_mul_F4_le_add (hne : u ≠ v) (hnadj : ¬ G.Adj u v) :
    2 * F4 G ≤ F4 (VertexCopy.graph G u v) + F4 (VertexCopy.graph G v u) := by
  have hE := card_edgeFinset_copy_add (G := G) (u := u) (v := v) hnadj
  have hEℝ : ((VertexCopy.graph G u v).edgeFinset.card : ℝ)
      + ((VertexCopy.graph G v u).edgeFinset.card : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hE
  have hW := optVal_copy_add_le (G := G) (u := u) (v := v) hne hnadj
  unfold F4
  linarith

/-- At least one of the two fine copy orientations does not decrease the mixed
fractional defect. -/
theorem F4_le_max (hne : u ≠ v) (hnadj : ¬ G.Adj u v) :
    F4 G ≤ F4 (VertexCopy.graph G u v) ∨ F4 G ≤ F4 (VertexCopy.graph G v u) := by
  by_contra h
  push_neg at h
  have := two_mul_F4_le_add hne hnadj
  linarith [h.1, h.2]

/-- **The symmetrization step for the fine copy path.**  For a chordal graph and
a nonadjacent pair of simplicial vertices, both one-vertex copies are chordal,
and at least one of them has mixed fractional defect at least that of `G`. -/
theorem exists_chordal_copy_F4_le (hne : u ≠ v) (hnadj : ¬ G.Adj u v)
    (hG : PaperIV.IsChordal G)
    (hu : PaperIV.ChordalBasics.IsSimplicial G u)
    (hv : PaperIV.ChordalBasics.IsSimplicial G v) :
    ∃ a b : V, ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧ a ≠ b ∧ ¬ G.Adj a b ∧
      PaperIV.IsChordal (VertexCopy.graph G a b) ∧ F4 G ≤ F4 (VertexCopy.graph G a b) := by
  rcases F4_le_max hne hnadj with h | h
  · exact ⟨u, v, Or.inl ⟨rfl, rfl⟩, hne, hnadj,
      VertexCopy.isChordal_graph_of_isSimplicial G hnadj hG hv, h⟩
  · exact ⟨v, u, Or.inr ⟨rfl, rfl⟩, Ne.symm hne, fun hadj => hnadj hadj.symm,
      VertexCopy.isChordal_graph_of_isSimplicial G (fun hadj => hnadj hadj.symm) hG hu, h⟩

end PaperIV.VertexCopyMonotone
