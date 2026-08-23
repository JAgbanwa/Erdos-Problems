/-
# Nibble — the combinatorial inputs to the refined Dross cut condition

`Nibble/DrossCutArith.lean` reduces the cut condition of a Dross transfer certificate at the
balanced base weight to the master inequality `Nibble.cut_master`.  This file supplies its six
combinatorial inputs for a graph at the Dross density `9|V| ≤ 10 δ(G)`:

* `Nibble.missFinset` — the non-neighbours of a vertex, and `Nibble.outsideOf` — the vertices
  outside the closed common neighbourhood of an edge (the *codegree defect* `σ(e)`);
* `Nibble.edgesMeeting`, `Nibble.edgesInside` and the double-counting identity
  `Nibble.card_edgesMeeting_add_card_edgesInside`;
* the two resulting estimates `Nibble.card_edgesMeeting_ge` and `Nibble.card_edgesMeeting_le`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DrossFlowDense
import Nibble.DrossCutArith

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Non-neighbourhoods -/

/-- The non-neighbours of `v`, excluding `v` itself. -/
def missFinset (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  Finset.univ \ insert v (G.neighborFinset v)

theorem mem_missFinset (G : SimpleGraph V) [DecidableRel G.Adj] {v x : V} :
    x ∈ missFinset G v ↔ x ≠ v ∧ ¬ G.Adj v x := by
  simp [missFinset]

/-- `|M(v)| + 1 + d(v) = |V|`. -/
theorem card_missFinset (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (missFinset G v).card + 1 + G.degree v = Fintype.card V := by
  classical
  have hv : v ∉ G.neighborFinset v := by simp
  have hcard : (insert v (G.neighborFinset v)).card = 1 + G.degree v := by
    rw [Finset.card_insert_of_notMem hv, SimpleGraph.card_neighborFinset_eq_degree]
    omega
  have hsub : insert v (G.neighborFinset v) ⊆ (Finset.univ : Finset V) := Finset.subset_univ _
  have hkey := Finset.card_sdiff_add_card_eq_card hsub
  rw [Finset.card_univ] at hkey
  rw [missFinset]
  omega

/-! ### The codegree defect -/

/-- The vertices outside the closed common neighbourhood of an edge. -/
def outsideOf (G : SimpleGraph V) [DecidableRel G.Adj] (e : EdgeV G) : Finset V :=
  Finset.univ \ (commonNbrs G e ∪ e.val)

theorem commonNbrs_disjoint_val (G : SimpleGraph V) [DecidableRel G.Adj] (e : EdgeV G) :
    Disjoint (commonNbrs G e) e.val := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hx2
  rw [commonNbrs, Finset.mem_filter] at hx
  exact (hx.2 x hx2).ne rfl

/-- `σ(e) + codeg(e) + 2 = |V|`. -/
theorem card_outsideOf (G : SimpleGraph V) [DecidableRel G.Adj] (e : EdgeV G) :
    (outsideOf G e).card + (commonNbrs G e).card + 2 = Fintype.card V := by
  classical
  have hval : e.val.card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp e.property).card_eq
  have hun : (commonNbrs G e ∪ e.val).card = (commonNbrs G e).card + 2 := by
    rw [Finset.card_union_of_disjoint (commonNbrs_disjoint_val G e), hval]
  have hsub : commonNbrs G e ∪ e.val ⊆ (Finset.univ : Finset V) := Finset.subset_univ _
  have hkey := Finset.card_sdiff_add_card_eq_card hsub
  rw [Finset.card_univ] at hkey
  rw [outsideOf]
  omega

/-! ### Edges meeting and edges inside a set -/

/-- The edges of `G` with at least one endpoint in `W`. -/
noncomputable def edgesMeeting (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    Finset (EdgeV G) :=
  Finset.univ.filter (fun e => (e.val ∩ W).Nonempty)

/-- The edges of `G` with both endpoints in `W`. -/
noncomputable def edgesInside (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    Finset (EdgeV G) :=
  Finset.univ.filter (fun e => e.val ⊆ W)

/-- **Double counting.**  Every edge with an endpoint in `W` is counted once, and every edge
inside `W` once more. -/
theorem card_edgesMeeting_add_card_edgesInside (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) :
    ((edgesMeeting G W).card : ℝ) + ((edgesInside G W).card : ℝ)
      = ∑ u ∈ W, (G.degree u : ℝ) := by
  classical
  have hmain := sum_edgeV_sum_val G (fun v => if v ∈ W then (1 : ℝ) else 0)
  have hrhs : ∑ v : V, (if v ∈ W then (1 : ℝ) else 0) * (G.degree v : ℝ)
      = ∑ u ∈ W, (G.degree u : ℝ) := by
    simp [ite_mul, Finset.sum_ite_mem]
  have hper : ∀ e : EdgeV G, (∑ x ∈ e.val, if x ∈ W then (1 : ℝ) else 0)
      = (if (e.val ∩ W).Nonempty then (1 : ℝ) else 0) + (if e.val ⊆ W then (1 : ℝ) else 0) := by
    intro e
    obtain ⟨u, v, huv, hadj, hval⟩ := exists_pair_of_edgeV G e
    rw [hval, Finset.sum_insert (by simpa using huv), Finset.sum_singleton]
    by_cases hu : u ∈ W <;> by_cases hv : v ∈ W <;>
      simp [hu, hv, Finset.insert_subset_iff, Finset.Nonempty]
  rw [Finset.sum_congr rfl (fun e (_ : e ∈ Finset.univ) => hper e)] at hmain
  rw [hrhs] at hmain
  rw [← hmain, Finset.sum_add_distrib]
  congr 1
  · rw [edgesMeeting, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
      nsmul_eq_mul, mul_one]
  · rw [edgesInside, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
      nsmul_eq_mul, mul_one]

/-- **Few edges inside a small set.** -/
theorem card_edgesInside_le (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    2 * ((edgesInside G W).card : ℝ) ≤ (W.card : ℝ) * ((W.card : ℝ) - 1) := by
  classical
  have hinj : ∀ e ∈ edgesInside G W, e.val ∈ Finset.powersetCard 2 W := by
    intro e he
    rw [edgesInside, Finset.mem_filter] at he
    exact Finset.mem_powersetCard.mpr
      ⟨he.2, (SimpleGraph.mem_cliqueFinset_iff.mp e.property).card_eq⟩
  have hcard : (edgesInside G W).card ≤ (Finset.powersetCard 2 W).card := by
    refine Finset.card_le_card_of_injOn (fun e => e.val) hinj ?_
    intro a _ b _ hab
    exact Subtype.ext hab
  rw [Finset.card_powersetCard] at hcard
  have h2 : 2 * ((W.card).choose 2) = W.card * (W.card - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self W.card).two_dvd
  have hnat : 2 * (edgesInside G W).card ≤ W.card * (W.card - 1) := by omega
  have hcast : (2 : ℝ) * ((edgesInside G W).card : ℝ) ≤ ((W.card * (W.card - 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rcases Nat.eq_zero_or_pos W.card with h0 | hpos
  · rw [h0] at hcast ⊢
    simpa using hcast
  · have hsub : ((W.card - 1 : ℕ) : ℝ) = (W.card : ℝ) - 1 := by
      have h1 : 1 ≤ W.card := hpos
      push_cast [Nat.cast_sub h1]
      ring
    push_cast [hsub] at hcast
    linarith

/-- **Many edges inside a set**, when the graph is dense: `2 e(W) ≥ ∑_{u ∈ W} (|W| + d(u) - n)`. -/
theorem two_mul_card_edgesInside_ge (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    ∑ u ∈ W, ((W.card : ℝ) + (G.degree u : ℝ) - (Fintype.card V : ℝ))
      ≤ 2 * ((edgesInside G W).card : ℝ) := by
  classical
  have hkey : ∀ u ∈ W, (W.card : ℝ) + (G.degree u : ℝ) - (Fintype.card V : ℝ)
      ≤ ((W.filter (fun w => G.Adj u w)).card : ℝ) := by
    intro u _
    have hun : W.filter (fun w => G.Adj u w) = W ∩ G.neighborFinset u := by
      ext w; simp [Finset.mem_inter]
    have hunion : (W ∪ G.neighborFinset u).card + (W ∩ G.neighborFinset u).card
        = W.card + (G.neighborFinset u).card := Finset.card_union_add_card_inter _ _
    have hle : (W ∪ G.neighborFinset u).card ≤ Fintype.card V := Finset.card_le_univ _
    have hR : ((W ∪ G.neighborFinset u).card : ℝ) + ((W ∩ G.neighborFinset u).card : ℝ)
        = (W.card : ℝ) + ((G.neighborFinset u).card : ℝ) := by exact_mod_cast hunion
    have hleR : ((W ∪ G.neighborFinset u).card : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hle
    have hnb : ((G.neighborFinset u).card : ℝ) = (G.degree u : ℝ) := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
    rw [hun]
    linarith
  have hsum : ∑ u ∈ W, ((W.filter (fun w => G.Adj u w)).card : ℝ)
      = 2 * ((edgesInside G W).card : ℝ) := by
    have := two_mul_card_edges_inside G W
    have hcast : ((∑ u ∈ W, (W.filter (fun w => G.Adj u w)).card : ℕ) : ℝ)
        = ((2 * ((Finset.univ : Finset (EdgeV G)).filter (fun e => e.val ⊆ W)).card : ℕ) : ℝ) :=
      congrArg (fun k : ℕ => (k : ℝ)) this
    push_cast at hcast
    rw [edgesInside]
    exact hcast
  calc ∑ u ∈ W, ((W.card : ℝ) + (G.degree u : ℝ) - (Fintype.card V : ℝ))
      ≤ ∑ u ∈ W, ((W.filter (fun w => G.Adj u w)).card : ℝ) := Finset.sum_le_sum hkey
    _ = 2 * ((edgesInside G W).card : ℝ) := hsum

/-- **Lower bound on the edges meeting `W`.** -/
theorem card_edgesMeeting_ge (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    (∑ u ∈ W, (G.degree u : ℝ)) - (W.card : ℝ) * ((W.card : ℝ) - 1) / 2
      ≤ ((edgesMeeting G W).card : ℝ) := by
  have h1 := card_edgesMeeting_add_card_edgesInside G W
  have h2 := card_edgesInside_le G W
  linarith

/-- **Upper bound on the edges meeting `W`.** -/
theorem card_edgesMeeting_le (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    ((edgesMeeting G W).card : ℝ)
      ≤ (1 / 2) * ∑ u ∈ W, ((G.degree u : ℝ) + (Fintype.card V : ℝ) - (W.card : ℝ)) := by
  have h1 := card_edgesMeeting_add_card_edgesInside G W
  have h2 := two_mul_card_edgesInside_ge G W
  have h3 : ∑ u ∈ W, ((W.card : ℝ) + (G.degree u : ℝ) - (Fintype.card V : ℝ))
      = (∑ u ∈ W, (G.degree u : ℝ))
        - ∑ u ∈ W, ((G.degree u : ℝ) + (Fintype.card V : ℝ) - (W.card : ℝ))
        + (∑ u ∈ W, (G.degree u : ℝ)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u _ => by ring)
  linarith

/-! ### The codegree defect at the Dross density -/

/-- Every vertex has few non-neighbours at the Dross density. -/
theorem card_missFinset_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) (w : V) :
    ((missFinset G w).card : ℝ) ≤ (Fintype.card V : ℝ) / 10 - 1 := by
  have h1 := card_missFinset G w
  have h2 : G.minDegree ≤ G.degree w := G.minDegree_le_degree w
  have h3 : (9 : ℝ) * (Fintype.card V : ℝ) ≤ 10 * (G.minDegree : ℝ) := by exact_mod_cast hdense
  have h4 : (G.minDegree : ℝ) ≤ (G.degree w : ℝ) := by exact_mod_cast h2
  have h5 : ((missFinset G w).card : ℝ) + 1 + (G.degree w : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) h1
  linarith

/-- The total number of non-adjacencies. -/
theorem sum_card_missFinset (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ w : V, ((missFinset G w).card : ℝ)
      = (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)
        - 2 * (Fintype.card (EdgeV G) : ℝ) := by
  have hper : ∀ w : V, ((missFinset G w).card : ℝ)
      = (Fintype.card V : ℝ) - 1 - (G.degree w : ℝ) := by
    intro w
    have h5 : ((missFinset G w).card : ℝ) + 1 + (G.degree w : ℝ) = (Fintype.card V : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (card_missFinset G w)
    linarith
  rw [Finset.sum_congr rfl (fun w (_ : w ∈ Finset.univ) => hper w)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← two_mul_card_edgeV G]

/-- Edges meeting the non-neighbourhood of `w` put `w` outside their closed common
neighbourhood. -/
theorem edgesMeeting_missFinset_subset (G : SimpleGraph V) [DecidableRel G.Adj] (w : V) :
    edgesMeeting G (missFinset G w)
      ⊆ Finset.univ.filter (fun e : EdgeV G => w ∈ outsideOf G e) := by
  classical
  intro e he
  rw [edgesMeeting, Finset.mem_filter] at he
  obtain ⟨x, hx⟩ := he.2
  rw [Finset.mem_inter] at hx
  obtain ⟨hxe, hxm⟩ := hx
  rw [mem_missFinset] at hxm
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rw [outsideOf, Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hmem
  rcases Finset.mem_union.mp hmem with hc | hv
  · rw [commonNbrs, Finset.mem_filter] at hc
    exact hxm.2 (hc.2 x hxe).symm
  · -- `w ∈ e.val` and `x ∈ e.val` with `x ≠ w` forces `G.Adj w x`
    obtain ⟨a, b, hab, hadj, hval⟩ := exists_pair_of_edgeV G e
    rw [hval] at hv hxe
    rcases Finset.mem_insert.mp hv with rfl | hv'
    · rcases Finset.mem_insert.mp hxe with rfl | hx'
      · exact hxm.1 rfl
      · rw [Finset.mem_singleton] at hx'; subst hx'; exact hxm.2 hadj
    · rw [Finset.mem_singleton] at hv'; subst hv'
      rcases Finset.mem_insert.mp hxe with rfl | hx'
      · exact hxm.2 hadj.symm
      · rw [Finset.mem_singleton] at hx'; exact hxm.1 hx'

/-- **The total codegree defect is large.**  This is the key global input to the refined cut
condition. -/
theorem sum_card_outsideOf_ge (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 20 ≤ Fintype.card V) (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) :
    (17 * (Fintype.card V : ℝ) / 20)
        * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)
          - 2 * (Fintype.card (EdgeV G) : ℝ))
      ≤ ∑ e : EdgeV G, ((outsideOf G e).card : ℝ) := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hnd
  have hn20 : (20 : ℝ) ≤ n := by rw [hnd]; exact_mod_cast hn
  have hdenseR : (9 : ℝ) * n ≤ 10 * (G.minDegree : ℝ) := by rw [hnd]; exact_mod_cast hdense
  -- double counting
  have h1 : ∀ e : EdgeV G, ((outsideOf G e).card : ℝ)
      = ∑ w : V, if w ∈ outsideOf G e then (1 : ℝ) else 0 := by
    intro e
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2 : ∀ w : V, ((Finset.univ.filter (fun e : EdgeV G => w ∈ outsideOf G e)).card : ℝ)
      = ∑ e : EdgeV G, if w ∈ outsideOf G e then (1 : ℝ) else 0 := by
    intro w
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]
  have hdc : ∑ e : EdgeV G, ((outsideOf G e).card : ℝ)
      = ∑ w : V, ((Finset.univ.filter (fun e : EdgeV G => w ∈ outsideOf G e)).card : ℝ) := by
    rw [Finset.sum_congr rfl (fun e (_ : e ∈ Finset.univ) => h1 e),
      Finset.sum_congr rfl (fun w (_ : w ∈ Finset.univ) => h2 w), Finset.sum_comm]
  -- the pointwise bound
  have hpt : ∀ w : V, (17 * n / 20) * ((missFinset G w).card : ℝ)
      ≤ ((Finset.univ.filter (fun e : EdgeV G => w ∈ outsideOf G e)).card : ℝ) := by
    intro w
    have hsub : ((edgesMeeting G (missFinset G w)).card : ℝ)
        ≤ ((Finset.univ.filter (fun e : EdgeV G => w ∈ outsideOf G e)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (edgesMeeting_missFinset_subset G w)
    have hmeet := card_edgesMeeting_ge G (missFinset G w)
    have hdeg : ((missFinset G w).card : ℝ) * ((9 : ℝ) * n / 10)
        ≤ ∑ u ∈ missFinset G w, (G.degree u : ℝ) := by
      calc ((missFinset G w).card : ℝ) * ((9 : ℝ) * n / 10)
          = ∑ _u ∈ missFinset G w, ((9 : ℝ) * n / 10) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := by
            refine Finset.sum_le_sum (fun u _ => ?_)
            have : (G.minDegree : ℝ) ≤ (G.degree u : ℝ) := by
              exact_mod_cast G.minDegree_le_degree u
            linarith
    have hsmall := card_missFinset_le G hdense w
    have hs0 : (0 : ℝ) ≤ ((missFinset G w).card : ℝ) := Nat.cast_nonneg _
    nlinarith only [hmeet, hsub, hdeg, hsmall, hs0]
  calc (17 * n / 20)
        * (n * (n - 1) - 2 * (Fintype.card (EdgeV G) : ℝ))
      = (17 * n / 20) * ∑ w : V, ((missFinset G w).card : ℝ) := by
        rw [sum_card_missFinset G]
    _ = ∑ w : V, (17 * n / 20) * ((missFinset G w).card : ℝ) := by rw [Finset.mul_sum]
    _ ≤ ∑ w : V, ((Finset.univ.filter (fun e : EdgeV G => w ∈ outsideOf G e)).card : ℝ) :=
        Finset.sum_le_sum (fun w _ => hpt w)
    _ = _ := hdc.symm

end Nibble
