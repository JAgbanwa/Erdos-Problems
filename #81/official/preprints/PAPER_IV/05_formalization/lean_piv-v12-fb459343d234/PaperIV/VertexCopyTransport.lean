import PaperIV.VertexCopyItems

/-!
# Transporting mixed `K₃/K₄` fractional packings across one fine vertex copy

Fix `u ≠ v` nonadjacent in `G` and let `H = VertexCopy.graph G u v` be the copy
of `v` onto `u`.  Given a fractional mixed packing `x` of `H`, we *pull it
back* to `G` by the explicit weight

```
transportWeight G u v x L =
  if u ∈ L then 0 else x.weight L + (if v ∈ L then x.weight (copyShift u v L) else 0)
```

i.e. every `H`-item through `u` is re-attached at `v`.  This is a genuine
transport of the LP data, not a restatement:

* `transport_value` : the pulled-back weight has *exactly* the same objective
  value as `x`;
* `transport_load_eq_zero_of_mem`, `transport_load_le_one`,
  `transport_load_le_two` : the exact edge loads of the pulled-back weight —
  zero on edges at `u`, at most one away from `v`, at most two at `v`.

Consequently the *average* of the two transports, one for each orientation of
the copy, is a literal feasible fractional packing of `G`
(`PaperIV.VertexCopyMonotone`).
-/

namespace PaperIV.VertexCopyTransport

open Finset
open PaperIV.FarRounding
open PaperIV.VertexCopyItems

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The load of a weight vector on one edge. -/
def loadAt (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ) (e : Sym2 V) : ℝ :=
  ∑ K ∈ items G, if e ∈ pairs K then w K else 0

theorem loadAt_eq_sum_filter (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℝ) (e : Sym2 V) :
    loadAt G w e = ∑ K ∈ (items G).filter (fun K => e ∈ pairs K), w K := by
  rw [loadAt, Finset.sum_filter]

theorem loadAt_le_one {G : SimpleGraph V} [DecidableRel G.Adj] (x : FracPacking G ℝ)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) : loadAt G x.weight e ≤ 1 :=
  x.capacity e he

variable (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)

/-- The pulled-back weight of a fractional packing of the copied graph. -/
noncomputable def transportWeight (x : FracPacking (VertexCopy.graph G u v) ℝ) :
    Finset V → ℝ := fun L =>
  if u ∈ L then 0
  else x.weight L + (if v ∈ L then x.weight (copyShift u v L) else 0)

variable {G u v}

theorem transportWeight_nonneg (x : FracPacking (VertexCopy.graph G u v) ℝ) (L : Finset V) :
    0 ≤ transportWeight G u v x L := by
  unfold transportWeight
  split_ifs with h1 h2
  · exact le_rfl
  · exact add_nonneg (x.weight_nonneg L) (x.weight_nonneg _)
  · simpa using x.weight_nonneg L

theorem transportWeight_of_mem {x : FracPacking (VertexCopy.graph G u v) ℝ} {L : Finset V}
    (h : u ∈ L) : transportWeight G u v x L = 0 := by
  simp [transportWeight, h]

theorem transportWeight_of_not_mem {x : FracPacking (VertexCopy.graph G u v) ℝ} {L : Finset V}
    (h : u ∉ L) :
    transportWeight G u v x L =
      x.weight L + (if v ∈ L then x.weight (copyShift u v L) else 0) := by
  simp [transportWeight, h]

/-! ### The two index sets -/

/-- Items of `G` avoiding the copy target are exactly the items of the copied
graph avoiding it. -/
theorem filter_items_not_mem :
    (items G).filter (fun L => u ∉ L)
      = (items (VertexCopy.graph G u v)).filter (fun L => u ∉ L) := by
  ext L
  simp only [Finset.mem_filter, mem_items]
  constructor
  · rintro ⟨hL, hu⟩
    exact ⟨(isItem_copy_iff_of_not_mem G hu).mpr hL, hu⟩
  · rintro ⟨hL, hu⟩
    exact ⟨(isItem_copy_iff_of_not_mem G hu).mp hL, hu⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- `copyShift` is injective where it is used. -/
theorem copyShift_injOn {s : Finset (Finset V)}
    (hs : ∀ L ∈ s, u ∉ L ∧ v ∈ L) :
    Set.InjOn (copyShift u v) s := by
  intro L hL M hM h
  have hL' := hs L hL
  have hM' := hs M hM
  calc L = copyShift v u (copyShift u v L) := (copyShift_copyShift hL'.1 hL'.2).symm
    _ = copyShift v u (copyShift u v M) := by rw [h]
    _ = M := copyShift_copyShift hM'.1 hM'.2

/-- The image of the shifted index set consists of items of the copied graph
through `u`. -/
theorem copyShift_mem_filter (hnadj : ¬ G.Adj u v) {L : Finset V}
    (hL : L ∈ ((items G).filter (fun L => u ∉ L)).filter (fun L => v ∈ L)) :
    copyShift u v L ∈ (items (VertexCopy.graph G u v)).filter (fun K => u ∈ K) := by
  rw [Finset.mem_filter, Finset.mem_filter] at hL
  exact Finset.mem_filter.mpr ⟨copyShift_mem_items G hnadj hL.1.2 hL.2 hL.1.1,
    mem_copyShift_self u v L⟩

theorem copyShift_symm_mem_filter (hne : u ≠ v) (hnadj : ¬ G.Adj u v) {K : Finset V}
    (hK : K ∈ (items (VertexCopy.graph G u v)).filter (fun K => u ∈ K)) :
    copyShift v u K ∈ ((items G).filter (fun L => u ∉ L)).filter (fun L => v ∈ L) := by
  rw [Finset.mem_filter, mem_items] at hK
  have hu : u ∉ copyShift v u K := by
    intro h
    rcases mem_copyShift.mp h with h1 | ⟨h1, -⟩
    · exact hne h1
    · exact h1 rfl
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, hu⟩, mem_copyShift_self v u K⟩
  exact mem_items.mpr (isItem_copyShift_symm G hne hnadj hK.2 hK.1)

/-! ### The objective value is transported exactly -/

/-- The pulled-back weight has exactly the objective value of the original
packing of the copied graph. -/
theorem transport_value (hne : u ≠ v) (hnadj : ¬ G.Adj u v)
    (x : FracPacking (VertexCopy.graph G u v) ℝ) :
    ∑ L ∈ items G, gainF ℝ L * transportWeight G u v x L = x.value := by
  have h1 : ∑ L ∈ items G, gainF ℝ L * transportWeight G u v x L
      = ∑ L ∈ (items G).filter (fun L => u ∉ L),
          gainF ℝ L * transportWeight G u v x L := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro L hL hnot
    have hu : u ∈ L := by
      by_contra hu
      exact hnot (Finset.mem_filter.mpr ⟨hL, hu⟩)
    simp [transportWeight_of_mem hu]
  have h2 : ∀ L ∈ (items G).filter (fun L => u ∉ L),
      gainF ℝ L * transportWeight G u v x L
        = gainF ℝ L * x.weight L
          + (if v ∈ L then gainF ℝ L * x.weight (copyShift u v L) else 0) := by
    intro L hL
    rw [transportWeight_of_not_mem (Finset.mem_filter.mp hL).2, mul_add]
    congr 1
    split_ifs <;> simp
  have hA : ∑ L ∈ (items G).filter (fun L => u ∉ L), gainF ℝ L * x.weight L
      = ∑ K ∈ (items (VertexCopy.graph G u v)).filter (fun K => u ∉ K),
          gainF ℝ K * x.weight K := by
    rw [filter_items_not_mem]
  have hB : ∑ L ∈ ((items G).filter (fun L => u ∉ L)).filter (fun L => v ∈ L),
        gainF ℝ L * x.weight (copyShift u v L)
      = ∑ K ∈ (items (VertexCopy.graph G u v)).filter (fun K => u ∈ K),
          gainF ℝ K * x.weight K := by
    refine Finset.sum_nbij' (i := copyShift u v) (j := copyShift v u)
      (fun L hL => copyShift_mem_filter hnadj hL)
      (fun K hK => copyShift_symm_mem_filter hne hnadj hK) ?_ ?_ ?_
    · intro L hL
      rw [Finset.mem_filter, Finset.mem_filter] at hL
      exact copyShift_copyShift hL.1.2 hL.2
    · intro K hK
      rw [Finset.mem_filter, mem_items] at hK
      exact copyShift_copyShift (not_mem_of_isItem_copy G hne hnadj hK.2 hK.1) hK.2
    · intro L hL
      rw [Finset.mem_filter, Finset.mem_filter] at hL
      have : (copyShift u v L).card = L.card := card_copyShift hL.1.2 hL.2
      unfold gainF
      rw [this]
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib, ← Finset.sum_filter, hA, hB,
    FracPacking.value]
  exact Finset.sum_filter_not_add_sum_filter _ _ _

/-! ### Edges of the copied graph -/

theorem mem_edgeFinset_copy_of_not_mem {e : Sym2 V} (he : e ∈ G.edgeFinset) (hu : u ∉ e) :
    e ∈ (VertexCopy.graph G u v).edgeFinset := by
  induction e using Sym2.ind with
  | _ a b =>
    have ha : a ≠ u := by rintro rfl; exact hu (by simp)
    have hb : b ≠ u := by rintro rfl; exact hu (by simp)
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he ⊢
    exact (VertexCopy.adj_of_ne_left_of_ne_right G ha hb).mpr he

theorem mem_edgeFinset_copy_iff_of_not_mem {e : Sym2 V} (hu : u ∉ e) :
    e ∈ (VertexCopy.graph G u v).edgeFinset ↔ e ∈ G.edgeFinset := by
  induction e using Sym2.ind with
  | _ a b =>
    have ha : a ≠ u := by rintro rfl; exact hu (by simp)
    have hb : b ≠ u := by rintro rfl; exact hu (by simp)
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact VertexCopy.adj_of_ne_left_of_ne_right G ha hb

theorem mem_edgeFinset_copy_of_adj (hnadj : ¬ G.Adj u v) {w : V} (h : G.Adj v w) :
    s(u, w) ∈ (VertexCopy.graph G u v).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact (VertexCopy.adj_copied_iff G hnadj w).mpr h

/-! ### The exact load decomposition -/

theorem loadAt_transport_eq (x : FracPacking (VertexCopy.graph G u v) ℝ) (e : Sym2 V) :
    loadAt G (transportWeight G u v x) e
      = (∑ L ∈ ((items G).filter (fun L => e ∈ pairs L)).filter (fun L => u ∉ L), x.weight L)
        + ∑ L ∈ (((items G).filter (fun L => e ∈ pairs L)).filter (fun L => u ∉ L)).filter
            (fun L => v ∈ L), x.weight (copyShift u v L) := by
  rw [loadAt_eq_sum_filter,
    ← Finset.sum_filter_add_sum_filter_not ((items G).filter (fun L => e ∈ pairs L))
      (fun L => u ∉ L)]
  have hzero : ∑ L ∈ ((items G).filter (fun L => e ∈ pairs L)).filter (fun L => ¬ (u ∉ L)),
      transportWeight G u v x L = 0 := by
    refine Finset.sum_eq_zero fun L hL => ?_
    have hmem : u ∈ L := by simpa using (Finset.mem_filter.mp hL).2
    exact transportWeight_of_mem hmem
  rw [hzero, add_zero,
    Finset.sum_congr rfl (fun L hL => transportWeight_of_not_mem (Finset.mem_filter.mp hL).2),
    Finset.sum_add_distrib, ← Finset.sum_filter]

/-- Transported weight puts no load at all on the edges at `u`. -/
theorem loadAt_transport_eq_zero (x : FracPacking (VertexCopy.graph G u v) ℝ) {e : Sym2 V}
    (hu : u ∈ e) : loadAt G (transportWeight G u v x) e = 0 := by
  refine Finset.sum_eq_zero fun L _ => ?_
  split_ifs with h
  · exact transportWeight_of_mem ((mem_pairs.mp h).1 u hu)
  · rfl

/-! ### Load bounds -/

private theorem part1_subset (e : Sym2 V) :
    ((items G).filter (fun L => e ∈ pairs L)).filter (fun L => u ∉ L)
      ⊆ (items (VertexCopy.graph G u v)).filter (fun K => e ∈ pairs K) := by
  intro L hL
  rw [Finset.mem_filter, Finset.mem_filter, mem_items] at hL
  exact Finset.mem_filter.mpr ⟨mem_items.mpr ((isItem_copy_iff_of_not_mem G hL.2).mpr hL.1.1),
    hL.1.2⟩

private theorem part2_subset (hnadj : ¬ G.Adj u v) (e f : Sym2 V)
    (hf : ∀ L ∈ (((items G).filter (fun L => e ∈ pairs L)).filter (fun L => u ∉ L)).filter
        (fun L => v ∈ L), f ∈ pairs (copyShift u v L)) :
    ((((items G).filter (fun L => e ∈ pairs L)).filter (fun L => u ∉ L)).filter
        (fun L => v ∈ L)).image (copyShift u v)
      ⊆ (items (VertexCopy.graph G u v)).filter (fun K => f ∈ pairs K) := by
  intro K hK
  obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, mem_items] at hL
  exact Finset.mem_filter.mpr ⟨mem_items.mpr (isItem_copyShift G hnadj hL.1.2 hL.2 hL.1.1.1),
    hf L (by
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, mem_items]
      exact hL)⟩

private theorem part2_sum_eq (x : FracPacking (VertexCopy.graph G u v) ℝ) (e : Sym2 V) :
    ∑ L ∈ (((items G).filter (fun L => e ∈ pairs L)).filter (fun L => u ∉ L)).filter
        (fun L => v ∈ L), x.weight (copyShift u v L)
      = ∑ K ∈ ((((items G).filter (fun L => e ∈ pairs L)).filter (fun L => u ∉ L)).filter
          (fun L => v ∈ L)).image (copyShift u v), x.weight K := by
  refine (Finset.sum_image ?_).symm
  intro L hL M hM h
  refine copyShift_injOn (s := (((items G).filter (fun L => e ∈ pairs L)).filter
    (fun L => u ∉ L)).filter (fun L => v ∈ L)) ?_ hL hM h
  intro N hN
  rw [Finset.mem_filter, Finset.mem_filter] at hN
  exact ⟨hN.1.2, hN.2⟩

/-- Away from `v`, the transported load is still at most the unit capacity. -/
theorem loadAt_transport_le_one (hnadj : ¬ G.Adj u v)
    (x : FracPacking (VertexCopy.graph G u v) ℝ) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) (hu : u ∉ e) (hv : v ∉ e) :
    loadAt G (transportWeight G u v x) e ≤ 1 := by
  have hfe : ∀ L ∈ (((items G).filter (fun L => e ∈ pairs L)).filter (fun L => u ∉ L)).filter
      (fun L => v ∈ L), e ∈ pairs (copyShift u v L) := by
    intro L hL
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter] at hL
    have hmem := mem_pairs.mp hL.1.1.2
    refine mem_pairs.mpr ⟨fun a ha => ?_, hmem.2⟩
    refine mem_copyShift.mpr (Or.inr ⟨?_, hmem.1 a ha⟩)
    rintro rfl
    exact hv ha
  have hsub1 := part1_subset (G := G) (u := u) (v := v) e
  have hsub2 := part2_subset (G := G) (u := u) (v := v) hnadj e e hfe
  have hdisj : Disjoint (((items G).filter (fun L => e ∈ pairs L)).filter (fun L => u ∉ L))
      (((((items G).filter (fun L => e ∈ pairs L)).filter (fun L => u ∉ L)).filter
        (fun L => v ∈ L)).image (copyShift u v)) := by
    rw [Finset.disjoint_right]
    intro K hK hK'
    obtain ⟨L, -, rfl⟩ := Finset.mem_image.mp hK
    exact (Finset.mem_filter.mp hK').2 (mem_copyShift_self u v L)
  have hunion : (((items G).filter (fun L => e ∈ pairs L)).filter (fun L => u ∉ L))
      ∪ ((((items G).filter (fun L => e ∈ pairs L)).filter (fun L => u ∉ L)).filter
          (fun L => v ∈ L)).image (copyShift u v)
      ⊆ (items (VertexCopy.graph G u v)).filter (fun K => e ∈ pairs K) :=
    Finset.union_subset hsub1 hsub2
  rw [loadAt_transport_eq, part2_sum_eq, ← Finset.sum_union hdisj]
  calc ∑ K ∈ _, x.weight K
      ≤ ∑ K ∈ (items (VertexCopy.graph G u v)).filter (fun K => e ∈ pairs K), x.weight K :=
        Finset.sum_le_sum_of_subset_of_nonneg hunion (fun K _ _ => x.weight_nonneg K)
    _ = loadAt (VertexCopy.graph G u v) x.weight e := (loadAt_eq_sum_filter _ _ _).symm
    _ ≤ 1 := loadAt_le_one x (mem_edgeFinset_copy_of_not_mem he hu)

/-- At `v` the transported load can double, but never exceeds two. -/
theorem loadAt_transport_le_two (hnadj : ¬ G.Adj u v)
    (x : FracPacking (VertexCopy.graph G u v) ℝ) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) :
    loadAt G (transportWeight G u v x) e ≤ 2 := by
  by_cases hu : u ∈ e
  · rw [loadAt_transport_eq_zero x hu]; norm_num
  by_cases hv : v ∈ e
  · obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hv
    have hadj : G.Adj v w := by
      rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    have hwu : w ≠ u := by rintro rfl; exact hu (by simp)
    have hwv : w ≠ v := hadj.ne'
    have hfe : ∀ L ∈ (((items G).filter (fun L => s(v, w) ∈ pairs L)).filter
        (fun L => u ∉ L)).filter (fun L => v ∈ L), s(u, w) ∈ pairs (copyShift u v L) := by
      intro L hL
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter] at hL
      have hmem := mk_mem_pairs.mp hL.1.1.2
      refine mk_mem_pairs.mpr ⟨mem_copyShift_self u v L, ?_, Ne.symm hwu⟩
      exact mem_copyShift.mpr (Or.inr ⟨hwv, hmem.2.1⟩)
    have h1 : ∑ L ∈ ((items G).filter (fun L => s(v, w) ∈ pairs L)).filter (fun L => u ∉ L),
        x.weight L ≤ 1 := by
      calc ∑ L ∈ _, x.weight L
          ≤ ∑ K ∈ (items (VertexCopy.graph G u v)).filter (fun K => s(v, w) ∈ pairs K),
              x.weight K :=
            Finset.sum_le_sum_of_subset_of_nonneg (part1_subset _) (fun K _ _ => x.weight_nonneg K)
        _ = loadAt (VertexCopy.graph G u v) x.weight s(v, w) := (loadAt_eq_sum_filter _ _ _).symm
        _ ≤ 1 := loadAt_le_one x (mem_edgeFinset_copy_of_not_mem he hu)
    have h2 : ∑ L ∈ (((items G).filter (fun L => s(v, w) ∈ pairs L)).filter
        (fun L => u ∉ L)).filter (fun L => v ∈ L), x.weight (copyShift u v L) ≤ 1 := by
      rw [part2_sum_eq]
      calc ∑ K ∈ _, x.weight K
          ≤ ∑ K ∈ (items (VertexCopy.graph G u v)).filter (fun K => s(u, w) ∈ pairs K),
              x.weight K :=
            Finset.sum_le_sum_of_subset_of_nonneg (part2_subset hnadj _ _ hfe)
              (fun K _ _ => x.weight_nonneg K)
        _ = loadAt (VertexCopy.graph G u v) x.weight s(u, w) := (loadAt_eq_sum_filter _ _ _).symm
        _ ≤ 1 := loadAt_le_one x (mem_edgeFinset_copy_of_adj hnadj hadj)
    rw [loadAt_transport_eq]
    linarith
  · have := loadAt_transport_le_one hnadj x he hu hv
    linarith

end PaperIV.VertexCopyTransport
