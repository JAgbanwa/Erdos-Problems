import PaperII.VertexCopy

/-!
# Paper II — L1 vertex-copy inequality (ledger L1)

Goal: `Φ_τ(G_{v→u}) + Φ_τ(G_{u→v}) ≥ 2·Φ_τ(G)` for nonadjacent `u,v`.

Structure (following the ledger):
* (a) edge-count identity  `e(G_{v→u}) + e(G_{u→v}) = 2 e(G)`  — this file (via Mathlib's
      `card_edgeFinset_replaceVertex_of_not_adj`);
* (b) cover transport      `τ₃*(G_{v→u}) + τ₃*(G_{u→v}) ≤ 2 τ₃*(G)`  — TODO;
* combine (a),(b) into the `Φ_τ` inequality — TODO.
-/

open scoped BigOperators
open Finset

namespace PaperII

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Degree is at most the number of edges (the incident edges form a subset of all edges). -/
theorem degree_le_edgeFinset_card (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v ≤ G.edgeFinset.card := by
  rw [← G.card_incidenceFinset_eq_degree]
  exact Finset.card_le_card (by simp [SimpleGraph.incidenceFinset, SimpleGraph.incidenceSet_subset])

/-- The off-diagonal `sym2` pairs of a 3-element set `{a,b,c}` are exactly its three edges. -/
theorem sym2_offdiag_triple {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (({a, b, c} : Finset V).sym2.filter (fun e => ¬ e.IsDiag))
      = {s(a, b), s(a, c), s(b, c)} := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, Finset.mem_insert,
      Finset.mem_singleton, Sym2.isDiag_iff_proj_eq, Sym2.eq_iff]
    aesop

/-- Relabeling `v ↦ u` (identity elsewhere), used to transport a cover across the copy. -/
def relabel (v u : V) : V → V := fun w => if w = v then u else w

/-- Transported cover `z' = z ∘ (relabel v u on pairs)`.  On an edge `s(v,x)` (x ≠ v) this is
    `z s(u,x)`; on an edge avoiding `v` it is unchanged. -/
noncomputable def copyCover (v u : V) (z : Sym2 V → ℝ) : Sym2 V → ℝ :=
  fun e => z (Sym2.map (relabel v u) e)

theorem relabel_of_ne {v u w : V} (hw : w ≠ v) : relabel v u w = w := by
  simp [relabel, hw]

@[simp] theorem relabel_self (v u : V) : relabel v u v = u := by simp [relabel]

theorem copyCover_pair (v u : V) (z : Sym2 V → ℝ) (x y : V) :
    copyCover v u z s(x, y) = z s(relabel v u x, relabel v u y) := by
  simp [copyCover, Sym2.map_pair_eq]

/-- Optimality: an optimal cover is `0` on any coordinate that lies in no constraint's support. -/
theorem optimalCover_zero_off_support {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : CoverSystem ι κ) (i : ι)
    (h : ∀ k, i ∉ A.support k) : optimalCover A i = 0 := by
  by_contra hi
  have hpos : 0 < optimalCover A i :=
    lt_of_le_of_ne ((optimalCover_mem A).1 i).1 (Ne.symm hi)
  have hyfeas : Function.update (optimalCover A) i 0 ∈ FeasibleCover A := by
    refine ⟨fun j => ?_, fun k => ?_⟩
    · by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj]; exact (optimalCover_mem A).1 j
    · have hsum : ∑ j ∈ A.support k, Function.update (optimalCover A) i 0 j
                = ∑ j ∈ A.support k, optimalCover A j :=
        Finset.sum_congr rfl fun j hj =>
          Function.update_of_ne (by rintro rfl; exact h k hj) _ _
      rw [hsum]; exact (optimalCover_mem A).2 k
  have key : coverCost (optimalCover A)
           = coverCost (Function.update (optimalCover A) i 0) + optimalCover A i := by
    simp only [coverCost]
    rw [← Finset.add_sum_erase Finset.univ (optimalCover A) (Finset.mem_univ i),
        ← Finset.add_sum_erase Finset.univ (Function.update (optimalCover A) i 0)
            (Finset.mem_univ i),
        Function.update_self,
        Finset.sum_congr rfl (fun j hj =>
          Function.update_of_ne (Finset.ne_of_mem_erase hj) (0 : ℝ) (optimalCover A))]
    ring
  have hle := tauStar_le_cost A hyfeas
  simp only [tauStar] at hle
  linarith [key]

/-- Relabeling fixes any pair avoiding `v`. -/
theorem map_relabel_of_not_mem {v u : V} {e : Sym2 V} (he : v ∉ e) :
    Sym2.map (relabel v u) e = e := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [Sym2.mem_iff, not_or] at he
    rw [Sym2.map_pair_eq, relabel_of_ne (Ne.symm he.1), relabel_of_ne (Ne.symm he.2)]

/-- Reindex a sum over the edges incident to `v` by the other endpoint. -/
theorem sum_incident (v : V) (f : Sym2 V → ℝ) :
    ∑ e ∈ Finset.univ.filter (fun e => v ∈ e), f e = ∑ x, f s(v, x) := by
  have himg : Finset.univ.filter (fun e : Sym2 V => v ∈ e)
            = Finset.univ.image (fun x => s(v, x)) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Sym2.mem_iff, Sym2.eq_iff]
      aesop
  rw [himg, Finset.sum_image]
  intro x _ y _ hxy
  rw [Sym2.eq_iff] at hxy
  rcases hxy with ⟨_, h⟩ | ⟨h1, h2⟩
  · exact h
  · exact h2.trans h1

/-- Pushing a relabel through a full sum: `∑ g(relabel x) = ∑ g − g v + g u`. -/
theorem sum_relabel (v u : V) (g : V → ℝ) :
    ∑ x, g (relabel v u x) = (∑ x, g x) - g v + g u := by
  rw [← Finset.add_sum_erase Finset.univ (fun x => g (relabel v u x)) (Finset.mem_univ v),
      ← Finset.add_sum_erase Finset.univ g (Finset.mem_univ v), relabel_self,
      Finset.sum_congr rfl (fun x hx => by
        rw [relabel_of_ne (Finset.ne_of_mem_erase hx)])]
  ring

/-- Cost of the transported cover (ledger L1, cost bookkeeping). -/
theorem coverCost_copyCover (v u : V) (z : Sym2 V → ℝ) :
    coverCost (copyCover v u z)
      = coverCost z - (∑ x, z s(v, x)) + (∑ x, z s(u, x)) - z s(u, v) + z s(u, u) := by
  have hP2 : ∀ e ∈ Finset.univ.filter (fun e => v ∉ e), copyCover v u z e = z e := by
    intro e he
    simp only [Finset.mem_filter] at he
    rw [copyCover, map_relabel_of_not_mem he.2]
  have hz_split : coverCost z
      = (∑ e ∈ Finset.univ.filter (fun e => v ∈ e), z e)
      + (∑ e ∈ Finset.univ.filter (fun e => v ∉ e), z e) := by
    rw [coverCost]; exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hcc_split : coverCost (copyCover v u z)
      = (∑ e ∈ Finset.univ.filter (fun e => v ∈ e), copyCover v u z e)
      + (∑ e ∈ Finset.univ.filter (fun e => v ∉ e), copyCover v u z e) := by
    rw [coverCost]; exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hP1 : (∑ e ∈ Finset.univ.filter (fun e => v ∈ e), copyCover v u z e)
      = (∑ x, z s(u, x)) - z s(u, v) + z s(u, u) := by
    rw [sum_incident v (copyCover v u z)]
    simp only [copyCover, Sym2.map_pair_eq, relabel_self]
    exact sum_relabel v u (fun y => z s(u, y))
  rw [hcc_split, hP1, Finset.sum_congr rfl hP2, hz_split, sum_incident v z]
  ring

/-- Sum of any `f` over the three edges of the triangle `{a,b,c}`. -/
theorem triangleEdges_sum (G : SimpleGraph V) [DecidableRel G.Adj] {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hT : IsTriangle G {a, b, c})
    (f : Sym2 V → ℝ) :
    ∑ e ∈ triangleEdges G ⟨{a, b, c}, hT⟩, f e = f s(a, b) + f s(a, c) + f s(b, c) := by
  have h1 : s(a, b) ∉ ({s(a, c), s(b, c)} : Finset (Sym2 V)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]; tauto
  have h2 : s(a, c) ∉ ({s(b, c)} : Finset (Sym2 V)) := by
    simp only [Finset.mem_singleton, Sym2.eq_iff]; tauto
  show ∑ e ∈ ({a, b, c} : Finset V).sym2.filter (fun e => ¬ e.IsDiag), f e = _
  rw [sym2_offdiag_triple hab hac hbc, Finset.sum_insert h1, Finset.sum_insert h2,
    Finset.sum_singleton]
  ring

/-- Adjacency in the copy translates to adjacency in `G` after relabeling `v ↦ u`. -/
theorem copyVertex_adj_relabel (G : SimpleGraph V) [DecidableRel G.Adj] {v u a b : V}
    (hab : (copyVertex G v u).Adj a b) :
    G.Adj (relabel v u a) (relabel v u b) := by
  by_cases ha : a = v <;> by_cases hb : b = v
  · exact absurd (ha.trans hb.symm) hab.ne
  · rw [ha] at hab ⊢
    rw [relabel_self, relabel_of_ne hb]
    exact (copyVertex_adj_v G v u b hb).mp hab
  · rw [hb] at hab ⊢
    rw [relabel_of_ne ha, relabel_self]
    exact ((copyVertex_adj_v G v u a ha).mp hab.symm).symm
  · rw [relabel_of_ne ha, relabel_of_ne hb]
    exact (copyVertex_adj_of_ne G v u a b ha hb).mp hab

/-- The transported cover stays in the unit box. -/
theorem copyCover_inUnitBox (v u : V) {z : Sym2 V → ℝ} (hz : InUnitBox z) :
    InUnitBox (copyCover v u z) := fun e => hz (Sym2.map (relabel v u) e)

/-- (b, feasibility) The transported cover satisfies every triangle constraint of the copy. -/
theorem copyCover_satisfiesCover (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    {z : Sym2 V → ℝ} (hz : z ∈ FeasibleCover (triangleCoverSystem G)) :
    SatisfiesCover (triangleCoverSystem (copyVertex G v u)) (copyCover v u z) := by
  rintro ⟨S, hS⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS.card_eq
  obtain ⟨hHab, hHac, hHbc⟩ := SimpleGraph.is3Clique_triple_iff.mp hS
  -- translate to G, with relabeled vertices
  have hGab : G.Adj (relabel v u a) (relabel v u b) := copyVertex_adj_relabel G hHab
  have hGac : G.Adj (relabel v u a) (relabel v u c) := copyVertex_adj_relabel G hHac
  have hGbc : G.Adj (relabel v u b) (relabel v u c) := copyVertex_adj_relabel G hHbc
  have hT' : IsTriangle G {relabel v u a, relabel v u b, relabel v u c} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hGab, hGac, hGbc⟩
  -- the constraint sum, via both triangleEdges expansions
  show 1 ≤ ∑ e ∈ triangleEdges (copyVertex G v u) ⟨{a, b, c}, hS⟩, copyCover v u z e
  rw [triangleEdges_sum (copyVertex G v u) hab hac hbc hS]
  simp only [copyCover_pair]
  have hfeas : 1 ≤ ∑ e ∈ triangleEdges G ⟨{relabel v u a, relabel v u b, relabel v u c}, hT'⟩, z e :=
    hz.2 ⟨{relabel v u a, relabel v u b, relabel v u c}, hT'⟩
  rw [triangleEdges_sum G hGab.ne hGac.ne hGbc.ne hT'] at hfeas
  exact hfeas

/-- (b) Ledger L1-cover, feasibility half: the transported cover is feasible for the copy. -/
theorem copyCover_mem (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    {z : Sym2 V → ℝ} (hz : z ∈ FeasibleCover (triangleCoverSystem G)) :
    copyCover v u z ∈ FeasibleCover (triangleCoverSystem (copyVertex G v u)) :=
  ⟨copyCover_inUnitBox v u hz.1, copyCover_satisfiesCover G hz⟩

/-- (a) Ledger L1-edges: `e(G_{v→u}) + e(G_{u→v}) = 2 e(G)` for nonadjacent `u, v`. -/
theorem edgeCard_copyVertex_add (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (huv : ¬ G.Adj u v) :
    (copyVertex G v u).edgeFinset.card + (copyVertex G u v).edgeFinset.card
      = 2 * G.edgeFinset.card := by
  have hvu : (copyVertex G v u).edgeFinset.card
      = G.edgeFinset.card + G.degree u - G.degree v := by
    unfold copyVertex; exact G.card_edgeFinset_replaceVertex_of_not_adj huv
  have huv2 : (copyVertex G u v).edgeFinset.card
      = G.edgeFinset.card + G.degree v - G.degree u := by
    unfold copyVertex; exact G.card_edgeFinset_replaceVertex_of_not_adj (fun h => huv h.symm)
  have hdv := degree_le_edgeFinset_card G v
  have hdu := degree_le_edgeFinset_card G u
  omega

/-- (b) Ledger L1-cover inequality: `τ₃*(G_{v→u}) + τ₃*(G_{u→v}) ≤ 2 τ₃*(G)`. -/
theorem tau3star_copyVertex_add (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (huv : ¬ G.Adj u v) (hne : u ≠ v) :
    tau3star (copyVertex G v u) + tau3star (copyVertex G u v) ≤ 2 * tau3star G := by
  set z := optimalCover (triangleCoverSystem G) with hzdef
  have hzfeas : z ∈ FeasibleCover (triangleCoverSystem G) := optimalCover_mem _
  -- the optimal cover vanishes on any non-edge (and on loops), by optimality
  have hz0 : ∀ (p q : V), ¬ G.Adj p q → z s(p, q) = 0 := by
    intro p q hpq
    apply optimalCover_zero_off_support
    rintro ⟨S, hS⟩ hmem
    simp only [triangleCoverSystem, triangleEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff,
      Sym2.isDiag_iff_proj_eq] at hmem
    obtain ⟨⟨hp, hq⟩, hd⟩ := hmem
    exact hpq (hS.isClique (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hq) hd)
  have hsum : coverCost (copyCover v u z) + coverCost (copyCover u v z) = 2 * coverCost z := by
    rw [coverCost_copyCover v u z, coverCost_copyCover u v z,
      hz0 u v huv, hz0 u u (by simp), hz0 v u (fun h => huv h.symm), hz0 v v (by simp)]
    ring
  have h1 : tau3star (copyVertex G v u) ≤ coverCost (copyCover v u z) :=
    tauStar_le_cost _ (copyCover_mem G hzfeas)
  have h2 : tau3star (copyVertex G u v) ≤ coverCost (copyCover u v z) :=
    tauStar_le_cost _ (copyCover_mem G hzfeas)
  have h3 : tau3star G = coverCost z := by simp only [tau3star, tauStar, hzdef]
  rw [h3]; linarith [hsum, h1, h2]

/-- **Ledger L1 (vertex-copy inequality).** For nonadjacent distinct `u, v`,
    `2·Φ_τ(G) ≤ Φ_τ(G_{v→u}) + Φ_τ(G_{u→v})`. -/
theorem phiTau_copyVertex_add (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (huv : ¬ G.Adj u v) (hne : u ≠ v) :
    2 * phiTau G ≤ phiTau (copyVertex G v u) + phiTau (copyVertex G u v) := by
  have hcover := tau3star_copyVertex_add G huv hne
  have h