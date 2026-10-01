import E34.Compress
import E34.Sampling

/-!
# E34 — pinned representations and the statement of Lemma 11

`PinnedOn Γ x G U` (Definition 2 of arXiv:1902.06135, combinatorial form): `G[U]` has a
subtree representation `(T_u)_{u ∈ U}` on some rooted tree `T`, together with a
*path-preserving* map `ι : Γ → T` (the image of a path of `Γ` lies on the corresponding path of
`T`), such that `ι (x u) ∈ T_u` for every `u ∈ U`.  Taking `T = Γ`, `ι = id` gives the paper's
notion for the topological tree underlying `Γ`; allowing any `T ⊇ ι(Γ)` only enlarges the set
of pinned graphs, so the version of Lemma 11 below is (formally) stronger than the paper's.

`Lemma11With m11` is Lemma 11 of the paper with sample size `m11 ε K`, where `K` is the number
of vertices of `Γ` (the gate set of the paper's Claim 1): if `G` is `ε`-far from chordal, a
sample with repetition of `m11 ε K` vertices is `x`-pinned with probability at most `1/2`.
-/

namespace E34

open Finset

open scoped Classical

variable {n : ℕ}

/-- `G[U]` has an `x`-pinned representation on a tree containing a path-preserving image of
`Γ`. -/
def PinnedOn {K : ℕ} (Γ : RTree K) (x : Fin n → Fin K) (G : SimpleGraph (Fin n))
    (U : Finset (Fin n)) : Prop :=
  ∃ (K' : ℕ) (T : RTree K') (ι : Fin K → Fin K') (Tu : Fin n → Finset (Fin K')),
    (∀ a b g, Γ.OnPath a b g → T.OnPath (ι a) (ι b) (ι g)) ∧
    (∀ u ∈ U, T.IsSub (Tu u) ∧ ι (x u) ∈ Tu u) ∧
    (∀ u ∈ U, ∀ v ∈ U, u ≠ v → (G.Adj u v ↔ (Tu u ∩ Tu v).Nonempty))

theorem PinnedOn.mono {K : ℕ} {Γ : RTree K} {x : Fin n → Fin K} {G : SimpleGraph (Fin n)}
    {U U' : Finset (Fin n)} (h : PinnedOn Γ x G U) (hU : U' ⊆ U) : PinnedOn Γ x G U' := by
  obtain ⟨K', T, ι, Tu, h1, h2, h3⟩ := h
  exact ⟨K', T, ι, Tu, h1, fun u hu => h2 u (hU hu),
    fun u hu v hv huv => h3 u (hU hu) v (hU hv) huv⟩

/-- The ancestor relation, hence subtrees and paths, only depend on the parent map. -/
theorem RTree.onPath_congr {K : ℕ} {Γ Γ' : RTree K} (h : Γ.par = Γ'.par) :
    Γ.OnPath = Γ'.OnPath := by
  have hA : Γ.Anc = Γ'.Anc := by
    funext y x; simp only [RTree.Anc, h]
  funext a b g
  simp only [RTree.OnPath, RTree.IsSub, RTree.IsSubAt, hA]

theorem pinnedOn_congr {K : ℕ} {Γ Γ' : RTree K} (h : Γ.par = Γ'.par) (x : Fin n → Fin K)
    (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) : PinnedOn Γ x G U ↔ PinnedOn Γ' x G U := by
  unfold PinnedOn; rw [RTree.onPath_congr h]

/-- **Lemma 11** of arXiv:1902.06135 (sampling with repetition, explicit sample size
`m11 ε K`; `K` is the number of vertices of the tree `Γ`). -/
def Lemma11With (m11 : ℝ → ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ (K : ℕ) (Γ : RTree K) (n : ℕ) (G : SimpleGraph (Fin n))
    (x : Fin n → Fin K),
    (∀ F : SimpleGraph (Fin n), AlonShapira.IsChordal F →
      ε * (n : ℝ) ^ 2 < (AlonShapira.editDist G F : ℝ)) →
    2 * (univ.filter (fun w : Fin (m11 ε K) → Fin n => PinnedOn Γ x G (img w))).card ≤
      n ^ (m11 ε K)

end E34
