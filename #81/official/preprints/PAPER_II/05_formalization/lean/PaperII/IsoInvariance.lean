import PaperII.Model
import PaperII.CoverRelabel

/-!
# Paper II — Isomorphism invariance of `τ₃*` and `Φ_τ`

A graph isomorphism `e : G ≃g G'` preserves the fractional triangle-cover number and hence the
deficit functional. Prove `tau3star_iso` by reducing to `PaperII.tauStar_congr` (already proven in
PaperII/CoverRelabel.lean): the isomorphism induces a coordinate equivalence on `Sym2` (via
`Sym2.map e`) and a constraint equivalence on triangles (a 3-clique maps to a 3-clique), and these
preserve the `triangleCoverSystem` support (`triangleEdges`). Then `phiTau_iso` follows using
`tau3star_iso` together with edge-count invariance (`SimpleGraph.Iso.card_edgeFinset_eq`).
-/

open scoped BigOperators

namespace PaperII

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- The `Sym2` coordinate equivalence induced by a bijection on vertices. -/
def sym2Equiv (e : V ≃ W) : Sym2 V ≃ Sym2 W where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv x := by rw [Sym2.map_map]; simp
  right_inv x := by rw [Sym2.map_map]; simp

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
@[simp] lemma sym2Equiv_apply (e : V ≃ W) (x : Sym2 V) : sym2Equiv e x = Sym2.map e x := rfl

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
@[simp] lemma sym2Equiv_toEmbedding_apply (e : V ≃ W) (x : Sym2 V) :
    (sym2Equiv e).toEmbedding x = Sym2.map e x := rfl

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
/-- A graph isomorphism sends a triangle to a triangle. -/
lemma isTriangle_map_iff (G : SimpleGraph V) (G' : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (e : G ≃g G') (s : Finset V) :
    IsTriangle G s ↔ IsTriangle G' (s.map e.toEquiv.toEmbedding) := by
  unfold IsTriangle;
  simp +decide [ SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Finset.map ];
  simp +decide [ Set.Pairwise, e.map_adj_iff ]

/-- The triangle constraint equivalence induced by a graph isomorphism. -/
def triangleEquiv (G : SimpleGraph V) (G' : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (e : G ≃g G') :
    Triangle G ≃ Triangle G' :=
  Equiv.subtypeEquiv (Equiv.finsetCongr e.toEquiv) (by
    intro s
    have hmap : (Equiv.finsetCongr e.toEquiv) s = s.map e.toEquiv.toEmbedding := by
      simp [Equiv.finsetCongr]
    rw [hmap]
    exact isTriangle_map_iff G G' e s)

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
@[simp] lemma triangleEquiv_val (G : SimpleGraph V) (G' : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (e : G ≃g G') (T : Triangle G) :
    (triangleEquiv G G' e T).1 = T.1.map e.toEquiv.toEmbedding := by
  rfl

omit [Fintype V] [Fintype W] in
/-- The support-matching condition needed for `tauStar_congr`. -/
lemma triangleEdges_map (G : SimpleGraph V) (G' : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (e : G ≃g G') (T : Triangle G) :
    triangleEdges G' (triangleEquiv G G' e T)
      = (triangleEdges G T).map (sym2Equiv e.toEquiv).toEmbedding := by
  -- Apply the definitions of `triangleEdges` and `triangleEquiv`.
  simp [triangleEdges, triangleEquiv_val];
  ext ⟨x, y⟩; simp [sym2Equiv]

/-- `τ₃*` is invariant under graph isomorphism. -/
theorem tau3star_iso (G : SimpleGraph V) (G' : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (e : G ≃g G') :
    tau3star G' = tau3star G := by
  unfold tau3star
  exact tauStar_congr (triangleCoverSystem G) (triangleCoverSystem G')
    (sym2Equiv e.toEquiv) (triangleEquiv G G' e) (triangleEdges_map G G' e)

/-- `Φ_τ` is invariant under graph isomorphism. -/
theorem phiTau_iso (G : SimpleGraph V) (G' : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (e : G ≃g G') :
    phiTau G' = phiTau G :=