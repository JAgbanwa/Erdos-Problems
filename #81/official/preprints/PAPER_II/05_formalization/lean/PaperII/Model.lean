import Mathlib
import PaperII.FiniteCover

/-!
# Paper II — Graph model (ledger D1–D3)

Triangles, the fractional triangle-cover number `τ₃*` (as a cover-LP minimum via
`PaperII.FiniteCover`), and the deficit functional `Φ_τ(G) = |E(G)| − 2·τ₃*(G)`.

Cover coordinates are taken to be all of `Sym2 V` (unordered pairs); coordinates that are
not edges lie in no triangle constraint, hence are `0` at the optimum, so the value equals
the ledger-D2 minimum over edge-covers.
-/

open scoped BigOperators

namespace PaperII

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- D1 (triangle): a 3-element clique of `G`. -/
def IsTriangle (G : SimpleGraph V) (s : Finset V) : Prop := G.IsNClique 3 s

/-- The triangles of `G`, as a subtype of `Finset V`. -/
def Triangle (G : SimpleGraph V) [DecidableRel G.Adj] : Type _ :=
  {s : Finset V // IsTriangle G s}

instance (G : SimpleGraph V) [DecidableRel G.Adj] : DecidablePred (IsTriangle G) :=
  fun _ => by unfold IsTriangle; infer_instance

instance (G : SimpleGraph V) [DecidableRel G.Adj] : Fintype (Triangle G) := by
  unfold Triangle; infer_instance

instance (G : SimpleGraph V) [DecidableRel G.Adj] : DecidableEq (Triangle G) := by
  unfold Triangle; infer_instance

/-- The three edges of a triangle, as unordered pairs (the off-diagonal pairs inside `T`). -/
def triangleEdges (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) :
    Finset (Sym2 V) :=
  T.1.sym2.filter (fun e => ¬ e.IsDiag)

theorem triangleEdges_nonempty (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) :
    (triangleEdges G T).Nonempty := by
  obtain ⟨s, hs⟩ := T
  have hcard : s.card = 3 := hs.card_eq
  obtain ⟨a, b, c, hab, _, _, rfl⟩ := Finset.card_eq_three.mp hcard
  refine ⟨s(a, b), ?_⟩
  simp only [triangleEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff,
    Sym2.isDiag_iff_proj_eq]
  refine ⟨⟨?_, ?_⟩, hab⟩ <;> simp

/-- The triangle cover system: coordinates `Sym2 V`, constraints indexed by triangles. -/
def triangleCoverSystem (G : SimpleGraph V) [DecidableRel G.Adj] :
    CoverSystem (Sym2 V) (Triangle G) where
  support := triangleEdges G
  support_nonempty := triangleEdges_nonempty G

/-- D2 (fractional triangle cover number) `τ₃*(G)`. -/
noncomputable def tau3star (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  tauStar (triangleCoverSystem G)

/-- D3 (deficit functional) `Φ_τ(G) = |E(G)| − 2·τ₃*(G)`. -/
noncomputable def phiTau (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (G.edgeFinset.card : ℝ) - 2 * tau3star G

theorem tau3star_nonneg (G : SimpleGraph V) [Decidable