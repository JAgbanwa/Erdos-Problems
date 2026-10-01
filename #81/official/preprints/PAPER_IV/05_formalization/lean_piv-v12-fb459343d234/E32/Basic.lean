import PaperIV.DefectSharpPublication
import PaperIV.ExtremalClassification

/-!
# E32 — vocabulary for quantitative stability at a fixed rooted defect `s`

* `E32.IsDefectRoot G s C D H` — a *root* of `G`: a clique `C` of `G`, a set `D` of exactly `s`
  defect vertices and the exterior `H`, the three sets partitioning the vertex set, with the size
  window `2 ≤ |C| ≤ |H|`.
* The extremal family `E_s(n,k) = (K_{k−s} ⊔ I_s) ∨ I_{n−k}` is the existing comparator
  `PaperIV.DefectComparatorGraph.defSplitGraph C D H` with `|C| = k − s`, `|D| = s`, `|H| = n − k`.
* `E32.rootEdit G C D H` — the edit distance (edge additions plus deletions) from `G` to
  `defSplitGraph C D H`, i.e. the cardinality of the symmetric difference of the edge sets.
* `E32.rootBaseline C D H = (|C| + |D|)·|H| − C(|C|,2)`, the unrestricted clique partition number of
  `defSplitGraph C D H` (`E32/Transfer.lean`, `E32/PieceIdentity.lean`).
* `E32.IsCanonicalPiece C D H K` — the zero-defect pieces of `E_s`: a root–exterior edge `{x,h}`
  (`x ∈ C ∪ D`, `h ∈ H`) or a triangle `{c,c',h}` with `c,c' ∈ C`, `h ∈ H`.
* `E32.NearestCore m k` — `k` is a nearest integer to `(2m+1)/6`, written without division as
  `|6k − (2m+1)| ≤ 3`.
* `E32.rsd G` — the rooted simplicial defect of `G` (least `s` with `RootedDefectAt G s`).
-/

namespace E32

open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.DefectComparatorGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A root of `G` at defect `s`: a clique `C`, exactly `s` defect vertices `D`, and the exterior
`H`, partitioning the vertices, with `2 ≤ |C| ≤ |H|`. -/
structure IsDefectRoot (G : SimpleGraph V) (s : ℕ) (C D H : Finset V) : Prop where
  disjCD : Disjoint C D
  disjCH : Disjoint C H
  disjDH : Disjoint D H
  cover : ∀ x : V, x ∈ C ∨ x ∈ D ∨ x ∈ H
  clique : G.IsClique (C : Set V)
  card_def : D.card = s
  two_le : 2 ≤ C.card
  core_le_hosts : C.card ≤ H.card

/-- Edit distance from `G` to the extremal graph `defSplitGraph C D H`. -/
def rootEdit (G : SimpleGraph V) [DecidableRel G.Adj] (C D H : Finset V) : ℕ :=
  PaperIV.EditMetric.editDist G.edgeFinset (defSplitGraph C D H).edgeFinset

/-- The partition number of the extremal graph with root `(C, D, H)`. -/
def rootBaseline (C D H : Finset V) : ℕ := (C.card + D.card) * H.card - C.card.choose 2

/-- The canonical (zero-defect) pieces of the extremal graph with root `(C, D, H)`. -/
def IsCanonicalPiece (C D H K : Finset V) : Prop :=
  (∃ x ∈ C ∪ D, ∃ h ∈ H, x ≠ h ∧ K = {x, h}) ∨
  (∃ c ∈ C, ∃ c' ∈ C, ∃ h ∈ H, c ≠ c' ∧ K = {c, c', h})

/-- `k` is a nearest integer to `(2m+1)/6`. -/
def NearestCore (m k : ℕ) : Prop := |(6 * (k : ℤ)) - (2 * (m : ℤ) + 1)| ≤ 3

/-- `G` is (literally, on its own vertex set) an extremal graph `E_s(n,k)` with an admissible
core size: `G = defSplitGraph C D H` with `|D| = s`, `k = |C| + s`, `|H| = n − k`, and `k` a
nearest integer to `(2(n+s)+1)/6`. -/
def IsAdmissibleExtremal (G : SimpleGraph V) (s : ℕ) : Prop :=
  ∃ C D H : Finset V, Disjoint C D ∧ Disjoint C H ∧ Disjoint D H ∧
    (∀ x : V, x ∈ C ∨ x ∈ D ∨ x ∈ H) ∧ D.card = s ∧
    G = defSplitGraph C D H ∧ NearestCore (Fintype.card V + s) (C.card + s)

theorem exists_rootedDefectAt (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ s, RootedDefectAt G s := ⟨_, rootedDefectAt_card G⟩

open Classical in
/-- The rooted simplicial defect `rsd(G)`: the least `s` with `RootedDefectAt G s`. -/
noncomputable def rsd (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Nat.find (exists_rootedDefectAt G)

/-- `rsd(G) ≤ s` is exactly `RootedDefectAt G s`. -/
theorem rsd_le_iff (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    rsd G ≤ s ↔ RootedDefectAt G s := by
  classical
  constructor
  · intro h
    exact rootedDefectAt_mono G h (Nat.find_spec (exists_rootedDefectAt G))
  · intro h
    exact Nat.find_min' _ h

/-- The nearest-integer condition is the optimal-core condition of Paper IV. -/
theorem nearestCore_iff_optimalCore (m k : ℕ) :
    NearestCore m k ↔ PaperIV.ExtremalClassification.OptimalCore m k := by
  unfold NearestCore PaperIV.ExtremalClassification.OptimalCore
  rw [abs_le]
  omega

end E32
