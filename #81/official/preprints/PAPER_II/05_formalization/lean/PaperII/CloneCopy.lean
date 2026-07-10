import PaperII.CloneSimplicial
import PaperII.L7

/-!
# Paper II — Clone-class count and the shared terminal predicate (S2/S3 interface)

* `cloneClassCount G` = `m(G)` = number of open-neighborhood clone classes (false-twin classes),
  computed as the number of distinct neighborhoods. This is the progress measure of L3/L6.
* `IsTerminal H` = property `(H)` of L7 verbatim (every two nonadjacent simplicial vertices have equal
  open neighborhoods). This is the SHARED terminal predicate: L6 terminates exactly at `IsTerminal`,
  and `terminal_characterization` (L7) turns `IsTerminal` into `IsCompleteSplit`. Freezing one predicate
  used by both the termination side (L3/L6) and the characterization side (L7) is what makes the L12
  assembly sound — L6 stops precisely where L7 guarantees complete-split.
-/

open scoped BigOperators
open Finset

namespace PaperII

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `m(G)`: the number of open-neighborhood clone classes (= number of distinct neighborhoods). -/
def cloneClassCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (univ.image (fun v => G.neighborFinset v)).card

/-- The shared terminal predicate = L7's property `(H)`: every two nonadjacent simplicial vertices
have equal open neighborhoods. Definitionally the hypothesis of `terminal_characterization`. -/
def IsTerminal (H : SimpleGraph V) : Prop :=
  ∀ x y : V, IsSimplicial H x → IsSimplicial H y → ¬ H.Adj x y →
    H.neighborSet x = H.neighborSet y

/-- The shared predicate feeds L7: a terminal chordal graph is complete-split. -/
theorem isCompleteSplit_of_isTerminal (H : SimpleGraph V) (hchord : ChordalStructure H)
    (hterm : IsTerminal H) : IsCompleteSplit H :=
  terminal_characterization H hchord hterm

/-- Underlying relation of the class-copy operation: reassign every vertex of the open-neighborhood
clone class `{v | N(v) = A}` the neighborhood `B`, leaving all other adjacencies unchanged. -/
def classCopyRel (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) : V → V → Prop := fun a b =>
  (G.neighborFinset a ≠ A ∧ G.neighborFinset b ≠ A ∧ G.Adj a b)
  ∨ (G.neighborFinset a = A ∧ b ∈ B)
  ∨ (G.neighborFinset b = A ∧ a ∈ B)

instance (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    DecidableRel (classCopyRel G A B) := fun a b => by unfold classCopyRel; infer_instance

/-- Ledger class-copy `G_{W₁→W₂}`: copy the **entire** open-neighborhood clone class `{v | N(v)=A}`
(source `W₁`, `A = N(W₁)`) onto the target neighborhood `B = N(W₂)`. Parametrizing by the neighborhood
`A` makes "move the maximal complete clone class" structural, not a fragile hypothesis. Defined directly
by adjacency; agrees with the iterated `replaceVertex` (D7) operation — the equivalence is a required
bridge lemma for the L2/L6 route (checked to coincide on examples, `classCopy_agrees`). -/
def classCopy (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel (classCopyRel G A B)

instance (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    DecidableRel (classCopy G A B).Adj := fun a b => by
  unfold classCopy; r