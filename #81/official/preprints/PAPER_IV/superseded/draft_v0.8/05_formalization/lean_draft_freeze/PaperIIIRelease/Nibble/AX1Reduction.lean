/-
# Nibble — AX1 reduction skeleton (the cross-project merge, proof-of-concept)

Replicates PaperIII's Layer-X `AX1` statement (cover-side `τ₃* − ν₃ ≤ ε n²`) and its `tau3Star` cover LP,
and proves AX1 REDUCES to exactly two remaining obligations:
  * `StrongDualityHyp` — `τ₃* ≤ ν₃*` (Aristotle core `b3ee717f`; reverse of the proven weak duality).
  * `NibbleGapHyp` — the UNCONDITIONAL packing gap `ν₃* − ν₃ ≤ ε n²` (`NibbleTheoremMost` + `②`
    near-regularity discharged for all large graphs).
The definitional bridges `Nibble.{nu3,nu3star} ↔ PaperIII.{nu3,nu3Star}` (proven in `YusterBridgePacking`,
`YusterBridgeFrac`) make the `ν₃, ν₃*` here the SAME as AX1's. `tau3Star`/`AX1Statement` are PaperIII's
forms (instance-binder variant of `PaperIII/AX.lean`'s `axiom AX1`).

* `ax1_of_strongDuality_and_nibbleGap` — the reduction. Discharging the two hyps closes AX1.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.YusterEdge

open Finset SimpleGraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- PaperIII `edgesIn`: edges of `G` contained in a vertex set `t`. -/
def edgesIn (t : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ t

/-- PaperIII `IsFracCover`: nonneg edge weights, total ≥ 1 inside each triangle. -/
def IsFracCover (y : Sym2 V → ℝ) : Prop :=
  (∀ e, 0 ≤ y e) ∧ ∀ t ∈ G.cliqueFinset 3, 1 ≤ ∑ e ∈ edgesIn G t, y e

/-- PaperIII `τ₃*`: the fractional triangle-cover optimum (LP value). -/
noncomputable def tau3Star : ℝ :=
  sInf {x | ∃ y : Sym2 V → ℝ, IsFracCover G y ∧ x = ∑ e ∈ G.edgeFinset, y e}

/-- **AX1 statement** (PaperIII Layer X, verbatim): the fractional–integral triangle-packing gap is
`o(n²)`, uniformly over graphs, read cover-side (`τ₃* − ν₃`). -/
def AX1Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V →
      tau3Star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- **The strong-duality obligation** (Aristotle core `b3ee717f`): `τ₃* ≤ ν₃*` for every graph
(the reverse of the proven weak duality; together they give `τ₃* = ν₃*`). -/
def StrongDualityHyp : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    tau3Star G ≤ nu3star G

/-- **The unconditional nibble-gap obligation** (`NibbleTheoremMost` + `②` near-regularity discharged
for all large graphs): `ν₃* − ν₃ ≤ ε n²` uniformly. -/
def NibbleGapHyp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V →
      nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- **AX1 REDUCTION.** AX1 follows from the two remaining obligations: cover-side strong duality
(`τ₃* ≤ ν₃*`) and the unconditional nibble packing gap (`ν₃* − ν₃ ≤ ε n²`). The definitional bridges
`Nibble.{nu3,nu3star} ↔ PaperIII.{nu3,nu3Star}` (already proven) make these the SAME `ν₃, ν₃*` as AX1's. -/
theorem ax1_of_strongDuality_and_nibbleGap
    (hdual : StrongDualityHyp) (hgap : NibbleGapHyp) : AX1Statement := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := hgap ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  have hg := hn₀ V G hV
  have hd := hdual G
  -- τ₃* − ν₃ ≤ ν₃* − ν₃ ≤ ε n²
  linarith

end Nibble.AX1
