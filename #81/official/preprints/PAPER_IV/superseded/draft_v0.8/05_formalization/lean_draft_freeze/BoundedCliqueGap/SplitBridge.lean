import BoundedCliqueGap.CompleteSplit
import PaperIV.SplitUniformIncidence

/-!
# Bridge: the complete split graph of the extract is the tree's `splitGraph`

The extracted development builds the complete split graph on a sum type,
`BoundedCliqueGap.CS K S : SimpleGraph (K ⊕ S)`, while the split-graph theory of this tree
works with `PaperIV.SplitUniformIncidence.splitGraph Core Hosts : SimpleGraph V`, a graph on a
fixed vertex type with the clique part and the independent part given as disjoint finsets.

This module records that the two are literally the same graph: with `Core` the left copy and
`Hosts` the right copy inside `K ⊕ S`, `CS K S = splitGraph Core Hosts`.

The *results* of the two developments are not interchangeable — the extract bounds the
triangular LP `ν₃*` on `CS`, whereas `PaperIV/SplitComplete*` computes the value of mixed
`K₂/K₃/K₄` clique partitions of `splitGraph` — but the underlying object is shared, so no
second notion of "complete split graph" is introduced by the extract.
-/

namespace BoundedCliqueGap

open Finset

variable {K S : Type*} [Fintype K] [Fintype S] [DecidableEq K] [DecidableEq S]

/-- The left copy of `K` inside `K ⊕ S`: the clique part. -/
def csCore (K S : Type*) [Fintype K] [DecidableEq K] [DecidableEq S] : Finset (K ⊕ S) :=
  Finset.univ.image Sum.inl

/-- The right copy of `S` inside `K ⊕ S`: the independent part. -/
def csHosts (K S : Type*) [Fintype S] [DecidableEq K] [DecidableEq S] : Finset (K ⊕ S) :=
  Finset.univ.image Sum.inr

@[simp] lemma mem_csCore {u : K ⊕ S} : u ∈ csCore K S ↔ u.isLeft := by
  cases u <;> simp [csCore]

@[simp] lemma mem_csHosts {u : K ⊕ S} : u ∈ csHosts K S ↔ u.isRight := by
  cases u <;> simp [csHosts]

/-- The clique part and the independent part are disjoint. -/
theorem disjoint_csCore_csHosts : Disjoint (csCore K S) (csHosts K S) := by
  refine Finset.disjoint_left.2 fun u hu hu' => ?_
  cases u <;> simp_all

/-- **The complete split graph of the extract is the tree's `splitGraph`.** -/
theorem cs_eq_splitGraph :
    CS K S = PaperIV.SplitUniformIncidence.splitGraph (csCore K S) (csHosts K S) := by
  ext u v
  rw [PaperIV.SplitUniformIncidence.splitGraph_adj_iff]
  cases u <;> cases v <;> simp [CS]

end BoundedCliqueGap
