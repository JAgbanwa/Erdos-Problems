/-
# BKLO Section 8 — absorber existence from the transformer chain.

Using the transformer calculus of `BKLO.Transformer` (Prop 8.2, proved), we reduce the existence of
an absorber for a `K₃`-divisible edge set `H` to the existence of the two expansion transformers of
§8.1 (Lemmas 8.4/8.7): `H ∼ Lₕ` and `Lₕ ∼ pK₃`, where `pK₃` is `p` vertex-disjoint triangles
(trivially decomposable).

The KEY assembly step is proved here:

  `absorber_of_transformer` — if `A'` is an `(H, K)`-transformer and `K` is triangle-decomposable
  (and `H`, `K` edge-disjoint), then `A' ∪ K` is an absorber for `H`.  (BKLO Lemma 8.8, taking
  `K = pK₃`.)

What remains — the expansion transformers themselves (the F-expansion / vertex-identification
construction of §8.1) — is the genuine combinatorial hole, isolated as `ExpansionChain`.
-/
import BKLO.Transformer

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- **Assembly step (BKLO Lemma 8.8).**  A transformer from `H` to a decomposable `K` yields an
absorber for `H`.  Proof: `A' ∪ K` decomposes (it is the transformer's `A' ∪ K` half), and
`(A' ∪ K) ∪ H = (A' ∪ H) ∪ K` decomposes as an edge-disjoint union of two decomposable sets. -/
theorem absorber_of_transformer {A' H K : Finset (Sym2 V)}
    (hT : IsTransformer A' H K) (hK : TriDecomp K) (dHK : Disjoint H K) :
    IsAbsorber (A' ∪ K) H := by
  obtain ⟨dA'H, dA'K, hd_A'H, hd_A'K⟩ := hT
  refine ⟨?_, ?_, ?_⟩
  · -- Disjoint (A' ∪ K) H
    exact Finset.disjoint_union_left.mpr ⟨dA'H, dHK.symm⟩
  · -- TriDecomp (A' ∪ K)  (the transformer's second half)
    exact hd_A'K
  · -- TriDecomp ((A' ∪ K) ∪ H) = TriDecomp ((A' ∪ H) ∪ K)
    have hdis : Disjoint (A' ∪ H) K := Finset.disjoint_union_left.mpr ⟨dA'K, dHK⟩
    have h := TriDecomp.union hdis hd_A'H hK
    convert h using 1
    ext x; simp only [Finset.mem_union]; tauto

/-- **Triangle-divisibility** of an edge set (the necessary condition for an absorber, BKLO
`F`-divisibility for `F = K₃`): every vertex meets an even number of edges of `H`, and the number
of edges is a multiple of three. -/
def TriDivisible (H : Finset (Sym2 V)) : Prop :=
  (∀ v : V, Even ((H.filter (fun e => v ∈ e)).card)) ∧ 3 ∣ H.card

/-- **The expansion chain (BKLO Lemmas 8.4 / 8.7), interface form.**  For every *triangle-divisible*
edge set `H` there is a decomposable `K` (namely `pK₃`) with an `(H, K)`-transformer edge-disjoint
from `H`.  This is the F-expansion / vertex-identification content of §8.1 — the genuine
combinatorial hole.  (Divisibility is essential: e.g. a single edge has no absorber.) -/
def ExpansionChain : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Sym2 V)), TriDivisible H →
    ∃ (A' K : Finset (Sym2 V)), IsTransformer A' H K ∧ TriDecomp K ∧ Disjoint H K

/-- **Absorber existence (BKLO Lemma 8.8) from the expansion chain.**  Immediate from
`absorber_of_transformer`; requires `H` triangle-divisible. -/
theorem absorber_existence_of_expansion (h : ExpansionChain) :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Sym2 V)), TriDivisible H →
      ∃ A : Finset (Sym2 V), IsAbsorber A H := by
  intro V _ _ H hdiv
  obtain ⟨A', K, hT, hK, dHK⟩ := h H hdiv
  exact ⟨A' ∪ K, absorber_of_transformer hT hK dHK⟩

end BKLO
