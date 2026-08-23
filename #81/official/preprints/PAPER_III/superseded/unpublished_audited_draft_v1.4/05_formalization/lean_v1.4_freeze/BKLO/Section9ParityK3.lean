/-
# BKLO §9 for `r = 2`, `F = K₃`: reducing Lemma 9.3 to one combinatorial construction

`BKLO.Lemma93K3S` (the repaired transcription of BKLO Lemma 9.3, p. 25 — the transcription
`BKLO.Lemma93K3` itself is refuted in `BKLO.not_lemma93K3`) asks for a triangle-decomposable
subgraph `Ppar ⊆ G` of maximum degree at most `γn` which can repair the part-parities of every
`2`-divisible graph on `S`.

`BKLO.ParityFamilyExists` below isolates exactly what has to be built: an edge-disjoint family `𝒯`
of triangles of `G`, of maximum degree at most `γn`, whose subfamilies realise the part-degree
parity vector of **every** triangle on `S`.  `BKLO.lemma93K3S_of_parityFamily` derives Lemma 9.3
from it; the derivation is the content of `BKLO/TriangleSums.lean` and `BKLO/ParityFamily.lean`:

* the parity vector `(x, W) ↦ d_E(x, W) mod 2` is additive over `F₂`-sums of edge sets;
* every `2`-divisible graph on `S` is an `F₂`-sum of triangles on `S` (`BKLO.even_graph_triSum`);
* so realising the parity vector of each single triangle suffices.

Everything here is `sorry`-free.
-/
import BKLO.ParityFamily

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- **The combinatorial core of BKLO §9 for `r = 2`, `F = K₃`.**

*For all `k ≥ 1` and `γ > 0` there is `n₀` such that: whenever `P` is a `(k, d)`-partition of `S`
for a graph `G` on `S` with `d ≥ 1/2 + γ` and `|S| ≥ n₀`, there is a family `𝒯` of pairwise
edge-disjoint triangles of `G` with `Δ(⋃𝒯) ≤ γ|S|` such that, for every triangle `T₀` on `S`, some
subfamily `𝒮 ⊆ 𝒯` has the same part-degree parities as `T₀`, i.e. `d_{⋃𝒮}(x, W) ≡ d_{T₀}(x, W)`
mod `2` for every part `W ∈ P` and every `x ∈ V_{<W}`.*

This is a finite, purely combinatorial statement: no probabilistic estimate enters it.  It is
proved unconditionally in `BKLO.parityFamilyExists_holds` (`BKLO/Section9ParityK3Proof.lean`). -/
def ParityFamilyExists : Prop :=
  ∀ (k : ℕ) (γ : ℝ), 0 < k → 0 < γ → ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (G : Finset (Sym2 V)) (S : Finset V) (P : Finset (Finset V))
      (idx : Finset V → ℕ) (d : ℝ),
      n₀ ≤ S.card → (∀ e ∈ G, ¬ e.IsDiag) → G ⊆ cliqueEdges S →
      1 / 2 + γ ≤ d → IsKDeltaPartition k d P G S →
      ∃ 𝒯 : Finset (Finset V), IsTriFamily 𝒯 ∧ famEdges 𝒯 ⊆ G ∧
        (∀ v : V, (edeg (famEdges 𝒯) v : ℝ) ≤ γ * (S.card : ℝ)) ∧
        ∀ T₀ : Finset V, T₀.card = 3 → T₀ ⊆ S →
          ∃ 𝒮 : Finset (Finset V), 𝒮 ⊆ 𝒯 ∧ ∀ W ∈ P, ∀ x ∈ beforeParts P idx W,
            flipv 𝒮 x W = ((degTo (cliqueEdges T₀) x W : ℕ) : ZMod 2)

/-- **BKLO Lemma 9.3 (repaired) follows from the parity-family construction.** -/
theorem lemma93K3S_of_parityFamily (h : ParityFamilyExists) : Lemma93K3S := by
  intro k γ hk hγ
  obtain ⟨n₀, H⟩ := h k γ hk hγ
  refine ⟨n₀, ?_⟩
  intro V _ G S P idx d hcard hloop hGS hd hpart
  obtain ⟨𝒯, hfam, hsub, hdeg, hreal⟩ := H G S P idx d hcard hloop hGS hd hpart
  have hcover : P.biUnion id = S := hpart.1.cover
  refine ⟨famEdges 𝒯, hsub, ?_, hdeg⟩
  refine isParityGraphK3S_of_realizable hfam ?_
  intro T₀ hT₀card hT₀sub
  rw [hcover] at hT₀sub
  exact hreal T₀ hT₀card hT₀sub

end BKLO
