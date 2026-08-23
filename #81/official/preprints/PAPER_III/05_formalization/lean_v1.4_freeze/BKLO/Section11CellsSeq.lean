/-
# BKLO §11, cells route: the vortex survives the reservation

This file removes the *partition-sequence* half of the §11 interface `BKLO.CellsAbsorptionK3`.

The point is BKLO's quantifier order: the absorber `A*` of §8 is reserved **before** the §10
near-optimal decomposition is run, but §10 has to be run on `E \ A*`, so the partition sequence
must be one of `E \ A*` and not merely one of `E`.  What is proved here is that this is a purely
quantitative matter: a partition sequence of `E` remains one of `E \ A*`, with each of its
densities degraded by `η`, as soon as `A*` is **spread along the sequence**, i.e. every vertex
sends at most `η|W|` reserved edges into every part `W` of every level.  This is the notion

* `BKLO.SpreadAlong` — spread along a partition sequence,

and the deletion lemma is

* `BKLO.PartSeq.sdiff_spread`.

Consequently the §11 interface reduces to a statement about the *reservation alone*:

* `BKLO.CellsAbsorberSpread` — given the vortex of `E`, reserve inside `E` an even-degree `A*`
  that is spread along the vortex and absorbs every even remainder confined to the bottom cells.

`BKLO.cellsAbsorptionK3_of_cellsAbsorberSpread` derives `BKLO.CellsAbsorptionK3` from it, using the
vortex `BKLO.exists_partSeq_dense_bounded` of §10 to produce the constant-size bottom cells.  So
after this file the only thing between the proved §10 core and `BKLO.TriDecompDense` is the §8
reservation itself, in the form `BKLO.CellsAbsorberSpread`.
-/
import BKLO.Section11Cells
import BKLO.VortexPartition

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### Deleting a graph that is spread over the parts -/

/-- Splitting the degree into a set across a deletion. -/
theorem degTo_sdiff_add_degTo_ge (E H : Finset (Sym2 V)) (x : V) (W : Finset V) :
    degTo E x W ≤ degTo (E \ H) x W + degTo H x W := by
  classical
  have hsub : nbhdIn E x W ⊆ nbhdIn (E \ H) x W ∪ nbhdIn H x W := by
    intro y hy
    rw [mem_nbhdIn] at hy
    by_cases hH : s(x, y) ∈ H
    · exact Finset.mem_union_right _ (mem_nbhdIn.2 ⟨hy.1, hH⟩)
    · exact Finset.mem_union_left _ (mem_nbhdIn.2 ⟨hy.1, Finset.mem_sdiff.2 ⟨hy.2, hH⟩⟩)
  calc degTo E x W ≤ (nbhdIn (E \ H) x W ∪ nbhdIn H x W).card := Finset.card_le_card hsub
    _ ≤ degTo (E \ H) x W + degTo H x W := Finset.card_union_le _ _

/-- **Degradation of a `(k, d)`-partition under the deletion of a graph spread over its parts.**
Only the degrees *into each part* matter, so this refines `BKLO.IsKDeltaPartition.sdiff`, which
asks for a bound on the maximum degree of the deleted graph. -/
theorem IsKDeltaPartition.sdiff_parts {k : ℕ} {d d' : ℝ} {P : Finset (Finset V)}
    {E H : Finset (Sym2 V)} {S : Finset V} (h : IsKDeltaPartition k d P E S)
    (hH : ∀ x : V, ∀ W ∈ P, (degTo H x W : ℝ) ≤ (d - d') * (W.card : ℝ)) :
    IsKDeltaPartition k d' P (E \ H) S := by
  refine ⟨h.1, fun x hx W hW => ?_⟩
  have h1 : (degTo E x W : ℝ) ≤ (degTo (E \ H) x W : ℝ) + (degTo H x W : ℝ) := by
    exact_mod_cast degTo_sdiff_add_degTo_ge E H x W
  have h2 := h.2 x hx W hW
  have h3 := hH x W hW
  linarith

/-! ### Spread along a partition sequence -/

/-- **`H` is `η`-spread along the partition sequence `L`, `Pl` on `S`**: every vertex sends at most
`η|W|` edges of `H` into every part `W` of every level of the sequence.

This is exactly the hypothesis under which a partition sequence survives the deletion of `H`
(`BKLO.PartSeq.sdiff_spread`).  Note that it is much weaker than a bound on the maximum degree of
`H`: a vertex may carry many edges of `H`, provided they are distributed over the parts. -/
def SpreadAlong (η : ℝ) :
    List (Finset (Finset V)) → Finset (Finset V) → Finset (Sym2 V) → Finset V → Prop
  | [], Pl, H, S => ∀ x : V, ∀ W ∈ restrictParts Pl S, (degTo H x W : ℝ) ≤ η * (W.card : ℝ)
  | (P :: rest), Pl, H, S =>
      (∀ x : V, ∀ W ∈ restrictParts P S, (degTo H x W : ℝ) ≤ η * (W.card : ℝ)) ∧
        (∀ W ∈ restrictParts P S, SpreadAlong η rest Pl H W)

/-- **A partition sequence survives the deletion of a graph spread along it.**

If `H` is `η`-spread along the sequence (`BKLO.SpreadAlong`), then the same sequence is a partition
sequence for `E - H`, with the top-level density and the internal density both degraded by `η`.
This is the step that lets BKLO §11 reserve the absorber *before* running the §10 iteration: the
vortex of `E` is still a vortex of `E \ A*`. -/
theorem PartSeq.sdiff_spread {k : ℕ} {ε η : ℝ} {m : ℕ} {H : Finset (Sym2 V)} :
    ∀ (L : List (Finset (Finset V))) (c δ : ℝ) (Pl : Finset (Finset V)) (E : Finset (Sym2 V))
      (S : Finset V), PartSeq k c δ ε m L Pl E S → SpreadAlong η L Pl H S →
      PartSeq k (c - η) (δ - η) ε m L Pl (E \ H) S := by
  intro L
  induction L with
  | nil =>
    intro c δ Pl E S hseq hsp
    exact ⟨hseq.1.sdiff_parts (fun x W hW => by
      have := hsp x W hW; simpa using (by linarith : (degTo H x W : ℝ) ≤ (c - (c - η)) * (W.card : ℝ))),
      hseq.2⟩
  | cons P rest ih =>
    intro c δ Pl E S hseq hsp
    refine ⟨hseq.1.sdiff_parts (fun x W hW => by
      have := hsp.1 x W hW
      simpa using (by linarith : (degTo H x W : ℝ) ≤ (c - (c - η)) * (W.card : ℝ))), ?_⟩
    intro W hW
    have hrec := ih (δ + 2 * ε) δ Pl (edgesIn E W) W (hseq.2 W hW) (hsp.2 W hW)
    have hdens : δ + 2 * ε - η = δ - η + 2 * ε := by ring
    rw [hdens] at hrec
    rw [edgesIn_sdiff]
    exact hrec

/-! ### The reservation interface -/

/-- **The §8 reservation in the cells form, on a given vortex.**

For every `ε ∈ (0, 1]`, every `k ≥ 16` and every prescribed bottom-cell size `m₀` there is a
threshold `n₀` such that: for every large dense triangle-divisible host `E` on `S` and every
partition sequence of `E` with bottom cells of size at least `m₀`, one can reserve inside `E` an
even-degree set `A` which

* is `ε`-spread along that partition sequence (`BKLO.SpreadAlong`), and
* absorbs every even-degree remainder confined to the bottom cells, subject only to the necessary
  divisibility `3 ∣ |A ∪ H|`.

This is BKLO §8 in the cells form: `A` is to be built as the edge-disjoint union, over the bottom
cells, of bounded per-cell absorbers, placed so that the reservation is spread. -/
def CellsAbsorberSpread : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ k m₀ : ℕ, 16 ≤ k → ∃ m₁ : ℕ, ∀ mmax : ℕ, ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V) (m : ℕ)
      (L : List (Finset (Finset V))) (Pl : Finset (Finset V)),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → TriDivisible E →
      (∀ v ∈ S, (9 / 10 + 4 * ε) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      m₀ ≤ m → m₁ ≤ m → m ≤ mmax →
      PartSeq k (9 / 10 + 2 * ε) (9 / 10 + ε) ε m L Pl E S →
      (∀ P ∈ restrictParts Pl S, P ⊆ S) →
      (∀ P ∈ restrictParts Pl S, ∀ Q ∈ restrictParts Pl S, P ≠ Q → Disjoint P Q) →
      S ⊆ (restrictParts Pl S).biUnion id →
      (∀ P ∈ restrictParts Pl S, m - 1 ≤ P.card ∧ P.card ≤ m) →
      (∀ P ∈ restrictParts Pl S, ∀ v ∈ P,
        (9 / 10 + 3 * ε) * (P.card : ℝ) ≤ (edeg (E ∩ cliqueEdges P) v : ℝ)) →
      ∃ A : Finset (Sym2 V), A ⊆ E ∧ EvenDegrees A ∧ SpreadAlong ε L Pl A S ∧
        ∀ H : Finset (Sym2 V), H ⊆ insideParts (E \ A) (restrictParts Pl S) →
          EvenDegrees H → 3 ∣ (A ∪ H).card → TriDecomp (A ∪ H)

/-- **The vortex half of `BKLO.CellsAbsorptionK3` is unconditional.**

Given the §8 reservation on a vortex (`BKLO.CellsAbsorberSpread`), the §11 interface
`BKLO.CellsAbsorptionK3` follows: take the vortex of `E` with constant-size bottom cells
(`BKLO.exists_partSeq_dense_bounded`), reserve `A` on it, and observe that the vortex is still a
vortex of `E \ A` because `A` is spread along it (`BKLO.PartSeq.sdiff_spread`). -/
theorem cellsAbsorptionK3_of_cellsAbsorberSpread (h : CellsAbsorberSpread) :
    CellsAbsorptionK3 := by
  classical
  intro ε hε hε1 k m₀ hk
  obtain ⟨m₁, hres0⟩ := h ε hε hε1 k m₀ hk
  obtain ⟨Mmax, n₂, hvortex⟩ :=
    exists_partSeq_dense_bounded (δ := 9 / 10 + ε) (ε := ε) hε hε1 hk (max m₀ m₁)
  obtain ⟨n₁, hres⟩ := hres0 Mmax
  refine ⟨max n₁ n₂, ?_⟩
  intro V _ E S hcard hES hdiv hdeg
  have hn₁ : n₁ ≤ S.card := le_trans (le_max_left _ _) hcard
  have hn₂ : n₂ ≤ S.card := le_trans (le_max_right _ _) hcard
  -- the vortex of `E`
  have hdegv : ∀ v ∈ S, (9 / 10 + ε + 3 * ε) * (S.card : ℝ) ≤ (edeg E v : ℝ) := by
    intro v hv
    have := hdeg v hv
    have heq : (9 / 10 + ε + 3 * ε) = (9 / 10 + 4 * ε) := by ring
    rw [heq]; exact this
  obtain ⟨m, L, Pl, hmmax₀, hmMmax, hseq, hPS, hPdisj, hPcover, hPcard, hPdeg⟩ :=
    hvortex E S hn₂ hES hdegv
  have hm₀ : m₀ ≤ m := le_trans (le_max_left _ _) hmmax₀
  have hm₁ : m₁ ≤ m := le_trans (le_max_right _ _) hmmax₀
  have hseq' : PartSeq k (9 / 10 + 2 * ε) (9 / 10 + ε) ε m L Pl E S := by
    have heq : (9 / 10 + ε + ε) = 9 / 10 + 2 * ε := by ring
    rwa [heq] at hseq
  have hPdeg' : ∀ P ∈ restrictParts Pl S, ∀ v ∈ P,
      (9 / 10 + 3 * ε) * (P.card : ℝ) ≤ (edeg (E ∩ cliqueEdges P) v : ℝ) := by
    intro P hP v hv
    have := hPdeg P hP v hv
    have heq : (9 / 10 + ε + 2 * ε) = 9 / 10 + 3 * ε := by ring
    rwa [heq] at this
  -- the reservation
  obtain ⟨A, hAE, hAev, hAsp, habs⟩ := hres E S m L Pl hn₁ hES hdiv hdeg hm₀ hm₁ hmMmax hseq'
    hPS hPdisj hPcover hPcard hPdeg'
  refine ⟨A, m, L, Pl, hAE, hAev, hm₀, ?_, habs⟩
  -- the vortex survives the reservation
  have hdel := PartSeq.sdiff_spread (k := k) (ε := ε) (η := ε) (m := m) (H := A)
    L (9 / 10 + 2 * ε) (9 / 10 + ε) Pl E S hseq' hAsp
  have h1 : (9 / 10 + 2 * ε - ε) = 9 / 10 + ε := by ring
  have h2 : (9 / 10 + ε - ε : ℝ) = 9 / 10 := by ring
  rwa [h1, h2] at hdel

/-- **The dense triangle-decomposition theorem from the nibble and the §8 cells reservation.**

Combining `BKLO.cellsAbsorptionK3_of_cellsAbsorberSpread` with the §11 assembly
`BKLO.triDecompDense_of_nibble_faithful`: the only hypothesis left besides the dense nibble is the
reservation `BKLO.CellsAbsorberSpread`. -/
theorem triDecompDense_of_nibble_cellsAbsorberSpread (hspread : CellsAbsorberSpread)
    (happ : ApproxTriDecompMinDeg (9 / 10)) : TriDecompDense :=
  triDecompDense_of_nibble_faithful (cellsAbsorptionK3_of_cellsAbsorberSpread hspread) happ

end BKLO
