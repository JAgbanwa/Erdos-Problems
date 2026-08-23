/-
# BKLO Lemma 10.12 for `r = 2`, repaired statement, and the fully-repaired §10 assembly

`BKLO.Lemma1012K3` (Section10Iteration.lean) is FALSE as transcribed (`BKLO.not_lemma1012K3`): it drops
the paper's hierarchy `1/k ≪ ε` for Lemma 10.12, and is falsified at `k = 2`.  This file restores the
missing hypothesis as `BKLO.Lemma1012K3'` (`Lemma1012K3` with `1/k ≤ ε` added) and shows the repair is
still enough for the §10 iteration and assembly:

* `BKLO.lemma_10_13_K3'` — Lemma 10.13 from the repaired `Lemma1012K3'` (the use-site applies Lemma
  10.12 with `ε/6`, and `1/k ≤ ε/8 ≤ ε/6` is exactly what `Lemma1012K3'` asks for);
* `BKLO.section10_K3_repaired'` — the fully-repaired §10 assembly, taking `ApproxTriDecompMinDeg δ`
  (the `δ_F^η` input, which BKLO's `lemma106K3Res_of_inputs` turns into the repaired Lemma 10.6) and
  the repaired `Lemma1012K3'`, with NO false hypothesis (`TransformStepK3` nor `Lemma1012K3`).

`Lemma1012K3'` itself is NOT proved here: it remains the deep §9-parity / §10.2 nibble input of the
paper.  Everything here is `sorry`-free.
-/
import BKLO.Section10Faithful

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-- **BKLO Lemma 10.12 for `r = 2`, repaired.**  `BKLO.Lemma1012K3` with the paper's missing
hierarchy hypothesis `1/k ≤ ε` restored — the condition whose omission `BKLO.not_lemma1012K3`
exploits at `k = 2`. -/
def Lemma1012K3' (δ : ℝ) : Prop :=
  ∀ (k : ℕ) (ε : ℝ), 0 < k → 0 < ε → 1 / (k : ℝ) ≤ ε → ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E G₀ : Finset (Sym2 V)) (S : Finset V)
      (P : Finset (Finset V)),
      n₀ ≤ S.card → (∀ e ∈ E, ¬ e.IsDiag) → E ⊆ cliqueEdges S → EvenDegrees E →
      G₀ ⊆ insideParts E P →
      IsKDeltaPartition k (δ + 3 * ε) P (E \ G₀) S →
      ∃ H : Finset (Sym2 V), H ⊆ insideParts E P \ G₀ ∧
        TriDecomp (crossParts E P ∪ H) ∧
        ∀ v : V, (edeg H v : ℝ) ≤ ε * (S.card : ℝ) / (2 * (k : ℝ) ^ 2)

/-- **BKLO Lemma 10.13 for `r = 2`, from the repaired `Lemma1012K3'`.**  Identical to
`BKLO.lemma_10_13_K3`, but consuming the repaired hypothesis: the iteration applies Lemma 10.12 with
`ε/6`, and `1/k ≤ ε/8 ≤ ε/6` supplies the restored hierarchy condition. -/
theorem lemma_10_13_K3' {δ ε : ℝ} {k : ℕ} (hk : 0 < k) (hε : 0 < ε) (hkε : 1 / (k : ℝ) ≤ ε / 8)
    (h12 : Lemma1012K3' δ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ {V : Type} [DecidableEq V] (L : List (Finset (Finset V))) (Pl : Finset (Finset V))
        (E : Finset (Sym2 V)) (S : Finset V),
        (∀ e ∈ E, ¬ e.IsDiag) → E ⊆ cliqueEdges S → EvenDegrees E →
        PartSeq k (δ + ε) δ ε m L Pl E S →
        ∃ Hstar : Finset (Sym2 V), Hstar ⊆ insideParts E (restrictParts Pl S) ∧
          TriDecomp (E \ Hstar) := by
  obtain ⟨n₀, hn₀⟩ := h12 k (ε / 6) hk (by linarith) (le_trans hkε (by linarith))
  obtain ⟨N, hNn₀, hgap⟩ := exists_iteration_threshold k ε hk hε hkε n₀
  refine ⟨N + 1, fun m hm V _ L Pl E S hloop hES hev hseq => ?_⟩
  refine lemma_10_13_aux (N := N) hk hε ?_ hgap hm L Pl E S hloop hES hev hseq
  intro E' G₀ S' P hcard hloop' hES' hev' hG₀ hpart
  exact hn₀ E' G₀ S' P (le_trans hNn₀ hcard) hloop' hES' hev' hG₀ hpart

/-- **The two halves of BKLO §10 for `r = 2`, fully repaired.**  Same conclusion as
`BKLO.section10_K3` / `BKLO.section10_K3_repaired`, but with BOTH false hypotheses removed:
`TransformStepK3 δ` is replaced by the `δ_F^η` input `ApproxTriDecompMinDeg δ` (via
`lemma106K3Res_of_inputs`), and the false `Lemma1012K3 δ` is replaced by the repaired
`Lemma1012K3' δ` (via `lemma_10_13_K3'`). -/
theorem section10_K3_repaired' {δ ε : ℝ} {k : ℕ} (hδ : (2 : ℝ) / 3 ≤ δ) (hδ1 : δ ≤ 1)
    (hk : 0 < k) (hε : 0 < ε) (hkε : 1 / (k : ℝ) ≤ ε / 8)
    (h103 : Lemma103K3) (happ : ApproxTriDecompMinDeg δ) (h12 : Lemma1012K3' δ) :
    Lemma106K3Res δ ∧
      ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
        ∀ {V : Type} [DecidableEq V] (L : List (Finset (Finset V))) (Pl : Finset (Finset V))
          (E : Finset (Sym2 V)) (S : Finset V),
          (∀ e ∈ E, ¬ e.IsDiag) → E ⊆ cliqueEdges S → EvenDegrees E →
          PartSeq k (δ + ε) δ ε m L Pl E S →
          ∃ Hstar : Finset (Sym2 V), Hstar ⊆ insideParts E (restrictParts Pl S) ∧
            TriDecomp (E \ Hstar) :=
  ⟨lemma106K3Res_of_inputs hδ hδ1 happ h103, lemma_10_13_K3' hk hε hkε h12⟩

end BKLO
