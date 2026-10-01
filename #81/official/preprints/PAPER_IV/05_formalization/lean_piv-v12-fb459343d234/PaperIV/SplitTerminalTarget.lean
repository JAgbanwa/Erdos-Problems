import PaperIV.SplitTerminalNear
import PaperIV.SplitBaselineTarget
import PaperIV.PhysicalToCliquePartition

/-!
# The complete-split terminal meets the Erdős #81 target unconditionally

`PaperIV.SplitTriangleFactorHighHost` constructs, for a complete split graph with an
*even* core of size `k = 2r+2` and at least `k - 1` hosts, a literal `K3` packing whose
physical completion is an exact partition with exactly

```
  k * (N - k) - C(k,2) = splitBaseline N k        (N = k + h)
```

pieces, and `PaperIV.SplitBaselineTarget.splitBaseline_le_targetSize` shows that **no**
split baseline can exceed the integral target `targetSize N = ⌊N(N+1)/6⌋`.

This module composes the two facts.  The result is unconditional and non-vacuous: the
extremal near-regime family (core `≈ n/3`, hosts `≈ 2n/3`) satisfies the hypotheses, and
the conclusion is the literal conclusion asked for by the near branch of the far/near
assembly — an exact clique partition of order at most four with at most `targetSize n`
pieces.

Nothing here is assumed: the packing, the exact partition, and the count all come from
the already proved literal constructions.
-/

namespace PaperIV.SplitTerminalTarget

open Finset PaperIV.Model PaperIV.PhysicalCompletion PaperIV.SplitUniformIncidence
open PaperIV.SplitTriangleFactor PaperIV.SplitTriangleFactorHighHost

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Monotonicity of the integral target -/

theorem targetSize_mono {m n : ℕ} (h : m ≤ n) :
    PaperIV.targetSize m ≤ PaperIV.targetSize n := by
  unfold PaperIV.targetSize
  exact Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

/-- Two disjoint vertex sets cannot together exceed the ambient vertex count. -/
theorem card_add_card_le_card_univ {Core Hosts : Finset V} (hd : Disjoint Core Hosts) :
    Core.card + Hosts.card ≤ Fintype.card V := by
  rw [← Finset.card_union_of_disjoint hd]
  simpa using Finset.card_le_univ (Core ∪ Hosts)

/-! ## The split baseline count is an integer below the target -/

/-- The exact even-core high-host completion count `k(N-k) - C(k,2)` never exceeds the
integral target `targetSize N`. -/
theorem split_count_le_targetSize {r h N : ℕ} (hkh : 2 * r + 1 ≤ h) (hN : N = 2 * r + 2 + h) :
    (2 * r + 2) * (N - (2 * r + 2)) - (2 * r + 2).choose 2 ≤ PaperIV.targetSize N := by
  have hNk : N - (2 * r + 2) = h := by omega
  have hchoose : (2 * r + 2).choose 2 = (r + 1) * (2 * r + 1) := choose_two_even r
  have hle : (r + 1) * (2 * r + 1) ≤ (2 * r + 2) * h := by
    calc (r + 1) * (2 * r + 1) ≤ (2 * r + 2) * (2 * r + 1) := by
          exact Nat.mul_le_mul_right _ (by omega)
      _ ≤ (2 * r + 2) * h := Nat.mul_le_mul_left _ hkh
  set m : ℕ := (2 * r + 2) * h - (r + 1) * (2 * r + 1) with hm
  have hmadd : m + (r + 1) * (2 * r + 1) = (2 * r + 2) * h := by omega
  have hSq : ((m : ℤ) : ℚ) = PaperIV.splitBaseline (N : ℚ) ((2 * r + 2 : ℕ) : ℚ) := by
    have hmQ : (m : ℚ) + ((r : ℚ) + 1) * (2 * (r : ℚ) + 1) = (2 * (r : ℚ) + 2) * (h : ℚ) := by
      exact_mod_cast congrArg (fun x : ℕ => (x : ℚ)) hmadd
    have hNQ : (N : ℚ) = 2 * (r : ℚ) + 2 + (h : ℚ) := by
      rw [hN]; push_cast; ring
    rw [PaperIV.splitBaseline, hNQ]
    push_cast
    linarith
  have hZ : (m : ℤ) ≤ (PaperIV.targetSize N : ℤ) :=
    PaperIV.SplitBaselineTarget.splitBaseline_le_targetSize hSq
  have hmle : m ≤ PaperIV.targetSize N := by exact_mod_cast hZ
  rw [hNk, hchoose]
  exact hmle

/-! ## The unconditional even-core terminal target theorem -/

/-- **Even core, host-rich complete split graph: the target is met.**  For every complete
split graph whose core has even size `k = 2r+2` and which has at least `k-1` hosts, the
literal round-robin terminal is an exact physical partition with at most
`targetSize (card V)` pieces. -/
theorem exists_exactPartition_card_le_targetSize_even {Core Hosts : Finset V}
    (hd : Disjoint Core Hosts) {r : ℕ} (hk : Core.card = 2 * r + 2)
    (hh : 2 * r + 1 ≤ Hosts.card) :
    ∃ P : Finset (Finset V),
      IsK34Packing (splitGraph Core Hosts) P ∧
      IsExactPartition (splitGraph Core Hosts) (completion (splitGraph Core Hosts) P) ∧
      (completion (splitGraph Core Hosts) P).card ≤ PaperIV.targetSize (Fintype.card V) := by
  obtain ⟨P, hK34, hpart, hcount⟩ :=
    exists_split_high_host_baseline hd hk hh (N := Core.card + Hosts.card) rfl
  refine ⟨P, hK34, hpart, ?_⟩
  rw [hcount]
  have harith : Core.card * (Core.card + Hosts.card - Core.card) - Core.card.choose 2
      ≤ PaperIV.targetSize (Core.card + Hosts.card) := by
    rw [hk]
    exact split_count_le_targetSize (r := r) hh rfl
  exact harith.trans (targetSize_mono (card_add_card_le_card_univ hd))

/-- The same statement in the language of the far/near assembly: an order `≤ 4` clique
partition of the complete split graph with at most `targetSize (card V)` pieces. -/
theorem exists_cliquePartition_le_targetSize_even {Core Hosts : Finset V}
    (hd : Disjoint Core Hosts) {r : ℕ} (hk : Core.card = 2 * r + 2)
    (hh : 2 * r + 1 ≤ Hosts.card) :
    ∃ Q : PaperIV.FarRounding.CliquePartition (splitGraph Core Hosts),
      Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize (Fintype.card V) := by
  obtain ⟨P, -, hpart, hcount⟩ := exists_exactPartition_card_le_targetSize_even hd hk hh
  exact PaperIV.PhysicalToCliquePartition.exists_cliquePartition_of_exactPartition_card_le
    hpart hcount

end PaperIV.SplitTerminalTarget

