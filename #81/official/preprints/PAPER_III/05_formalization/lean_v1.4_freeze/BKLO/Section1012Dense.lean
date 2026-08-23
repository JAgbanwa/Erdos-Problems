/-
# BKLO Lemma 10.12 for `r = 2` (repaired) in the dense regime — the reduction to the hard case

`BKLO.Lemma1012K3'` (`BKLO/Section1012Repaired.lean`) quantifies over every `k` and every
`ε ≥ 1/k`.  In the Erdős #81 dense regime `9/10 ≤ δ ≤ 1` a large part of that range is *vacuous*:
the hypothesis `IsKDeltaPartition k (δ + 3ε) P (E \ G₀) S` forces `δ + 3ε ≤ 1`, because a degree
into a part never exceeds the size of the part.  Combined with the restored hierarchy hypothesis
`1/k ≤ ε` this kills every `k` with `k < 3/(1 - δ)`; for `δ ≥ 9/10` that is every `k ≤ 30`.

This file isolates that reduction, `sorry`-free:

* `BKLO.Lemma1012K3'At` — the statement of `Lemma1012K3'` at one pair `(k, ε)`;
* `BKLO.lemma1012K3'At_of_one_lt` — `Lemma1012K3'At δ k ε` holds vacuously when `1 < δ + 3ε`;
* `BKLO.lemma1012K3'_of_hard_case` — hence `Lemma1012K3' δ` follows from its restriction to the
  *hard case* `30 ≤ k`, `1/k ≤ ε` and `δ + 3ε ≤ 1`.
-/
import BKLO.Section1012Repaired

open Finset

namespace BKLO

/-- The statement of `BKLO.Lemma1012K3'` at one pair `(k, ε)`. -/
def Lemma1012K3'At (δ : ℝ) (k : ℕ) (ε : ℝ) : Prop :=
  ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E G₀ : Finset (Sym2 V)) (S : Finset V)
      (P : Finset (Finset V)),
      n₀ ≤ S.card → (∀ e ∈ E, ¬ e.IsDiag) → E ⊆ cliqueEdges S → EvenDegrees E →
      G₀ ⊆ insideParts E P →
      IsKDeltaPartition k (δ + 3 * ε) P (E \ G₀) S →
      ∃ H : Finset (Sym2 V), H ⊆ insideParts E P \ G₀ ∧
        TriDecomp (crossParts E P ∪ H) ∧
        ∀ v : V, (edeg H v : ℝ) ≤ ε * (S.card : ℝ) / (2 * (k : ℝ) ^ 2)

/-- `Lemma1012K3' δ` is exactly the conjunction of its instances `Lemma1012K3'At δ k ε`. -/
theorem lemma1012K3'_iff (δ : ℝ) :
    Lemma1012K3' δ ↔
      ∀ (k : ℕ) (ε : ℝ), 0 < k → 0 < ε → 1 / (k : ℝ) ≤ ε → Lemma1012K3'At δ k ε :=
  Iff.rfl

/-- **The vacuous range.**  A degree into a part `W` is at most `|W|`, so a `(k, d)`-partition with
`d > 1` cannot exist once the parts are nonempty.  Hence `Lemma1012K3'At δ k ε` holds trivially
whenever `1 < δ + 3ε`. -/
theorem lemma1012K3'At_of_one_lt {δ ε : ℝ} {k : ℕ} (hk : 0 < k) (h : 1 < δ + 3 * ε) :
    Lemma1012K3'At δ k ε := by
  refine ⟨k, ?_⟩
  intro V _ E G₀ S P hcard _ _ _ _ hpart
  exfalso
  obtain ⟨heq, hdeg⟩ := hpart
  have hPne : P.Nonempty := by
    rw [← Finset.card_pos, heq.card_parts]; exact hk
  obtain ⟨W, hW⟩ := hPne
  have hWpos : 0 < W.card := by
    have h1 : 1 ≤ S.card / k := Nat.one_le_div_iff hk |>.2 hcard
    exact lt_of_lt_of_le Nat.zero_lt_one (le_trans h1 (heq.size_lower W hW))
  obtain ⟨x, hx⟩ := Finset.card_pos.1 hWpos
  have hxS : x ∈ S := heq.subset_of_mem hW hx
  have h1 := hdeg x hxS W hW
  have h2 : (degTo (E \ G₀) x W : ℝ) ≤ (W.card : ℝ) := by
    exact_mod_cast degTo_le_card (E \ G₀) x W
  have hWR : (0 : ℝ) < (W.card : ℝ) := by exact_mod_cast hWpos
  nlinarith [h1, h2, hWR]

/-- **Reduction of the repaired Lemma 10.12 to its hard case.**  In the dense regime
`9/10 ≤ δ ≤ 1` it suffices to prove `Lemma1012K3'At δ k ε` when `30 ≤ k`, `1/k ≤ ε` and
`δ + 3ε ≤ 1`: every other pair `(k, ε)` allowed by `Lemma1012K3'` is vacuous. -/
theorem lemma1012K3'_of_hard_case {δ : ℝ} (hδ : (9 : ℝ) / 10 ≤ δ)
    (hard : ∀ (k : ℕ) (ε : ℝ), 30 ≤ k → 0 < ε → 1 / (k : ℝ) ≤ ε → δ + 3 * ε ≤ 1 →
      Lemma1012K3'At δ k ε) :
    Lemma1012K3' δ := by
  intro k ε hk hε hkε
  by_cases hle : δ + 3 * ε ≤ 1
  · refine hard k ε ?_ hε hkε hle
    -- `1/k ≤ ε` and `δ + 3ε ≤ 1` with `δ ≥ 9/10` force `k ≥ 30`
    by_contra hk30
    push_neg at hk30
    have hkR : (k : ℝ) < 30 := by exact_mod_cast hk30
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have h1 : 1 / (30 : ℝ) < 1 / (k : ℝ) := by
      apply one_div_lt_one_div_of_lt hkpos hkR
    linarith
  · exact lemma1012K3'At_of_one_lt hk (lt_of_not_ge hle)

end BKLO
