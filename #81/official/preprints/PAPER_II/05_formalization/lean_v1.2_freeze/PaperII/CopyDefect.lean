import PaperII.L1

/-!
# Paper II — copy defect `Δ` and copy gain `Γ` (v1.0.1 observation, §4.2)

Notation for the editorial observation of Paper II §4.2, at the atomic (vertex-copy) level, where
`G_{a→b} = copyVertex G a b`:

* `copyDefect G a b = Φτ(G_{a→b}) + Φτ(G_{b→a}) − 2·Φτ(G)`  (the paper's `Δ_F`);
* `copyGamma  G a b = max{Φτ(G_{a→b}), Φτ(G_{b→a})} − Φτ(G)`  (the paper's `Γ_F`).

Two facts: `Δ ≥ 0` for nonadjacent distinct vertices (this is the ledger L1 vertex-copy inequality
`phiTau_copyVertex_add`), and `Γ ≥ Δ/2` (max ≥ average), unconditionally. This is an *observation*
recording existing content in the paper's notation, not a stability theorem.
-/

open scoped BigOperators

namespace PaperII

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Copy defect `Δ_Φτ(a,b) = Φτ(G_{a→b}) + Φτ(G_{b→a}) − 2·Φτ(G)`. -/
noncomputable def copyDefect (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) : ℝ :=
  phiTau (copyVertex G a b) + phiTau (copyVertex G b a) - 2 * phiTau G

/-- Copy gain `Γ_Φτ(a,b) = max{Φτ(G_{a→b}), Φτ(G_{b→a})} − Φτ(G)`. -/
noncomputable def copyGamma (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) : ℝ :=
  max (phiTau (copyVertex G a b)) (phiTau (copyVertex G b a)) - phiTau G

/-- **Copy defect is nonnegative** for nonadjacent distinct `a, b` (ledger L1). -/
theorem copyDefect_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V}
    (hab : ¬ G.Adj a b) (hne : a ≠ b) : 0 ≤ copyDefect G a b := by
  have h := phiTau_copyVertex_add G (u := b) (v := a)
    (fun hba => hab hba.symm) (fun h => hne h.symm)
  unfold copyDefect
  linarith

/-- **`Γ ≥ Δ/2`** (a maximum is at least the average), for any `a, b`. -/
theorem copyGamma_ge_half_copyDefect (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    copyDefect G a b / 2 ≤ copyGamma G a b := by
  unfold copyDefect copyGamma
  have h1 := le_max_left (phiTau (copyVertex G a b)) (phiTau (copyVertex G b a))
  have h2 := le_max_right (phiTau (copyVertex G a b)) (phiTau (copyVertex G b a))
  linarith

end PaperII
