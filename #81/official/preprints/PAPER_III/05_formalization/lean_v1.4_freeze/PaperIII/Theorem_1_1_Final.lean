/-
# Paper III — FINAL, unconditional assembly

`Theorem_1_1` / `Corollary_1_2` for split graphs, `Φ(G) ≤ n²/6 + C·n`, with **no** remaining
assumptions: the two interfaces `AX1Assumption` and `AX2Assumption` are discharged here from the
two closed ingredients living in the `nibble` package:

* **AX1** — `Nibble.AX1.ax1Statement_holds` (Haxell–Rödl / Yuster fractional–integral gap, closed
  unconditionally via the box-allocation nibble; see `Nibble.AX1Closed`).
* **AX2** — `BKLO.triangle_decomposition_dense` (Barber–Kühn–Lo–Osthus §11 cells route + Dross
  approximate decomposition, closed unconditionally; bridged to `Ax2.TriangleDecomposable` by
  `Ax2.BKLOBridge.triDecomp_iff = Iff.rfl`, then to `HasTriangleDecomposition` by
  `PaperIII.hasTriangleDecomposition_of_ax2`).

Target after this file builds:
`#print axioms PaperIII.Theorem_1_1` = `[propext, Classical.choice, Quot.sound]`.
-/
import PaperIII.Main
import PaperIII.AX2Bridge
import PaperIII.AX1NibbleBridge
import Nibble.AX1Closed
import BKLO.MainDenseUnconditional
import Ax2.PartB.BKLO.Bridge

namespace PaperIII

open SimpleGraph

/-- **AX1, unconditionally.** The fractional–integral triangle-packing gap `τ₃* − ν₃ ≤ ε n²` holds
uniformly, from the closed nibble statement `Nibble.AX1.ax1Statement_holds`.  (Body mirrors the
proven `AX1_from_residual` bridge, sourcing the closed statement instead of a residual hypothesis.) -/
theorem AX1_holds : AX1Assumption := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := Nibble.AX1.ax1Statement_holds ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  have h := hn₀ V G hV
  have hnu : Nibble.YusterE.nu3 G = nu3 G := by
    rw [nu3]
    exact Nibble.YusterE.nu3_eq_trianglePacking_sSup G
  rw [hnu] at h
  simpa using h

/-- **AX2, unconditionally.** Every triangle-divisible graph of min-degree `≥ (0.9 + ε)·n` (for `n`
large) has an exact triangle decomposition, from `BKLO.triangle_decomposition_dense` through the
definitional bridge to `Ax2.TriangleDecomposable` and `hasTriangleDecomposition_of_ax2`. -/
theorem AX2_holds : AX2Assumption := by
  intro ε hε
  obtain ⟨n₀, hmain⟩ := BKLO.triangle_decomposition_dense ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ H _ hcard hdeg hn hδ
  have hdiv : (3 ∣ H.edgeFinset.card ∧ ∀ v, Even (H.degree v)) :=
    ⟨Nat.dvd_of_mod_eq_zero hcard, hdeg⟩
  have hδ' : (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (H.minDegree : ℝ) := by
    convert hδ using 2 <;> norm_num
  have hbklo : BKLO.TriangleDecomposable H := hmain H hn hdiv hδ'
  have hax2 : Ax2.TriangleDecomposable H := (Ax2.BKLOBridge.triDecomp_iff H).mpr hbklo
  exact hasTriangleDecomposition_of_ax2 H hax2

/-- **Theorem 1.1 (Paper III), unconditional.** There is an absolute constant `C` with
`Φ(G) ≤ n²/6 + C·n` for every split graph `G`. -/
theorem Theorem_1_1 :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) :=
  Theorem_1_1_of_AX1_AX2 AX1_holds AX2_holds

/-- **Corollary 1.2 (Paper III), unconditional.** The same bound for the clique-partition number,
`cp(G) ≤ n²/6 + C·n`. -/
theorem Corollary_1_2 :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) :=
  Corollary_1_2_of_AX1_AX2 AX1_holds AX2_holds

end PaperIII
