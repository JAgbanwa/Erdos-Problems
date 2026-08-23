/-
# hNib discharged: the dense max-degree nibble input is unconditionally true

`Nibble.denseTriNibbleMaxDeg_holds` (Nibble/DenseTriNibbleMaxDeg.lean) proves — from the real packing
engine `Nibble.nibbleTheoremMostCeil_holds` — that every dense graph (`δ(G) ≥ (9/10)|V|`) has an
edge-disjoint triangle family whose leftover has maximum degree `≤ η|V|`.  Its output shape is that
of `BKLO.IsApproxTriangleDecompMaxDeg`, modulo `Nibble.edgesOf = BKLO.cliqueEdges`.

This file records that identification and discharges `BKLO.FracToApproxMaxDegDense` — the honest,
true form of Input 2′ (the general `BKLO.FracToApproxMaxDeg` is false on the `K₄`-book, but the AX2
chain only ever applies it to dense graphs, which is exactly this form).

No `sorry`; axiom-clean.
-/
import Nibble.DenseTriNibbleMaxDeg
import BKLO.NibbleMaxDegDense

open Finset

namespace Ax2.BKLOBridge

variable {V : Type*} [DecidableEq V]

/-- `Nibble.edgesOf` and `BKLO.cliqueEdges` are the same edge set. -/
theorem edgesOf_eq_cliqueEdges (t : Finset V) : Nibble.edgesOf t = BKLO.cliqueEdges t := by
  ext e
  rw [Nibble.mem_edgesOf, BKLO.mem_cliqueEdgesV]
  exact And.comm

/-- `BKLO.FracToApproxMaxDegDense` holds, from `Nibble.denseTriNibbleMaxDeg_holds`. -/
theorem fracToApproxMaxDegDense_holds : BKLO.FracToApproxMaxDegDense := by
  intro η hη
  obtain ⟨n₀, h⟩ := Nibble.denseTriNibbleMaxDeg_holds η hη
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hn _hfrac hδ
  -- density: (9/10)|V| ≤ δ(G)  (real)  →  9|V| ≤ 10 δ(G)  (nat)
  have hδ' : 9 * Fintype.card V ≤ 10 * G.minDegree := by
    have h10 : (9 : ℝ) * (Fintype.card V : ℝ) ≤ 10 * (G.minDegree : ℝ) := by nlinarith [hδ]
    exact_mod_cast h10
  obtain ⟨P, htri, hpair, hdeg⟩ := h G hn hδ'
  -- rewrite `edgesOf` to `cliqueEdges` throughout
  have hbi : P.biUnion Nibble.triEdges = P.biUnion BKLO.cliqueEdges :=
    Finset.biUnion_congr rfl (fun t _ => edgesOf_eq_cliqueEdges t)
  refine ⟨P, htri, ?_, ?_⟩
  · -- pairwise-disjoint `cliqueEdges`, from the `Set.Pairwise` disjointness of `triEdges`
    intro s hs t ht hst
    have hd := hpair hs ht hst
    simpa only [Nibble.triEdges, edgesOf_eq_cliqueEdges] using hd
  · -- per-vertex leftover bound, with the leftover set rewritten
    intro v
    have hv := hdeg v
    rwa [hbi] at hv

end Ax2.BKLOBridge
