import PaperIV.ChordalCoreMissing
import PaperIV.RootRegularizationBridge

/-!
# From near localization to an RD09-ready root

This module composes the chordal-core calibration with literal root
regularization.  It removes the previous mismatch between rational normalized
bounds and the denominator-cleared natural inequalities used by the physical
constructor.
-/

namespace PaperIV.NearH1CalibratedRoot

open PaperIV.RootVocab

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_regularizedRoot_of_split_comparator
    (G S : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel S.Adj]
    (hchordal : PaperIV.IsChordal G) (C : Finset V) (hC : C.Nonempty)
    (hS : ∀ x y, S.Adj x y ↔
      (PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C)).Adj x y)
    {delta residual : ℚ}
    (hn : 2 * (10 : ℚ) ^ 13 ≤ (Fintype.card V : ℚ))
    (hdelta : delta ≤ (PaperIV.NearH1Calibration.eta +
      6 * PaperIV.NearH1Calibration.eps) * (Fintype.card V : ℚ) ^ 2 +
      (Fintype.card V : ℚ) / 6 + 1 / 24)
    (hres : residual ^ 2 ≤ 24 * delta)
    (hresDef : residual = 6 * (C.card : ℚ) -
      2 * (Fintype.card V : ℚ) - 1)
    (hedit : (PaperIV.EditMetric.editDist G.edgeFinset S.edgeFinset : ℚ) ≤
      PaperIV.NearH1Calibration.eps * (Fintype.card V : ℚ) ^ 2) :
    Nonempty (PaperIV.NearH1RootRegularization.RegularizedRoot G) := by
  classical
  obtain ⟨P, -, hP, -, -, -, -,
      hbalUpperQ, hbalLowerQ, hpQ, hdefectQ⟩ :=
    PaperIV.ChordalCoreMissing.exists_core_clique_with_calibration
      G S hchordal C hC hS hn hdelta hres hresDef hedit
  have hp : 1024 ≤ P.card := by
    exact_mod_cast hpQ
  have hPcard : P.card ≤ Fintype.card V := by
    simpa using Finset.card_le_univ P
  have houtQ : ((outsideVertices P).card : ℚ) =
      (Fintype.card V : ℚ) - (P.card : ℚ) := by
    rw [card_outsideVertices, Nat.cast_sub hPcard]
  have hbalanceUpperQ :
      64 * ((outsideVertices P).card : ℚ) ≤ 129 * (P.card : ℚ) := by
    rw [houtQ]
    linarith
  have hbalanceUpper :
      64 * (outsideVertices P).card ≤ 129 * P.card := by
    exact_mod_cast hbalanceUpperQ
  -- `hdefectQ` ya viene en el mismo vocabulario en el que esta enunciado el puente: no hay
  -- nada que traducir aqui.  La traduccion ocurre una sola vez, dentro de
  -- `exists_regularizedRoot_engineFree`.
  have hdefectQ' :
      (65536 : ℚ) *
          (((outsideEdges G P).card + missingIncidences G P : ℕ) : ℚ) ≤
        (P.card : ℚ) * (P.card : ℚ) := by
    calc
      (65536 : ℚ) *
          (((outsideEdges G P).card + missingIncidences G P : ℕ) : ℚ) ≤
          65536 * ((P.card : ℚ) ^ 2 / 65536) :=
        mul_le_mul_of_nonneg_left hdefectQ (by norm_num)
      _ = (P.card : ℚ) * (P.card : ℚ) := by
        ring
  have hdefect :
      65536 * ((outsideEdges G P).card + missingIncidences G P) ≤
        P.card * P.card := by
    exact_mod_cast hdefectQ'
  have hbalanceLower :
      127 * P.card ≤ 64 * (outsideVertices P).card := by
    have hbalanceLowerQ :
        (127 : ℚ) * P.card ≤ 64 * (outsideVertices P).card := by
      rw [houtQ]
      linarith
    exact_mod_cast hbalanceLowerQ
  exact PaperIV.RootRegularizationBridge.exists_regularizedRoot_engineFree
    hchordal P hP hp hbalanceLower hbalanceUpper hdefect

end PaperIV.NearH1CalibratedRoot
