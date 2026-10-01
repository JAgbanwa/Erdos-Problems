import PaperIV.NearH1Localization
import PaperIV.RootedDefectZeroChordal
import PaperIV.CertifiedOptimumExistence

/-!
# The fixed-`L = 4` localization interface for rooted simplicial defect `s`

This module states, with every model written out explicitly, the critical
interface of the fixed-defect programme, and proves the instance that the
present tree can support.

## The models

* the fractional value is the **certified mixed `K₃/K₄` optimum** `w` of
  `PaperIV.FarRounding.CertifiedFractionalOptimum`; the fractional
  `K₂/K₃/K₄` *partition* value of `G` is then `q₄*(G) = e(G) - w`, which is the
  quantity the far/near dichotomy of this project splits on (it equals
  `PaperIV.VertexCopyGate.F4' G` by `CertifiedF4Bridge.F4'_eq_edge_sub_certified`);
* the near hypothesis is `n²/6 - η·n² ≤ q₄*(G)`;
* the conclusion is a **real clique** `A` of `G` with `| |A| - n/3 | ≤ ε·n`
  and `D_A + e(G - A) ≤ ε·n²`, where
  `D_A = PaperIV.RootVocab.missingIncidences G A` is the number of missing
  root–outside incidences and `e(G - A) = (PaperIV.RootVocab.outsideEdges G A).card`
  is the number of edges with both ends outside `A`.

## What is proved here

`fixedL4LocalizationAt_defectZero` : `FixedL4LocalizationAt 0 (1/100)`.  The
defect-zero class is exactly the chordal class
(`PaperIV.RootedDefectZero.rootedDefect_zero_iff_isChordal`), and the near
structural package of `PaperIV.NearH1StructureWitness` delivers a regularized
*real* clique root whose size window and mass envelope give the two bounds with
the explicit constant `ε = 1/100` and `η = PaperIV.NearH1Calibration.eta`.

## What is *not* proved here, and is not hidden anywhere

* `FixedL4Localization 0` — the same statement **for every** `ε > 0` — is not
  proved *in this module*; it is proved in `PaperIV.FixedL4LocalizationAllEps`
  (`fixedL4Localization_defectZero`) from
  `IntegralStability.chordal_linear_stability_sixteen` with `η ≍ ε²`.
* `FixedL4LocalizationAt s ε` for any `s ≥ 1` is open.  It does **not** follow
  from the published bounded-defect theorem for unrestricted clique orders: the
  fractional localization used there selects a cutoff `L = L(ε)` that may exceed
  `4`, and a large value of the `L = 4` functional `q₄*` does not bound `q_L*`
  from below for `L > 4`.
* Consequently nothing in this module is used to claim the fixed-size target for
  `s ≥ 1`; the only unconditional fixed-size target proved in this tree is the
  defect-zero one, `PaperIV.DefectZeroTarget`.
-/

namespace PaperIV.FixedL4

open Finset
open PaperIV.FarRounding
open PaperIV.RootedSimplicialDefect
open PaperIV.RootVocab

variable {n : ℕ}

/-- The literal localization output: a **real clique** of `G` of size `n/3` up to
`ε·n`, with at most `ε·n²` missing cross incidences plus outside edges. -/
structure LocalizedClique (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (eps : ℚ) where
  /-- the located clique -/
  core : Finset (Fin n)
  /-- it is a clique of `G`, not of an approximating graph -/
  isClique : G.IsClique (core : Set (Fin n))
  /-- its order is `n/3` up to `ε n` -/
  size_window : |(core.card : ℚ) - (n : ℚ) / 3| ≤ eps * (n : ℚ)
  /-- missing cross incidences plus edges outside the clique are at most `ε n²` -/
  mass_small : ((missingIncidences G core : ℚ) + ((outsideEdges G core).card : ℚ)) ≤
    eps * (n : ℚ) ^ 2

/-- **Fixed-`L = 4` localization at defect `s` and precision `ε`.**  For some
quadratic margin `η > 0` and all large orders, a graph of rooted simplicial
defect `s` whose certified fractional `K₂/K₃/K₄` partition value is within
`η n²` of `n²/6` carries a localized real clique. -/
def FixedL4LocalizationAt (s : ℕ) (eps : ℚ) : Prop :=
  ∃ eta : ℚ, 0 < eta ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], RootedDefectAt G s →
      ∀ w : ℚ, CertifiedFractionalOptimum G w →
        (n : ℚ) ^ 2 / 6 - eta * (n : ℚ) ^ 2 ≤ (G.edgeFinset.card : ℚ) - w →
          Nonempty (LocalizedClique G eps)

/-- The full interface: localization at defect `s` for **every** precision. -/
def FixedL4Localization (s : ℕ) : Prop :=
  ∀ eps : ℚ, 0 < eps → FixedL4LocalizationAt s eps

/-! ## Elementary structure of the interface -/

/-- Localization is monotone in the precision. -/
theorem fixedL4LocalizationAt_mono_eps {s : ℕ} {eps eps' : ℚ} (h : eps ≤ eps')
    (hloc : FixedL4LocalizationAt s eps) :
    FixedL4LocalizationAt s eps' := by
  obtain ⟨eta, heta, N, hN⟩ := hloc
  refine ⟨eta, heta, N, ?_⟩
  intro n hn' G _ hdef w hw hnear
  obtain ⟨L⟩ := hN n hn' G hdef w hw hnear
  have hn0 : (0 : ℚ) ≤ (n : ℚ) := by positivity
  refine ⟨⟨L.core, L.isClique, ?_, ?_⟩⟩
  · exact le_trans L.size_window (by nlinarith [abs_nonneg ((L.core.card : ℚ) - (n : ℚ) / 3)])
  · exact le_trans L.mass_small (by nlinarith [sq_nonneg ((n : ℚ))])

/-- A smaller defect parameter is a stronger hypothesis on the graph, so
localization at defect `t` implies localization at every defect `s ≤ t`. -/
theorem fixedL4LocalizationAt_antitone_defect {s t : ℕ} (hst : s ≤ t) {eps : ℚ}
    (hloc : FixedL4LocalizationAt t eps) : FixedL4LocalizationAt s eps := by
  obtain ⟨eta, heta, N, hN⟩ := hloc
  refine ⟨eta, heta, N, ?_⟩
  intro n hn G _ hdef w hw hnear
  exact hN n hn G (rootedDefectAt_mono G hst hdef) w hw hnear

/-! ## The proved instance: defect zero, explicit precision `1/100` -/

/-- **Defect-zero localization.**  Every chordal (equivalently, rooted defect
`0`) graph of order at least `4·10¹²` whose certified fractional partition value
is within `η n²` of `n²/6` contains a real clique of order `n/3 ± n/100` whose
missing cross incidences and outside edges total at most `n²/100`. -/
theorem exists_localizedClique_of_chordal_near {n : ℕ} (hn : 4 * 10 ^ 12 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hchordal : PaperIV.IsChordal G)
    {w : ℚ} (hw : CertifiedFractionalOptimum G w)
    (hnear : (n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2 ≤
      (G.edgeFinset.card : ℚ) - w) :
    Nonempty (LocalizedClique G (1 / 100)) := by
  classical
  have hnear' : ¬ ((G.edgeFinset.card : ℚ) - w <
      (n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2) := by
    exact not_lt.2 hnear
  obtain ⟨W⟩ :=
    PaperIV.NearH1Localization.exists_nearStructureWitness_of_nearRegime hn G hchordal hw hnear'
  set R := W.regularized with hR
  set A : Finset (Fin n) := R.root with hA
  have hcard : Fintype.card (Fin n) = n := by simp
  -- vertex counts
  have houtside : (outsideVertices A).card = n - A.card := by
    have hdef : outsideVertices A = Finset.univ \ A := rfl
    rw [hdef, Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ, hcard]
  have hAle : A.card ≤ n := by
    simpa [hcard] using Finset.card_le_univ A
  have hrefle : R.reference.card ≤ n := by
    simpa [hcard] using Finset.card_le_univ R.reference
  -- the size window, from the calibrated ratios of the regularized root
  have hlow : 98 * n ≤ 300 * A.card := by
    have h1 : 33 * Fintype.card (Fin n) ≤ 100 * R.reference.card := R.reference_order_lower
    have h2 : 99 * R.reference.card ≤ 100 * A.card := R.root_lower_ratio
    rw [hcard] at h1
    omega
  have hhigh : 300 * A.card ≤ 101 * n := by
    have h2 : 99 * R.reference.card ≤ 100 * A.card := R.root_lower_ratio
    have h4 : 48 * (2 * A.card - (outsideVertices A).card) ≤ R.reference.card := R.slack_ratio
    rw [houtside] at h4
    omega
  -- the mass envelope
  have hmass : 2000 * (missingIncidences G A + 2 * (outsideEdges G A).card) ≤
      11 * R.reference.card ^ 2 := R.mass_envelope
  refine ⟨⟨A, R.isClique, ?_, ?_⟩⟩
  · have hlowQ : 98 * (n : ℚ) ≤ 300 * (A.card : ℚ) := by exact_mod_cast hlow
    have hhighQ : 300 * (A.card : ℚ) ≤ 101 * (n : ℚ) := by exact_mod_cast hhigh
    rw [abs_le]
    constructor <;> linarith
  · have hrefQ : (R.reference.card : ℚ) ≤ (n : ℚ) := by exact_mod_cast hrefle
    have href0 : (0 : ℚ) ≤ (R.reference.card : ℚ) := by positivity
    have hmassQ : 2000 * ((missingIncidences G A : ℚ) + 2 * ((outsideEdges G A).card : ℚ)) ≤
        11 * (R.reference.card : ℚ) ^ 2 := by exact_mod_cast hmass
    have hout0 : (0 : ℚ) ≤ ((outsideEdges G A).card : ℚ) := by positivity
    nlinarith

/-- **Defect-zero localization, packaged.**  `FixedL4LocalizationAt 0 (1/100)`
holds with the calibrated margin `η = PaperIV.NearH1Calibration.eta`. -/
theorem fixedL4LocalizationAt_defectZero :
    FixedL4LocalizationAt 0 (1 / 100) := by
  refine ⟨PaperIV.NearH1Calibration.eta, by norm_num [PaperIV.NearH1Calibration.eta],
    4 * 10 ^ 12, ?_⟩
  intro n hn G _ hdef w hw hnear
  exact exists_localizedClique_of_chordal_near hn G
    (PaperIV.RootedDefectZero.isChordal_of_rootedDefect_zero hdef) hw hnear

end PaperIV.FixedL4
