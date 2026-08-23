/-
# Nibble — the coupled block-allocation residual at **near-uniform cluster densities**

`Nibble.AX1.BlockCoverResidualCoupled` (`Nibble.CoreGapBlockCoverCoupled`) is the last atom of the
AX1 route: it asks, inside a regular equipartition, for a family of block sub-triples with pairwise
disjoint vertex-pair rectangles whose covering sum reaches the fractional optimum of the
regularity-reduced graph.

This file proves that residual in the **near-uniform regime**: when every pair of distinct clusters
has edge density either `0` or a value in a window `[d, D]` with `D ≤ (1 + ρ)·d`, for a tolerance
`ρ > 0` that the residual names itself.  This is the regime of a blow-up — the case the equal-density
sanity check `Nibble.AX1.nu3_blowUp_ge_general` describes — together with a `Θ(ε)` window around it.

In that regime the prescribed block sizes `τ·(opposite density)` of `Nibble.AX1.IsGridSubTriple` all
lie between `L/2` and `L` for a single slot length `L`, so each cluster can be cut into `p` equal
slots, a block is an initial segment of a slot of the exactly prescribed size, and a member is a
triangle of the `p`-blow-up of the cluster graph.  The construction is:

* cut every cluster into `p = ⌊mmin/L⌋` slots of size `L = ⌈2α·mmax⌉` with `Nibble.AX1.blockOf`, and
  take inside each slot the initial block of the prescribed size `⌈τ·density⌉`;
* take the members from an edge-disjoint triangle family of the blow-up of the cluster graph,
  supplied by `Nibble.AX1.exists_edgeDisjoint_triangles_blowUp` — the **weighted nibble with slack**
  (`Nibble.fracNibble_withSlack`) applied to the lifted fractional packing, whose threshold `q₀`
  depends on the accuracy alone and not on the number of clusters;
* two members share at most one slot, so their rectangles are disjoint
  (`Nibble.AX1.tripleRect_disjoint_of_cells_inter`);
* the covering sum is compared with `ν₃*` of the regularity-reduced graph through the cluster LP
  aggregation `Nibble.AX1.nu3star_regularityReduced_le_host`.

* `Nibble.AX1.NearUniformClusterDensities` — the density hypothesis;
* `Nibble.AX1.BlockCoverResidualCoupledNearUniform` — the residual restricted to it;
* `Nibble.AX1.blockCoverResidualCoupledNearUniform_holds` — the proof.

The general (widely varying density) case is *not* covered: there the prescribed block size in a
cluster depends on the density of the *opposite* pair, so the cells of the cluster-pair grids are
rectangles of many different shapes, coherently linked along the shared cluster axes, and the
packing is no longer the triangle hypergraph of a blow-up.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapBlockCoverCoupled
import Nibble.CoreGapClusterHost
import Nibble.BlowUpFracNibble
import Nibble.BlockCoverUniformAux
import Nibble.BlockSplit
import Mathlib.Data.List.GetD

open Finset SimpleGraph Hypergraph Nibble.YusterE
open scoped Classical

set_option maxHeartbeats 1600000

namespace Nibble.AX1

/-! ### The arithmetic of the count -/

/-- `q₀/(2(q₀+1)) ≤ 1/2`: the slot length `2α·mmax` fits `q₀` times in half a cluster. -/
private theorem q0_half_bound (q₀ : ℕ) :
    (q₀ : ℝ) * (2 * (1 / (4 * ((q₀ : ℝ) + 1)))) ≤ 1 / 2 := by
  have hpos : (0:ℝ) < 4 * ((q₀ : ℝ) + 1) := by positivity
  have hq : (0:ℝ) ≤ (q₀ : ℝ) := Nat.cast_nonneg _
  have hid : (q₀ : ℝ) * (2 * (1 / (4 * ((q₀ : ℝ) + 1)))) = (q₀ : ℝ) / (2 * ((q₀ : ℝ) + 1)) := by
    field_simp
    ring
  rw [hid, div_le_iff₀ (by positivity)]
  linarith only []

/-- `(1+u)³(1-3u) ≤ 1` for `u ≥ 0`: the density window loses at most a `3·`spread fraction. -/
private theorem cube_window_bound (u : ℝ) (hu : 0 ≤ u) : (1 + u) ^ 3 * (1 - 3 * u) ≤ 1 := by
  linarith only [sq_nonneg u, pow_nonneg hu 3, pow_nonneg hu 4, mul_nonneg hu hu]

/-- `L²·(d³/D²) = (L/D)²·d³`. -/
private theorem sq_div_cube_eq (L D d : ℝ) (hD : D ≠ 0) :
    L ^ 2 * (d ^ 3 / D ^ 2) = (L / D) ^ 2 * d ^ 3 := by
  field_simp

/-- The counting inequality behind the covering clause: the members cover the fraction
`(p·L/mmax)²` of every cluster pair, and the three losses — the uncovered margin of each cluster,
the spread `t` of the density window and the nibble error — are all below the accuracy. -/
private theorem nearUniform_count_arith {ε α D nu n kp mmax mmin L pL t : ℝ}
    (hε : 0 < ε) (hα0 : 0 < α) (hαε : α ≤ ε / 200)
    (hD0 : 0 < D) (hD1 : D ≤ 1)
    (ht1 : t ≤ 1) (htD : D * (1 - 3 * (ε / 200)) ≤ t)
    (hnu0 : 0 ≤ nu) (hnukp : nu ≤ kp ^ 2)
    (hkp1 : 1 ≤ kp) (hkpn : kp ≤ n)
    (hmax : mmax ≤ mmin + 1) (hminmax : mmin ≤ mmax) (hmmin0 : 0 ≤ mmin)
    (hn1 : kp * mmin ≤ n) (hn0 : 0 < n)
    (hL : L ≤ 2 * α * mmax + 1) (hL1 : 1 ≤ L)
    (hpL1 : pL ≤ mmin) (hpL2 : mmin - L ≤ pL) (hpL0 : 0 ≤ pL)
    (hbig : 8 * kp * n ≤ 4 / 10 * ε * n ^ 2) :
    D * mmax ^ 2 * nu ≤ pL ^ 2 * nu * t - ε / 8 * (pL * kp) ^ 2 * t + ε * n ^ 2 := by
  have hmmax0 : (0:ℝ) ≤ mmax := le_trans hmmin0 hminmax
  have hkp0 : (0:ℝ) < kp := by linarith only [hkp1]
  have hn2 : (0:ℝ) < n ^ 2 := by positivity
  -- the area actually used
  have harea : pL * kp ≤ n := by
    have h := mul_le_mul_of_nonneg_right hpL1 hkp0.le
    calc pL * kp ≤ mmin * kp := h
      _ = kp * mmin := by ring
      _ ≤ n := hn1
  have harea2 : (pL * kp) ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ (by positivity) harea 2
  have hdisc : ε / 8 * (pL * kp) ^ 2 * t ≤ ε / 8 * n ^ 2 := by
    have h1 : (pL * kp) ^ 2 * t ≤ n ^ 2 := by nlinarith only [harea2, ht1, sq_nonneg (pL * kp)]
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ ε / 8)
    calc ε / 8 * (pL * kp) ^ 2 * t = ε / 8 * ((pL * kp) ^ 2 * t) := by ring
      _ ≤ ε / 8 * n ^ 2 := h2
  -- the uncovered margin of a cluster
  have hgap : mmax ^ 2 - pL ^ 2 ≤ 4 * α * mmax ^ 2 + 4 * mmax := by
    have h1 : mmax - pL ≤ 1 + L := by linarith only [hmax, hpL2]
    have h2 : mmax + pL ≤ 2 * mmax := by linarith only [hminmax, hpL1]
    have h3 : (mmax - pL) * (mmax + pL) ≤ (1 + L) * (2 * mmax) :=
      mul_le_mul h1 h2 (by linarith) (by linarith)
    have h4 : (1 + L) * (2 * mmax) ≤ (2 + 2 * α * mmax) * (2 * mmax) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith only [h3, h4]
  have hgap0 : 0 ≤ mmax ^ 2 - pL ^ 2 := by nlinarith only [hpL0, hpL1, hminmax]
  have hkm : kp * mmax ≤ 2 * n := by
    have h1 : kp * mmax ≤ kp * (mmin + 1) := mul_le_mul_of_nonneg_left hmax hkp0.le
    linarith only [h1, hn1, hkpn, hkp0]
  have hkm2 : (kp * mmax) ^ 2 ≤ 4 * n ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ kp * mmax) hkm 2
    linarith only [h]
  -- the loss coming from the margin
  have hDnu : D * nu ≤ kp ^ 2 := by
    have h : D * nu ≤ 1 * nu := mul_le_mul_of_nonneg_right hD1 hnu0
    linarith only [hnukp, h]
  have hmargin : D * nu * (mmax ^ 2 - pL ^ 2) ≤ kp ^ 2 * (4 * α * mmax ^ 2 + 4 * mmax) :=
    mul_le_mul hDnu hgap hgap0 (by positivity)
  have hstep2 : kp ^ 2 * (4 * α * mmax ^ 2) ≤ 16 * α * n ^ 2 := by
    have h : kp ^ 2 * (4 * α * mmax ^ 2) = 4 * α * (kp * mmax) ^ 2 := by ring
    rw [h]
    have h2 := mul_le_mul_of_nonneg_left hkm2 (by positivity : (0:ℝ) ≤ 4 * α)
    linarith only [h2]
  have hstep3 : kp ^ 2 * (4 * mmax) ≤ 8 * kp * n := by
    have h : kp ^ 2 * (4 * mmax) = 4 * kp * (kp * mmax) := by ring
    rw [h]
    have h2 := mul_le_mul_of_nonneg_left hkm (by positivity : (0:ℝ) ≤ 4 * kp)
    linarith only [h2]
  have hstep4 : 16 * α * n ^ 2 ≤ 8 / 100 * ε * n ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hαε (le_of_lt hn2)
    linarith only [h]
  have hmargin2 : D * nu * (mmax ^ 2 - pL ^ 2) ≤ 48 / 100 * (ε * n ^ 2) := by
    have h : kp ^ 2 * (4 * α * mmax ^ 2 + 4 * mmax)
        = kp ^ 2 * (4 * α * mmax ^ 2) + kp ^ 2 * (4 * mmax) := by ring
    linarith only [hmargin, hstep2, hstep3, hstep4, hbig, h ▸ hmargin]
  -- the loss coming from the density window
  have hpLmax : pL ^ 2 ≤ mmax ^ 2 := by nlinarith only [hpL0, hpL1, hminmax]
  have hwindow : nu * (D * (3 * (ε / 200))) * pL ^ 2 ≤ 6 / 100 * (ε * n ^ 2) := by
    have h1 : nu * (D * (3 * (ε / 200))) * pL ^ 2 ≤ kp ^ 2 * (3 * (ε / 200)) * mmax ^ 2 := by
      have hA : nu * (D * (3 * (ε / 200))) ≤ kp ^ 2 * (3 * (ε / 200)) := by
        have h := mul_le_mul_of_nonneg_right hDnu (by positivity : (0:ℝ) ≤ 3 * (ε / 200))
        linarith only [h]
      have hB : (0:ℝ) ≤ nu * (D * (3 * (ε / 200))) := by positivity
      exact mul_le_mul hA hpLmax (by positivity) (by positivity)
    have h2 : kp ^ 2 * (3 * (ε / 200)) * mmax ^ 2 = 3 * (ε / 200) * (kp * mmax) ^ 2 := by ring
    have h3 := mul_le_mul_of_nonneg_left hkm2 (by positivity : (0:ℝ) ≤ 3 * (ε / 200))
    linarith only [h1, h2 ▸ h1, h3]
  -- putting the two losses together
  have hlow : pL ^ 2 * nu * (D * (1 - 3 * (ε / 200))) ≤ pL ^ 2 * nu * t :=
    mul_le_mul_of_nonneg_left htD (by positivity)
  have hid : pL ^ 2 * nu * (D * (1 - 3 * (ε / 200)))
      = D * pL ^ 2 * nu - nu * (D * (3 * (ε / 200))) * pL ^ 2 := by ring
  have hid2 : D * mmax ^ 2 * nu - D * pL ^ 2 * nu = D * nu * (mmax ^ 2 - pL ^ 2) := by ring
  linarith only [hdisc, hmargin2, hwindow, hlow, hid, hid2, mul_pos hε hn2]

/-- Three products with all factors above their floors. -/
private theorem three_terms_lower {d T x y z a b c : ℝ} (hd0 : 0 ≤ d) (hT0 : 0 ≤ T)
    (hx : d ≤ x) (hy : d ≤ y) (hz : d ≤ z) (ha : T ≤ a) (hb : T ≤ b) (hc : T ≤ c) :
    3 * (d * T * T) ≤ x * a * b + y * a * c + z * b * c := by
  have hTa : 0 ≤ a := le_trans hT0 ha
  have hTb : 0 ≤ b := le_trans hT0 hb
  have hTc : 0 ≤ c := le_trans hT0 hc
  have key : ∀ u v w : ℝ, d ≤ u → T ≤ v → T ≤ w → 0 ≤ v → d * T * T ≤ u * v * w := by
    intro u v w hu hv hw hv0
    have hu0 : 0 ≤ u := le_trans hd0 hu
    have hvw : T * T ≤ v * w := mul_le_mul hv hw hT0 hv0
    calc d * T * T = d * (T * T) := by ring
      _ ≤ u * (v * w) := mul_le_mul hu hvw (by positivity) hu0
      _ = u * v * w := by ring
  have h1 : d * T * T ≤ x * a * b := key x a b hx ha hb hTa
  have h2 : d * T * T ≤ y * a * c := key y a c hy ha hc hTa
  have h3 : d * T * T ≤ z * b * c := key z b c hz hb hc hTb
  linarith only [h1, h2, h3]

/-! ### The near-uniform regime -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Near-uniform cluster densities**: every pair of distinct clusters has edge density `0` or a
density in the window `[d, D]`. -/
def NearUniformClusterDensities (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (d D : ℝ) : Prop :=
  ∀ S ∈ P.parts, ∀ T ∈ P.parts, S ≠ T →
    (G.edgeDensity S T : ℝ) = 0 ∨
      (d ≤ (G.edgeDensity S T : ℝ) ∧ (G.edgeDensity S T : ℝ) ≤ D)

/-- With near-uniform cluster densities, a pair of distinct clusters carries at most `D·mmax²`
edges: this is the capacity feeding the cluster-LP aggregation. -/
theorem card_interedges_le_of_nearUniformDensities (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {d D : ℝ} (hD0 : 0 < D) {mmax : ℕ}
    (hcardle : ∀ S ∈ P.parts, #S ≤ mmax) (hdich : NearUniformClusterDensities G P d D) :
    ∀ S ∈ P.parts, ∀ T ∈ P.parts, S ≠ T → (#(G.interedges S T) : ℝ) ≤ D * (mmax : ℝ) ^ 2 := by
  intro S hS T hT hST
  have hS0 : (0:ℚ) < (#S : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr (P.nonempty_of_mem_parts hS)
  have hT0 : (0:ℚ) < (#T : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr (P.nonempty_of_mem_parts hT)
  have hEq : (#(G.interedges S T) : ℝ) = (G.edgeDensity S T : ℝ) * ((#S : ℝ) * (#T : ℝ)) := by
    have h : (G.edgeDensity S T : ℚ) = (#(G.interedges S T) : ℚ) / ((#S : ℚ) * (#T : ℚ)) :=
      SimpleGraph.edgeDensity_def (G := G) S T
    have h2 : (#(G.interedges S T) : ℚ) = (G.edgeDensity S T : ℚ) * ((#S : ℚ) * (#T : ℚ)) := by
      rw [h, div_mul_cancel₀ _ (by positivity : ((#S : ℚ) * (#T : ℚ)) ≠ 0)]
    exact_mod_cast h2
  have hdle : (G.edgeDensity S T : ℝ) ≤ D := by
    rcases hdich S hS T hT hST with h | h
    · rw [h]; linarith only [hD0]
    · exact h.2
  have hSle : (#S : ℝ) ≤ (mmax : ℝ) := by exact_mod_cast hcardle S hS
  have hTle : (#T : ℝ) ≤ (mmax : ℝ) := by exact_mod_cast hcardle T hT
  have hd0' : (0:ℝ) ≤ (G.edgeDensity S T : ℝ) := by exact_mod_cast G.edgeDensity_nonneg S T
  have hS0' : (0:ℝ) ≤ (#S : ℝ) := by positivity
  have hT0' : (0:ℝ) ≤ (#T : ℝ) := by positivity
  have h1 : (#S : ℝ) * (#T : ℝ) ≤ (mmax : ℝ) * (mmax : ℝ) :=
    mul_le_mul hSle hTle hT0' (le_trans hS0' hSle)
  have h2 : (G.edgeDensity S T : ℝ) * ((#S : ℝ) * (#T : ℝ)) ≤ D * ((mmax : ℝ) * (mmax : ℝ)) :=
    mul_le_mul hdle h1 (by positivity) hD0.le
  rw [hEq]
  linarith only [h2]

/-- **The coupled block-allocation residual, in the near-uniform regime.**  Word for word
`Nibble.AX1.BlockCoverResidualCoupled`, with the extra hypothesis that the cluster densities are
either `0` or inside a window `[d, D]` of relative width `ρ`, the tolerance `ρ` being named by the
residual alongside the regularity window. -/
def BlockCoverResidualCoupledNearUniform : Prop :=
  ∀ ε δ ε₂ T₀ : ℝ, 0 < ε → 0 < δ → δ ≤ 1 → δ ≤ ε → 0 < ε₂ → 0 < T₀ →
  ∃ ε₁₀ ρ : ℝ, 0 < ε₁₀ ∧ 0 < ρ ∧
    ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ ε₁₀ → ε₁ ≤ 1 →
    ∃ α : ℝ, ε₁ / 8 ≤ α ∧ 2 * α ≤ 1 ∧ ε₁ / 8 / α ≤ ε₂ ∧
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (P : Finpartition (univ : Finset V)),
      n₀ ≤ Fintype.card V →
      P.IsEquipartition →
      4 / ε₁ ≤ (P.parts.card : ℝ) →
      (P.parts.card : ℝ) ≤ ((SzemerediRegularity.bound (ε₁ / 8) ⌈4 / ε₁⌉₊ : ℕ) : ℝ) →
      P.IsUniform G (ε₁ / 8) →
      ∀ d D : ℝ, δ ≤ d → d ≤ D → D ≤ 1 → D ≤ d * (1 + ρ) →
      NearUniformClusterDensities G P d D →
      ∃ (τ : ℝ) (k : ℕ) (U W X A B C : ℕ → Finset V),
        T₀ ≤ τ ∧
        (∀ i < k, IsGridSubTriple G P (ε₁ / 8) δ α τ (U i) (W i) (X i) (A i) (B i) (C i)) ∧
        (∀ i < k, ∀ j < k, i ≠ j →
          Disjoint (tripleRect (A i) (B i) (C i)) (tripleRect (A j) (B j) (C j))) ∧
        nu3star (G.regularityReduced P (ε₁ / 8) (ε₁ / 4))
          ≤ (∑ i ∈ Finset.range k,
              ((G.edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
                + (G.edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
                + (G.edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ))) / 3
            + ε * (Fintype.card V : ℝ) ^ 2

/-- **The coupled block-allocation residual holds at near-uniform cluster densities.** -/
theorem blockCoverResidualCoupledNearUniform_holds : BlockCoverResidualCoupledNearUniform := by
  classical
  intro ε δ ε₂ T₀ hε hδ0 hδ1 hδε hε₂0 hT₀0
  obtain ⟨q₀, hq₀0, hblow⟩ := exists_edgeDisjoint_triangles_blowUp (ε := ε / 8) (by positivity)
  set α : ℝ := min (1 / 8) (min (ε / 200) (1 / (4 * ((q₀ : ℝ) + 1)))) with hαdef
  have hq₀R : (0:ℝ) < (q₀ : ℝ) := by exact_mod_cast hq₀0
  have hα0 : 0 < α := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hα8 : α ≤ 1 / 8 := min_le_left _ _
  have hαε : α ≤ ε / 200 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hαq : α ≤ 1 / (4 * ((q₀ : ℝ) + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hm1 : (0:ℝ) < min 1 ε := lt_min one_pos hε
  refine ⟨8 * α * min 1 ε₂, min 1 ε / 200, by positivity, by positivity, ?_⟩
  intro ε₁ hε₁0 hε₁le hε₁1
  have hmin1 : min 1 ε₂ ≤ 1 := min_le_left _ _
  have hmin2 : min 1 ε₂ ≤ ε₂ := min_le_right _ _
  have hminε : min 1 ε ≤ 1 := min_le_left _ _
  have hminε' : min 1 ε ≤ ε := min_le_right _ _
  have hm10 : (0:ℝ) < min 1 ε₂ := lt_min one_pos hε₂0
  have hε₁α : ε₁ / 8 ≤ α * min 1 ε₂ := by linarith
  refine ⟨α, by nlinarith, by linarith, ?_, ?_⟩
  · rw [div_le_iff₀ hα0]
    nlinarith
  -- ### the size threshold
  set KB : ℕ := SzemerediRegularity.bound (ε₁ / 8) ⌈4 / ε₁⌉₊ with hKBdef
  refine ⟨KB * (4 * q₀ + ⌈T₀ / α⌉₊ + 10) + ⌈20 * (KB : ℝ) / ε⌉₊ + 10, ?_⟩
  intro V _ _ G _ P hV hP hPl hPb hPu d D hδd hdD hD1 hDd hdich
  have hd0 : 0 < d := lt_of_lt_of_le hδ0 hδd
  have hD0 : 0 < D := lt_of_lt_of_le hd0 hdD
  have hDd2 : D ≤ 2 * d := by
    have h : d * (1 + min 1 ε / 200) ≤ d * 2 := by
      refine mul_le_mul_of_nonneg_left ?_ hd0.le
      linarith
    linarith
  -- ### the clusters
  have hkpR : (0:ℝ) < (#P.parts : ℝ) := lt_of_lt_of_le (by positivity) hPl
  have hkpN : 0 < #P.parts := by exact_mod_cast hkpR
  have hpne : P.parts.Nonempty := Finset.card_pos.mp hkpN
  set kp : ℕ := #P.parts with hkpdef
  set mmax : ℕ := P.parts.sup' hpne Finset.card with hmmaxdef
  set mmin : ℕ := P.parts.inf' hpne Finset.card with hmmindef
  obtain ⟨Smin, hSminmem, hSmineq⟩ := Finset.exists_mem_eq_inf' hpne Finset.card
  obtain ⟨Smax, hSmaxmem, hSmaxeq⟩ := Finset.exists_mem_eq_sup' hpne Finset.card
  have hminmax : mmin ≤ mmax := by
    rw [hmmindef, hSmineq, hmmaxdef]; exact Finset.le_sup' _ hSminmem
  have hmm1 : mmax ≤ mmin + 1 := by
    rw [hmmaxdef, hSmaxeq, hmmindef, hSmineq]
    exact hP (Finset.mem_coe.mpr hSmaxmem) (Finset.mem_coe.mpr hSminmem)
  have hcardle : ∀ S ∈ P.parts, #S ≤ mmax := fun S hS => Finset.le_sup' _ hS
  have hcardge : ∀ S ∈ P.parts, mmin ≤ #S := fun S hS => Finset.inf'_le _ hS
  have hsumparts : ∑ S ∈ P.parts, #S = Fintype.card V := by
    rw [P.sum_card_parts, Finset.card_univ]
  have hnhi : Fintype.card V ≤ kp * mmax := by
    calc Fintype.card V = ∑ S ∈ P.parts, #S := hsumparts.symm
      _ ≤ ∑ _S ∈ P.parts, mmax := Finset.sum_le_sum (fun S hS => hcardle S hS)
      _ = kp * mmax := by rw [Finset.sum_const, smul_eq_mul]
  have hnlo : kp * mmin ≤ Fintype.card V := by
    calc kp * mmin = ∑ _S ∈ P.parts, mmin := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ S ∈ P.parts, #S := Finset.sum_le_sum (fun S hS => hcardge S hS)
      _ = Fintype.card V := hsumparts
  have hkpKB : kp ≤ KB := by exact_mod_cast hPb
  have hKB0 : 0 < KB := lt_of_lt_of_le hkpN hkpKB
  have hmminbig : 4 * q₀ + ⌈T₀ / α⌉₊ + 9 ≤ mmin := by
    have h1 : KB * (4 * q₀ + ⌈T₀ / α⌉₊ + 10) ≤ Fintype.card V := le_trans (by omega) hV
    have h2 : Fintype.card V ≤ KB * (mmin + 1) := by
      refine le_trans hnhi ?_
      exact Nat.mul_le_mul hkpKB (by omega)
    have h3 : KB * (4 * q₀ + ⌈T₀ / α⌉₊ + 10) ≤ KB * (mmin + 1) := le_trans h1 h2
    have h4 := Nat.le_of_mul_le_mul_left h3 hKB0
    omega
  have hnbig : ⌈20 * (KB : ℝ) / ε⌉₊ ≤ Fintype.card V := le_trans (by omega) hV
  have hmmax0 : 0 < mmax := lt_of_lt_of_le (by omega) hminmax
  have hmmin0 : 0 < mmin := by omega
  -- ### the slots
  set L : ℕ := ⌈2 * α * (mmax : ℝ)⌉₊ with hLdef
  have hLlb : 2 * α * (mmax : ℝ) ≤ (L : ℝ) := Nat.le_ceil _
  have hLub : (L : ℝ) ≤ 2 * α * (mmax : ℝ) + 1 := by
    have h := Nat.ceil_lt_add_one (le_of_lt (by positivity : (0:ℝ) < 2 * α * (mmax : ℝ)))
    rw [hLdef]; linarith
  have hL0 : 0 < L := Nat.ceil_pos.mpr (by positivity)
  have hL1 : (1:ℝ) ≤ (L : ℝ) := by exact_mod_cast hL0
  set p : ℕ := mmin / L with hpdef
  have hpL : p * L ≤ mmin := Nat.div_mul_le_self _ _
  have hpL2 : mmin < (p + 1) * L := by
    have h1 : L * p + mmin % L = mmin := Nat.div_add_mod mmin L
    have h2 : mmin % L < L := Nat.mod_lt _ hL0
    calc mmin = L * p + mmin % L := h1.symm
      _ < L * p + L := by omega
      _ = (p + 1) * L := by ring
  have hmmaxR : (mmax : ℝ) ≤ (mmin : ℝ) + 1 := by exact_mod_cast hmm1
  have hq₀p : q₀ ≤ p := by
    rw [hpdef, Nat.le_div_iff_mul_le hL0]
    have hR : ((q₀ * L : ℕ) : ℝ) ≤ ((mmin : ℕ) : ℝ) := by
      push_cast
      have h1 : (q₀ : ℝ) * (L : ℝ) ≤ (q₀ : ℝ) * (2 * α * (mmax : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hLub (by positivity)
      have h2 : (q₀ : ℝ) * (2 * α) ≤ 1 / 2 := by
        have h3 : (q₀ : ℝ) * (2 * α) ≤ (q₀ : ℝ) * (2 * (1 / (4 * ((q₀ : ℝ) + 1)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
        have h4 : (q₀ : ℝ) * (2 * (1 / (4 * ((q₀ : ℝ) + 1)))) ≤ 1 / 2 := q0_half_bound q₀
        linarith
      have h5 : (4 : ℝ) * (q₀ : ℝ) ≤ (mmin : ℝ) := by
        have h : 4 * q₀ ≤ mmin := by omega
        exact_mod_cast h
      have hqa0 : (0:ℝ) ≤ (q₀ : ℝ) * (2 * α) := by positivity
      have hA : (q₀ : ℝ) * (2 * α) * (mmax : ℝ) ≤ 1 / 2 * ((mmin : ℝ) + 1) := by
        calc (q₀ : ℝ) * (2 * α) * (mmax : ℝ) ≤ (q₀ : ℝ) * (2 * α) * ((mmin : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left hmmaxR hqa0
          _ ≤ 1 / 2 * ((mmin : ℝ) + 1) := mul_le_mul_of_nonneg_right h2 (by positivity)
      have hid : (q₀ : ℝ) * (2 * α * (mmax : ℝ) + 1)
          = (q₀ : ℝ) * (2 * α) * (mmax : ℝ) + (q₀ : ℝ) := by ring
      have hmmin9 : (9:ℝ) ≤ (mmin : ℝ) := by
        have h : 9 ≤ mmin := by omega
        exact_mod_cast h
      linarith only [h1, hA, hid, h5, hmmin9]
    exact_mod_cast hR
  have hp0 : 0 < p := lt_of_lt_of_le hq₀0 hq₀p
  -- ### the block scale
  set τ : ℝ := (L : ℝ) / D with hτdef
  have hτD : τ * D = (L : ℝ) := by rw [hτdef]; field_simp
  have hτ0 : 0 < τ := by rw [hτdef]; positivity
  have hτd2 : (L : ℝ) / 2 ≤ τ * d := by
    have h : τ * D ≤ τ * (2 * d) := mul_le_mul_of_nonneg_left hDd2 hτ0.le
    rw [hτD] at h; linarith
  have hτT₀ : T₀ ≤ τ := by
    have hTa : T₀ / α ≤ (⌈T₀ / α⌉₊ : ℝ) := Nat.le_ceil _
    have hcast : ((⌈T₀ / α⌉₊ : ℕ) : ℝ) ≤ (mmin : ℝ) := by
      have h : ⌈T₀ / α⌉₊ ≤ mmin := by omega
      exact_mod_cast h
    have h1 : T₀ ≤ α * (mmin : ℝ) := by
      have h : T₀ / α ≤ (mmin : ℝ) := le_trans hTa hcast
      rw [div_le_iff₀ hα0] at h; linarith
    have h2 : α * (mmin : ℝ) ≤ (L : ℝ) := by
      have h := mul_le_mul_of_nonneg_left
        (show (mmin:ℝ) ≤ (mmax:ℝ) by exact_mod_cast hminmax) hα0.le
      linarith
    have h3 : (L : ℝ) ≤ τ := by
      have h : τ * D ≤ τ * 1 := mul_le_mul_of_nonneg_left hD1 hτ0.le
      rw [hτD] at h; linarith
    linarith
  -- ### the cluster graph and its blow-up
  set Wc := {S : Finset V // S ∈ P.parts} with hWcdef
  set Hst : SimpleGraph Wc := hostGraph G P (ε₁ / 8) (ε₁ / 4) with hHstdef
  haveI : Nonempty Wc := ⟨⟨Smin, hSminmem⟩⟩
  haveI : Nonempty (Fin p) := ⟨⟨0, hp0⟩⟩
  obtain ⟨Sfam, hSsub, hSint, hScard⟩ := hblow Hst p hq₀p
  set l : List (Finset (Wc × Fin p)) := Sfam.toList with hldef
  set k : ℕ := #Sfam with hkdef
  have hlen : l.length = k := Finset.length_toList _
  set memb : ℕ → (Wc × Fin p) × (Wc × Fin p) × (Wc × Fin p) :=
    fun i => pick3 (l.getD i ∅) with hmembdef
  set blk : Wc × Fin p → Finset V := fun c => blockOf (c.1 : Finset V) L (c.2 : ℕ) with hblkdef
  set sblk : Wc × Fin p → Wc → Wc → Finset V := fun c S T =>
    blockOf (blk c) ⌈τ * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ)⌉₊ 0 with hsblkdef
  -- the members
  have hmemS : ∀ i < k, l.getD i ∅ ∈ Sfam := by
    intro i hi
    rw [List.getD_eq_getElem l ∅ (by omega : i < l.length)]
    exact Finset.mem_toList.mp (List.getElem_mem _)
  have hclique : ∀ i < k, (blowUp Hst p).IsNClique 3 (l.getD i ∅) := fun i hi =>
    SimpleGraph.mem_cliqueFinset_iff.mp (hSsub (hmemS i hi))
  have hcard3 : ∀ i < k, #(l.getD i ∅) = 3 := fun i hi => (hclique i hi).card_eq
  have hne3 : ∀ i < k, ∀ j < k, i ≠ j → l.getD i ∅ ≠ l.getD j ∅ := by
    intro i hi j hj hij
    rw [List.getD_eq_getElem l ∅ (by omega : i < l.length),
      List.getD_eq_getElem l ∅ (by omega : j < l.length)]
    intro h
    exact hij ((Finset.nodup_toList Sfam).getElem_inj_iff.mp h)
  have hdata : ∀ i < k,
      ((memb i).1 ≠ (memb i).2.1 ∧ (memb i).1 ≠ (memb i).2.2 ∧ (memb i).2.1 ≠ (memb i).2.2) ∧
      ((memb i).1 ∈ l.getD i ∅ ∧ (memb i).2.1 ∈ l.getD i ∅ ∧ (memb i).2.2 ∈ l.getD i ∅) ∧
      (Hst.Adj (memb i).1.1 (memb i).2.1.1 ∧ Hst.Adj (memb i).1.1 (memb i).2.2.1 ∧
        Hst.Adj (memb i).2.1.1 (memb i).2.2.1) := by
    intro i hi
    obtain ⟨hab, hac, hbc, -⟩ := pick3_spec (hcard3 i hi)
    obtain ⟨hma, hmb, hmc⟩ := pick3_mem (hcard3 i hi)
    have hcl := hclique i hi
    refine ⟨⟨hab, hac, hbc⟩, ⟨hma, hmb, hmc⟩, ?_, ?_, ?_⟩
    · exact hcl.1 hma hmb hab
    · exact hcl.1 hma hmc hac
    · exact hcl.1 hmb hmc hbc
  -- the density of an edge of the cluster graph
  have hdens : ∀ Sv Tv : Wc, Hst.Adj Sv Tv →
      d ≤ (G.edgeDensity (Sv : Finset V) (Tv : Finset V) : ℝ) ∧
        (G.edgeDensity (Sv : Finset V) (Tv : Finset V) : ℝ) ≤ D := by
    intro Sv Tv hadj
    obtain ⟨hne, -, hden⟩ := hostGraph_adj.mp hadj
    rcases hdich _ Sv.2 _ Tv.2 hne with h | h
    · rw [h] at hden; linarith
    · exact h
  have hgood : ∀ Sv Tv : Wc, Hst.Adj Sv Tv →
      (Sv : Finset V) ≠ (Tv : Finset V) ∧ G.IsUniform (ε₁ / 8) (Sv : Finset V) (Tv : Finset V) ∧
        δ ≤ (G.edgeDensity (Sv : Finset V) (Tv : Finset V) : ℝ) := by
    intro Sv Tv hadj
    obtain ⟨hne, huni, -⟩ := hostGraph_adj.mp hadj
    exact ⟨hne, huni, le_trans hδd (hdens Sv Tv hadj).1⟩
  -- the slots and the blocks inside them
  have hblkcard : ∀ c : Wc × Fin p, #(blk c) = L := by
    intro c
    refine card_blockOf _ hL0 ?_
    have hlt : (c.2 : ℕ) < p := c.2.isLt
    have h1 : ((c.2 : ℕ) + 1) * L ≤ p * L := Nat.mul_le_mul_right _ (by omega)
    exact le_trans h1 (le_trans hpL (hcardge _ c.1.2))
  have hblksub : ∀ c : Wc × Fin p, blk c ⊆ (c.1 : Finset V) := fun c => blockOf_subset _ _ _
  have hblkdisj : ∀ c c' : Wc × Fin p, c ≠ c' → Disjoint (blk c) (blk c') := by
    intro c c' hcc
    by_cases h1 : c.1 = c'.1
    · have h2 : (c.2 : ℕ) ≠ (c'.2 : ℕ) := by
        intro h
        exact hcc (Prod.ext h1 (Fin.ext h))
      rw [hblkdef]
      simp only
      rw [h1]
      exact blockOf_disjoint _ _ h2
    · have hne : (c.1 : Finset V) ≠ (c'.1 : Finset V) := fun h => h1 (Subtype.ext h)
      exact Finset.disjoint_of_subset_left (hblksub c)
        (Finset.disjoint_of_subset_right (hblksub c') (P.disjoint c.1.2 c'.1.2 hne))
  have hsblksub : ∀ (c : Wc × Fin p) (S T : Wc), sblk c S T ⊆ blk c :=
    fun c S T => blockOf_subset _ _ _
  have hsubcl : ∀ (c : Wc × Fin p) (S T : Wc), sblk c S T ⊆ (c.1 : Finset V) :=
    fun c S T => Finset.Subset.trans (hsblksub c S T) (hblksub c)
  have hsblk : ∀ (c : Wc × Fin p) (S T : Wc), Hst.Adj S T →
      τ * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ) ≤ (#(sblk c S T) : ℝ) ∧
        (#(sblk c S T) : ℝ)
          ≤ τ * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ) + 1 ∧
        τ * d ≤ (#(sblk c S T) : ℝ) := by
    intro c S T hadj
    obtain ⟨hlo, hhi⟩ := hdens S T hadj
    set x : ℝ := (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ) with hxdef
    have hx0 : 0 < τ * x := by
      have : 0 < x := lt_of_lt_of_le hd0 hlo
      positivity
    have hjle : ⌈τ * x⌉₊ ≤ L := by
      have h1 : τ * x ≤ (L : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hhi hτ0.le
        rw [hτD] at h; exact h
      have h2 : ⌈τ * x⌉₊ ≤ ⌈(L : ℝ)⌉₊ := Nat.ceil_le_ceil h1
      simpa using h2
    have hj0 : 0 < ⌈τ * x⌉₊ := Nat.ceil_pos.mpr hx0
    have hcard : #(sblk c S T) = ⌈τ * x⌉₊ := by
      rw [hsblkdef]
      refine card_blockOf _ hj0 ?_
      rw [hblkcard]
      simpa using hjle
    rw [hcard]
    refine ⟨Nat.le_ceil _, ?_, ?_⟩
    · exact le_of_lt (Nat.ceil_lt_add_one hx0.le)
    · exact le_trans (mul_le_mul_of_nonneg_left hlo hτ0.le) (Nat.le_ceil _)
  -- ### the family
  refine ⟨τ, k,
    fun i => ((memb i).1.1 : Finset V), fun i => ((memb i).2.1.1 : Finset V),
    fun i => ((memb i).2.2.1 : Finset V),
    fun i => sblk (memb i).1 (memb i).2.1.1 (memb i).2.2.1,
    fun i => sblk (memb i).2.1 (memb i).1.1 (memb i).2.2.1,
    fun i => sblk (memb i).2.2 (memb i).1.1 (memb i).2.1.1,
    hτT₀, ?_, ?_, ?_⟩
  · -- the shape of a member
    intro i hi
    obtain ⟨-, -, hAB, hAC, hBC⟩ := hdata i hi
    have hsize : ∀ (c : Wc × Fin p) (S T : Wc), Hst.Adj S T →
        α * ((#(c.1 : Finset V) : ℕ) : ℝ) ≤ (#(sblk c S T) : ℝ) := by
      intro c S T hadj
      have h1 : ((#(c.1 : Finset V) : ℕ) : ℝ) ≤ (mmax : ℝ) := by
        exact_mod_cast hcardle _ c.1.2
      have h2 : α * ((#(c.1 : Finset V) : ℕ) : ℝ) ≤ α * (mmax : ℝ) :=
        mul_le_mul_of_nonneg_left h1 hα0.le
      have h3 := (hsblk c S T hadj).2.2
      linarith [hτd2, hLlb]
    refine ⟨⟨(memb i).1.1.2, (memb i).2.1.1.2, (memb i).2.2.1.2,
      (hgood _ _ hAB).1, (hgood _ _ hAC).1, (hgood _ _ hBC).1,
      (hgood _ _ hAB).2.1, (hgood _ _ hAB).2.2, (hgood _ _ hAC).2.1, (hgood _ _ hAC).2.2,
      (hgood _ _ hBC).2.1, (hgood _ _ hBC).2.2⟩,
      hsubcl _ _ _, hsubcl _ _ _, hsubcl _ _ _, hsize _ _ _ hBC, hsize _ _ _ hAC, hsize _ _ _ hAB, ?_, ?_, ?_⟩
    · obtain ⟨h1, h2, -⟩ := hsblk (memb i).1 (memb i).2.1.1 (memb i).2.2.1 hBC
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨h1, h2, -⟩ := hsblk (memb i).2.1 (memb i).1.1 (memb i).2.2.1 hAC
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨h1, h2, -⟩ := hsblk (memb i).2.2 (memb i).1.1 (memb i).2.1.1 hAB
      rw [abs_le]; constructor <;> linarith
  · -- the rectangles are disjoint
    intro i hi j hj hij
    obtain ⟨⟨hab, hac, hbc⟩, ⟨hma, hmb, hmc⟩, -⟩ := hdata i hi
    obtain ⟨⟨hab', hac', hbc'⟩, ⟨hma', hmb', hmc'⟩, -⟩ := hdata j hj
    refine tripleRect_disjoint_of_cells_inter blk hblkdisj ?_
      hma hmb hmc hab hac hbc hma' hmb' hmc' hab' hac' hbc'
      (hsblksub _ _ _) (hsblksub _ _ _) (hsblksub _ _ _)
      (hsblksub _ _ _) (hsblksub _ _ _) (hsblksub _ _ _)
    exact hSint _ (hmemS i hi) _ (hmemS j hj) (hne3 i hi j hj hij)
  · -- the covering clause
    set R : SimpleGraph V := G.regularityReduced P (ε₁ / 8) (ε₁ / 4) with hRdef
    have hsumge : (k : ℝ) * (3 * (d * (τ * d) * (τ * d)))
        ≤ (∑ i ∈ Finset.range k,
        ((G.edgeDensity ((memb i).1.1 : Finset V) ((memb i).2.1.1 : Finset V) : ℝ)
            * (#(sblk (memb i).1 (memb i).2.1.1 (memb i).2.2.1) : ℝ)
            * (#(sblk (memb i).2.1 (memb i).1.1 (memb i).2.2.1) : ℝ)
          + (G.edgeDensity ((memb i).1.1 : Finset V) ((memb i).2.2.1 : Finset V) : ℝ)
            * (#(sblk (memb i).1 (memb i).2.1.1 (memb i).2.2.1) : ℝ)
            * (#(sblk (memb i).2.2 (memb i).1.1 (memb i).2.1.1) : ℝ)
          + (G.edgeDensity ((memb i).2.1.1 : Finset V) ((memb i).2.2.1 : Finset V) : ℝ)
            * (#(sblk (memb i).2.1 (memb i).1.1 (memb i).2.2.1) : ℝ)
            * (#(sblk (memb i).2.2 (memb i).1.1 (memb i).2.1.1) : ℝ))) := by
      have hterm : ∀ i ∈ Finset.range k, 3 * (d * (τ * d) * (τ * d))
          ≤ ((G.edgeDensity ((memb i).1.1 : Finset V) ((memb i).2.1.1 : Finset V) : ℝ)
              * (#(sblk (memb i).1 (memb i).2.1.1 (memb i).2.2.1) : ℝ)
              * (#(sblk (memb i).2.1 (memb i).1.1 (memb i).2.2.1) : ℝ)
            + (G.edgeDensity ((memb i).1.1 : Finset V) ((memb i).2.2.1 : Finset V) : ℝ)
              * (#(sblk (memb i).1 (memb i).2.1.1 (memb i).2.2.1) : ℝ)
              * (#(sblk (memb i).2.2 (memb i).1.1 (memb i).2.1.1) : ℝ)
            + (G.edgeDensity ((memb i).2.1.1 : Finset V) ((memb i).2.2.1 : Finset V) : ℝ)
              * (#(sblk (memb i).2.1 (memb i).1.1 (memb i).2.2.1) : ℝ)
              * (#(sblk (memb i).2.2 (memb i).1.1 (memb i).2.1.1) : ℝ)) := by
        intro i hi
        obtain ⟨-, -, hAB, hAC, hBC⟩ := hdata i (Finset.mem_range.mp hi)
        exact three_terms_lower hd0.le (by positivity)
          (hdens _ _ hAB).1 (hdens _ _ hAC).1 (hdens _ _ hBC).1
          (hsblk _ _ _ hBC).2.2 (hsblk _ _ _ hAC).2.2 (hsblk _ _ _ hAB).2.2
      have h := Finset.sum_le_sum hterm
      rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    -- the LP of the cluster graph
    have hcap := card_interedges_le_of_nearUniformDensities G P hD0 hcardle hdich
    have hhost : nu3star R ≤ (D * (mmax : ℝ) ^ 2) * nu3star Hst :=
      nu3star_regularityReduced_le_host G P (ε₁ / 8) (ε₁ / 4) (by positivity) hcap
    have hnu0 : 0 ≤ nu3star Hst := nu3star_nonneg _
    have hcardWcN : Fintype.card Wc = kp := card_hostGraph_vertices P
    have hcardWc : (Fintype.card Wc : ℝ) = (kp : ℝ) := by exact_mod_cast hcardWcN
    have hnukp : nu3star Hst ≤ (kp : ℝ) ^ 2 := by
      have h := nu3star_le_card_sq Hst
      rwa [hcardWc] at h
    have hknib : (p : ℝ) ^ 2 * nu3star Hst - ε / 8 * ((p : ℝ) * (Fintype.card Wc : ℝ)) ^ 2
        ≤ (k : ℝ) := hScard
    rw [hcardWc] at hknib
    -- the spread of the density window
    set t : ℝ := d ^ 3 / D ^ 2 with htdef
    have ht1 : t ≤ 1 := by
      rw [htdef, div_le_one (by positivity)]
      have hd2 : d ^ 2 ≤ D ^ 2 := by nlinarith only [hd0, hdD]
      have hd1 : d ≤ 1 := le_trans hdD hD1
      nlinarith only [hd2, hd1, sq_nonneg d]
    have htD : D * (1 - 3 * (ε / 200)) ≤ t := by
      have hu0 : (0:ℝ) ≤ min 1 ε / 200 := by positivity
      have hcube : D ^ 3 * (1 - 3 * (min 1 ε / 200)) ≤ d ^ 3 := by
        have h1 : D ^ 3 ≤ d ^ 3 * (1 + min 1 ε / 200) ^ 3 := by
          have h := pow_le_pow_left₀ hD0.le hDd 3
          calc D ^ 3 ≤ (d * (1 + min 1 ε / 200)) ^ 3 := h
            _ = d ^ 3 * (1 + min 1 ε / 200) ^ 3 := by ring
        have h2 : (1 + min 1 ε / 200) ^ 3 * (1 - 3 * (min 1 ε / 200)) ≤ 1 :=
          cube_window_bound _ hu0
        nlinarith only [h1, h2, pow_pos hd0 3, hu0, hminε]
      have hstep : D * (1 - 3 * (min 1 ε / 200)) ≤ t := by
        rw [htdef, le_div_iff₀ (by positivity : (0:ℝ) < D ^ 2)]
        linarith only [hcube]
      have hmono : D * (1 - 3 * (ε / 200)) ≤ D * (1 - 3 * (min 1 ε / 200)) := by
        refine mul_le_mul_of_nonneg_left ?_ hD0.le
        linarith
      linarith
    have hTTeq : (L : ℝ) ^ 2 * t = τ ^ 2 * d ^ 3 := by
      rw [htdef, hτdef]
      exact sq_div_cube_eq _ _ _ (ne_of_gt hD0)
    -- the arithmetic
    have hkpn : (kp : ℝ) ≤ (Fintype.card V : ℝ) := by
      have h : kp ≤ Fintype.card V := by
        calc kp = kp * 1 := by ring
          _ ≤ kp * mmin := Nat.mul_le_mul_left _ hmmin0
          _ ≤ Fintype.card V := hnlo
      exact_mod_cast h
    have hkp1R : (1:ℝ) ≤ (kp : ℝ) := by exact_mod_cast hkpN
    have hn0 : (0:ℝ) < (Fintype.card V : ℝ) := by linarith only [hkpn, hkp1R]
    have hbig : 8 * (kp : ℝ) * (Fintype.card V : ℝ)
        ≤ 4 / 10 * ε * (Fintype.card V : ℝ) ^ 2 := by
      have h1 : 20 * (KB : ℝ) / ε ≤ (Fintype.card V : ℝ) := by
        refine le_trans (Nat.le_ceil _) ?_
        exact_mod_cast hnbig
      have h2 : 20 * (KB : ℝ) ≤ ε * (Fintype.card V : ℝ) := by
        rw [div_le_iff₀ hε] at h1; linarith
      have h3 : (kp : ℝ) ≤ (KB : ℝ) := hPb
      have hKBn : (KB : ℝ) ≤ ε * (Fintype.card V : ℝ) / 20 := by linarith
      have hstep : 8 * (kp : ℝ) ≤ 8 * (ε * (Fintype.card V : ℝ) / 20) := by linarith
      calc 8 * (kp : ℝ) * (Fintype.card V : ℝ)
          ≤ 8 * (ε * (Fintype.card V : ℝ) / 20) * (Fintype.card V : ℝ) :=
            mul_le_mul_of_nonneg_right hstep hn0.le
        _ = 4 / 10 * ε * (Fintype.card V : ℝ) ^ 2 := by ring
    have harith := nearUniform_count_arith (ε := ε) (α := α) (D := D) (nu := nu3star Hst)
      (n := (Fintype.card V : ℝ)) (kp := (kp : ℝ)) (mmax := (mmax : ℝ)) (mmin := (mmin : ℝ))
      (L := (L : ℝ)) (pL := (p : ℝ) * (L : ℝ)) (t := t)
      hε hα0 hαε hD0 hD1 ht1 htD hnu0 hnukp (by exact_mod_cast hkpN) hkpn hmmaxR
      (by exact_mod_cast hminmax) (Nat.cast_nonneg _) (by exact_mod_cast hnlo) hn0 hLub hL1
      (by exact_mod_cast hpL) (by
        have h : (mmin : ℝ) < ((p : ℝ) + 1) * (L : ℝ) := by exact_mod_cast hpL2
        linarith only [h]) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hbig
    -- the nibble count, scaled by the value of one member
    have hTT0 : (0:ℝ) ≤ τ ^ 2 * d ^ 3 := mul_nonneg (sq_nonneg _) (pow_nonneg hd0.le 3)
    have hmul := mul_le_mul_of_nonneg_right hknib hTT0
    have hexp1 : ((p : ℝ) ^ 2 * nu3star Hst - ε / 8 * ((p : ℝ) * (kp : ℝ)) ^ 2) * (τ ^ 2 * d ^ 3)
        = ((p : ℝ) * (L : ℝ)) ^ 2 * nu3star Hst * t
          - ε / 8 * (((p : ℝ) * (L : ℝ)) * (kp : ℝ)) ^ 2 * t := by
      rw [← hTTeq]; ring
    rw [hexp1] at hmul
    have hfinal : (D * (mmax : ℝ) ^ 2) * nu3star Hst
        ≤ (k : ℝ) * (3 * (d * (τ * d) * (τ * d))) / 3 + ε * (Fintype.card V : ℝ) ^ 2 := by
      have hid : (k : ℝ) * (3 * (d * (τ * d) * (τ * d))) / 3 = (k : ℝ) * (τ ^ 2 * d ^ 3) := by
        ring
      rw [hid]
      linarith only [harith, hmul]
    have hdiv3 : ∀ x y : ℝ, x ≤ y → x / 3 ≤ y / 3 := fun _ _ h => by linarith
    exact le_trans hhost (le_trans hfinal (add_le_add (hdiv3 _ _ hsumge) le_rfl))

/-! ### Axiom check -/

section AxCheck

#print axioms Nibble.AX1.blockCoverResidualCoupledNearUniform_holds

end AxCheck

end Nibble.AX1
