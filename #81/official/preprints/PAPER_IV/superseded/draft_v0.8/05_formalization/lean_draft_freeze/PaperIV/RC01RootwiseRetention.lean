import PaperIV.RC01RootedMomentAdapter
import PaperIV.RC01RootwiseCleanupBudget

/-!
# RC01: from rooted moments to literal cleanup loss

This is the quantitative bridge certified first by Certo.  It keeps the two
physical scales separate: a rooted `K3` fibre has size at most `t`, while a
rooted `K4` fibre has size at most `t²`.
-/

namespace PaperIV.RC01RootwiseRetention

set_option maxHeartbeats 800000

open Finset
open PaperIV.PatternCounting
open PaperIV.PatternPoolGeometry
open PaperIV.RC01CleanFiber
open PaperIV.RC01RegularVolume
open PaperIV.RC01RootwiseReference
open PaperIV.RC01RootedMomentAdapter
open PaperIV.RegularityFormat
open PaperIV.PartitionBridge
open PaperIV.RootedCountingBridge

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-- For one physical root position of a regular triple, the total number of
copies deleted above its bad roots has the certified one-third budget. -/
theorem three_mul_rootLoss3_le {δ u c v : ℚ}
    (hδ : 0 ≤ δ) (hu : 0 < u) (hc : 0 < c) (hv : 0 ≤ v)
    (R : EqualRegularity G δ) (V : Fin 3 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVinj : Function.Injective V)
    (hcard : ∀ i, (V i).card = R.size)
    (hdisc : ∀ i j : Fin 3, i ≠ j →
      PaperIV.OneStepEstimate.DiscrepAt G δ
        (G.edgeDensity (V i) (V j)) (V i) (V j))
    (hvolume : c * (R.size : ℚ) ^ 3 ≤
      profileVolume (G := G) (partOf R) (regularPattern V))
    (hvchoice : 33 * δ ≤ v * u ^ 2 * c ^ 3)
    {pq : Finset (Option (Finset α))}
    (hpq : pq ∈ (regularPattern V).powersetCard 2) :
    3 * (∑ e ∈ badRoots G (partOf R)
        (rootwiseReference (G := G) (partOf R)) u (regularPattern V) pq,
      ((fiber (profileFiber G (partOf R) (regularPattern V))
        (rootEdge (partOf R) pq) e).card : ℚ))
      ≤ v * profileVolume (G := G) (partOf R) (regularPattern V) := by
  have htN : 1 ≤ R.size := R.size_pos
  have ht : (0 : ℚ) < R.size := by exact_mod_cast R.size_pos
  rw [Finset.mem_powersetCard] at hpq
  have hne : (profileFiber G (partOf R) (regularPattern V)).Nonempty := by
    rw [profileVolume_eq_card] at hvolume
    have hpos : (0 : ℚ) < c * (R.size : ℚ) ^ 3 := by positivity
    have : (0 : ℚ) < ((profileFiber G (partOf R) (regularPattern V)).card : ℚ) :=
      hpos.trans_le hvolume
    exact Finset.card_pos.1 (by exact_mod_cast this)
  let A := rootwiseReference (G := G) (partOf R) (regularPattern V) pq
  let β : ℚ := ((badRoots G (partOf R)
    (rootwiseReference (G := G) (partOf R)) u (regularPattern V) pq).card : ℚ)
  have hmean : c * (R.size : ℚ) ≤ A := by
    apply rootwiseReference_lower_of_volume_scale (G := G) hpq.2 hpq.1
      (show (0 : ℚ) < (R.size : ℚ) ^ 2 by positivity)
    · calc
        (c * (R.size : ℚ)) * (R.size : ℚ) ^ 2
            = c * (R.size : ℚ) ^ 3 := by ring
        _ ≤ profileVolume (G := G) (partOf R) (regularPattern V) := hvolume
    · exact pairScale_le_sq_any_root3 R V hV hVinj htN hcard hpq.2 hpq.1
  have hmoment : β * (u * A) ^ 2 ≤ 11 * δ * (R.size : ℚ) ^ 4 := by
    exact badRoots_mul_sq_le_any_root3 hδ R V hV hVinj hcard hdisc hne hu
      (Finset.mem_powersetCard.2 hpq)
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have huscale : u * (c * (R.size : ℚ)) ≤ u * A :=
    mul_le_mul_of_nonneg_left hmean (le_of_lt hu)
  have hA0 : 0 ≤ A := (show (0 : ℚ) ≤ c * (R.size : ℚ) by positivity).trans hmean
  have hsquare : (u * (c * (R.size : ℚ))) ^ 2 ≤ (u * A) ^ 2 :=
    (sq_le_sq₀ (by positivity) (mul_nonneg (le_of_lt hu) hA0)).2 huscale
  have hbadScaled : (β * u ^ 2 * c ^ 2) * (R.size : ℚ) ^ 2
      ≤ (11 * δ * (R.size : ℚ) ^ 2) * (R.size : ℚ) ^ 2 := by
    calc
      (β * u ^ 2 * c ^ 2) * (R.size : ℚ) ^ 2
          = β * (u * (c * (R.size : ℚ))) ^ 2 := by ring
      _ ≤ β * (u * A) ^ 2 := mul_le_mul_of_nonneg_left hsquare hβ
      _ ≤ 11 * δ * (R.size : ℚ) ^ 4 := hmoment
      _ = (11 * δ * (R.size : ℚ) ^ 2) * (R.size : ℚ) ^ 2 := by ring
  have hbad : β * u ^ 2 * c ^ 2 ≤ 11 * δ * (R.size : ℚ) ^ 2 :=
    le_of_mul_le_mul_right hbadScaled (by positivity)
  have hrootBudget : 3 * β * (R.size : ℚ) ≤
      v * profileVolume (G := G) (partOf R) (regularPattern V) :=
    PaperIV.RC01RootwiseCleanupBudget.k3_loss_le hu ht hc hv hbad hvolume hvchoice
  have hsum : (∑ e ∈ badRoots G (partOf R)
        (rootwiseReference (G := G) (partOf R)) u (regularPattern V) pq,
      ((fiber (profileFiber G (partOf R) (regularPattern V))
        (rootEdge (partOf R) pq) e).card : ℚ)) ≤ β * (R.size : ℚ) := by
    calc
      _ ≤ ∑ _e ∈ badRoots G (partOf R)
          (rootwiseReference (G := G) (partOf R)) u (regularPattern V) pq,
          (R.size : ℚ) := by
            apply Finset.sum_le_sum
            intro e he
            exact_mod_cast physical_rootFiber3_card_le_any_root R V hV hVinj hcard
              hpq.2 hpq.1 e
      _ = β * (R.size : ℚ) := by
            simp [β]
  calc
    3 * (∑ e ∈ badRoots G (partOf R)
        (rootwiseReference (G := G) (partOf R)) u (regularPattern V) pq,
      ((fiber (profileFiber G (partOf R) (regularPattern V))
        (rootEdge (partOf R) pq) e).card : ℚ))
        ≤ 3 * (β * (R.size : ℚ)) := by gcongr
    _ = 3 * β * (R.size : ℚ) := by ring
    _ ≤ v * profileVolume (G := G) (partOf R) (regularPattern V) := hrootBudget

/-- The corresponding one-sixth budget for one physical root position of a
regular `K4`. -/
theorem six_mul_rootLoss4_le {δ u c v : ℚ}
    (hδ : 0 ≤ δ) (hu : 0 < u) (hc : 0 < c) (hv : 0 ≤ v)
    (R : EqualRegularity G δ) (V : Fin 4 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVinj : Function.Injective V)
    (hcard : ∀ i, (V i).card = R.size)
    (hdisc : ∀ i j : Fin 4, i ≠ j →
      PaperIV.OneStepEstimate.DiscrepAt G δ
        (G.edgeDensity (V i) (V j)) (V i) (V j))
    (hvolume : c * (R.size : ℚ) ^ 4 ≤
      profileVolume (G := G) (partOf R) (regularPattern V))
    (hvchoice : 138 * δ ≤ v * u ^ 2 * c ^ 3)
    {pq : Finset (Option (Finset α))}
    (hpq : pq ∈ (regularPattern V).powersetCard 2) :
    6 * (∑ e ∈ badRoots G (partOf R)
        (rootwiseReference (G := G) (partOf R)) u (regularPattern V) pq,
      ((fiber (profileFiber G (partOf R) (regularPattern V))
        (rootEdge (partOf R) pq) e).card : ℚ))
      ≤ v * profileVolume (G := G) (partOf R) (regularPattern V) := by
  have htN : 1 ≤ R.size := R.size_pos
  have ht : (0 : ℚ) < R.size := by exact_mod_cast R.size_pos
  rw [Finset.mem_powersetCard] at hpq
  have hne : (profileFiber G (partOf R) (regularPattern V)).Nonempty := by
    rw [profileVolume_eq_card] at hvolume
    have hpos : (0 : ℚ) < c * (R.size : ℚ) ^ 4 := by positivity
    have : (0 : ℚ) < ((profileFiber G (partOf R) (regularPattern V)).card : ℚ) :=
      hpos.trans_le hvolume
    exact Finset.card_pos.1 (by exact_mod_cast this)
  let A := rootwiseReference (G := G) (partOf R) (regularPattern V) pq
  let β : ℚ := ((badRoots G (partOf R)
    (rootwiseReference (G := G) (partOf R)) u (regularPattern V) pq).card : ℚ)
  have hmean : c * (R.size : ℚ) ^ 2 ≤ A := by
    apply rootwiseReference_lower_of_volume_scale (G := G) hpq.2 hpq.1
      (show (0 : ℚ) < (R.size : ℚ) ^ 2 by positivity)
    · calc
        (c * (R.size : ℚ) ^ 2) * (R.size : ℚ) ^ 2
            = c * (R.size : ℚ) ^ 4 := by ring
        _ ≤ profileVolume (G := G) (partOf R) (regularPattern V) := hvolume
    · exact pairScale_le_sq_any_root4 R V hV hVinj htN hcard hpq.2 hpq.1
  have hmoment : β * (u * A) ^ 2 ≤ 23 * δ * (R.size : ℚ) ^ 6 := by
    exact badRoots_mul_sq_le_any_root4 hδ R V hV hVinj hcard hdisc hne hu
      (Finset.mem_powersetCard.2 hpq)
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have huscale : u * (c * (R.size : ℚ) ^ 2) ≤ u * A :=
    mul_le_mul_of_nonneg_left hmean (le_of_lt hu)
  have hA0 : 0 ≤ A :=
    (show (0 : ℚ) ≤ c * (R.size : ℚ) ^ 2 by positivity).trans hmean
  have hsquare : (u * (c * (R.size : ℚ) ^ 2)) ^ 2 ≤ (u * A) ^ 2 :=
    (sq_le_sq₀ (by positivity) (mul_nonneg (le_of_lt hu) hA0)).2 huscale
  have hbadScaled : (β * u ^ 2 * c ^ 2) * (R.size : ℚ) ^ 4
      ≤ (23 * δ * (R.size : ℚ) ^ 2) * (R.size : ℚ) ^ 4 := by
    calc
      (β * u ^ 2 * c ^ 2) * (R.size : ℚ) ^ 4
          = β * (u * (c * (R.size : ℚ) ^ 2)) ^ 2 := by ring
      _ ≤ β * (u * A) ^ 2 := mul_le_mul_of_nonneg_left hsquare hβ
      _ ≤ 23 * δ * (R.size : ℚ) ^ 6 := hmoment
      _ = (23 * δ * (R.size : ℚ) ^ 2) * (R.size : ℚ) ^ 4 := by ring
  have hbad : β * u ^ 2 * c ^ 2 ≤ 23 * δ * (R.size : ℚ) ^ 2 :=
    le_of_mul_le_mul_right hbadScaled (by positivity)
  have hrootBudget : 6 * β * (R.size : ℚ) ^ 2 ≤
      v * profileVolume (G := G) (partOf R) (regularPattern V) :=
    PaperIV.RC01RootwiseCleanupBudget.k4_loss_le hu ht hc hv hbad hvolume hvchoice
  have hsum : (∑ e ∈ badRoots G (partOf R)
        (rootwiseReference (G := G) (partOf R)) u (regularPattern V) pq,
      ((fiber (profileFiber G (partOf R) (regularPattern V))
        (rootEdge (partOf R) pq) e).card : ℚ)) ≤ β * (R.size : ℚ) ^ 2 := by
    calc
      _ ≤ ∑ _e ∈ badRoots G (partOf R)
          (rootwiseReference (G := G) (partOf R)) u (regularPattern V) pq,
          ((R.size : ℚ) ^ 2) := by
            apply Finset.sum_le_sum
            intro e he
            exact_mod_cast physical_rootFiber4_card_le_any_root R V hV hVinj hcard
              hpq.2 hpq.1 e
      _ = β * (R.size : ℚ) ^ 2 := by simp [β]
  calc
    6 * (∑ e ∈ badRoots G (partOf R)
        (rootwiseReference (G := G) (partOf R)) u (regularPattern V) pq,
      ((fiber (profileFiber G (partOf R) (regularPattern V))
        (rootEdge (partOf R) pq) e).card : ℚ))
        ≤ 6 * (β * (R.size : ℚ) ^ 2) := by gcongr
    _ = 6 * β * (R.size : ℚ) ^ 2 := by ring
    _ ≤ v * profileVolume (G := G) (partOf R) (regularPattern V) := hrootBudget

/-- All three root positions can be cleaned simultaneously with total relative
loss `v`. -/
theorem cleanFiber_card_ge_rootwise_K3 {δ u c v : ℚ}
    (hδ : 0 ≤ δ) (hu : 0 < u) (hc : 0 < c) (hv : 0 ≤ v)
    (R : EqualRegularity G δ) (V : Fin 3 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVinj : Function.Injective V)
    (hcard : ∀ i, (V i).card = R.size)
    (hdisc : ∀ i j : Fin 3, i ≠ j →
      PaperIV.OneStepEstimate.DiscrepAt G δ
        (G.edgeDensity (V i) (V j)) (V i) (V j))
    (hvolume : c * (R.size : ℚ) ^ 3 ≤
      profileVolume (G := G) (partOf R) (regularPattern V))
    (hvchoice : 33 * δ ≤ v * u ^ 2 * c ^ 3) :
    (1 - v) * profileVolume (G := G) (partOf R) (regularPattern V) ≤
      ((cleanFiber G (partOf R)
        (rootwiseReference (G := G) (partOf R)) u (regularPattern V)).card : ℚ) := by
  let L := fun pq : Finset (Option (Finset α)) =>
    ∑ e ∈ badRoots G (partOf R)
        (rootwiseReference (G := G) (partOf R)) u (regularPattern V) pq,
      ((fiber (profileFiber G (partOf R) (regularPattern V))
        (rootEdge (partOf R) pq) e).card : ℚ)
  have hscaled : 3 * (∑ pq ∈ (regularPattern V).powersetCard 2, L pq)
      ≤ 3 * (v * profileVolume (G := G) (partOf R) (regularPattern V)) := by
    calc
      3 * (∑ pq ∈ (regularPattern V).powersetCard 2, L pq)
          = ∑ pq ∈ (regularPattern V).powersetCard 2, 3 * L pq := by
              rw [Finset.mul_sum]
      _ ≤ ∑ _pq ∈ (regularPattern V).powersetCard 2,
          v * profileVolume (G := G) (partOf R) (regularPattern V) := by
            apply Finset.sum_le_sum
            intro pq hpq
            exact three_mul_rootLoss3_le hδ hu hc hv R V hV hVinj hcard hdisc
              hvolume hvchoice hpq
      _ = 3 * (v * profileVolume (G := G) (partOf R) (regularPattern V)) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard,
              card_regularPattern V hVinj]
            norm_num [Nat.choose]
  have hloss : ∑ pq ∈ (regularPattern V).powersetCard 2, L pq
      ≤ v * profileVolume (G := G) (partOf R) (regularPattern V) :=
    le_of_mul_le_mul_left hscaled (by norm_num)
  apply cleanFiber_card_ge_of_total_root_loss (G := G) (partOf R)
    (rootwiseReference (G := G) (partOf R)) u (regularPattern V)
  · rw [profileVolume_eq_card]
  · exact hloss

/-- All six root positions of a `K4` can be cleaned simultaneously with total
relative loss `v`. -/
theorem cleanFiber_card_ge_rootwise_K4 {δ u c v : ℚ}
    (hδ : 0 ≤ δ) (hu : 0 < u) (hc : 0 < c) (hv : 0 ≤ v)
    (R : EqualRegularity G δ) (V : Fin 4 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVinj : Function.Injective V)
    (hcard : ∀ i, (V i).card = R.size)
    (hdisc : ∀ i j : Fin 4, i ≠ j →
      PaperIV.OneStepEstimate.DiscrepAt G δ
        (G.edgeDensity (V i) (V j)) (V i) (V j))
    (hvolume : c * (R.size : ℚ) ^ 4 ≤
      profileVolume (G := G) (partOf R) (regularPattern V))
    (hvchoice : 138 * δ ≤ v * u ^ 2 * c ^ 3) :
    (1 - v) * profileVolume (G := G) (partOf R) (regularPattern V) ≤
      ((cleanFiber G (partOf R)
        (rootwiseReference (G := G) (partOf R)) u (regularPattern V)).card : ℚ) := by
  let L := fun pq : Finset (Option (Finset α)) =>
    ∑ e ∈ badRoots G (partOf R)
        (rootwiseReference (G := G) (partOf R)) u (regularPattern V) pq,
      ((fiber (profileFiber G (partOf R) (regularPattern V))
        (rootEdge (partOf R) pq) e).card : ℚ)
  have hscaled : 6 * (∑ pq ∈ (regularPattern V).powersetCard 2, L pq)
      ≤ 6 * (v * profileVolume (G := G) (partOf R) (regularPattern V)) := by
    calc
      6 * (∑ pq ∈ (regularPattern V).powersetCard 2, L pq)
          = ∑ pq ∈ (regularPattern V).powersetCard 2, 6 * L pq := by
              rw [Finset.mul_sum]
      _ ≤ ∑ _pq ∈ (regularPattern V).powersetCard 2,
          v * profileVolume (G := G) (partOf R) (regularPattern V) := by
            apply Finset.sum_le_sum
            intro pq hpq
            exact six_mul_rootLoss4_le hδ hu hc hv R V hV hVinj hcard hdisc
              hvolume hvchoice hpq
      _ = 6 * (v * profileVolume (G := G) (partOf R) (regularPattern V)) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard,
              card_regularPattern V hVinj]
            norm_num [Nat.choose]
  have hloss : ∑ pq ∈ (regularPattern V).powersetCard 2, L pq
      ≤ v * profileVolume (G := G) (partOf R) (regularPattern V) :=
    le_of_mul_le_mul_left hscaled (by norm_num)
  apply cleanFiber_card_ge_of_total_root_loss (G := G) (partOf R)
    (rootwiseReference (G := G) (partOf R)) u (regularPattern V)
  · rw [profileVolume_eq_card]
  · exact hloss

/-- Ready-to-use regular-triple instance: the lower-volume premise is derived
from the literal regular counting lemma. -/
theorem cleanFiber_card_ge_regular_K3 {δ d₀ u v : ℚ}
    (hδ : 0 ≤ δ) (hd₀ : 0 ≤ d₀) (hu : 0 < u) (hv : 0 ≤ v)
    (hcoef : 0 < d₀ ^ 3 - 3 * δ)
    (R : EqualRegularity G δ) (V : Fin 3 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVinj : Function.Injective V)
    (hcard : ∀ i, (V i).card = R.size)
    (hdisc : ∀ i j : Fin 3, i ≠ j →
      PaperIV.OneStepEstimate.DiscrepAt G δ
        (G.edgeDensity (V i) (V j)) (V i) (V j))
    (hgood : ∀ e ∈ patK3, (V e.1, V e.2) ∉ R.bad)
    (hdens : ∀ e ∈ patK3, d₀ ≤ G.edgeDensity (V e.1) (V e.2))
    (hvchoice : 33 * δ ≤ v * u ^ 2 * (d₀ ^ 3 - 3 * δ) ^ 3) :
    (1 - v) * profileVolume (G := G) (partOf R) (regularPattern V) ≤
      ((cleanFiber G (partOf R)
        (rootwiseReference (G := G) (partOf R)) u (regularPattern V)).card : ℚ) := by
  have hvolume : (d₀ ^ 3 - 3 * δ) * (R.size : ℚ) ^ 3 ≤
      profileVolume (G := G) (partOf R) (regularPattern V) := by
    calc
      (d₀ ^ 3 - 3 * δ) * (R.size : ℚ) ^ 3
          ≤ patCount G V patK3 :=
            patCount_K3_ge hδ hd₀ R V hV
              (fun e he hEq => patK3_ne e he (hVinj hEq)) hgood hdens
      _ ≤ profileVolume (G := G) (partOf R) (regularPattern V) := by
            rw [profileVolume_eq_card]
            exact patCount_K3_le_profileFiber R V hV hVinj
  exact cleanFiber_card_ge_rootwise_K3 hδ hu hcoef hv R V hV hVinj hcard hdisc
    hvolume hvchoice

/-- Ready-to-use regular-`K4` instance. -/
theorem cleanFiber_card_ge_regular_K4 {δ d₀ u v : ℚ}
    (hδ : 0 ≤ δ) (hd₀ : 0 ≤ d₀) (hu : 0 < u) (hv : 0 ≤ v)
    (hcoef : 0 < d₀ ^ 6 - 6 * δ)
    (R : EqualRegularity G δ) (V : Fin 4 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVinj : Function.Injective V)
    (hcard : ∀ i, (V i).card = R.size)
    (hdisc : ∀ i j : Fin 4, i ≠ j →
      PaperIV.OneStepEstimate.DiscrepAt G δ
        (G.edgeDensity (V i) (V j)) (V i) (V j))
    (hgood : ∀ e ∈ patK4, (V e.1, V e.2) ∉ R.bad)
    (hdens : ∀ e ∈ patK4, d₀ ≤ G.edgeDensity (V e.1) (V e.2))
    (hvchoice : 138 * δ ≤ v * u ^ 2 * (d₀ ^ 6 - 6 * δ) ^ 3) :
    (1 - v) * profileVolume (G := G) (partOf R) (regularPattern V) ≤
      ((cleanFiber G (partOf R)
        (rootwiseReference (G := G) (partOf R)) u (regularPattern V)).card : ℚ) := by
  have hvolume : (d₀ ^ 6 - 6 * δ) * (R.size : ℚ) ^ 4 ≤
      profileVolume (G := G) (partOf R) (regularPattern V) := by
    calc
      (d₀ ^ 6 - 6 * δ) * (R.size : ℚ) ^ 4
          ≤ patCount G V patK4 :=
            patCount_K4_ge hδ hd₀ R V hV
              (fun e he hEq => patK4_ne e he (hVinj hEq)) hgood hdens
      _ ≤ profileVolume (G := G) (partOf R) (regularPattern V) := by
            rw [profileVolume_eq_card]
            exact patCount_K4_le_profileFiber R V hV hVinj
  exact cleanFiber_card_ge_rootwise_K4 hδ hu hcoef hv R V hV hVinj hcard hdisc
    hvolume hvchoice

end PaperIV.RC01RootwiseRetention
