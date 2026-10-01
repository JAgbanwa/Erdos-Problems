import SublinearSequences
import PieceEdgeStability

/-! Arbitrary orders tending to infinity and an eventual nearness hypothesis.
One root controls both the count and the edge mass of all noncanonical pieces. -/
namespace PaperIV.SublinearResearch
open Finset Filter Asymptotics PaperIV.FarRounding PaperIV.RootedSimplicialDefect
open PaperIV.RootVocab PaperIV.RootPartitionStability

theorem sequence_arbitrary_orders_partition_bound
    (order : ℕ → ℕ) (horder : Tendsto order atTop atTop)
    (G : ∀ n : ℕ, SimpleGraph (Fin (order n))) [∀ n, DecidableRel (G n).Adj]
    (s : ℕ → ℕ) (hG : ∀ n, RootedDefectAt (G n) (s n))
    (hs : (fun n => (s n : ℝ)) =o[atTop] (fun n => (order n : ℝ))) :
    ∃ Q : ∀ n, CliquePartition (G n), (∀ n, (Q n).OrderAtMost 4) ∧
      (fun n => max 0 (((Q n).size : ℝ)-(order n : ℝ)^2/6))
        =o[atTop] (fun n => (order n : ℝ)^2) := by
  classical
  choose Q hQ hmin using fun n => exists_minimum_order_four_partition (G n)
  refine ⟨Q,hQ,?_⟩
  have hsRat := (rational_isLittleO_iff (fun n => (s n : ℚ)) (fun n => (order n : ℚ))).mp
    (by simpa using hs)
  have hexcess : (fun n => ((max 0 (((Q n).size : ℚ)-(order n : ℚ)^2/6) : ℚ) : ℝ))
      =o[atTop] (fun n => (((order n : ℚ)^2 : ℚ) : ℝ)) := by
    apply (rational_isLittleO_iff _ _).mpr
    intro ε hε
    obtain ⟨θ,hθ,N,hbound⟩ := uniform_sublinear_partition_bound ε hε
    filter_upwards [horder.eventually (eventually_ge_atTop N), hsRat θ hθ] with n hn hsn
    have hsn' : (s n : ℚ) ≤ θ*(order n) := by simpa using hsn
    obtain ⟨P,hP,hsize⟩ := hbound (order n) (s n) hn hsn' (G n) (hG n)
    have hmin' : ((Q n).size : ℚ) ≤ P.size := by exact_mod_cast hmin n P hP
    rw [abs_of_nonneg (le_max_left _ _), abs_of_nonneg (sq_nonneg _)]
    apply max_le
    · positivity
    · linarith
  simpa only [Rat.cast_max, Rat.cast_zero, Rat.cast_sub, Rat.cast_natCast,
    Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using hexcess

/-- One clique root per graph, selected independently of epsilon and of Q.
The nonnegative error e=o(n^2) simultaneously bounds noncanonical pieces in
ALL unrestricted clique partitions with size at most M(n)+tau.
-/
theorem sequence_arbitrary_orders_stability
    (order : ℕ → ℕ) (horder : Tendsto order atTop atTop)
    (G : ∀ n : ℕ, SimpleGraph (Fin (order n))) [∀ n, DecidableRel (G n).Adj]
    (s : ℕ → ℕ) (δ : ℕ → ℚ)
    (hG : ∀ n, RootedDefectAt (G n) (s n))
    (hs : (fun n => (s n : ℝ)) =o[atTop] (fun n => (order n : ℝ)))
    (hδ : (fun n => (δ n : ℝ)) =o[atTop] (fun n => (order n : ℝ)^2))
    (hnear : ∀ᶠ n in atTop, ∀ Q : CliquePartition (G n), Q.OrderAtMost 4 →
      (order n : ℚ)^2/6-δ n ≤ Q.size) :
    ∃ R : ∀ n, Finset (Fin (order n)), (∀ n, (G n).IsClique (R n : Set (Fin (order n)))) ∧
      (fun n => ((R n).card : ℝ)-(order n : ℝ)/3) =o[atTop] (fun n => (order n : ℝ)) ∧
      (fun n => (missingIncidences (G n) (R n) : ℝ)+(outsideEdges (G n) (R n)).card)
        =o[atTop] (fun n => (order n : ℝ)^2) ∧
      ∃ e : ℕ → ℚ, (∀ n, 0 ≤ e n) ∧
        (fun n => (e n : ℝ)) =o[atTop] (fun n => (order n : ℝ)^2) ∧
        (∀ n (Q : CliquePartition (G n)) (τ : ℚ), (Q.size : ℚ) ≤ targetSize (order n)+τ →
          ((noncanonicalPieces (R n) Q).card : ℚ) ≤ τ+e n) ∧
        (∀ n (Q : CliquePartition (G n)) (τ : ℚ), (Q.size : ℚ) ≤ targetSize (order n)+τ →
          (noncanonicalEdgeMass (R n) Q : ℚ) ≤ 10*τ+10*e n) := by
  classical
  choose R hR hmin using fun n => exists_minimum_rootScore (G n)
  have hsRat := (rational_isLittleO_iff (fun n => (s n : ℚ)) (fun n => (order n : ℚ))).mp
    (by simpa using hs)
  have hδRat := (rational_isLittleO_iff δ (fun n => (order n : ℚ)^2)).mp
    (by simpa using hδ)
  have hscore : ∀ ε : ℚ, 0 < ε → ∀ᶠ n in atTop,
      rootScore (G n) (R n) ≤ ε*(order n : ℚ)^2 := by
    intro ε hε
    let a : ℚ := min (ε/4) 1
    have ha : 0 < a := lt_min (by positivity) (by norm_num)
    have ha1 : a ≤ 1 := min_le_right _ _
    have haε : 4*a ≤ ε := by have := min_le_left (ε/4) (1 : ℚ); dsimp [a]; linarith
    obtain ⟨η,θ,hη,hθ,N,hloc⟩ := uniform_sublinear_localization a ha
    filter_upwards [horder.eventually (eventually_ge_atTop (max N 1)),hsRat θ hθ,hδRat η hη,hnear] with n hn hsn hδn hnnear
    have hsn' : (s n : ℚ) ≤ θ*(order n) := by simpa using hsn
    have hδn' : δ n ≤ η*(order n : ℚ)^2 :=
      (le_abs_self _).trans (by simpa using hδn)
    obtain ⟨S,hS,hw,hm,_⟩ := hloc (order n) (s n) ((le_max_left _ _).trans hn) hsn'
      (G n) (hG n) (fun Q hQ => by have := hnnear Q hQ; linarith)
    have hb := rootScore_le_of_localization (G n) S ((le_max_right _ _).trans hn) ha ha1 hw hm
    have hh := hmin n S hS
    have hscale := mul_le_mul_of_nonneg_right haε (sq_nonneg (order n : ℚ))
    linarith
  refine ⟨R,hR,?_,?_,fun n => 3*rootScore (G n) (R n),?_,?_,?_⟩
  · have hwin : (fun n => ((((R n).card : ℚ)-(order n : ℚ)/3 : ℚ) : ℝ))
        =o[atTop] (fun n => ((order n : ℚ) : ℝ)) := by
      apply (rational_isLittleO_iff _ _).mpr
      intro ε hε
      filter_upwards [horder.eventually (eventually_ge_atTop 1),hscore ε hε] with n hn hb
      have hnq : (0 : ℚ) < order n := by exact_mod_cast (show 0 < order n by omega)
      have hc := (rootScore_components (G n) (R n)).2.1
      rw [abs_of_nonneg (Nat.cast_nonneg (order n) : (0 : ℚ) ≤ (order n : ℚ))]
      apply le_of_mul_le_mul_right (a := (order n : ℚ)) _ hnq
      nlinarith only [hc,hb]
    simpa using hwin
  · have hmass : (fun n => (((missingIncidences (G n) (R n) : ℚ)+
          (outsideEdges (G n) (R n)).card : ℚ) : ℝ))
        =o[atTop] (fun n => (((order n : ℚ)^2 : ℚ) : ℝ)) := by
      apply (rational_isLittleO_iff _ _).mpr
      intro ε hε
      filter_upwards [hscore ε hε] with n hb
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (sq_nonneg _)]
      exact ((rootScore_components (G n) (R n)).2.2.1).trans hb
    simpa using hmass
  · intro n
    exact mul_nonneg (by norm_num) (rootScore_components (G n) (R n)).1
  · have he : (fun n => ((3*rootScore (G n) (R n) : ℚ) : ℝ))
        =o[atTop] (fun n => (((order n : ℚ)^2 : ℚ) : ℝ)) := by
      apply (rational_isLittleO_iff _ _).mpr
      intro ε hε
      filter_upwards [hscore (ε/3) (by positivity)] with n hb
      rw [abs_of_nonneg (mul_nonneg (by norm_num) (rootScore_components (G n) (R n)).1),
        abs_of_nonneg (sq_nonneg _)]
      linarith
    simpa using he
  · constructor
    · intro n Q τ hQ
      exact noncanonical_le_rootScore (G n) (hR n) Q τ hQ
    · intro n Q τ hQ
      have h := noncanonicalEdgeMass_le_rootScore (G n) (hR n) Q τ hQ
      linarith

end PaperIV.SublinearResearch
