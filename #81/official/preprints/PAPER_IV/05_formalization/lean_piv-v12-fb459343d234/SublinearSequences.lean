import AsymptoticTools
import RootScore
import SublinearPartitionBound

/-! Literal sequence versions of the uniform theorems. The bound on partition
size uses positive excess: sparse graphs need not have size asymptotic to n^2/6.
The structural root is selected once and works for every unrestricted partition.
-/
namespace PaperIV.SublinearResearch
open Finset Filter Asymptotics PaperIV.FarRounding PaperIV.RootedSimplicialDefect
open PaperIV.RootVocab PaperIV.RootPartitionStability

theorem exists_minimum_order_four_partition {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
      ∀ P : CliquePartition G, P.OrderAtMost 4 → Q.size ≤ P.size := by
  classical
  have hex : ∃ m : ℕ, ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size = m := by
    obtain ⟨Q,hQ,_⟩ := exists_cliquePartition_of_packing (Packing.empty : Packing G)
    exact ⟨Q.size,Q,hQ,rfl⟩
  obtain ⟨Q,hQ,hsize⟩ := Nat.find_spec hex
  refine ⟨Q,hQ,fun P hP => ?_⟩
  rw [hsize]
  exact Nat.find_min' hex ⟨P,hP,rfl⟩

theorem sequence_sublinear_partition_bound
    (G : ∀ n : ℕ, SimpleGraph (Fin n)) [∀ n, DecidableRel (G n).Adj]
    (s : ℕ → ℕ) (hG : ∀ n, RootedDefectAt (G n) (s n))
    (hs : (fun n => (s n : ℝ)) =o[atTop] (fun n => (n : ℝ))) :
    ∃ Q : ∀ n, CliquePartition (G n), (∀ n, (Q n).OrderAtMost 4) ∧
      (fun n => max 0 (((Q n).size : ℝ)-(n : ℝ)^2/6))
        =o[atTop] (fun n => (n : ℝ)^2) := by
  classical
  choose Q hQ hmin using fun n => exists_minimum_order_four_partition (G n)
  refine ⟨Q,hQ,?_⟩
  have hsRat := (rational_isLittleO_iff (fun n => (s n : ℚ)) (fun n => (n : ℚ))).mp
    (by simpa using hs)
  have hexcess : (fun n => ((max 0 (((Q n).size : ℚ)-(n : ℚ)^2/6) : ℚ) : ℝ))
      =o[atTop] (fun n => (((n : ℚ)^2 : ℚ) : ℝ)) := by
    apply (rational_isLittleO_iff _ _).mpr
    intro ε hε
    obtain ⟨θ,hθ,N,hbound⟩ := uniform_sublinear_partition_bound ε hε
    filter_upwards [eventually_ge_atTop N, hsRat θ hθ] with n hn hsn
    have hsn' : (s n : ℚ) ≤ θ*n := by simpa using hsn
    obtain ⟨P,hP,hsize⟩ := hbound n (s n) hn hsn' (G n) (hG n)
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
theorem sequence_sublinear_stability
    (G : ∀ n : ℕ, SimpleGraph (Fin n)) [∀ n, DecidableRel (G n).Adj]
    (s : ℕ → ℕ) (δ : ℕ → ℚ)
    (hG : ∀ n, RootedDefectAt (G n) (s n))
    (hs : (fun n => (s n : ℝ)) =o[atTop] (fun n => (n : ℝ)))
    (hδ : (fun n => (δ n : ℝ)) =o[atTop] (fun n => (n : ℝ)^2))
    (hnear : ∀ n, ∀ Q : CliquePartition (G n), Q.OrderAtMost 4 →
      (n : ℚ)^2/6-δ n ≤ Q.size) :
    ∃ R : ∀ n, Finset (Fin n), (∀ n, (G n).IsClique (R n : Set (Fin n))) ∧
      (fun n => ((R n).card : ℝ)-(n : ℝ)/3) =o[atTop] (fun n => (n : ℝ)) ∧
      (fun n => (missingIncidences (G n) (R n) : ℝ)+(outsideEdges (G n) (R n)).card)
        =o[atTop] (fun n => (n : ℝ)^2) ∧
      ∃ e : ℕ → ℚ, (∀ n, 0 ≤ e n) ∧
        (fun n => (e n : ℝ)) =o[atTop] (fun n => (n : ℝ)^2) ∧
        ∀ n (Q : CliquePartition (G n)) (τ : ℚ), (Q.size : ℚ) ≤ targetSize n+τ →
          ((noncanonicalPieces (R n) Q).card : ℚ) ≤ τ+e n := by
  classical
  choose R hR hmin using fun n => exists_minimum_rootScore (G n)
  have hsRat := (rational_isLittleO_iff (fun n => (s n : ℚ)) (fun n => (n : ℚ))).mp
    (by simpa using hs)
  have hδRat := (rational_isLittleO_iff δ (fun n => (n : ℚ)^2)).mp
    (by simpa using hδ)
  have hscore : ∀ ε : ℚ, 0 < ε → ∀ᶠ n in atTop,
      rootScore (G n) (R n) ≤ ε*(n : ℚ)^2 := by
    intro ε hε
    let a : ℚ := min (ε/4) 1
    have ha : 0 < a := lt_min (by positivity) (by norm_num)
    have ha1 : a ≤ 1 := min_le_right _ _
    have haε : 4*a ≤ ε := by have := min_le_left (ε/4) (1 : ℚ); dsimp [a]; linarith
    obtain ⟨η,θ,hη,hθ,N,hloc⟩ := uniform_sublinear_localization a ha
    filter_upwards [eventually_ge_atTop (max N 1),hsRat θ hθ,hδRat η hη] with n hn hsn hδn
    have hsn' : (s n : ℚ) ≤ θ*n := by simpa using hsn
    have hδn' : δ n ≤ η*(n : ℚ)^2 :=
      (le_abs_self _).trans (by simpa using hδn)
    obtain ⟨S,hS,hw,hm,_⟩ := hloc n (s n) ((le_max_left _ _).trans hn) hsn'
      (G n) (hG n) (fun Q hQ => by have := hnear n Q hQ; linarith)
    have hb := rootScore_le_of_localization (G n) S ((le_max_right _ _).trans hn) ha ha1 hw hm
    have hh := hmin n S hS
    have hscale := mul_le_mul_of_nonneg_right haε (sq_nonneg (n : ℚ))
    linarith
  refine ⟨R,hR,?_,?_,fun n => 3*rootScore (G n) (R n),?_,?_,?_⟩
  · have hwin : (fun n => ((((R n).card : ℚ)-(n : ℚ)/3 : ℚ) : ℝ))
        =o[atTop] (fun n => ((n : ℚ) : ℝ)) := by
      apply (rational_isLittleO_iff _ _).mpr
      intro ε hε
      filter_upwards [eventually_ge_atTop 1,hscore ε hε] with n hn hb
      have hnq : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
      have hc := (rootScore_components (G n) (R n)).2.1
      rw [abs_of_nonneg (Nat.cast_nonneg n : (0 : ℚ) ≤ (n : ℚ))]
      apply le_of_mul_le_mul_right (a := (n : ℚ)) _ hnq
      nlinarith only [hc,hb]
    simpa using hwin
  · have hmass : (fun n => (((missingIncidences (G n) (R n) : ℚ)+
          (outsideEdges (G n) (R n)).card : ℚ) : ℝ))
        =o[atTop] (fun n => (((n : ℚ)^2 : ℚ) : ℝ)) := by
      apply (rational_isLittleO_iff _ _).mpr
      intro ε hε
      filter_upwards [hscore ε hε] with n hb
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (sq_nonneg _)]
      exact ((rootScore_components (G n) (R n)).2.2.1).trans hb
    simpa using hmass
  · intro n
    exact mul_nonneg (by norm_num) (rootScore_components (G n) (R n)).1
  · have he : (fun n => ((3*rootScore (G n) (R n) : ℚ) : ℝ))
        =o[atTop] (fun n => (((n : ℚ)^2 : ℚ) : ℝ)) := by
      apply (rational_isLittleO_iff _ _).mpr
      intro ε hε
      filter_upwards [hscore (ε/3) (by positivity)] with n hb
      rw [abs_of_nonneg (mul_nonneg (by norm_num) (rootScore_components (G n) (R n)).1),
        abs_of_nonneg (sq_nonneg _)]
      linarith
    simpa using he
  · intro n Q τ hQ
    exact noncanonical_le_rootScore (G n) (hR n) Q τ hQ

end PaperIV.SublinearResearch
#print axioms PaperIV.SublinearResearch.sequence_sublinear_partition_bound
#print axioms PaperIV.SublinearResearch.sequence_sublinear_stability
