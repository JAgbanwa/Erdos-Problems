import SublinearStability

/-! Sublinear-defect near-extremal localization, including a size window.
The integral formulation is stronger than assuming a near-extremal certified
fractional optimum. Both are exported, and neither uses a chosen partition root.
-/
namespace PaperIV.SublinearResearch
open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect
open PaperIV.RootVocab PaperIV.RootPartitionStability

private theorem window_arithmetic {x v : ℚ} (hv : 10 ≤ v)
    (h : (3/2 : ℚ)*(x-1/6)^2 ≤ v^2/100+1) : |x| ≤ v := by
  rw [abs_le]
  constructor
  · by_contra hn
    have hlt : x < -v := lt_of_not_ge hn
    have hp : 0 ≤ (-x-v)*(-x+v) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  · by_contra hn
    have hlt : v < x := lt_of_not_ge hn
    have hp : 0 ≤ (x-v)*(x+v-1/3) := mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- Uniform integral localization under rsd(G) <= theta*n. The root is a
clique in G itself and works simultaneously for all unrestricted partitions. -/
theorem uniform_sublinear_localization (ε : ℚ) (hε : 0 < ε) :
    ∃ η θ : ℚ, 0 < η ∧ 0 < θ ∧ ∃ N : ℕ, ∀ n s : ℕ, N ≤ n →
    (s : ℚ) ≤ θ*n → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj],
    RootedDefectAt G s →
    (∀ Q : CliquePartition G, Q.OrderAtMost 4 →
      (n : ℚ)^2/6-η*(n : ℚ)^2 ≤ Q.size) →
    ∃ R : Finset (Fin n), G.IsClique (R : Set (Fin n)) ∧
      |(R.card : ℚ)-(n : ℚ)/3| ≤ ε*n ∧
      (missingIncidences G R : ℚ)+(outsideEdges G R).card ≤ ε*(n : ℚ)^2 ∧
      ∀ (Q : CliquePartition G) (τ : ℚ), (Q.size : ℚ) ≤ targetSize n+τ →
        ((noncanonicalPieces R Q).card : ℚ) ≤ τ+ε*(n : ℚ)^2 := by
  classical
  let e : ℚ := min ε 1
  have he : 0 < e := lt_min hε (by norm_num)
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  have he2 : e^2 ≤ e := by nlinarith
  have heacc : e^2/100 ≤ ε := by nlinarith
  obtain ⟨η,θ,hη,hθ,N,hstab⟩ := uniform_sublinear_stability (e^2/100) (by positivity)
  refine ⟨η/2,θ,by positivity,hθ,max N (max ⌈1/η⌉₊ ⌈10/e⌉₊),?_⟩
  intro n s hn hs G _ hG hmin
  have hN : N ≤ n := (le_max_left _ _).trans hn
  have hceilη : ⌈1/η⌉₊ ≤ n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hceile : ⌈10/e⌉₊ ≤ n :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hηrec : 1/η ≤ (n : ℚ) := (Nat.le_ceil _).trans (by exact_mod_cast hceilη)
  have herec : 10/e ≤ (n : ℚ) := (Nat.le_ceil _).trans (by exact_mod_cast hceile)
  have hηn : 1 ≤ (n : ℚ)*η := (div_le_iff₀ hη).mp hηrec
  have hen : 10 ≤ (n : ℚ)*e := (div_le_iff₀ he).mp herec
  have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg _
  have hscale := mul_le_mul_of_nonneg_left hηn hn0
  have htarget := targetSize_cast_le_continuous n
  have hmin' : ∀ Q : CliquePartition G, Q.OrderAtMost 4 →
      (targetSize n : ℚ)-η*(n : ℚ)^2 ≤ Q.size := by
    intro Q hQ
    have hp := hmin Q hQ
    nlinarith only [hp,htarget,hscale]
  obtain ⟨R,hR,hedit,_,hgap,hpart⟩ := hstab n s hN hs G hG hmin'
  have hescale := mul_le_mul_of_nonneg_right heacc (sq_nonneg (n : ℚ))
  have hdev := FixedL4.sq_dev_le_of_targetSize_sub_baseline n (R.card : ℚ)
  have hdev' : (3/2 : ℚ)*((R.card : ℚ)-(n : ℚ)/3-1/6)^2 ≤
      (e*n)^2/100+1 := by nlinarith only [hdev,hgap]
  have hwindow := window_arithmetic (v := e*n) (by nlinarith only [hen]) hdev'
  refine ⟨R,hR,hwindow.trans (mul_le_mul_of_nonneg_right heε hn0),?_,?_⟩
  · rw [SplitEditIdentity.editDist_split_eq G hR] at hedit
    push_cast at hedit
    linarith only [hedit,hescale]
  · intro Q τ hQ
    exact (hpart Q τ hQ).trans (by linarith only [hescale])

/-- The same uniform structural and partition conclusion from F4-nearness.
The value w is linked to the actual graph by primal-dual certification. -/
theorem uniform_sublinear_fractional_localization (ε : ℚ) (hε : 0 < ε) :
    ∃ η θ : ℚ, 0 < η ∧ 0 < θ ∧ ∃ N : ℕ, ∀ n s : ℕ, N ≤ n →
    (s : ℚ) ≤ θ*n → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj],
    RootedDefectAt G s → ∀ w : ℚ, CertifiedFractionalOptimum G w →
    (n : ℚ)^2/6-η*(n : ℚ)^2 ≤ (G.edgeFinset.card : ℚ)-w →
    ∃ R : Finset (Fin n), G.IsClique (R : Set (Fin n)) ∧
      |(R.card : ℚ)-(n : ℚ)/3| ≤ ε*n ∧
      (missingIncidences G R : ℚ)+(outsideEdges G R).card ≤ ε*(n : ℚ)^2 ∧
      ∀ (Q : CliquePartition G) (τ : ℚ), (Q.size : ℚ) ≤ targetSize n+τ →
        ((noncanonicalPieces R Q).card : ℚ) ≤ τ+ε*(n : ℚ)^2 := by
  obtain ⟨η,θ,hη,hθ,N,h⟩ := uniform_sublinear_localization ε hε
  refine ⟨η,θ,hη,hθ,N,?_⟩
  intro n s hn hs G _ hG w hw hnear
  exact h n s hn hs G hG (fun Q hQ =>
    hnear.trans (FixedL4.size_ge_edge_sub_certified hw Q hQ))

end PaperIV.SublinearResearch
#print axioms PaperIV.SublinearResearch.uniform_sublinear_localization
#print axioms PaperIV.SublinearResearch.uniform_sublinear_fractional_localization
