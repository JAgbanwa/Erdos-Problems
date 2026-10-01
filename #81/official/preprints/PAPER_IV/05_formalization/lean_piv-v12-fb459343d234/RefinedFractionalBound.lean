import RootCliquePrices
import SublinearStability

/-! Refined fractional bound from the signed-star argument (Okechukwu, Lemma 3.1)
with the capped last-row charges retained. Bounds refer to certified mixed
optima on the original graph, not arbitrary dual values.
-/
namespace PaperIV.SublinearResearch
open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect

theorem exception_charge_le (s q : ℕ) :
    (∑ j ∈ range q, ((min s j : ℕ) : ℚ)) ≤ (s : ℚ)*q := by
  calc
    _ ≤ ∑ _j ∈ range q, (s : ℚ) := sum_le_sum (fun j _ => by exact_mod_cast min_le_left s j)
    _ = _ := by simp [mul_comm]

theorem high_star_exact_envelope (n s c α W : ℚ) (hc : (n+1)/2 ≤ c) (hcn : c ≤ n)
    (htri : W ≤ (n-2*c+1)*α+c*(c-1)/2+s*(n-c))
    (hfour : W ≤ (n-c)*α+c*(c-1)/12+s*(n-c)) :
    W ≤ c*(5*n-4*c-1)/12+s*(n-c) := by
  by_cases ha : α ≤ 5*c/12
  · have hp := mul_nonneg (show 0 ≤ n-c by linarith) (show 0 ≤ 5*c/12-α by linarith)
    nlinarith only [hfour,hp]
  · have hp := mul_nonneg (show 0 ≤ 2*c-n-1 by linarith) (show 0 ≤ α-5*c/12 by linarith)
    nlinarith only [htri,hp]

theorem high_star_combined (n s c α W : ℚ) (hc : (n+1)/2 ≤ c) (hcn : c ≤ n)
    (htri : W ≤ (n-2*c+1)*α+c*(c-1)/2+s*(n-c))
    (hfour : W ≤ (n-c)*α+c*(c-1)/12+s*(n-c)) :
    W ≤ n*s+(5*n-1-12*s)^2/192 := by
  have hmid := high_star_exact_envelope n s c α W hc hcn htri hfour
  nlinarith only [hmid,sq_nonneg (8*c-(5*n-1-12*s))]

/-- A real-graph producer of the two star inequalities, with exact and coarse
exception budgets both available. The clique is selected globally by price. -/
theorem certified_star_accounts_strict {n s : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : RootedDefectAt G s)
    {w : ℚ} (hw : CertifiedFractionalOptimum G w) :
    ∃ c : ℕ, c < n ∧ ∃ α : ℚ, 0 ≤ α ∧ α ≤ c ∧
      (G.edgeFinset.card : ℚ)-w ≤ ((n : ℚ)-2*c+1)*α+(c.choose 2 : ℚ)+
        (∑ j ∈ range (n-c), ((min s j : ℕ) : ℚ)) ∧
      (4 ≤ c → (G.edgeFinset.card : ℚ)-w ≤
        ((n : ℚ)-c)*α+(c.choose 2 : ℚ)/6+(s : ℚ)*((n : ℚ)-c)) := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨y,hy⟩ := exists_certified_signed_cover hw
  obtain ⟨v,C,hC,hv,ha0,hac,hmax⟩ := exists_maximum_signed_star y
  have hcn : C.card ≤ n := by simpa using card_le_univ C
  have hvnot : v ∉ C := fun hvC => (hv v hvC).ne rfl
  have hclt : C.card < n := by
    have hi := card_le_univ (insert v C)
    rw [card_insert_of_notMem hvnot, Fintype.card_fin] at hi
    omega
  have helim := signed_elimination_bound G hG (signedPrice y) (signedPrice_le_one y)
    (∑ u ∈ C, signedPrice y s(v,u)) hmax C hC univ (subset_univ _)
  rw [edgesWithin_univ,hy,card_univ,Fintype.card_fin] at helim
  have htri := signed_root_triangle_bound y hC hv
  have hnc : ((n-C.card : ℕ) : ℚ) = (n : ℚ)-C.card := Nat.cast_sub hcn
  rw [hnc] at helim
  refine ⟨C.card,hclt,_,ha0,hac,?_,?_⟩
  · nlinarith only [helim,htri]
  · intro hc
    have hfour := signed_root_K4_bound y hC hc
    have hcharge := exception_charge_le s (n-C.card)
    rw [hnc] at hcharge
    linarith

/-- Compatibility wrapper retaining the original account interface. -/
theorem certified_star_accounts {n s : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : RootedDefectAt G s)
    {w : ℚ} (hw : CertifiedFractionalOptimum G w) :
    ∃ c : ℕ, c ≤ n ∧ ∃ α : ℚ, 0 ≤ α ∧ α ≤ c ∧
      (G.edgeFinset.card : ℚ)-w ≤ ((n : ℚ)-2*c+1)*α+(c.choose 2 : ℚ)+
        (∑ j ∈ range (n-c), ((min s j : ℕ) : ℚ)) ∧
      (4 ≤ c → (G.edgeFinset.card : ℚ)-w ≤
        ((n : ℚ)-c)*α+(c.choose 2 : ℚ)/6+(s : ℚ)*((n : ℚ)-c)) := by
  obtain ⟨c,hc,hrest⟩ := certified_star_accounts_strict hn G hG hw
  exact ⟨c,hc.le,hrest⟩

/-- Uniform in s (not an eventual fixed-s statement), on the band 4s <= n.
The integer baseline is retained in the small-root branch, so no illicit
rounding-down of a fractional inequality is used. -/
theorem certified_refined_fractional_bound {n s : ℕ} (hn : 8 ≤ n) (hs : 4*s ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : RootedDefectAt G s)
    {w : ℚ} (hw : CertifiedFractionalOptimum G w) :
    (G.edgeFinset.card : ℚ)-w ≤ (targetSize (n-s) : ℚ)+(n : ℚ)*s-((s+1).choose 2 : ℚ) := by
  obtain ⟨c,hcn,α,ha0,hac,htri,hfour⟩ := certified_star_accounts (by omega) G hG hw
  have hsn : s ≤ n := by omega
  have hnq : (8 : ℚ) ≤ n := by exact_mod_cast hn
  have hsq : 4*(s : ℚ) ≤ n := by exact_mod_cast hs
  have hs0 : (0 : ℚ) ≤ s := Nat.cast_nonneg _
  have hcnq : (c : ℚ) ≤ n := by exact_mod_cast hcn
  have hcast : ((n-s : ℕ) : ℚ) = (n : ℚ)-s := Nat.cast_sub hsn
  by_cases hc : (c : ℚ) ≤ ((n : ℚ)+1)/2
  · have hcN : 2*c ≤ n+1 := by exact_mod_cast (show 2*(c : ℚ) ≤ n+1 by linarith)
    have hsqN : s ≤ n-c := by omega
    rw [exception_charge_exact s (n-c) hsqN,Nat.cast_sub hcn] at htri
    have hbase := integral_baseline_le_target (n-s) c
    rw [hcast] at hbase
    have hprod : 0 ≤ ((n : ℚ)-2*c+1)*((c : ℚ)-α) := mul_nonneg (by linarith) (by linarith)
    simp only [splitBaseline] at hbase
    simp only [Nat.cast_choose_two,Nat.cast_add,Nat.cast_one] at htri ⊢
    nlinarith only [htri,hbase,hprod]
  · have hc4 : 4 ≤ c := by
      have : (4 : ℚ) < c := by linarith
      exact_mod_cast this.le
    have hcharge := exception_charge_le s (n-c)
    rw [Nat.cast_sub hcn] at hcharge
    have hhigh := high_star_combined (n : ℚ) s c α ((G.edgeFinset.card : ℚ)-w)
      (by linarith) hcnq
      (by simp only [Nat.cast_choose_two] at htri; linarith)
      (by
        have hf := hfour hc4
        norm_num [Nat.cast_choose_two,div_div] at hf ⊢
        exact hf)
    have hmargin := high_star_refined_margin (n : ℚ) s hnq hs0 hsq
    have hfloor := FixedL4.continuous_le_targetSize_add (n-s)
    rw [hcast] at hfloor
    unfold refinedRealTarget realTarget at hmargin
    simp only [Nat.cast_choose_two,Nat.cast_add,Nat.cast_one]
    nlinarith only [hhigh,hmargin,hfloor]

end PaperIV.SublinearResearch
#print axioms PaperIV.SublinearResearch.certified_star_accounts
#print axioms PaperIV.SublinearResearch.certified_refined_fractional_bound
