import RootPartition
import NormalizedCliqueCore
import NormalizedDeficit
import ResidualExcess
import CliqueShiftArithmetic

namespace FixedDefectStability
open Finset PaperIV.FarRounding PaperIV.DefectTargetArithmetic
  PaperIV.DefectComparatorGraph PaperIV.EditMetric A4S1.TerminalPacking A4S1.IndepAll

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset V} {s : ℕ}

/-- Quantitative stability for normalized inputs. The target root is a literal
clique of G, the defect class has exactly s vertices, and all vertex and edit
accounts are derived. No existence or distance interface is assumed. -/
theorem normalized_stability (h : AllInput G A s) (δ : ℚ) (hδ : 0 ≤ δ)
    (hlower : ∀ Q : CliquePartition G, Q.OrderAtMost 4 →
      (defectTarget s (Fintype.card V) : ℚ)-δ ≤ Q.size) :
    ∃ C D J : Finset V,
      Disjoint C D ∧ Disjoint C J ∧ Disjoint D J ∧
      (∀ x, x ∈ C ∨ x ∈ D ∨ x ∈ J) ∧
      G.IsClique (C : Set V) ∧ D.card=s ∧ 2 ≤ C.card ∧ C.card ≤ J.card ∧
      (editDist G.edgeFinset (defSplitGraph C D J).edgeFinset : ℚ) ≤
        40000*((s:ℚ)+1)^3*δ := by
  let S := pCore G A s
  let H := pHost G A s
  let W := pT G A s
  let n := Fintype.card V
  let E := (inEdges G S).card-(S.card-s).choose 2
  let miss := S.card*H.card-crossCount G S H
  obtain ⟨C,hC,hcl,r,hrs,hcard,htwo,hwindow,hr⟩ := normalized_clique_core h
  obtain ⟨D,J,hCD,hCJ,hDJ,hcov,hDs,h2,hCJcard,hdist⟩ :=
    exists_root_partition (G := G) s r S H W C
      core_host_disjoint core_T_disjoint cover hC hcl hcard htwo hwindow
  refine ⟨C,D,J,hCD,hCJ,hDJ,hcov,hcl,hDs,h2,hCJcard,?_⟩
  have hs : s ≤ S.card := by change C.card+s+r=S.card at hcard; omega
  have hchoose := choose_sub_identity S.card s hs
  have heg := h.core_eg (le_refl s) h.no_core_pairs
  have hege : (S.card-s).choose 2 ≤ (inEdges G S).card := by
    change S.card.choose 2+(s+1).choose 2 ≤ (inEdges G S).card+s*S.card at heg
    omega
  have hcross : crossCount G S H ≤ S.card*H.card := by
    unfold crossCount
    simpa only [card_product] using card_filter_le (S ×ˢ H) (fun p : V × V => G.Adj p.1 p.2)
  have hmiss : (miss:ℚ)=(S.card:ℚ)*H.card-crossCount G S H := by
    dsimp [miss]
    rw [Nat.cast_sub hcross,Nat.cast_mul]
  have hEq : (E:ℚ)=(inEdges G S).card-(S.card.choose 2:ℚ)-
      ((s+1).choose 2:ℚ)+(s:ℚ)*S.card := by
    have hchooseq : ((S.card-s).choose 2:ℚ)+(s:ℚ)*S.card=
        (S.card.choose 2:ℚ)+((s+1).choose 2:ℚ) := by exact_mod_cast hchoose
    dsimp [E]
    rw [Nat.cast_sub hege]
    linarith only [hchooseq]
  obtain ⟨L,hL,hbase,hcredit,hbudget⟩ := normalized_deficit_budget h δ hlower
  have hR : 0 ≤ residualCredit G A s L := by
    have hnonneg : (0:ℚ) ≤ (pT G A s).card*scW V s/800 := by
      have hwpos : (0:ℚ) < scW V s := lt_of_lt_of_le h.v_pos h.v_le_w
      positivity
    exact hnonneg.trans hcredit
  have hb : (miss:ℚ)+(inEdges G H).card/(2000*((s:ℚ)+1)^2)+
      residualCredit G A s L ≤ δ := by
    rw [hmiss]
    dsimp [S,H]
    linarith only [hbudget,hbase]
  have hnt : (n:ℚ)*W.card ≤ 800*((s:ℚ)+1)^2*residualCredit G A s L := by
    have hp := mul_le_mul_of_nonneg_right
      (show (pT G A s).card*scW V s ≤ 800*residualCredit G A s L by
        linarith only [hcredit]) (sq_nonneg ((s:ℚ)+1))
    have hn := scW_mul (V := V) (s := s)
    dsimp [n,W]
    nlinarith only [hp,congrArg (fun x : ℚ => (pT G A s).card*x) hn]
  have hE : (E:ℚ) ≤ residualCredit G A s L+(n:ℚ)*W.card := by
    rw [hEq]
    exact core_excess_le_residual h L hL
  have hdel := core_deletion_bound S.card s r C.card (inEdges G S).card n
    hcard (card_le_univ S)
  have hdist' : editDist G.edgeFinset (defSplitGraph C D J).edgeFinset ≤
      miss+(inEdges G H).card+E+2*(r*n)+2*(W.card*n) := by
    change _ ≤ E+r*n at hdel
    change _ ≤ ((inEdges G S).card-C.card.choose 2)+(inEdges G H).card+
      miss+(2*W.card+r)*n at hdist
    nlinarith only [hdist,hdel]
  have hdistq : (editDist G.edgeFinset (defSplitGraph C D J).edgeFinset:ℚ) ≤
      (miss:ℚ)+(inEdges G H).card+E+2*((r:ℚ)*n)+2*((n:ℚ)*W.card) := by
    rw [Nat.mul_comm W.card n] at hdist'
    exact_mod_cast hdist'
  have hrq : (r:ℚ)*n ≤ 16*(s:ℚ)*E := by exact_mod_cast hr
  exact clique_edit_bound s δ miss (inEdges G H).card (residualCredit G A s L)
    E ((n:ℚ)*W.card) ((r:ℚ)*n) _ hδ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      hR hb hnt hE hrq hdistq

end FixedDefectStability
#print axioms FixedDefectStability.normalized_stability
