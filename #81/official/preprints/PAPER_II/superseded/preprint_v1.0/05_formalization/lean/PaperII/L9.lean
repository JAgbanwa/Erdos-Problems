import PaperII.CompleteSplit
import PaperII.Model
import PaperII.EdgeCount
import PaperII.L1
import PaperII.L9Packing
import Mathlib

/-!
# Paper II — Exact terminal cover value `τ₃*(S_{p,q})` (ledger L9 = Prop 6.2)

`P = C(p,2) = p*(p-1)/2` is the number of clique edges; `p*q` is the number of radial edges.
Frozen statement (Prop 6.2):
  τ₃*(S_{p,q}) = 0                    if p ≤ 1, or (p,q)=(2,0);
  τ₃*(S_{p,q}) = (P + p*q)/3          if p ≥ 3 and q ≤ p-1;   (unsaturated branch)
  τ₃*(S_{p,q}) = P                    if p ≥ 2 and q ≥ p-1.   (saturated branch)

`tau3star` is `PaperII.tau3star` (a real number, the fractional-triangle-cover LP minimum via
`PaperII.FiniteCover.tauStar`). Prove by exhibiting an optimal feasible cover (upper bound) and a
matching fractional triangle packing / LP-dual certificate (lower bound). See the ledger L8+L9
calculation: symmetrized LP `min{ P·x + p·q·y : x,y ≥ 0 }` with `3x ≥ 1` (present iff p≥3) and
`x + 2y ≥ 1` (present iff p≥2, q≥1). The optimum is `x=y=1/3` (unsat branch) or `x=1,y=0` (sat branch).
-/

open scoped BigOperators
open Finset

namespace PaperII

/-! ## Generic finite-cover lemmas (weak LP duality and cost of indicator covers) -/

section Generic

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype κ] [DecidableEq κ]

/-- Cost of an indicator cover `i ↦ if i ∈ S then c else 0` is `c · |S|`. -/
theorem coverCost_indicator (S : Finset ι) (c : ℝ) :
    coverCost (fun i => if i ∈ S then c else 0) = c * S.card := by
  unfold coverCost
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- If there are no constraints, the optimal cover value is `0`. -/
theorem tauStar_eq_zero_of_isEmpty (A : CoverSystem ι κ) [IsEmpty κ] :
    tauStar A = 0 := by
  have hz : (fun _ : ι => (0 : ℝ)) ∈ FeasibleCover A := by
    refine ⟨fun i => ⟨le_refl 0, by norm_num⟩, ?_⟩
    intro k; exact (IsEmpty.false k).elim
  have h1 : tauStar A ≤ coverCost (fun _ : ι => (0 : ℝ)) := tauStar_le_cost A hz
  have h2 : coverCost (fun _ : ι => (0 : ℝ)) = 0 := by simp [coverCost]
  have h3 := tauStar_nonneg A
  linarith [h1, h2]

/-- **Weak LP duality.** A fractional packing `w ≥ 0` with, for every coordinate `i`, total
weight `∑_{k : i ∈ support k} w k ≤ 1`, lower-bounds the optimum: `∑ k, w k ≤ tauStar A`. -/
theorem tauStar_ge_packing (A : CoverSystem ι κ) (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hpack : ∀ i, ∑ k ∈ Finset.univ.filter (fun k => i ∈ A.support k), w k ≤ 1) :
    (∑ k, w k) ≤ tauStar A := by
  set z := optimalCover A with hz
  have hzmem : z ∈ FeasibleCover A := optimalCover_mem A
  have hznn : ∀ i, 0 ≤ z i := fun i => (hzmem.1 i).1
  have hzcov : ∀ k, 1 ≤ ∑ i ∈ A.support k, z i := hzmem.2
  -- ∑ k, w k ≤ ∑ k, w k * (∑ i ∈ support k, z i)
  have step1 : (∑ k, w k) ≤ ∑ k, w k * (∑ i ∈ A.support k, z i) := by
    apply Finset.sum_le_sum
    intro k _
    have := hzcov k
    nlinarith [hw k, this]
  -- swap the double sum
  have swap : (∑ k, ∑ i ∈ A.support k, w k * z i)
      = ∑ i, ∑ k ∈ Finset.univ.filter (fun k => i ∈ A.support k), w k * z i := by
    rw [Finset.sum_comm' (t' := Finset.univ)
      (s' := fun i => Finset.univ.filter (fun k => i ∈ A.support k))]
    intro x y; simp
  have step2 : (∑ k, w k * (∑ i ∈ A.support k, z i))
      = ∑ i, z i * (∑ k ∈ Finset.univ.filter (fun k => i ∈ A.support k), w k) := by
    calc (∑ k, w k * (∑ i ∈ A.support k, z i))
        = ∑ k, ∑ i ∈ A.support k, w k * z i := by
          apply Finset.sum_congr rfl; intro k _; rw [Finset.mul_sum]
      _ = ∑ i, ∑ k ∈ Finset.univ.filter (fun k => i ∈ A.support k), w k * z i := swap
      _ = ∑ i, z i * (∑ k ∈ Finset.univ.filter (fun k => i ∈ A.support k), w k) := by
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  -- each term ≤ z i
  have step3 : (∑ i, z i * (∑ k ∈ Finset.univ.filter (fun k => i ∈ A.support k), w k))
      ≤ ∑ i, z i := by
    apply Finset.sum_le_sum
    intro i _
    have hpi := hpack i
    nlinarith [hznn i, hpi]
  have : (∑ k, w k) ≤ ∑ i, z i := by
    calc (∑ k, w k) ≤ ∑ k, w k * (∑ i ∈ A.support k, z i) := step1
      _ = _ := step2
      _ ≤ ∑ i, z i := step3
  simpa [tauStar, coverCost, hz] using this

end Generic

/-! ## Upper bound: the `1/3`-on-edges cover -/

section Upper

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The `1/3`-on-edges cover of a graph `G`. -/
noncomputable def thirdCover (G : SimpleGraph V) [DecidableRel G.Adj] : Sym2 V → ℝ :=
  fun e => if e ∈ G.edgeFinset then (1/3 : ℝ) else 0

/-- The `1/3`-on-edges cover is feasible for the triangle cover system. -/
theorem thirdCover_mem (G : SimpleGraph V) [DecidableRel G.Adj] :
    thirdCover G ∈ FeasibleCover (triangleCoverSystem G) := by
  refine ⟨fun e => ?_, ?_⟩
  · unfold thirdCover; split <;> norm_num
  · rintro ⟨s, hs⟩
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs.card_eq
    obtain ⟨hAab, hAac, hAbc⟩ := SimpleGraph.is3Clique_triple_iff.mp hs
    show 1 ≤ ∑ e ∈ triangleCoverSystem G |>.support ⟨{a, b, c}, hs⟩, thirdCover G e
    show 1 ≤ ∑ e ∈ triangleEdges G ⟨{a, b, c}, hs⟩, thirdCover G e
    rw [triangleEdges_sum G hab hac hbc hs]
    have e1 : thirdCover G s(a, b) = 1/3 := by
      unfold thirdCover; rw [if_pos]; rw [SimpleGraph.mem_edgeFinset]; exact hAab
    have e2 : thirdCover G s(a, c) = 1/3 := by
      unfold thirdCover; rw [if_pos]; rw [SimpleGraph.mem_edgeFinset]; exact hAac
    have e3 : thirdCover G s(b, c) = 1/3 := by
      unfold thirdCover; rw [if_pos]; rw [SimpleGraph.mem_edgeFinset]; exact hAbc
    rw [e1, e2, e3]; norm_num

/-- Cost of the `1/3`-on-edges cover is `|E(G)|/3`. -/
theorem coverCost_thirdCover (G : SimpleGraph V) [DecidableRel G.Adj] :
    coverCost (thirdCover G) = (G.edgeFinset.card : ℝ) / 3 := by
  unfold thirdCover
  rw [coverCost_indicator]; ring

/-- Generic upper bound `τ₃*(G) ≤ |E(G)|/3`. -/
theorem tau3star_le_edge_third (G : SimpleGraph V) [DecidableRel G.Adj] :
    tau3star G ≤ (G.edgeFinset.card : ℝ) / 3 := by
  have h := tauStar_le_cost (triangleCoverSystem G) (thirdCover_mem G)
  rwa [coverCost_thirdCover] at h

end Upper

/-! ## Clique-edge cover (upper bound for the saturated branch) -/

/-- The set of clique edges `s(inl a, inl b)` (`a ≠ b`) of `S_{p,q}`. -/
noncomputable def cliqueEdgeFinset (p q : ℕ) : Finset (Sym2 (Fin p ⊕ Fin q)) :=
  (⊤ : SimpleGraph (Fin p)).edgeFinset.image (Sym2.map (Sum.inl : Fin p → Fin p ⊕ Fin q))

theorem card_cliqueEdgeFinset (p q : ℕ) : (cliqueEdgeFinset p q).card = p.choose 2 := by
  unfold cliqueEdgeFinset
  rw [Finset.card_image_of_injective _ (Sym2.map.injective Sum.inl_injective),
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  simp

theorem mem_cliqueEdgeFinset_iff (p q : ℕ) (e : Sym2 (Fin p ⊕ Fin q)) :
    e ∈ cliqueEdgeFinset p q ↔ ∃ a b : Fin p, a ≠ b ∧ e = s(Sum.inl a, Sum.inl b) := by
  unfold cliqueEdgeFinset
  constructor
  · rw [Finset.mem_image]
    rintro ⟨d, hd, rfl⟩
    induction d using Sym2.ind with
    | _ x y =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at hd
      exact ⟨x, y, hd, by simp⟩
  · rintro ⟨a, b, hab, rfl⟩
    rw [Finset.mem_image]
    refine ⟨s(a, b), ?_, by simp⟩
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]; exact hab

/-- The clique-edge cover: weight `1` on clique edges, `0` elsewhere. -/
noncomputable def cliqueCover (p q : ℕ) : Sym2 (Fin p ⊕ Fin q) → ℝ :=
  fun e => if e ∈ cliqueEdgeFinset p q then (1 : ℝ) else 0

theorem coverCost_cliqueCover (p q : ℕ) :
    coverCost (cliqueCover p q) = (p.choose 2 : ℝ) := by
  unfold cliqueCover
  rw [coverCost_indicator, card_cliqueEdgeFinset]; ring

/-
The clique-edge cover is feasible for `S_{p,q}` (every triangle contains ≥ 1 clique edge).
-/
theorem cliqueCover_mem (p q : ℕ) :
    cliqueCover p q ∈ FeasibleCover (triangleCoverSystem (completeSplit p q)) := by
  constructor;
  · intro e; unfold cliqueCover; aesop;
  · intro ⟨ s, hs ⟩;
    -- Since $s$ is a triangle, it must contain at least one edge from the clique.
    obtain ⟨a, b, hab⟩ : ∃ a b : Fin p ⊕ Fin q, a ∈ s ∧ b ∈ s ∧ a ≠ b ∧ (completeSplit p q).Adj a b ∧ (a.isLeft ∧ b.isLeft) := by
      obtain ⟨a, b, c, ha, hb, hc, habc⟩ : ∃ a b c : Fin p ⊕ Fin q, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ s = {a, b, c} := by
        have := Finset.card_eq_three.mp hs.2; obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hac ⟩ := this; use a, b, c; aesop;
      have h_adj : (completeSplit p q).Adj a b ∧ (completeSplit p q).Adj a c ∧ (completeSplit p q).Adj b c := by
        have := hs.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      cases a <;> cases b <;> cases c <;> simp_all +decide [ completeSplit_inl_inl, completeSplit_inl_inr, completeSplit_inr_inl, completeSplit_inr_inr ];
    refine' le_trans _ ( Finset.single_le_sum ( fun x _ => _ ) ( show s(a, b) ∈ _ from _ ) ) <;> norm_num [ cliqueCover ];
    · rcases a with ( a | a ) <;> rcases b with ( b | b ) <;> simp_all +decide [ cliqueEdgeFinset ];
      rw [ if_pos ⟨ s(a, b), by aesop ⟩ ];
    · split_ifs <;> norm_num;
    · convert Finset.mem_filter.mpr ⟨ Finset.mem_sym2_iff.mpr _, _ ⟩;
      · grind;
      · aesop

/-- Upper bound for the saturated branch: `τ₃*(S_{p,q}) ≤ C(p,2)`. -/
theorem tau3star_completeSplit_le_choose (p q : ℕ) :
    tau3star (completeSplit p q) ≤ (p.choose 2 : ℝ) := by
  have h := tauStar_le_cost (triangleCoverSystem (completeSplit p q)) (cliqueCover_mem p q)
  rwa [coverCost_cliqueCover] at h

/-! ## Lower bounds via fractional triangle packings -/

/-- **Master packing lower bound.** For packing weights `wA, wB ≥ 0` satisfying the clique- and
radial-edge constraints, the total packing weight lower-bounds `τ₃*`. -/
theorem packing_bound (p q : ℕ) {wA wB : ℝ} (hwA : 0 ≤ wA) (hwB : 0 ≤ wB)
    (hclique : ((p - 2 : ℕ) : ℝ) * wA + (q : ℝ) * wB ≤ 1)
    (hradial : ((p - 1 : ℕ) : ℝ) * wB ≤ 1) :
    wA * (p.choose 3 : ℝ) + wB * ((p.choose 2 : ℝ) * (q : ℝ))
      ≤ tau3star (completeSplit p q) := by
  have hpack : ∀ i, ∑ k ∈ Finset.univ.filter
      (fun k => i ∈ (triangleCoverSystem (completeSplit p q)).support k),
      (fun T => packWeight p q wA wB T.1) k ≤ 1 := by
    intro i
    show (∑ k ∈ Finset.univ.filter
      (fun k => i ∈ triangleEdges (completeSplit p q) k), packWeight p q wA wB k.1) ≤ 1
    rw [sum_over_triangles_through p q i (packWeight p q wA wB)]
    exact packWeight_through_le_one p q hclique hradial i
  have h := tauStar_ge_packing (triangleCoverSystem (completeSplit p q))
    (fun T => packWeight p q wA wB T.1)
    (fun k => packWeight_nonneg p q hwA hwB k.1) hpack
  rw [sum_over_triangles p q (packWeight p q wA wB), sum_packWeight_total] at h
  exact h

/-
Lower bound, unsaturated branch: `(C(p,2) + p·q)/3 ≤ τ₃*(S_{p,q})` for `p ≥ 3`, `q ≤ p-1`.
-/
theorem tau3star_completeSplit_unsat_ge (p q : ℕ) (hp : 3 ≤ p) (hq : q ≤ p - 1) :
    ((p.choose 2 : ℝ) + (p : ℝ) * q) / 3 ≤ tau3star (completeSplit p q) := by
  have h3 : (3 : ℝ) * (p.choose 3 : ℝ) = (p.choose 2 : ℝ) * ((p : ℝ) - 2) := by
    norm_cast;
    rw [ Int.subNatNat_of_le ( by linarith ) ] ; norm_cast;
    convert Nat.choose_succ_right_eq p 2 using 1 ; ring
  have h2 : (2 : ℝ) * (p.choose 2 : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by
    rw [ Nat.choose_two_right ];
    cases p <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ] at *;
    ring
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    linarith [ show ( p : ℝ ) ≥ 3 by norm_cast ]
  have hp2 : (p : ℝ) - 2 ≠ 0 := by
    linarith [ show ( p : ℝ ) ≥ 3 by norm_cast ]
  have hwA : 0 ≤ ((p : ℝ) - 1 - (q : ℝ)) / (((p : ℝ) - 1) * ((p : ℝ) - 2)) := by
    exact div_nonneg ( sub_nonneg_of_le ( by linarith [ show ( q : ℝ ) + 1 ≤ p by norm_cast; omega ] ) ) ( mul_nonneg ( sub_nonneg_of_le ( by norm_cast; linarith ) ) ( sub_nonneg_of_le ( by norm_cast; linarith ) ) )
  have hwB : 0 ≤ 1 / ((p : ℝ) - 1) := by
    exact div_nonneg zero_le_one ( by linarith [ show ( p : ℝ ) ≥ 3 by norm_cast ] )
  have hclique : ((p - 2 : ℕ) : ℝ) * (((p : ℝ) - 1 - (q : ℝ)) / (((p : ℝ) - 1) * ((p : ℝ) - 2))) + (q : ℝ) * (1 / ((p : ℝ) - 1)) ≤ 1 := by
    rw [ Nat.cast_sub ] <;> push_cast;
    · field_simp;
      rw [ div_le_iff₀ ] <;> linarith [ show ( p : ℝ ) ≥ 3 by norm_cast ];
    · linarith
  have hradial : ((p - 1 : ℕ) : ℝ) * (1 / ((p : ℝ) - 1)) ≤ 1 := by
    rw [ Nat.cast_pred ( by linarith ), mul_div_cancel₀ _ hp1 ]
  have H := packing_bound p q hwA hwB hclique hradial;
  convert H using 1;
  grind

/-
Lower bound, saturated branch: `C(p,2) ≤ τ₃*(S_{p,q})` for `p ≥ 2`, `q ≥ p-1`.
-/
theorem tau3star_completeSplit_sat_ge (p q : ℕ) (hp : 2 ≤ p) (hq : p - 1 ≤ q) :
    (p.choose 2 : ℝ) ≤ tau3star (completeSplit p q) := by
  convert packing_bound p q ( show 0 ≤ 0 by norm_num ) ( show 0 ≤ ( 1 : ℝ ) / q by positivity ) _ _ using 1 <;> norm_num;
  · rw [ inv_mul_eq_div, eq_div_iff ] ; norm_cast ; linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ p ) ];
  · exact div_self_le_one _;
  · exact div_le_one_of_le₀ ( mod_cast hq ) ( Nat.cast_nonneg _ )

/-! ## Degenerate cases: no triangles -/

theorem completeSplit_triangle_isEmpty_of_le_one (p q : ℕ) (hp : p ≤ 1) :
    IsEmpty (Triangle (completeSplit p q)) := by
  constructor;
  interval_cases p <;> simp_all +decide [ IsTriangle ];
  · rintro ⟨ s, hs ⟩;
    rcases hs.2 with h ; simp_all +decide [ Finset.card_eq_three ];
    obtain ⟨ a, b, hab, c, hac, hbc, rfl ⟩ := h; have := hs.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
  · rintro ⟨ s, hs ⟩;
    rcases Finset.card_eq_three.mp hs.card_eq with ⟨ a, b, c, hab, hbc, hac ⟩ ; rcases a with ( _ | a ) <;> rcases b with ( _ | b ) <;> rcases c with ( _ | c ) <;> simp_all +decide [ IsTriangle ];
    all_goals simp_all +decide [ Fin.eq_zero, SimpleGraph.isNClique_iff ]

theorem completeSplit_triangle_isEmpty_two_zero :
    IsEmpty (Triangle (completeSplit 2 0)) := by
  refine ⟨fun T => ?_⟩
  have hc := T.2.card_eq
  have hle := Finset.card_le_univ T.1
  simp [Fintype.card_sum] at hle
  omega

/-! ## The four ledger theorems -/

/-- L9 degenerate case `p ≤ 1`: no triangles, cover value `0`. -/
theorem tau3star_completeSplit_of_le_one (p q : ℕ) (hp : p ≤ 1) :
    tau3star (completeSplit p q) = 0 := by
  haveI := completeSplit_triangle_isEmpty_of_le_one p q hp
  exact tauStar_eq_zero_of_isEmpty _

/-- L9 degenerate case `S_{2,0} = K_2`: no triangles, cover value `0`. -/
theorem tau3star_completeSplit_two_zero :
    tau3star (completeSplit 2 0) = 0 := by
  haveI := completeSplit_triangle_isEmpty_two_zero
  exact tauStar_eq_zero_of_isEmpty _

/-- L9 unsaturated branch `p ≥ 3, q ≤ p-1`: `τ₃* = (C(p,2) + p*q)/3`. -/
theorem tau3star_completeSplit_unsat (p q : ℕ) (hp : 3 ≤ p) (hq : q ≤ p - 1) :
    tau3star (completeSplit p q) = ((p.choose 2 : ℝ) + (p : ℝ) * q) / 3 := by
  refine le_antisymm ?_ (tau3star_completeSplit_unsat_ge p q hp hq)
  have h := tau3star_le_edge_third (completeSplit p q)
  rw [completeSplit_card_edgeFinset] at h
  push_cast at h ⊢
  linarith

/-- L9 satura