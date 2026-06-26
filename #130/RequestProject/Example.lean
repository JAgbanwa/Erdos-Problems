import RequestProject.Defs
set_option maxHeartbeats 4000000
/-!
# A concrete finite lower-bound example (Section 5, Example 5.1)
Five explicit points with `s = √195`:
* `Q1 = (0,0)`, `Q2 = (21,0)`, `Q3 = (-19/2, 3s/2)`, `Q4 = (93/2, 3s/2)`, `Q5 = (68, 4s)`.
All ten pairwise distances are integers, and the five points are in general position
(no three collinear, no four concyclic). Hence there is a finite general-position set whose
integer-distance graph contains a clique of size `5`.
-/
open scoped BigOperators
open EuclideanGeometry
open Classical
namespace IntDistK5
/-- `s = √195`. -/
noncomputable def s : ℝ := Real.sqrt 195
lemma s_sq : s ^ 2 = 195 := by
  rw [s, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 195)]
lemma s_nonneg : 0 ≤ s := Real.sqrt_nonneg _
noncomputable def Q1 : Plane := !₂[0, 0]
noncomputable def Q2 : Plane := !₂[21, 0]
noncomputable def Q3 : Plane := !₂[-19/2, 3 * s / 2]
noncomputable def Q4 : Plane := !₂[93/2, 3 * s / 2]
noncomputable def Q5 : Plane := !₂[68, 4 * s]
/-
Distance between two points given by coordinates.
-/
lemma dist_pts (a b c d : ℝ) :
    dist (!₂[a, b] : Plane) (!₂[c, d]) = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ]
lemma s_pos : 0 < s := Real.sqrt_pos.mpr (by norm_num)
/-
Distance from a coordinate point to an arbitrary point `O`.
-/
lemma dist_pt_gen (a b : ℝ) (O : Plane) :
    dist (!₂[a, b] : Plane) O = Real.sqrt ((a - O 0) ^ 2 + (b - O 1) ^ 2) := by
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ]
/-
A 2D non-collinearity criterion via the (doubled signed area) determinant.
-/
lemma not_collinear_2d (a b c : Plane)
    (h : (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) ≠ 0) :
    ¬ Collinear ℝ ({a, b, c} : Set Plane) := by
  contrapose! h;
  rw [ collinear_iff_exists_forall_eq_smul_vadd ] at h;
  obtain ⟨ p₀, v, h ⟩ := h; obtain ⟨ r₁, hr₁ ⟩ := h a ( by norm_num ) ; obtain ⟨ r₂, hr₂ ⟩ := h b ( by norm_num ) ; obtain ⟨ r₃, hr₃ ⟩ := h c ( by norm_num ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
  ring
/-
A 2D non-concyclicity criterion: if no center `(p,q)` is equidistant from the four points,
they are not cospherical.
-/
lemma not_cospherical_2d (a b c d : Plane)
    (h : ¬ ∃ p q : ℝ,
        (a 0 - p) ^ 2 + (a 1 - q) ^ 2 = (b 0 - p) ^ 2 + (b 1 - q) ^ 2 ∧
        (a 0 - p) ^ 2 + (a 1 - q) ^ 2 = (c 0 - p) ^ 2 + (c 1 - q) ^ 2 ∧
        (a 0 - p) ^ 2 + (a 1 - q) ^ 2 = (d 0 - p) ^ 2 + (d 1 - q) ^ 2) :
    ¬ Cospherical ({a, b, c, d} : Set Plane) := by
  contrapose! h;
  obtain ⟨ p, hp ⟩ := h;
  obtain ⟨ radius, h ⟩ := hp; use p 0, p 1; simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ] ;
  exact ⟨ by rw [ ← Real.sqrt_inj ( by positivity ) ( by positivity ), h.1, h.2.1 ], by rw [ ← Real.sqrt_inj ( by positivity ) ( by positivity ), h.1, h.2.2.1 ], by rw [ ← Real.sqrt_inj ( by positivity ) ( by positivity ), h.1, h.2.2.2 ] ⟩
/-- The five points as a finite set. -/
noncomputable def F : Finset Plane := {Q1, Q2, Q3, Q4, Q5}
lemma F_card : F.card = 5 := by
  convert Finset.card_insert_of_notMem _ using 1;
  · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> norm_num [ Q2, Q3, Q4, Q5 ];
  · unfold Q1 Q2 Q3 Q4 Q5; simp +decide [ funext_iff, Fin.forall_fin_two ] ;
    norm_num
/-
All ten pairwise distances among the five points are positive integers.
-/
theorem F_pairwise_intDist :
    ∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → IsIntDist P Q := by
  unfold F; simp +decide [ Q1, Q2, Q3, Q4, Q5 ] ;
  norm_num [ IsIntDist, dist_pts ];
  ring_nf; norm_num [ s_sq ] ;
  norm_cast ; aesop
/-
No three of the five points are collinear.
-/
theorem F_noThreeCollinear : NoThreeCollinear (↑F : Set Plane) := by
  intro s hs hc h;
  -- By definition of $F$, we know that every element in $s$ is one of $Q1$, $Q2$, $Q3$, $Q4$, or $Q5$.
  have h_elements : ∀ x ∈ s, x = Q1 ∨ x = Q2 ∨ x = Q3 ∨ x = Q4 ∨ x = Q5 := by
    intro x hx; specialize hs hx; unfold F at hs; aesop;
  obtain ⟨x, y, z, hx, hy, hz, h_distinct⟩ : ∃ x y z : Plane, x ∈ s ∧ y ∈ s ∧ z ∈ s ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} := by
    rw [ Finset.card_eq_three ] at hc; obtain ⟨ x, y, z, hxy, hyz, hxz ⟩ := hc; use x, y, z; aesop;
  rcases h_elements x hx with ( rfl | rfl | rfl | rfl | rfl ) <;> rcases h_elements y hy with ( rfl | rfl | rfl | rfl | rfl ) <;> rcases h_elements z hz with ( rfl | rfl | rfl | rfl | rfl ) <;> norm_num [ h_distinct ] at h ⊢;
  all_goals norm_num at h_distinct;
  all_goals apply not_collinear_2d _ _ _ _ h; simp +decide [ Q1, Q2, Q3, Q4, Q5 ] ;
  all_goals ring_nf; norm_num [ s_pos.ne' ] ;
/-
No four of the five points are concyclic.
-/
theorem F_noFourConcyclic : NoFourConcyclic (↑F : Set Plane) := by
  intros s hs hs_card hs_cospherical
  have h_four_points : s = {Q1, Q2, Q3, Q4} ∨ s = {Q1, Q2, Q3, Q5} ∨ s = {Q1, Q2, Q4, Q5} ∨ s = {Q1, Q3, Q4, Q5} ∨ s = {Q2, Q3, Q4, Q5} := by
    have h_four_points : ∀ t : Finset Plane, t ⊆ {Q1, Q2, Q3, Q4, Q5} → t.card = 4 → t = {Q1, Q2, Q3, Q4} ∨ t = {Q1, Q2, Q3, Q5} ∨ t = {Q1, Q2, Q4, Q5} ∨ t = {Q1, Q3, Q4, Q5} ∨ t = {Q2, Q3, Q4, Q5} := by
      intros t ht ht_card
      have h_four_points : t = {Q1, Q2, Q3, Q4} ∨ t = {Q1, Q2, Q3, Q5} ∨ t = {Q1, Q2, Q4, Q5} ∨ t = {Q1, Q3, Q4, Q5} ∨ t = {Q2, Q3, Q4, Q5} := by
        have h_distinct : Q1 ≠ Q2 ∧ Q1 ≠ Q3 ∧ Q1 ≠ Q4 ∧ Q1 ≠ Q5 ∧ Q2 ≠ Q3 ∧ Q2 ≠ Q4 ∧ Q2 ≠ Q5 ∧ Q3 ≠ Q4 ∧ Q3 ≠ Q5 ∧ Q4 ≠ Q5 := by
          unfold Q1 Q2 Q3 Q4 Q5; norm_num [ ← List.ofFn_inj ] ;
        have h_four_points : ∀ t : Finset Plane, t ⊆ ({Q1, Q2, Q3, Q4, Q5} : Finset Plane) → t.card = 4 → t = {Q1, Q2, Q3, Q4} ∨ t = {Q1, Q2, Q3, Q5} ∨ t = {Q1, Q2, Q4, Q5} ∨ t = {Q1, Q3, Q4, Q5} ∨ t = {Q2, Q3, Q4, Q5} := by
          intros t ht ht_card
          have h_four_points : t = {Q1, Q2, Q3, Q4} ∨ t = {Q1, Q2, Q3, Q5} ∨ t = {Q1, Q2, Q4, Q5} ∨ t = {Q1, Q3, Q4, Q5} ∨ t = {Q2, Q3, Q4, Q5} := by
            have h_four_points : t ∈ Finset.powersetCard 4 ({Q1, Q2, Q3, Q4, Q5} : Finset Plane) := by
              exact Finset.mem_powersetCard.mpr ⟨ ht, ht_card ⟩
            simp_all +decide [ Finset.powersetCard ];
            rcases h_four_points with ⟨ a, ha, rfl ⟩ ; rcases ha with ( ⟨ b, hb, rfl ⟩ | ⟨ b, hb, rfl ⟩ | ⟨ b, hb, rfl ⟩ | ⟨ b, hb, rfl ⟩ | rfl ) <;> simp_all +decide [ Finset.ext_iff ] ;
            · rcases hb.1 with ( rfl | rfl ) <;> simp_all +decide [ Finset.subset_iff ];
            · rcases hb.1 with ( rfl | rfl ) <;> simp_all +decide [ Finset.subset_iff ];
            · rcases hb.1 with ( rfl | rfl ) <;> simp_all +decide [ Finset.subset_iff ];
            · rcases hb.1 with ( rfl | rfl ) <;> simp_all +decide [ Finset.subset_iff ]
          exact h_four_points;
        exact h_four_points t ( fun x hx => by simpa using ht hx ) ht_card
      exact h_four_points;
    exact h_four_points s hs hs_card;
  obtain rfl | rfl | rfl | rfl | rfl := h_four_points <;> simp_all +decide;
  · refine' not_cospherical_2d Q1 Q2 Q3 Q4 _ hs_cospherical;
    unfold Q1 Q2 Q3 Q4; norm_num;
    grind;
  · refine' not_cospherical_2d Q1 Q2 Q3 Q5 _ hs_cospherical;
    unfold Q1 Q2 Q3 Q5; norm_num;
    intro x hx y hy; nlinarith [ s_sq, s_pos ] ;
  · apply not_cospherical_2d Q1 Q2 Q4 Q5;
    · unfold Q1 Q2 Q4 Q5; norm_num [ s ] ;
      grind;
    · assumption;
  · apply not_cospherical_2d Q1 Q3 Q4 Q5;
    · unfold Q1 Q3 Q4 Q5; norm_num [ s ] ;
      grind +splitIndPred;
    · assumption;
  · apply not_cospherical_2d Q2 Q3 Q4 Q5;
    · unfold Q2 Q3 Q4 Q5; norm_num [ s_sq ] ; intros; nlinarith [ s_pos ] ;
    · assumption
/-- **Example 5.1.** There exists a finite set in general position whose integer-distance graph
contains a clique of size `5` (all five points pairwise at integer distance). -/
theorem exists_general_position_int_K5 :
    ∃ F : Finset Plane, NoThreeCollinear (↑F : Set Plane) ∧ NoFourConcyclic (↑F : Set Plane) ∧
      F.card = 5 ∧ ∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → IsIntDist P Q :=
  ⟨F, F_noThreeCollinear, F_noFourConcyclic, F_card, F_pairwise_intDist⟩
end IntDistK5
