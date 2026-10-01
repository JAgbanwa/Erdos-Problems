import E34.L11Claim2

/-!
# E34 — Lemma 11, Claims 4 and 5

Given a colouring `ψ` of the pin problem, for a node `c` of `Γ` (the section `(c, par c)`):
`Lc c` = vertices whose colour contains `c` but not `par c`, `Rc c` = the converse.

* `claim4` — an `M₂` of `G[Lc ∩ X, Rc ∩ X]` without conflicting pair in `X` is an induced `C₄`.
* `claim5_count` — counting form of Claim 5: sequences of length `y` inducing a chordal graph
  are at most `(y+1)(1-η)^(y-1) n^y + y² · conf ψ · n^(y-2)` when `G[Lc, Rc]` is `η`-far from
  chain graphs.
-/

namespace E34

open Finset

open scoped Classical

variable {n K : ℕ}

/-- Left side of the section at `c`. -/
noncomputable def Lc (Γ : RTree K) (ψ : Fin n → Finset (Fin K)) (c : Fin K) : Finset (Fin n) :=
  univ.filter (fun u => c ∈ ψ u ∧ Γ.par c ∉ ψ u)

/-- Right side of the section at `c`. -/
noncomputable def Rc (Γ : RTree K) (ψ : Fin n → Finset (Fin K)) (c : Fin K) : Finset (Fin n) :=
  univ.filter (fun u => c ∉ ψ u ∧ Γ.par c ∈ ψ u)

theorem disjoint_Lc_Rc (Γ : RTree K) (ψ : Fin n → Finset (Fin K)) (c : Fin K) :
    Disjoint (Lc Γ ψ c) (Rc Γ ψ c) := by
  rw [disjoint_left]
  intro u hu hu'
  exact (mem_filter.1 hu').2.1 (mem_filter.1 hu).2.1

/-- The ordered conflicting pairs of a colouring. -/
noncomputable def confSet (P : SetColoring n K) (ψ : Fin n → Finset (Fin K)) :
    Finset (Fin n × Fin n) :=
  univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ ¬ P.compat p.1 (ψ p.1) p.2 (ψ p.2))

theorem card_confSet (P : SetColoring n K) (ψ : Fin n → Finset (Fin K)) :
    (confSet P ψ).card = P.conf ψ := rfl

/-- **Claim 4 of Lemma 11.** -/
theorem claim4 (Γ : RTree K) (x : Fin n → Fin K) (G : SimpleGraph (Fin n))
    (ψ : Fin n → Finset (Fin K)) (c : Fin K) (X : Finset (Fin n))
    (hM : HasM2 G (Lc Γ ψ c) (Rc Γ ψ c) X)
    (hX : ∀ u ∈ X, ∀ v ∈ X, u ≠ v → (pinProblem Γ x G).compat u (ψ u) v (ψ v)) :
    ¬ AlonShapira.IsChordal (G.induce (X : Set (Fin n))) := by
  obtain ⟨l1, hl1, l2, hl2, r1, hr1, r2, hr2, h11, h22, h12, h21⟩ := hM
  rw [mem_inter] at hl1 hl2 hr1 hr2
  have hl12 : l1 ≠ l2 := fun h => h21 (h ▸ h11)
  have hr12 : r1 ≠ r2 := fun h => h12 (h ▸ h11)
  have hLR := disjoint_Lc_Rc Γ ψ c
  have hadjL : G.Adj l1 l2 := by
    by_contra hna
    have hc := hX l1 hl1.2 l2 hl2.2 hl12
    rw [pinProblem_compat_iff] at hc
    exact disjoint_left.1 (hc.2 hna) (mem_filter.1 hl1.1).2.1 (mem_filter.1 hl2.1).2.1
  have hadjR : G.Adj r1 r2 := by
    by_contra hna
    have hc := hX r1 hr1.2 r2 hr2.2 hr12
    rw [pinProblem_compat_iff] at hc
    exact disjoint_left.1 (hc.2 hna) (mem_filter.1 hr1.1).2.2 (mem_filter.1 hr2.1).2.2
  have hne1 : l1 ≠ r2 := fun h => disjoint_left.1 hLR hl1.1 (h ▸ hr2.1)
  have hne2 : r1 ≠ l2 := fun h => disjoint_left.1 hLR hl2.1 (h ▸ hr1.1)
  exact not_chordal_of_c4 G X hl1.2 hr1.2 hr2.2 hl2.2 h11 hadjR (G.adj_symm h22) hadjL.symm h12
    (fun h => h21 (G.adj_symm h)) hne1 hne2

/-- Sequences with two prescribed values. -/
theorem card_pair_at (y : ℕ) {i j : Fin y} (hij : i ≠ j) (a b : Fin n) :
    (univ.filter (fun w : Fin y → Fin n => w i = a ∧ w j = b)).card ≤ n ^ (y - 2) := by
  have hsub : univ.filter (fun w : Fin y → Fin n => w i = a ∧ w j = b) ⊆
      Fintype.piFinset (fun k => if k = i then {a} else if k = j then {b} else univ) := by
    intro w hw
    rw [mem_filter] at hw
    rw [Fintype.mem_piFinset]
    intro k
    by_cases hki : k = i
    · subst hki; simp [hw.2.1]
    · by_cases hkj : k = j
      · subst hkj; simp [hki, hw.2.2]
      · simp [hki, hkj]
  refine (card_le_card hsub).trans (le_of_eq ?_)
  rw [Fintype.card_piFinset]
  simp only [apply_ite Finset.card, card_singleton, card_univ, Fintype.card_fin]
  rw [prod_ite, prod_const_one, one_mul, prod_ite, prod_const_one, one_mul, prod_const]
  congr 1
  rw [filter_filter]
  have h1 : (univ.filter (fun k : Fin y => k = i)).card = 1 := by rw [filter_eq' univ i]; simp
  have h2 : ((univ.filter (fun k : Fin y => ¬ k = i)).filter (fun k => k = j)).card = 1 := by
    rw [filter_filter]
    have : univ.filter (fun k : Fin y => ¬ k = i ∧ k = j) = {j} := by
      ext k; simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨fun h => hij h.symm, rfl⟩
    rw [this, card_singleton]
  have h3 := card_filter_add_card_filter_not (s := (univ : Finset (Fin y))) (fun k => k = i)
  have h4 := card_filter_add_card_filter_not (s := univ.filter (fun k : Fin y => ¬ k = i))
    (fun k => k = j)
  rw [card_univ, Fintype.card_fin, h1] at h3
  rw [h2, filter_filter] at h4
  omega

/-- Sequences hitting a set of ordered pairs at two distinct positions. -/
theorem card_hit_pairs (y : ℕ) (S : Finset (Fin n × Fin n)) :
    (univ.filter (fun w : Fin y → Fin n => ∃ i j, i ≠ j ∧ (w i, w j) ∈ S)).card ≤
      y ^ 2 * S.card * n ^ (y - 2) := by
  have hsub : univ.filter (fun w : Fin y → Fin n => ∃ i j, i ≠ j ∧ (w i, w j) ∈ S) ⊆
      ((univ : Finset (Fin y × Fin y)).filter (fun p => p.1 ≠ p.2)).biUnion (fun p =>
        S.biUnion (fun q => univ.filter (fun w : Fin y → Fin n => w p.1 = q.1 ∧ w p.2 = q.2))) := by
    intro w hw
    obtain ⟨i, j, hij, hS⟩ := (mem_filter.1 hw).2
    exact mem_biUnion.2 ⟨(i, j), mem_filter.2 ⟨mem_univ _, hij⟩,
      mem_biUnion.2 ⟨(w i, w j), hS, mem_filter.2 ⟨mem_univ _, rfl, rfl⟩⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ p ∈ (univ : Finset (Fin y × Fin y)).filter (fun p => p.1 ≠ p.2),
        (S.biUnion (fun q => univ.filter (fun w : Fin y → Fin n => w p.1 = q.1 ∧ w p.2 = q.2))).card
      ≤ ∑ _p ∈ (univ : Finset (Fin y × Fin y)).filter (fun p => p.1 ≠ p.2), S.card * n ^ (y - 2) := by
        refine sum_le_sum (fun p hp => card_biUnion_le.trans ?_)
        have hp' := (mem_filter.1 hp).2
        calc ∑ q ∈ S, (univ.filter (fun w : Fin y → Fin n => w p.1 = q.1 ∧ w p.2 = q.2)).card
            ≤ ∑ _q ∈ S, n ^ (y - 2) := sum_le_sum (fun q _ => card_pair_at y hp' q.1 q.2)
          _ = S.card * n ^ (y - 2) := by rw [sum_const, smul_eq_mul]
    _ ≤ y ^ 2 * (S.card * n ^ (y - 2)) := by
        rw [sum_const, smul_eq_mul]
        refine Nat.mul_le_mul_right _ ((card_filter_le _ _).trans (le_of_eq ?_))
        simp [sq]
    _ = y ^ 2 * S.card * n ^ (y - 2) := by ring

/-- **Claim 5 of Lemma 11** (counting form). -/
theorem claim5_count (Γ : RTree K) (x : Fin n → Fin K) (G : SimpleGraph (Fin n))
    (ψ : Fin n → Finset (Fin K)) (c : Fin K) (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hfar : ∀ rk : Fin n → ℕ, η * (n : ℝ) ^ 2 < chainMisOn G (Lc Γ ψ c) (Rc Γ ψ c) univ rk)
    (y : ℕ) :
    ((univ.filter (fun w : Fin y → Fin n =>
      AlonShapira.IsChordal (G.induce ((img w : Finset (Fin n)) : Set (Fin n))))).card : ℝ) ≤
      (y + 1) * (1 - η) ^ (y - 1) * (n : ℝ) ^ y +
        y ^ 2 * (pinProblem Γ x G).conf ψ * (n : ℝ) ^ (y - 2) := by
  have hsub : univ.filter (fun w : Fin y → Fin n =>
      AlonShapira.IsChordal (G.induce ((img w : Finset (Fin n)) : Set (Fin n)))) ⊆
      univ.filter (fun w : Fin y → Fin n => ¬ HasM2 G (Lc Γ ψ c) (Rc Γ ψ c) (img w)) ∪
      univ.filter (fun w : Fin y → Fin n => ∃ i j, i ≠ j ∧
        (w i, w j) ∈ confSet (pinProblem Γ x G) ψ) := by
    intro w hw
    rw [mem_filter] at hw
    by_cases hM : HasM2 G (Lc Γ ψ c) (Rc Γ ψ c) (img w)
    · refine mem_union_right _ (mem_filter.2 ⟨mem_univ _, ?_⟩)
      by_contra hno
      push_neg at hno
      apply claim4 Γ x G ψ c (img w) hM _ hw.2
      intro u hu v hv huv
      obtain ⟨i, rfl⟩ := (mem_img w u).1 hu
      obtain ⟨j, rfl⟩ := (mem_img w v).1 hv
      have hij : i ≠ j := fun h => huv (h ▸ rfl)
      have := hno i j hij
      simp only [confSet, mem_filter, mem_univ, true_and, not_and, not_not] at this
      exact this huv
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hM⟩)
  have h1 := thm6 G (Lc Γ ψ c) (Rc Γ ψ c) (disjoint_Lc_Rc Γ ψ c) η hη hη1 hfar y
  have h2 := card_hit_pairs (n := n) y (confSet (pinProblem Γ x G) ψ)
  rw [card_confSet] at h2
  have h2' : ((univ.filter (fun w : Fin y → Fin n => ∃ i j, i ≠ j ∧
        (w i, w j) ∈ confSet (pinProblem Γ x G) ψ)).card : ℝ) ≤
      y ^ 2 * (pinProblem Γ x G).conf ψ * (n : ℝ) ^ (y - 2) := by exact_mod_cast h2
  have hU := (card_le_card hsub).trans (card_union_le _ _)
  have hU' : ((univ.filter (fun w : Fin y → Fin n =>
      AlonShapira.IsChordal (G.induce ((img w : Finset (Fin n)) : Set (Fin n))))).card : ℝ) ≤
      ((univ.filter (fun w : Fin y → Fin n => ¬ HasM2 G (Lc Γ ψ c) (Rc Γ ψ c) (img w))).card : ℝ) +
      ((univ.filter (fun w : Fin y → Fin n => ∃ i j, i ≠ j ∧
        (w i, w j) ∈ confSet (pinProblem Γ x G) ψ)).card : ℝ) := by exact_mod_cast hU
  linarith

end E34
