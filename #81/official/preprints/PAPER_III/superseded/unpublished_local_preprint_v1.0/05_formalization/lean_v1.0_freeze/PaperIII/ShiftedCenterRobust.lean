/-
# Paper III — §5.3 robust shifted-center packing bound

This file restricts the shifted-center construction to an arbitrary set `J` of
independent hosts.  Deficient hosts may therefore be discarded before applying the
three-family QQI/RRQ/IRQ packing argument.
-/
import PaperIII.E_7

namespace PaperIII

set_option maxHeartbeats 800000

open SplitGraph Finset

namespace ShiftedCenter

/-- The shifted defect sum over a selected host set `J`. -/
def AJ (G : SplitGraph) (R : Finset (Fin G.p)) (J : Finset (Fin G.q)) : ℕ :=
  ∑ i ∈ J, tt G R i

/-- The squared shifted defect sum over a selected host set `J`. -/
def A2J (G : SplitGraph) (R : Finset (Fin G.p)) (J : Finset (Fin G.q)) : ℕ :=
  ∑ i ∈ J, (tt G R i) ^ 2

/-- The reserved-gain sum over a selected host set `J`. -/
def BJ (G : SplitGraph) (R : Finset (Fin G.p)) (J : Finset (Fin G.q)) : ℕ :=
  ∑ i ∈ J, gg G R i

/-- The robust shifted-center loss ratio `θ_R = max(ρ-1,0)/b`. -/
noncomputable def thetaR (G : SplitGraph) (R : Finset (Fin G.p)) : ℝ :=
  (max (R.card - 1) 0 : ℕ) / (G.p - R.card : ℝ)

end ShiftedCenter

/-- The split graph induced by retaining precisely the independent hosts in `J`.
The clique and every retained clique-neighbourhood are unchanged. -/
noncomputable def restrictHosts (G : SplitGraph) (J : Finset (Fin G.q)) : SplitGraph where
  p := G.p
  q := J.card
  N a := G.N ((J.orderIsoOfFin rfl a : J) : Fin G.q)

/-- Restricting the independent side of a split graph cannot increase its maximum
triangle-packing number beyond that of the original graph. -/
private lemma restrictHosts_nu3_le (G : SplitGraph) (J : Finset (Fin G.q)) :
    (restrictHosts G J).nu3' ≤ G.nu3' := by
  unfold nu3' nu3
  apply csSup_le
  · exact ⟨0, ⟨∅, by simp [IsTrianglePacking], rfl⟩⟩
  · intro b hb
    obtain ⟨T, hT_packing, rfl⟩ := Set.mem_setOf.mp hb
    -- Define the embedding from (restrictHosts G J).V to G.V
    let f : (restrictHosts G J).V → G.V := fun v =>
      match v with
      | Sum.inl a => Sum.inl a
      | Sum.inr i => Sum.inr (J.orderIsoOfFin rfl i)
    -- Show f is injective
    have hf_inj : Function.Injective f := by
      intro x y hxy
      cases x with
      | inl a =>
        cases y with
        | inl a' => injection hxy; simp_all
        | inr i => cases hxy
      | inr i =>
        cases y with
        | inl a => cases hxy
        | inr i' =>
          injection hxy with h
          simp at h
          congr
    -- Define T' as the image of T under f
    let T' := T.image (fun t => t.image f)
    -- Show T' has the same cardinality as T
    have hcard : T'.card = T.card := by
      apply Finset.card_image_of_injOn
      intro t₁ ht₁ t₂ ht₂ h_equiv
      apply Finset.image_injective hf_inj
      exact h_equiv
    -- Show T' is a triangle packing in G.graph
    have hT'_packing : IsTrianglePacking G.graph T' := by
      rcases hT_packing with ⟨hT_cliques, hT_disjoint⟩
      constructor
      · intro t' ht'
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
        have hTt : (restrictHosts G J).graph.IsNClique 3 t := hT_cliques t ht
        -- f preserves adjacency
        have hf_adj : ∀ v w, (restrictHosts G J).graph.Adj v w → G.graph.Adj (f v) (f w) := by
          intro v w hadj
          cases v with
          | inl a =>
            cases w with
            | inl a' =>
              simp only [SplitGraph.graph, SplitGraph.Adj] at hadj ⊢
              simp [f, hadj]
            | inr i =>
              simp only [SplitGraph.graph, SplitGraph.Adj] at hadj ⊢
              simp [f] at hadj ⊢
              exact hadj
          | inr i =>
            cases w with
            | inl a =>
              simp only [SplitGraph.graph, SplitGraph.Adj] at hadj ⊢
              simp [f] at hadj ⊢
              exact hadj
            | inr _ => exact False.elim hadj
        -- Show image f t is a 3-clique
        simp only [SimpleGraph.isNClique_iff] at hTt
        have h_card : (Finset.image f t).card = 3 := by
          rw [Finset.card_image_of_injective _ hf_inj]
          exact hTt.2
        have h_clique : G.graph.IsNClique 3 (Finset.image f t) := by
          simp only [SimpleGraph.isNClique_iff] at hTt ⊢
          refine ⟨?clique, h_card⟩
          intro v' hv' w' hw' hvw
          rw [Finset.mem_coe, Finset.mem_image] at hv' hw'
          obtain ⟨v, hv, rfl⟩ := hv'
          obtain ⟨w, hw, rfl⟩ := hw'
          have hvw' : v ≠ w := by
            intro heq
            exact hvw (heq ▸ rfl)
          exact hf_adj v w (hTt.1 hv hw hvw')
        exact h_clique
      · intro t₁' ht₁' t₂' ht₂' hne
        rw [Finset.mem_coe, Finset.mem_image] at ht₁' ht₂'
        obtain ⟨t₁, ht₁, rfl⟩ := ht₁'
        obtain ⟨t₂, ht₂, rfl⟩ := ht₂'
        rw [← Finset.image_inter _ _ hf_inj]
        have hcard_le : (t₁ ∩ t₂).card ≤ 1 := hT_disjoint ht₁ ht₂ (fun heq => hne (heq ▸ rfl))
        exact Finset.card_image_of_injective _ hf_inj ▸ hcard_le
    refine hcard ▸ le_csSup ?_ ⟨T', hT'_packing, rfl⟩
    use (univ : Finset (Finset G.V)).card
    intro b hb
    obtain ⟨T', hT'_packing, rfl⟩ := hb
    exact Finset.card_le_card (Finset.subset_univ _)


/-- Averaging the QQI contribution over `J`: expansion of
`q_J⁻¹ Σ_{i∈J} C(b-t_i,2)` into the robust shifted-center form. -/
private lemma subset_choose_average_identity (G : SplitGraph) (R : Finset (Fin G.p))
    (J : Finset (Fin G.q)) (hJ : 0 < J.card)
    (ht : ∀ i ∈ J, ShiftedCenter.tt G R i ≤ G.p - R.card) :
    (1 / (J.card : ℝ)) * ∑ i ∈ J,
        (((G.p - R.card - ShiftedCenter.tt G R i).choose 2 : ℕ) : ℝ)
      = (((G.p - R.card).choose 2 : ℕ) : ℝ)
        - (((2 * (G.p - R.card) - 1 : ℕ) : ℝ) *
              (ShiftedCenter.AJ G R J : ℝ) - (ShiftedCenter.A2J G R J : ℝ)) /
            (2 * (J.card : ℝ)) := by
  let b := G.p - R.card
  -- For each i ∈ J, (b - tt i).choose 2 = (b - tt i) * (b - tt i - 1) / 2
  have h_choose : ∀ i ∈ J, ((b - ShiftedCenter.tt G R i).choose 2 : ℝ) =
      (((b - ShiftedCenter.tt G R i) * (b - ShiftedCenter.tt G R i - 1) : ℕ) : ℝ) / 2 := by
    intro i hi
    rw [Nat.choose_two_right]
    have hdiv : 2 ∣ (b - ShiftedCenter.tt G R i) * (b - ShiftedCenter.tt G R i - 1) :=
      Nat.even_mul_pred_self _ |> Even.two_dvd
    rw [Nat.cast_div hdiv]
    push_cast
    rw [div_eq_mul_inv]
    norm_cast
  -- Expand the product in ℝ
  have h_expand : ∀ i ∈ J,
      (((b - ShiftedCenter.tt G R i) * (b - ShiftedCenter.tt G R i - 1) : ℕ) : ℝ) =
      (b : ℝ) * ((b : ℝ) - 1) - 2 * (b : ℝ) * (ShiftedCenter.tt G R i : ℝ) +
        (ShiftedCenter.tt G R i : ℝ) ^ 2 + (ShiftedCenter.tt G R i : ℝ) := by
    intro i hi
    have htti := ht i hi
    have hb_nn : b ≥ ShiftedCenter.tt G R i := htti
    by_cases h : b - ShiftedCenter.tt G R i = 0
    · rw [h]
      norm_num
      rw [Nat.sub_eq_zero_iff_le] at h
      have htti_eq : ShiftedCenter.tt G R i = b := by omega
      rw [htti_eq]
      ring
    · have hb_ge_tti1 : 1 ≤ b - ShiftedCenter.tt G R i := Nat.pos_of_ne_zero h
      rw [Nat.cast_mul, Nat.cast_sub hb_nn]
      have h2 : ((b - ShiftedCenter.tt G R i - 1 : ℕ) : ℝ) = (b : ℝ) - (ShiftedCenter.tt G R i : ℝ) - 1 := by
        rw [show (b - ShiftedCenter.tt G R i - 1 : ℕ) = (b - ShiftedCenter.tt G R i) - 1 by rfl,
            Nat.cast_sub hb_ge_tti1, Nat.cast_sub hb_nn]
        norm_num
      rw [h2]
      ring
  -- Rewrite the LHS sum using h_choose and h_expand
  open ShiftedCenter in
  have h_sum_expand : ∑ i ∈ J,
      ((b : ℝ) * ((b : ℝ) - 1) - 2 * (b : ℝ) * (ShiftedCenter.tt G R i : ℝ) +
        (ShiftedCenter.tt G R i : ℝ) ^ 2 + (ShiftedCenter.tt G R i : ℝ)) =
      J.card * (b : ℝ) * ((b : ℝ) - 1) - ((2 * (b : ℝ) - 1) * (AJ G R J : ℝ) - (A2J G R J : ℝ)) := by
    have : ∑ i ∈ J,
        ((b : ℝ) * ((b : ℝ) - 1) - 2 * (b : ℝ) * (ShiftedCenter.tt G R i : ℝ) +
          (ShiftedCenter.tt G R i : ℝ) ^ 2 + (ShiftedCenter.tt G R i : ℝ)) =
        ∑ _i ∈ J, (b : ℝ) * ((b : ℝ) - 1) - ∑ i ∈ J, 2 * (b : ℝ) * (ShiftedCenter.tt G R i : ℝ) +
          ∑ i ∈ J, (ShiftedCenter.tt G R i : ℝ) ^ 2 + ∑ i ∈ J, (ShiftedCenter.tt G R i : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [this]
    simp [Finset.sum_const]
    rw [show ∑ i ∈ J, 2 * (b : ℝ) * (ShiftedCenter.tt G R i : ℝ) =
          (2 * (b : ℝ)) * ∑ i ∈ J, (ShiftedCenter.tt G R i : ℝ) by
        rw [Finset.mul_sum]]
    simp [AJ, A2J]
    ring
  have hb_choose : ((b.choose 2 : ℕ) : ℝ) = (b : ℝ) * ((b : ℝ) - 1) / 2 := by
    rw [Nat.choose_two_right]
    rw [Nat.cast_div (Nat.even_mul_pred_self _ |> Even.two_dvd) two_ne_zero]
    by_cases hb : b = 0
    · simp [hb]
    · have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hb
      rw [Nat.cast_mul]
      rw [Nat.cast_sub hb1]
      norm_num
  have hJne : (J.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hJ)
  have h_lhs : (1 / (J.card : ℝ)) * ∑ i ∈ J, ((b - ShiftedCenter.tt G R i).choose 2 : ℝ) =
      (1 / (2 * J.card : ℝ)) * (J.card * (b : ℝ) * ((b : ℝ) - 1) -
        ((2 * (b : ℝ) - 1) * (AJ G R J : ℝ) - (A2J G R J : ℝ))) := by
    have h1 : ∑ i ∈ J, ((b - ShiftedCenter.tt G R i).choose 2 : ℝ) =
        ∑ i ∈ J, (((b : ℝ) * ((b : ℝ) - 1) - 2 * (b : ℝ) * (ShiftedCenter.tt G R i : ℝ) +
          (ShiftedCenter.tt G R i : ℝ) ^ 2 + (ShiftedCenter.tt G R i : ℝ)) / 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [h_choose i hi, h_expand i hi]
    rw [h1, ← Finset.sum_div, h_sum_expand]
    field_simp [hJne]
  rw [h_lhs, hb_choose]
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  have h2Jne : (2 : ℝ) * J.card ≠ 0 := mul_ne_zero h2ne hJne
  have goal_eq : (1 : ℝ) / (2 * ↑J.card) * (↑J.card * ↑b * (↑b - 1) - ((2 * ↑b - 1) * ↑(AJ G R J) - ↑(A2J G R J))) =
      ↑b * (↑b - 1) / 2 - ((2 * ↑b - 1) * ↑(AJ G R J) - ↑(A2J G R J)) / (2 * ↑J.card) := by
    field_simp [hJne, h2ne]
  convert goal_eq using 2
  · simp only [b]
    congr 1
    by_cases hb : 1 ≤ G.p - R.card
    · norm_num [Nat.cast_sub (by omega : 1 ≤ 2 * (G.p - R.card))]
    · push_neg at hb
      interval_cases G.p - R.card
      -- Now G.p - R.card = 0, so tt i = 0 for all i ∈ J, hence AJ = 0
      have hAJ : AJ G R J = 0 := by
        simp only [AJ]
        exact Finset.sum_eq_zero fun i hi => Nat.eq_zero_of_le_zero (ht i hi)
      simp [hAJ]

open ShiftedCenter in
/-- **§5.3 (robust shifted-center packing bound).**  Let `R` be reserved clique
vertices and retain only the independent hosts in `J`.  Put `b = p-|R|` and
`r_b = rp b`.  If `b ≥ 2`, `b ≥ rp |R|`, `|J| ≥ r_b`, and every retained host has
at least `max{|R|, |J|-r_b}` neighbours in the unreserved clique, then the
three-family QQI/RRQ/IRQ packing bound holds with all profile sums restricted to `J`.
In particular, hosts failing the neighbourhood threshold may be discarded. -/
theorem reserved_gain_packing_bound_subset (G : SplitGraph) (R : Finset (Fin G.p))
    (J : Finset (Fin G.q))
    (hb2 : 2 ≤ G.p - R.card)
    (hbrho : rp R.card ≤ G.p - R.card)
    (hJrb : rp (G.p - R.card) ≤ J.card)
    (hhost : ∀ i ∈ J,
      max R.card (J.card - rp (G.p - R.card)) ≤ (G.N i \ R).card) :
    (((G.p - R.card).choose 2 : ℕ) : ℝ) + ((R.card.choose 2 : ℕ) : ℝ)
      - (((2 * (G.p - R.card) - 1 : ℕ) : ℝ) * (AJ G R J : ℝ) -
          (A2J G R J : ℝ)) / (2 * (J.card : ℝ))
      + (1 - thetaR G R) *
          ((J.card - rp (G.p - R.card) : ℕ) : ℝ) * (BJ G R J : ℝ) /
            (J.card : ℝ)
      ≤ (G.nu3' : ℝ) := by
  have hnu := restrictHosts_nu3_le G J
  -- J is nonempty because rp (G.p - R.card) ≤ J.card and rp ≥ 0
  have hJpos : 0 < J.card := by
    have hrp_pos : 0 < rp (G.p - R.card) := by
      unfold rp
      grind
    exact Nat.lt_of_lt_of_le hrp_pos hJrb
  -- First derive tt ≤ G.p - R.card from hhost
  have htt : ∀ i ∈ J, ShiftedCenter.tt G R i ≤ G.p - R.card := by
    intro i hi
    simp only [ShiftedCenter.tt]
    have : (Finset.univ \ R).card = G.p - R.card := by
      simp [Finset.card_sdiff, Finset.card_univ]
    rw [← this]
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢
    exact hx.2
  -- Use subset_choose_average_identity to rewrite the LHS
  have hid : (1 / (J.card : ℝ)) * ∑ i ∈ J,
      (((G.p - R.card - ShiftedCenter.tt G R i).choose 2 : ℕ) : ℝ)
    = (((G.p - R.card).choose 2 : ℕ) : ℝ)
      - (((2 * (G.p - R.card) - 1 : ℕ) : ℝ) * (ShiftedCenter.AJ G R J : ℝ) -
          (ShiftedCenter.A2J G R J : ℝ)) / (2 * (J.card : ℝ)) :=
    subset_choose_average_identity G R J hJpos htt
  -- Rewrite the goal using hid
  have hgoal_eq : (((G.p - R.card).choose 2 : ℕ) : ℝ) + ((R.card.choose 2 : ℕ) : ℝ)
      - (((2 * (G.p - R.card) - 1 : ℕ) : ℝ) * (AJ G R J : ℝ) - (A2J G R J : ℝ)) / (2 * (J.card : ℝ))
      + (1 - thetaR G R) * ((J.card - rp (G.p - R.card) : ℕ) : ℝ) * (BJ G R J : ℝ) / (J.card : ℝ)
    = (R.card.choose 2 : ℕ) + (1 / (J.card : ℝ)) * ∑ i ∈ J,
        (((G.p - R.card - ShiftedCenter.tt G R i).choose 2 : ℕ) : ℝ)
      + (1 - thetaR G R) * ((J.card - rp (G.p - R.card) : ℕ) : ℝ) * (BJ G R J : ℝ) / (J.card : ℝ) := by
    linarith
  rw [hgoal_eq]
  -- Now apply reserved_gain_packing_bound to the restricted graph
  let G' := restrictHosts G J
  have hb2' : 2 ≤ G'.p - R.card := by simp [G']; exact hb2
  have hqrb' : rp (G'.p - R.card) ≤ G'.q := by simp [G']; exact hJrb
  have hbrho' : rp R.card ≤ G'.p - R.card := by simp [G']; exact hbrho
  -- Need: ∀ i', max R.card (G'.q - rp (G'.p - R.card)) ≤ (G'.p - R.card) - tt G' R i'
  -- For G' = restrictHosts G J, we have G'.N i' = G.N (J.orderIsoOfFin rfl i')
  have hcond : ∀ i' : Fin G'.q, max R.card (G'.q - rp (G'.p - R.card)) ≤
      (G'.p - R.card) - tt G' R i' := by
    intro i'
    -- The index in J corresponding to i'
    let j := (J.orderIsoOfFin rfl i' : Fin G.q)
    have hj : j ∈ J := Subtype.mem (J.orderIsoOfFin rfl i')
    -- tt G' R i' = tt G R j
    have htt_eq : tt G' R i' = tt G R j := rfl
    rw [htt_eq]
    -- Now use hhost
    have h := hhost j hj
    -- Simplify using the definitions
    have h1 : G'.p = G.p := rfl
    have h2 : G'.q = J.card := rfl
    simp only [h1, h2] at *
    -- We need: (G.p - #R) - tt G R j ≥ max (#R) (#J - rp (G.p - #R))
    -- Key identity: (G.p - #R) - tt G R j = (G.N j \ R).card
    have key : (G.p - R.card) - ShiftedCenter.tt G R j = (G.N j \ R).card := by
      simp only [ShiftedCenter.tt, SplitGraph.S]
      -- ((G.N j)ᶜ \ R).card + (G.N j \ R).card = G.p - R.card
      -- because (G.N j)ᶜ \ R and G.N j \ R partition Finset.univ \ R
      have hpart : ((G.N j)ᶜ \ R) ∪ (G.N j \ R) = Finset.univ \ R := by
        ext x
        simp [Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl]
        tauto
      have hsubset : ((G.N j)ᶜ \ R) ⊆ Finset.univ \ R := by
        simp [Finset.sdiff_subset_sdiff, Finset.subset_univ]
      have hRsub : R ⊆ R := Finset.Subset.refl R
      have hcard_univ_sdiff : (Finset.univ \ R).card = G.p - R.card := by
        simp [Finset.card_sdiff, Finset.card_univ]
      rw [← hcard_univ_sdiff, ← Finset.card_sdiff_of_subset hsubset]
      congr 1
      ext x
      simp [Finset.mem_sdiff, Finset.mem_compl]
      tauto
    rw [key]
    exact h
  -- Apply reserved_gain_packing_bound to G'
  have hpac := reserved_gain_packing_bound G' R hb2' hqrb' hbrho' hcond
  have hnu' : ((restrictHosts G J).nu3' : ℝ) ≤ (G.nu3' : ℝ) := mod_cast hnu
  refine le_trans ?_ hnu'
  -- Need to show the goal equals the LHS of hpac
  -- Convert hpac's LHS to match our goal
  have hpp : G'.p = G.p := rfl
  have hqp : G'.q = J.card := rfl
  -- Convert the sum: sum over G'.q ≃ sum over J
  calc (R.card.choose 2 : ℕ) + 1 / (J.card : ℝ) * ∑ i ∈ J,
        (((G.p - R.card - ShiftedCenter.tt G R i).choose 2 : ℕ) : ℝ)
      + (1 - thetaR G R) * ((J.card - rp (G.p - R.card) : ℕ) : ℝ) * (BJ G R J : ℝ) / (J.card : ℝ)
    _ = (R.card.choose 2 : ℕ) + 1 / (G'.q : ℝ) * ∑ i : Fin G'.q,
        (((G'.p - R.card - ShiftedCenter.tt G' R i).choose 2 : ℕ) : ℝ)
      + (1 - (R.card - 1 : ℕ) / ((G'.p : ℕ) - (R.card : ℕ) : ℝ))
        * ((G'.q - rp (G'.p - R.card) : ℕ) : ℝ) / (G'.q : ℝ) * (BR G' R : ℝ) := by
        -- Need to show:
        -- 1. Sum over G'.q = sum over J
        -- 2. thetaR G R = (R.card - 1) / (G.p - R.card)
        -- 3. BJ G R J = BR G' R
        simp [hpp, hqp]
        -- First, thetaR G R = max (R.card - 1) 0 / (G.p - R.card)
        -- We need to show this equals (R.card - 1) / (G.p - R.card)
        -- Note: (R.card - 1) as Nat.cast of (R.card - 1) equals max (R.card - 1) 0 when R.card ≥ 1
        -- and equals 0 when R.card = 0 (since 0 - 1 = 0 in Nat)
        have htheta : thetaR G R = ((R.card - 1 : ℕ) : ℝ) / ((G.p : ℕ) - (R.card : ℕ) : ℝ) := by
          simp only [thetaR]
          congr 1
          simp only [Nat.max_eq_left (Nat.zero_le _)]
        -- Sum over G'.q = sum over J using the order isomorphism
        have hsum_eq : ∑ x : Fin G'.q, (((G.p - R.card - ShiftedCenter.tt G' R x).choose 2 : ℕ) : ℝ)
            = ∑ i ∈ J, (((G.p - R.card - ShiftedCenter.tt G R i).choose 2 : ℕ) : ℝ) := by
          -- G'.q = J.card definitionally
          symm
          rw [← Finset.sum_attach]
          -- J.attach = univ for the subtype J
          rw [show J.attach = Finset.univ from Finset.attach_eq_univ]
          -- Now both sides are sums over the same Fintype, but with different terms
          -- LHS: ∑ x : J, f x where f x = ... tt G R x ...
          -- RHS: ∑ x : Fin G'.q, g x where g x = ... tt G' R x ...
          -- Use equivalence Fin J.card ≃ J to reindex
          have hG'q : G'.q = J.card := rfl
          -- Create the equivalence
          let iso : Fin J.card ≃ J := Finset.orderIsoOfFin J rfl
          -- The types Fin G'.q and Fin J.card are definitionally equal
          -- Rewrite RHS using the equivalence
          symm
          rw [← Equiv.sum_comp iso]
          rfl
        -- BJ G R J = BR G' R
        have hBJ_BR : (BJ G R J : ℝ) = (BR G' R : ℝ) := by
          -- BJ G R J = ∑ i ∈ J, gg G R i
          -- BR G' R = ∑ i : Fin G'.q, gg G' R i
          -- Use equivalence Fin J.card ≃ J to reindex
          symm
          have hG'q : G'.q = J.card := rfl
          let iso : Fin J.card ≃ J := Finset.orderIsoOfFin J rfl
          -- LHS: ∑ i : Fin G'.q, gg G' R i
          -- RHS: ∑ i ∈ J, gg G R i
          -- Reindex using iso : Fin J.card ≃ J
          simp only [BR, BJ]
          simp only [restrictHosts] at *
          -- Now goal is: ∑ x, ↑(gg G' R x) = ∑ x ∈ J, ↑(gg G R x)
          -- where x : Fin G'.q on LHS and x ∈ J on RHS
          -- G'.q = J.card and there's a bijection
          rw [← Finset.sum_attach]
          -- LHS: ∑ x ∈ univ.attach (Fin G'.q), gg G' R x
          -- RHS: ∑ i ∈ J, gg G R i
          -- Use the equivalence Fin J.card ≃ J to reindex
          rw [Finset.sum_attach]
          -- Now LHS: ∑ x : Fin G'.q, gg G' R x
          -- RHS: ∑ x : J, gg G R x.val
          -- Use equivalence Fin G'.q ≃ J
          have heq2 : G'.q = J.card := rfl
          -- Create equivalence Fin G'.q ≃ Fin J.card ≃ J
          have h1 : Fintype.card (Fin G'.q) = J.card := by simp [heq2]
          let iso1 : Fin G'.q ≃ Fin J.card := Equiv.refl (Fin G'.q)
          let iso2 : Fin J.card ≃ J := Finset.orderIsoOfFin J rfl
          let e : Fin G'.q ≃ J := iso1.trans iso2
          conv_rhs => rw [← Finset.sum_attach]
          -- J.attach = univ for subtype J
          rw [show J.attach = Finset.univ from Finset.attach_eq_univ]
          rw [← Equiv.sum_comp e]
          rw [Nat.cast_inj]
          apply Finset.sum_congr rfl
          intro x _
          simp [gg]
          -- Need: G'.S x = G.S (e x)
          -- G'.S x = (G'.N x)ᶜ = (G.N (J.orderIsoOfFin rfl x))ᶜ
          -- e x = iso2 (iso1 x) where iso2 = J.orderIsoOfFin rfl
          -- Since G'.q = J.card, iso1 should be identity
          have he_eq : ↑(e x) = J.orderIsoOfFin rfl x := by
            simp [e, iso2, iso1]
            rfl
          rw [he_eq]
          rfl
        rw [hsum_eq, hBJ_BR, htheta]
        ring
    _ ≤ ((restrictHosts G J).nu3' : ℝ) := hpac

end PaperIII
