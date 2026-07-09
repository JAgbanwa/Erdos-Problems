import Mathlib
open scoped BigOperators
open scoped Classical
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
/-!
# A rigorous lower bound and finiteness proof for a two-colour finite-sums Ramsey number
This file formalises the contents of the note *"A Rigorous Lower Bound and Finiteness Proof
for a Two-Colour Finite-Sums Ramsey Number"*.
Let `F(k)` be the least integer `N` such that every two-colouring of `{1, …, N}` contains a
`k`-element set `A` for which all non-empty subset sums of `A` are defined inside `{1, …, N}`
(equivalently `∑_{a ∈ A} a ≤ N`) and have the same colour.
The main result (`F_estimate`) is that for every `k ≥ 1`,
`4 ^ (k - 1) ≤ F k` and `F k` exists (is finite).
The lower bound uses the colouring `n ↦ ν₂(n) mod 2`.  The finiteness proof uses Hindman's
finite-sums theorem (available in Mathlib as `Hindman.exists_FS_of_finite_cover`) together with
a compactness extraction implemented via a non-principal ultrafilter limit of colourings.
-/
open Filter Hindman
attribute [local instance] Ultrafilter.add Ultrafilter.addSemigroup
namespace FiniteSumsFk
/-- `Good k N` holds iff every two-colouring `χ : ℕ → Bool` admits a `k`-element set `A` of
positive integers, whose total sum is `≤ N` (so that all non-empty subset sums lie in
`{1, …, N}`), and on which `χ` is constant on the set of non-empty subset sums. -/
def Good (k N : ℕ) : Prop :=
  ∀ χ : ℕ → Bool, ∃ A : Finset ℕ,
    A.card = k ∧ (∀ a ∈ A, 0 < a) ∧ (∑ a ∈ A, a) ≤ N ∧
      ∃ c : Bool, ∀ S : Finset ℕ, S ⊆ A → S.Nonempty → χ (∑ a ∈ S, a) = c
/-- `F k` is the least `N` for which `Good k N` holds. -/
noncomputable def F (k : ℕ) : ℕ := sInf {N | Good k N}
/-! ## Arithmetic helpers on the `2`-adic valuation -/
/-- The `2`-adic valuation of an odd number is `0`. -/
theorem val2_odd (a : ℕ) (h : Odd a) : padicValNat 2 a = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  rw [Nat.odd_iff] at h
  omega
/-- Multiplying by `4` raises the `2`-adic valuation by `2`. -/
theorem val2_four_mul (m : ℕ) (hm : 0 < m) :
    padicValNat 2 (4 * m) = padicValNat 2 m + 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : (4:ℕ) = 2^2 := by norm_num
  rw [h4, padicValNat.mul (by norm_num) (by omega), padicValNat.prime_pow]
  omega
/-- Multiplying by `2` raises the `2`-adic valuation by `1`. -/
theorem val2_two_mul (m : ℕ) (hm : 0 < m) :
    padicValNat 2 (2 * m) = padicValNat 2 m + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
  omega
/-- Multiplying by `2 ^ t` raises the `2`-adic valuation by `t`. -/
theorem val2_pow_two_mul (t m : ℕ) (hm : 0 < m) :
    padicValNat 2 (2 ^ t * m) = t + padicValNat 2 m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow]
/-! ## The explicit lower bound (Section 2) -/
/-- `HasEvenSS A` : every non-empty subset sum of `A` has even `2`-adic valuation. -/
def HasEvenSS (A : Finset ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ A → S.Nonempty → Even (padicValNat 2 (∑ a ∈ S, a))
/-- A positive integer whose `2`-adic valuation is even and which is not odd is divisible by `4`. -/
theorem four_dvd_of_even_val (a : ℕ) (ha : 0 < a) (hev : Even (padicValNat 2 a))
    (hno : ¬ Odd a) : 4 ∣ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.not_odd_iff_even] at hno
  have h2 : 2 ∣ a := hno.two_dvd
  have h1 : 1 ≤ padicValNat 2 a := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    have := padicValNat.eq_zero_iff (p := 2) (n := a)
    rw [h0] at this
    rcases this.mp rfl with h | h | h
    · norm_num at h
    · omega
    · exact h h2
  have h2le : 2 ≤ padicValNat 2 a := by
    rcases hev with ⟨t, ht⟩; omega
  have : (2:ℕ)^2 ∣ a := by
    rw [padicValNat_dvd_iff]
    right; exact h2le
  simpa using this
/-
If every element of `T` is divisible by `4`, positive, and `T` has even subset sums, then
dividing every element by `4` gives a set `T.image (· / 4)` with the same cardinality, positive
elements, total sum a quarter of that of `T`, and again even subset sums.
-/
theorem divFourPack (T : Finset ℕ) (hdvd : ∀ x ∈ T, 4 ∣ x) (hpos : ∀ x ∈ T, 0 < x)
    (hss : HasEvenSS T) :
    (T.image (· / 4)).card = T.card ∧
      (∀ b ∈ T.image (· / 4), 0 < b) ∧
      (∑ a ∈ T, a) = 4 * ∑ b ∈ T.image (· / 4), b ∧
      HasEvenSS (T.image (· / 4)) := by
  refine' ⟨ _, _, _, _ ⟩;
  · exact Finset.card_image_of_injOn fun x hx y hy hxy => by linarith [ Nat.div_mul_cancel ( hdvd x hx ), Nat.div_mul_cancel ( hdvd y hy ) ] ;
  · grind;
  · rw [ Finset.mul_sum _ _ _, Finset.sum_image ];
    · exact Finset.sum_congr rfl fun x hx => by rw [ Nat.mul_div_cancel' ( hdvd x hx ) ] ;
    · exact fun x hx y hy hxy => by linarith [ Nat.div_mul_cancel ( hdvd x hx ), Nat.div_mul_cancel ( hdvd y hy ) ] ;
  · intro S' hS' hS'_nonempty
    obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S ⊆ T ∧ S.Nonempty ∧ S.image (fun x => x / 4) = S' := by
      use Finset.filter (fun x => x / 4 ∈ S') T;
      grind +qlia;
    -- By definition of $S'$, we have $\sum_{b \in S'} b = \sum_{a \in S} a / 4$.
    have h_sum_eq : ∑ b ∈ S', b = ∑ a ∈ S, a / 4 := by
      rw [ ← hS.2.2, Finset.sum_image ];
      exact fun x hx y hy hxy => by linarith [ Nat.div_mul_cancel ( hdvd x ( hS.1 hx ) ), Nat.div_mul_cancel ( hdvd y ( hS.1 hy ) ) ] ;
    -- Since $\sum_{a \in S} a = 4 \sum_{a \in S} a / 4$, we have $\sum_{a \in S} a = 4 \sum_{b \in S'} b$.
    have h_sum_eq' : ∑ a ∈ S, a = 4 * ∑ b ∈ S', b := by
      rw [ h_sum_eq, Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun x hx => by rw [ Nat.mul_div_cancel' ( hdvd x ( hS.1 hx ) ) ] ;
    have := hss S hS.1 hS.2.1; simp_all +decide [ Nat.even_add ] ;
    rw [ show ( 4 : ℕ ) = 2 ^ 2 by norm_num, padicValNat.mul, padicValNat.pow ] at this <;> simp_all +decide [ parity_simps ];
    exact Exists.elim hS.2.1 fun x hx => ⟨ x, hx, Nat.le_of_dvd ( hpos x ( hS.1 hx ) ) ( hdvd x ( hS.1 hx ) ) ⟩
/-
Merging two elements `u, v` of `A` into their sum `u + v` preserves the property of having
even subset sums.  (Used for the two-odd-element case: replacing `u, v` by `u + v`.)
-/
theorem evenSS_merge (A : Finset ℕ) (u v : ℕ) (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v)
    (hnotin : u + v ∉ A \ {u, v}) (hss : HasEvenSS A) :
    HasEvenSS (insert (u + v) (A \ {u, v})) := by
  intro S hS_sub hS_nonempty
  -- Define S' as described
  set S' := (S.erase (u + v)) ∪ (if (u+v) ∈ S then ({u, v} : Finset ℕ) else ∅) with hS'_eq;
  -- We must show `∑ a ∈ S', a = ∑ a ∈ S, a`.
  have hsum_eq : ∑ a ∈ S', a = ∑ a ∈ S, a := by
    by_cases h : u + v ∈ S <;> simp_all +decide [ Finset.sum_union ];
    rw [ Finset.sum_insert, Finset.sum_insert ] <;> simp_all +decide [ Finset.subset_iff ];
    · rw [ ← add_assoc, ← Finset.sum_erase_add _ _ h, add_comm ];
    · grind;
    · grind;
  grind +locals
/-
Under the even-subset-sum hypothesis, a set of positive integers has at most two odd
elements: three odd elements would contain two congruent mod `4`, whose sum has `2`-adic
valuation exactly `1`.
-/
theorem odd_count_le_two (A : Finset ℕ) (hss : HasEvenSS A) :
    (A.filter (fun a => Odd a)).card ≤ 2 := by
  by_contra h_contra;
  -- By `Finset.two_lt_card`, there are three distinct odd elements `x, y, z ∈ A`.
  obtain ⟨x, y, z, hx, hy, hz, hxy, hyz, hxz⟩ : ∃ x y z, x ∈ A ∧ y ∈ A ∧ z ∈ A ∧ Odd x ∧ Odd y ∧ Odd z ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z := by
    rcases Finset.two_lt_card.mp ( not_le.mp h_contra ) with ⟨ x, hx, y, hy, hxy ⟩ ; use x, y ; aesop;
  -- Among three odd numbers, two are congruent mod 4 (residues are 1 or 3), so their sum is ≡ 2 (mod 4), i.e. equals 2 * m with m odd, giving padicValNat 2 (sum) = 1 by val2_two_mul/padicValNat.mul and val2_odd.
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, a ∈ ({x, y, z} : Finset ℕ) ∧ b ∈ ({x, y, z} : Finset ℕ) ∧ a ≠ b ∧ padicValNat 2 (a + b) = 1 := by
    obtain ⟨ k₁, rfl ⟩ := hxy; obtain ⟨ k₂, rfl ⟩ := hyz; obtain ⟨ k₃, rfl ⟩ := hxz.1; simp_all +decide [ Nat.even_add ] ;
    norm_num [ show 2 * k₁ + 1 + ( 2 * k₂ + 1 ) = 2 * ( k₁ + k₂ + 1 ) by ring, show 2 * k₁ + 1 + ( 2 * k₃ + 1 ) = 2 * ( k₁ + k₃ + 1 ) by ring, show 2 * k₂ + 1 + ( 2 * k₃ + 1 ) = 2 * ( k₂ + k₃ + 1 ) by ring, padicValNat.mul ];
    lia;
  have := hss { a, b } ?_ ?_ <;> simp_all +decide [ Finset.sum_pair ];
  grind
/-
**Lemma 2.1.**  If `A` is a non-empty set of positive integers all of whose non-empty
subset sums have even `2`-adic valuation, then `∑_{a ∈ A} a ≥ 4 ^ (|A| - 1)`.
We phrase the conclusion in terms of `A.card` and prove it by strong induction on the total
sum `∑ a ∈ A, a`.
-/
theorem lower_structural (A : Finset ℕ) (hne : A.Nonempty) (hpos : ∀ a ∈ A, 0 < a)
    (heven : ∀ S : Finset ℕ, S ⊆ A → S.Nonempty → Even (padicValNat 2 (∑ a ∈ S, a))) :
    4 ^ (A.card - 1) ≤ ∑ a ∈ A, a := by
  revert A;
  intro A hA hpos hss;
  induction' n : ∑ a ∈ A, a using Nat.strong_induction_on with n ih generalizing A;
  by_cases h_card : A.card = 1;
  · rw [ Finset.card_eq_one ] at h_card ; aesop;
  · by_cases h_odd : (A.filter (fun a => Odd a)).card = 0;
    · -- Since every element of `A` is divisible by `4`, we can apply `divFourPack` to get `B := A.image (·/4)` with `B.card = A.card`, positivity, `∑ A = 4 * ∑ B`, and `HasEvenSS B`.
      obtain ⟨B, hB⟩ : ∃ B : Finset ℕ, B.card = A.card ∧ (∀ b ∈ B, 0 < b) ∧ (∑ a ∈ A, a) = 4 * (∑ b ∈ B, b) ∧ HasEvenSS B := by
        have h_div_four : ∀ a ∈ A, 4 ∣ a := by
          intro a ha; specialize hss { a } ; simp_all +decide ;
          exact four_dvd_of_even_val a ( hpos a ha ) hss ( by simpa using h_odd ha );
        have := divFourPack A h_div_four hpos (fun S hS hS' => hss S hS hS');
        exact ⟨ _, this ⟩;
      specialize ih ( ∑ b ∈ B, b ) ?_ B ?_ ?_ ?_ rfl;
      · linarith [ show 0 < ∑ b ∈ B, b from Finset.sum_pos hB.2.1 ( Finset.card_pos.mp ( by linarith [ Finset.card_pos.mpr hA ] ) ) ];
      · exact Finset.card_pos.mp ( by linarith [ Finset.card_pos.mpr hA ] );
      · exact hB.2.1;
      · exact hB.2.2.2;
      · grind;
    · by_cases h_odd : (A.filter (fun a => Odd a)).card = 1;
      · obtain ⟨u, hu⟩ : ∃ u ∈ A, Odd u ∧ ∀ v ∈ A, v ≠ u → ¬Odd v := by
          obtain ⟨ u, hu ⟩ := Finset.card_eq_one.mp h_odd;
          simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
          exact ⟨ u, hu.1.1, hu.1.2, fun v hv hvu => by_contra fun hv' => hvu <| hu.2 v hv <| by simpa using hv' ⟩;
        -- Let $T = A \setminus \{u\}$. Every element of $T$ is divisible by $4$.
        set T := A.erase u with hT_def
        have hT_div : ∀ x ∈ T, 4 ∣ x := by
          intros x hx
          have hx_even : ¬Odd x := by
            grind
          have hx_div : 4 ∣ x := by
            apply four_dvd_of_even_val x (hpos x (Finset.mem_of_mem_erase hx)) (by
            specialize hss { x } ; aesop) hx_even
          exact hx_div;
        -- Apply `divFourPack` to get `B := T.image (·/4)`, `B.card = T.card = A.card - 1`, `∑ T = 4∑B`, `HasEvenSS B`.
        obtain ⟨B, hB_card, hB_pos, hB_sum, hB_ss⟩ : ∃ B : Finset ℕ, B.card = T.card ∧ (∀ b ∈ B, 0 < b) ∧ (∑ a ∈ T, a) = 4 * ∑ b ∈ B, b ∧ HasEvenSS B := by
          use T.image (· / 4);
          apply divFourPack T hT_div (fun x hx => hpos x (Finset.mem_of_mem_erase hx)) (fun S hS hS_nonempty => hss S (Finset.Subset.trans hS (Finset.erase_subset _ _)) hS_nonempty);
        -- Note `∑ A = u + ∑ T = u + 4∑B` (via `Finset.add_sum_erase`). `∑ B < ∑ A`.
        have h_sum_A : ∑ a ∈ A, a = u + 4 * ∑ b ∈ B, b := by
          rw [ ← hB_sum, ← Finset.sum_erase_add _ _ hu.1, add_comm ]
        have h_sum_B_lt_sum_A : ∑ b ∈ B, b < ∑ a ∈ A, a := by
          grind;
        specialize ih ( ∑ b ∈ B, b ) ( by linarith ) B ; simp_all +decide [ Finset.card_erase_of_mem hu.1 ];
        rcases k : Finset.card A with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ];
        linarith [ ih ( Finset.card_pos.mp ( by linarith ) ) hB_ss, Nat.pos_of_ne_zero ( show u ≠ 0 from ne_of_gt ( hpos u hu.1 ) ) ];
      · -- Since there are exactly two odd elements in A, let's denote them by u and v.
        obtain ⟨u, v, hu, hv, huv⟩ : ∃ u v : ℕ, u ∈ A ∧ v ∈ A ∧ u ≠ v ∧ Odd u ∧ Odd v ∧ ∀ a ∈ A, Odd a → a = u ∨ a = v := by
          have h_odd_card : (A.filter (fun a => Odd a)).card = 2 := by
            have h_odd_card : (A.filter (fun a => Odd a)).card ≤ 2 := by
              apply odd_count_le_two A hss;
            interval_cases _ : Finset.card ( Finset.filter ( fun a => Odd a ) A ) <;> simp_all +decide;
          rw [ Finset.card_eq_two ] at h_odd_card;
          obtain ⟨ u, v, hne, heq ⟩ := h_odd_card; use u, v; simp_all +decide [ Finset.ext_iff ] ;
          grind;
        -- Since $u + v$ is even and has even 2-adic valuation, it must be divisible by 4.
        have huv_div4 : 4 ∣ (u + v) := by
          have huv_even : Even (padicValNat 2 (u + v)) := by
            convert hss { u, v } ( by aesop_cat ) ( by aesop_cat ) using 1 ; simp +decide [ *, Finset.sum_pair ];
          apply four_dvd_of_even_val (u + v) (by linarith [hpos u hu, hpos v hv]) huv_even (by
          grind);
        -- Since $u + v \notin A \setminus \{u, v\}$, we can apply the evenSS_merge lemma.
        have huv_notin : u + v ∉ A \ {u, v} := by
          intro huv_in_A
          have huv_sum : padicValNat 2 (u + v + (u + v)) = padicValNat 2 (u + v) + 1 := by
            rw [ ← two_mul, padicValNat.mul ] <;> norm_num ; linarith [ hpos u hu, hpos v hv ];
            grind;
          have := hss { u + v, u, v } ?_ ?_ <;> simp_all +decide [ Finset.sum_pair, parity_simps ];
          · obtain ⟨ k, hk ⟩ := huv_div4; simp_all +decide [ Nat.even_iff, Nat.add_mod, Nat.mul_mod ] ;
            rw [ show 4 * k = 2 ^ 2 * k by ring, padicValNat.mul, padicValNat.pow ] at this <;> simp_all +decide [ Nat.even_iff ];
            · have := hss { u, v } ?_ ?_ <;> simp_all +decide [ Finset.sum_pair, parity_simps ];
              · rw [ show 4 * k = 2 ^ 2 * k by ring, padicValNat.mul, padicValNat.pow ] at this <;> simp_all +decide [ Nat.even_iff ];
                · exact absurd this ( by rw [ Nat.odd_iff.mp ‹_› ] ; norm_num );
                · grind;
              · exact Finset.insert_subset_iff.mpr ⟨ hu, Finset.singleton_subset_iff.mpr hv ⟩;
            · linarith [ hpos u hu, hpos v hv ];
          · simp_all +decide [ Finset.insert_subset_iff ];
        -- Let $T = \text{insert}(u + v, A \setminus \{u, v\})$.
        set T := insert (u + v) (A \ {u, v}) with hT_def;
        -- By the evenSS_merge lemma, $T$ has even subset sums.
        have hT_evenSS : HasEvenSS T := by
          apply evenSS_merge A u v hu hv huv.left huv_notin hss;
        -- Since $T$ has even subset sums and all elements are divisible by 4, we can apply the divFourPack lemma.
        have hT_divFourPack : (T.image (· / 4)).card = T.card ∧ (∀ b ∈ T.image (· / 4), 0 < b) ∧ (∑ a ∈ T, a) = 4 * ∑ b ∈ T.image (· / 4), b ∧ HasEvenSS (T.image (· / 4)) := by
          apply divFourPack T;
          · simp +zetaDelta at *;
            exact ⟨ huv_div4, fun a ha ha' ha'' => four_dvd_of_even_val a ( hpos a ha ) ( hss { a } ( by aesop ) ( by aesop ) ) ( by intro H; specialize huv; have := huv.2.2.2 a ha H; tauto ) ⟩;
          · grind +qlia;
          · exact hT_evenSS;
        -- Since $T$ has even subset sums and all elements are divisible by 4, we can apply the induction hypothesis to $T.image (· / 4)$.
        have h_ind : 4 ^ ((T.image (· / 4)).card - 1) ≤ ∑ b ∈ T.image (· / 4), b := by
          apply ih (∑ b ∈ T.image (· / 4), b);
          · have h_sum_T : ∑ a ∈ T, a = ∑ a ∈ A, a := by
              rw [ Finset.sum_insert ] <;> simp +decide [ *, Finset.sum_sdiff ];
              rw [ ← n, ← Finset.sum_sdiff ( Finset.insert_subset hu ( Finset.singleton_subset_iff.mpr hv ) ) ] ; simp +decide [ *, Finset.sum_pair ];
              ring;
            linarith [ show ∑ a ∈ A, a > 0 from Finset.sum_pos hpos hA ];
          · exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_insert_self _ _ ) ⟩;
          · exact hT_divFourPack.2.1;
          · exact hT_divFourPack.2.2.2;
          · rfl;
        have hT_sum : ∑ a ∈ T, a = ∑ a ∈ A, a := by
          rw [ Finset.sum_insert ] <;> simp +decide [ *, Finset.sum_sdiff ];
          rw [ ← n, ← Finset.sum_sdiff ( Finset.insert_subset hu ( Finset.singleton_subset_iff.mpr hv ) ) ] ; simp +decide [ *, Finset.sum_insert, Finset.sum_singleton ];
          ring;
        grind +splitImp
/-
**Corollary 2.2 (key inequality).**  If `A` is a `k`-element set of positive integers whose
non-empty subset sums are monochromatic under the colouring `n ↦ ν₂(n) mod 2`, then
`∑_{a ∈ A} a ≥ 4 ^ (k - 1)`.
-/
theorem sum_ge_of_monochromatic (k : ℕ) (hk : 1 ≤ k) (A : Finset ℕ)
    (hcard : A.card = k) (hpos : ∀ a ∈ A, 0 < a)
    (hmono : ∃ c : Bool, ∀ S : Finset ℕ, S ⊆ A → S.Nonempty →
      decide (Even (padicValNat 2 (∑ a ∈ S, a))) = c) :
    4 ^ (k - 1) ≤ ∑ a ∈ A, a := by
  -- By `Finset.exists_mem_eq_inf'` there is `a₁ ∈ A` with `padicValNat 2 a₁ = t`.
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ ∈ A, ∀ a ∈ A, padicValNat 2 a ≥ padicValNat 2 a₁ := by
    exact Finset.exists_min_image _ _ ( Finset.card_pos.mp ( by linarith ) ) |> fun ⟨ a, ha₁, ha₂ ⟩ => ⟨ a, ha₁, fun b hb => ha₂ b hb ⟩
  generalize_proofs at *; (
  -- Let `A' := A.image (fun a => a / 2^t)`. The map is injective on `A` (all elements divisible by `2^t`: if `a/2^t = a'/2^t` then `a = 2^t*(a/2^t) = 2^t*(a'/2^t) = a'`), so `A'.card = A.card = k`, and every element of `A'` is positive.
  set t := padicValNat 2 a₁
  set A' := A.image (fun a => a / 2 ^ t)
  have hA'_card : A'.card = A.card := by
    rw [ Finset.card_image_of_injOn ];
    intros a ha b hb hab; have := Nat.div_mul_cancel ( show 2 ^ t ∣ a from Nat.dvd_trans ( pow_dvd_pow _ ( ha₁.2 a ha ) ) ( Nat.ordProj_dvd _ _ ) ) ; have := Nat.div_mul_cancel ( show 2 ^ t ∣ b from Nat.dvd_trans ( pow_dvd_pow _ ( ha₁.2 b hb ) ) ( Nat.ordProj_dvd _ _ ) ) ; aesop;
  have hA'_pos : ∀ b ∈ A', 0 < b := by
    exact fun b hb => by obtain ⟨ a, ha, rfl ⟩ := Finset.mem_image.mp hb; exact Nat.div_pos ( Nat.le_of_dvd ( hpos a ha ) ( Nat.dvd_trans ( pow_dvd_pow _ ( ha₁.2 a ha ) ) ( Nat.ordProj_dvd _ _ ) ) ) ( pow_pos ( by decide ) _ ) ;
  have hA'_sum : ∑ a ∈ A, a = 2 ^ t * ∑ b ∈ A', b := by
    rw [ Finset.mul_sum _ _ _, Finset.sum_image ];
    · exact Finset.sum_congr rfl fun x hx => by rw [ Nat.mul_div_cancel' ( Nat.dvd_trans ( pow_dvd_pow _ ( ha₁.2 x hx ) ) ( Nat.ordProj_dvd _ _ ) ) ] ;
    · grind
  generalize_proofs at *; (
  -- Establish `HasEvenSS`-style hypothesis for `A'`: take `S' ⊆ A'` nonempty; let `S := A.filter (fun a => a/2^t ∈ S') ⊆ A`, which is nonempty and satisfies `S.image (·/2^t) = S'`.
  have hA'_evenSS : ∀ S' ⊆ A', S'.Nonempty → Even (padicValNat 2 (∑ b ∈ S', b)) := by
    intros S' hS'_sub hS'_nonempty
    obtain ⟨S, hS_sub, hS_nonempty, hS_image⟩ : ∃ S ⊆ A, S.Nonempty ∧ S.image (fun a => a / 2 ^ t) = S' := by
      use Finset.filter (fun a => a / 2 ^ t ∈ S') A; simp_all +decide [ Finset.subset_iff ] ; (
      exact ⟨ by obtain ⟨ x, hx ⟩ := hS'_nonempty; obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp ( hS'_sub hx ) ; exact ⟨ y, by aesop ⟩, Finset.Subset.antisymm ( Finset.image_subset_iff.mpr fun x hx => by aesop ) ( fun x hx => by obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp ( hS'_sub hx ) ; exact Finset.mem_image.mpr ⟨ y, by aesop ⟩ ) ⟩ ;)
    generalize_proofs at *; (
    -- Then `2^t * ∑ b ∈ S', b = ∑ a ∈ S, a =: s` (as for the total sum).
    have hS_sum : ∑ a ∈ S, a = 2 ^ t * ∑ b ∈ S', b := by
      rw [ ← hS_image, Finset.mul_sum _ _ _, Finset.sum_image ];
      · exact Finset.sum_congr rfl fun x hx => by rw [ Nat.mul_div_cancel' ( Nat.dvd_trans ( pow_dvd_pow _ ( ha₁.2 x ( hS_sub hx ) ) ) ( Nat.ordProj_dvd _ _ ) ) ] ;
      · intro x hx y hy; have := Finset.card_image_iff.mp ( by aesop : Finset.card ( Finset.image ( fun a => a / 2 ^ t ) A ) = Finset.card A ) ; aesop;
    generalize_proofs at *; (
    -- From `hmono`, both `Even (padicValNat 2 s)` and `Even t` are equivalent to `c = true`, hence `padicValNat 2 s` and `t` have the same parity.
    obtain ⟨c, hc⟩ := hmono
    have h_parity : Even (padicValNat 2 (∑ a ∈ S, a)) ↔ Even t := by
      have := hc { a₁ } ; simp_all +decide ;
      grind
    generalize_proofs at *; (
    -- Since `∑ b ∈ S', b > 0`, `val2_pow_two_mul` gives `padicValNat 2 s = t + padicValNat 2 (∑ b ∈ S', b)`.
    have h_val2_sum : padicValNat 2 (∑ a ∈ S, a) = t + padicValNat 2 (∑ b ∈ S', b) := by
      rw [ hS_sum, padicValNat.mul ] <;> norm_num [ Nat.ne_of_gt ( Finset.sum_pos ( fun x hx => hA'_pos x ( hS'_sub hx ) ) hS'_nonempty ) ]
    generalize_proofs at *; (
    grind))))
  generalize_proofs at *; (
  -- Apply `lower_structural A'` (nonempty, positive, the even-subset-sum hypothesis just shown): `4^(A'.card - 1) ≤ ∑ b∈A', b`.
  have hA'_lower : 4 ^ (A'.card - 1) ≤ ∑ b ∈ A', b := by
    apply lower_structural A' (by
    exact ⟨ _, Finset.mem_image_of_mem _ ha₁.1 ⟩) hA'_pos hA'_evenSS
  generalize_proofs at *; (
  exact hcard ▸ hA'_card ▸ hA'_sum ▸ le_trans hA'_lower ( Nat.le_mul_of_pos_left _ ( pow_pos ( by decide ) _ ) )))))
/-- Any `N` witnessing `Good k N` (for `k ≥ 1`) satisfies `N ≥ 4 ^ (k - 1)`; this is the
lower-bound half of the estimate, obtained by testing against the `ν₂ mod 2` colouring. -/
theorem good_lower (k N : ℕ) (hk : 1 ≤ k) (h : Good k N) : 4 ^ (k - 1) ≤ N := by
  obtain ⟨A, hcard, hpos, hsum, c, hc⟩ := h (fun n => decide (Even (padicValNat 2 n)))
  have := sum_ge_of_monochromatic k hk A hcard hpos ⟨c, hc⟩
  omega
/-! ## Finiteness via Hindman's theorem (Sections 3–4) -/
/-- There exists a non-principal idempotent ultrafilter on `ℕ`.  (Section 3: Ellis–Numakura
applied to the compact right-topological semigroup of ultrafilters finer than the cofinite
filter.) -/
theorem exists_nonprincipal_idempotent :
    ∃ U : Ultrafilter ℕ, U + U = U ∧ (↑U : Filter ℕ) ≤ Filter.cofinite := by
  set s : Set (Ultrafilter ℕ) := {U : Ultrafilter ℕ | (↑U : Filter ℕ) ≤ Filter.cofinite} with hs
  have hcompact : IsCompact s := by
    refine IsClosed.isCompact ?_
    simp only [hs, le_cofinite_iff_compl_singleton_mem, Set.setOf_forall]
    exact isClosed_iInter fun x => ultrafilter_isClosed_basic ({x}ᶜ)
  have hne : s.Nonempty := ⟨hyperfilter ℕ, hyperfilter_le_cofinite⟩
  have hsub : ∀ U ∈ s, ∀ V ∈ s, U + V ∈ s := by
    intro U _ V hV
    simp only [hs, Set.mem_setOf_eq] at hV ⊢
    rw [le_cofinite_iff_compl_singleton_mem]
    intro n
    have key : ∀ᶠ m in (U : Filter ℕ), ∀ᶠ m' in (V : Filter ℕ),
        (m + m') ∈ ({n}ᶜ : Set ℕ) := by
      filter_upwards with m
      have hcof : {m' : ℕ | m + m' ∈ ({n}ᶜ : Set ℕ)} ∈ (V : Filter ℕ) := by
        apply hV
        rw [Filter.mem_cofinite]
        apply Set.Finite.subset (Set.finite_Iic n)
        intro m' hm'
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_singleton_iff, not_not] at hm'
        simp only [Set.mem_Iic]; omega
      filter_upwards [hcof] with m' hm' using hm'
    exact (Ultrafilter.eventually_add U V (· ∈ ({n}ᶜ : Set ℕ))).2 key
  obtain ⟨U, hUs, hidem⟩ := exists_idempotent_in_compact_add_subsemigroup
    (fun r => Ultrafilter.continuous_add_left r) s hne hcompact hsub
  exact ⟨U, hidem, hUs⟩
/-- Applying Hindman's theorem (via a non-principal idempotent ultrafilter) to a two-colouring
`χ` produces a stream `b` of **positive** integers and a colour `cval` such that every non-empty
finite sum of entries of `b` receives colour `cval`. -/
theorem exists_pos_FS_stream (χ : ℕ → Bool) :
    ∃ (b : Stream' ℕ) (cval : Bool),
      (∀ i, 0 < b.get i) ∧
      ∀ s : Finset ℕ, s.Nonempty → χ (∑ i ∈ s, b.get i) = cval := by
  obtain ⟨U, hidem, hUcof⟩ := exists_nonprincipal_idempotent
  have hpos_mem : {n : ℕ | 0 < n} ∈ U := by
    have h0 : ({0}ᶜ : Set ℕ) ∈ U := (le_cofinite_iff_compl_singleton_mem.mp hUcof) 0
    apply Filter.mem_of_superset h0
    intro n hn; simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hn
    simp only [Set.mem_setOf_eq]; omega
  obtain ⟨cval, hcval⟩ : ∃ cval : Bool, {n : ℕ | χ n = cval} ∈ U := by
    rcases U.mem_or_compl_mem {n : ℕ | χ n = true} with h | h
    · exact ⟨true, h⟩
    · refine ⟨false, ?_⟩
      apply Filter.mem_of_superset h
      intro n hn; simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hn ⊢
      simpa using hn
  set s₀ : Set ℕ := {n : ℕ | χ n = cval} ∩ {n : ℕ | 0 < n} with hs₀
  have hs₀U : s₀ ∈ U := Filter.inter_mem hcval hpos_mem
  obtain ⟨b, hb⟩ := exists_FS_of_large U hidem s₀ hs₀U
  refine ⟨b, cval, ?_, ?_⟩
  · intro i
    have : b.get i ∈ s₀ := hb (FS.singleton b i)
    exact this.2
  · intro s hs
    have : (∑ i ∈ s, b.get i) ∈ s₀ := hb (FS.finset_sum b s hs)
    exact this.1
/-
For a single two-colouring `χ`, Hindman's theorem yields a `k`-element set `A` of positive
integers whose non-empty subset sums are monochromatic under `χ`.
-/
theorem hindman_mono (k : ℕ) (χ : ℕ → Bool) :
    ∃ A : Finset ℕ, A.card = k ∧ (∀ a ∈ A, 0 < a) ∧
      ∃ c : Bool, ∀ S : Finset ℕ, S ⊆ A → S.Nonempty → χ (∑ a ∈ S, a) = c := by
  obtain ⟨ b, cval, hb1, hb2 ⟩ := exists_pos_FS_stream χ;
  -- Define prefix sums `P j := ∑ i ∈ Finset.range j, b.get i`, block boundaries `M : ℕ → ℕ` by `M 0 = 0`, `M (t+1) = M t + P (M t) + 1`.
  set P : ℕ → ℕ := fun j => ∑ i ∈ Finset.range j, b.get i
  set M : ℕ → ℕ := fun t => Nat.recOn t 0 (fun t Mt => Mt + P Mt + 1);
  -- Define block sums `y t := ∑ i ∈ blk t, b.get i`.
  set y : ℕ → ℕ := fun t => ∑ i ∈ Finset.Ico (M t) (M (t + 1)), b.get i;
  -- Show that `y` is strictly monotone.
  have hy_mono : StrictMono y := by
    refine' strictMono_nat_of_lt_succ fun t => _;
    have h_y_ge_P : ∀ t, y t ≥ P (M t) + 1 := by
      have h_y_ge_P : ∀ t, y t ≥ (M (t + 1) - M t) := by
        exact fun t => le_trans ( by norm_num ) ( Finset.sum_le_sum fun _ _ => hb1 _ );
      grind;
    refine' lt_of_lt_of_le _ ( h_y_ge_P ( t + 1 ) );
    exact Nat.lt_succ_of_le ( Finset.sum_le_sum_of_subset ( Finset.subset_iff.mpr fun i hi => Finset.mem_range.mpr ( by linarith [ Finset.mem_Ico.mp hi ] ) ) );
  refine' ⟨ Finset.image y ( Finset.range k ), _, _, cval, _ ⟩ <;> norm_num [ Finset.card_image_of_injective _ hy_mono.injective ];
  · exact fun t ht => Finset.sum_pos ( fun _ _ => hb1 _ ) ( Finset.nonempty_Ico.mpr ( by aesop ) );
  · intro S hS hS_nonempty
    obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T ⊆ Finset.range k ∧ S = T.image y := by
      use Finset.filter (fun t => y t ∈ S) (Finset.range k);
      grind;
    convert hb2 ( Finset.biUnion T fun t => Finset.Ico ( M t ) ( M ( t + 1 ) ) ) _ using 1;
    · rw [ hT.2, Finset.sum_image <| by intros a ha b hb hab; exact hy_mono.injective hab ];
      rw [ Finset.sum_biUnion ];
      intros t ht t' ht' hne; simp_all +decide [ Finset.disjoint_left ] ;
      intro a ha₁ ha₂ ha₃; contrapose! hne;
      exact le_antisymm ( le_of_not_gt fun h => by linarith [ show M ( t' + 1 ) ≤ M t from by exact monotone_nat_of_le_succ ( fun n => by exact Nat.le_succ_of_le ( Nat.le_add_right _ _ ) ) ( by linarith ) ] ) ( le_of_not_gt fun h => by linarith [ show M ( t + 1 ) ≤ M t' from by exact monotone_nat_of_le_succ ( fun n => by exact Nat.le_succ_of_le ( Nat.le_add_right _ _ ) ) ( by linarith ) ] );
    · obtain ⟨ t, ht ⟩ := hS_nonempty; obtain ⟨ u, hu, rfl ⟩ := Finset.mem_image.mp ( hT.2 ▸ ht ) ; exact ⟨ _, Finset.mem_biUnion.mpr ⟨ u, hu, Finset.left_mem_Ico.mpr <| Nat.lt_succ_of_le <| Nat.le_add_right _ _ ⟩ ⟩ ;
/-- **Lemma 4.1 / Corollary 4.2.**  For every `k` there exists `N` with `Good k N`; i.e. `F k`
is finite. -/
theorem good_exists (k : ℕ) : ∃ N, Good k N := by
  by_contra hcon
  push_neg at hcon
  have hbad : ∀ N, ∃ χ : ℕ → Bool, ∀ A : Finset ℕ, A.card = k → (∀ a ∈ A, 0 < a) →
      (∑ a ∈ A, a) ≤ N → ∀ c : Bool, ∃ S : Finset ℕ, S ⊆ A ∧ S.Nonempty ∧ χ (∑ a ∈ S, a) ≠ c := by
    intro N
    have h := hcon N
    unfold Good at h
    push_neg at h
    exact h
  choose χ_ hχ using hbad
  set U : Ultrafilter ℕ := hyperfilter ℕ with hU
  set χ : ℕ → Bool := fun n => if {N | χ_ N n = true} ∈ U then true else false with hχdef
  have hagree : ∀ n, ∀ᶠ N in (↑U : Filter ℕ), χ_ N n = χ n := by
    intro n
    by_cases h : {N | χ_ N n = true} ∈ U
    · have hcn : χ n = true := by simp [hχdef, h]
      filter_upwards [Ultrafilter.mem_coe.mpr h] with N hN
      rw [hcn]; simpa using hN
    · have hcn : χ n = false := by simp [hχdef, h]
      filter_upwards [Ultrafilter.mem_coe.mpr (Ultrafilter.compl_mem_iff_notMem.mpr h)] with N hN
      rw [hcn]; simpa using hN
  obtain ⟨A, hcard, hpos, cc, hmono⟩ := hindman_mono k χ
  set M := ∑ a ∈ A, a with hM
  set 𝒮 : Finset (Finset ℕ) := A.powerset.filter (fun S => S.Nonempty) with h𝒮
  have h1 : ∀ᶠ N in (↑U : Filter ℕ), M ≤ N := by
    have hmem : {N | M ≤ N} ∈ U := by
      apply mem_hyperfilter_of_finite_compl
      apply Set.Finite.subset (Set.finite_Iio M)
      intro N hN; simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hN
      simp only [Set.mem_Iio]; omega
    filter_upwards [Ultrafilter.mem_coe.mpr hmem] with N hN using hN
  have h2 : ∀ᶠ N in (↑U : Filter ℕ), ∀ S ∈ 𝒮, χ_ N (∑ a ∈ S, a) = χ (∑ a ∈ S, a) := by
    rw [Finset.eventually_all]
    intro S _; exact hagree _
  obtain ⟨N, hN1, hN2⟩ := (h1.and h2).exists
  obtain ⟨S, hSsub, hSne, hSne'⟩ := hχ N A hcard hpos hN1 cc
  have hSmem : S ∈ 𝒮 := by
    rw [h𝒮, Finset.mem_filter, Finset.mem_powerset]; exact ⟨hSsub, hSne⟩
  have hval := hN2 S hSmem
  rw [hmono S hSsub hSne] at hval
  exact hSne' hval
/-! ## The main estimate -/
/-- `Good k` is upward closed: if `N ≤ M` and `Good k N`, then `Good k M`. -/
theorem good_mono {k N M : ℕ} (hNM : N ≤ M) (h : Good k N) : Good k M := by
  intro χ
  obtain ⟨A, hcard, hpos, hsum, hc⟩ := h χ
  exact ⟨A, hcard, hpos, le_trans hsum hNM, hc⟩
/-- `Good k (F k)` holds: the infimum is attained. -/
theorem good_F (k : ℕ) : Good k (F k) := Nat.sInf_mem (good_exists k)
/-- **Theorem 1.2.**  For every `k ≥ 1`, `F k` exists (`Good k (F k)`) and satisfies
`4 ^ (k - 1) ≤ F k`. -/
theorem F_estimate (k : ℕ) (hk : 1 ≤ k) : 4 ^ (k - 1) ≤ F k ∧ Good k (F k) :=
  ⟨good_lower k (F k) hk (good_F k), good_F k⟩
end FiniteSumsFk
