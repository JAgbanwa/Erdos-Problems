/-
# The partition sequence of BKLO §10 exists in a dense graph

`BKLO.exists_balanced_parts` (`BKLO/EquitablePartitionDense.lean`) splits a vertex set into parts
of prescribed sizes in which no vertex has more than its share of non-neighbours.  Here that is
turned into the two statements BKLO §10 consumes:

* `BKLO.exists_kDeltaPartition_dense` — a graph on `S` of minimum degree `(δ + 3ε)|S|` has, for
  `|S|` large, a `(k, δ+ε)`-partition in the sense of `BKLO.IsKDeltaPartition`;
* `BKLO.exists_partSeq_dense` — hence a one-level partition sequence
  `BKLO.PartSeq k (δ+ε) δ ε m [] P E S` with `m = ⌈|S|/k⌉`, which is what
  `BKLO.lemma_10_13_K3'` runs on.

A single level is all that is needed: the §10 iteration only asks that the bottom parts be small
compared with `|S|`, and `⌈|S|/k⌉ ≤ γ|S|` already for `k ≥ 2/γ`, while the hierarchy of
`BKLO.Lemma1012K3'` is a *lower* bound `1/k ≤ ε` on `k`.  So both constraints are satisfied by
taking `k` large, and no recursion — which would need a density parameter increasing down the
levels — is required.

Everything here is `sorry`-free.
-/
import BKLO.EquitablePartitionDense
import BKLO.Section10Iteration

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- The size condition of the sampling lemma, in real arithmetic: if `n > 131072k⁶/ε⁴` and the
parts have size at least `n/(2k)`, then the union bound of `BKLO.exists_balanced_sample` applies to
the `2n` events. -/
private theorem sampling_threshold_arith {ε θ nR cR kR : ℝ} (hε0 : 0 < ε)
    (hk : 2 ≤ kR) (hθ : θ = ε / (2 * kR)) (hn0 : 0 < nR) (hc : nR ≤ 2 * kR * cR)
    (hn : 131072 * kR ^ 6 / ε ^ 4 < nR) :
    2 * nR < (θ ^ 2 * cR / 32) ^ 2 := by
  have hk0 : (0 : ℝ) < kR := by linarith
  have hc0 : 0 < cR := by nlinarith only [hc, hn0, hk0]
  have hθv : θ ^ 2 = ε ^ 2 / (4 * kR ^ 2) := by
    rw [hθ]; field_simp; ring
  have hexp : (θ ^ 2 * cR / 32) ^ 2 = ε ^ 4 * cR ^ 2 / (16384 * kR ^ 4) := by
    rw [hθv]; field_simp; ring
  rw [hexp]
  have hcsq : nR ^ 2 ≤ 4 * kR ^ 2 * cR ^ 2 := by
    linarith only [mul_self_le_mul_self hn0.le hc]
  have hbig : 131072 * kR ^ 6 < ε ^ 4 * nR := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < ε ^ 4)] at hn
    linarith
  rw [lt_div_iff₀ (by positivity : (0:ℝ) < 16384 * kR ^ 4)]
  have he4 : (0 : ℝ) < ε ^ 4 := by positivity
  have h1 : ε ^ 4 * nR ^ 2 ≤ ε ^ 4 * (4 * kR ^ 2 * cR ^ 2) :=
    mul_le_mul_of_nonneg_left hcsq he4.le
  have h2 : 131072 * kR ^ 6 * nR < ε ^ 4 * nR * nR := by
    linarith only [mul_lt_mul_of_pos_right hbig hn0]
  have hmain : (4 * kR ^ 2) * (2 * nR * (16384 * kR ^ 4))
      < (4 * kR ^ 2) * (ε ^ 4 * cR ^ 2) := by linarith only [h1, h2]
  exact lt_of_mul_lt_mul_left hmain (by positivity)


omit [DecidableEq V] in
/-- The size of every part produced by `BKLO.exists_balanced_parts` occurs in the prescribed list of
sizes. -/
theorem card_mem_of_forall₂ {Ps : List (Finset V)} {L : List ℕ}
    (h : List.Forall₂ (fun Q c => Q.card = c) Ps L) : ∀ Q ∈ Ps, ∃ c ∈ L, Q.card = c := by
  induction h with
  | nil => intro Q hQ; exact absurd hQ (by simp)
  | @cons Q' c' Ps' L' hh _ ih =>
      intro Q hQ
      rcases List.mem_cons.1 hQ with rfl | hQ'
      · exact ⟨c', List.mem_cons_self .., hh⟩
      · obtain ⟨c, hc, hQc⟩ := ih Q hQ'
        exact ⟨c, List.mem_cons_of_mem _ hc, hQc⟩

set_option maxHeartbeats 1000000 in
/-- **A `(k, δ+ε)`-partition exists in a dense graph.**  Every graph on `S` in which each vertex has
at least `(δ + 3ε)|S|` neighbours has, for `|S|` large, an equitable partition into `k` parts in
which every vertex of `S` has at least `(δ + ε)|W|` neighbours in every part `W`. -/
theorem exists_kDeltaPartition_dense {δ ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {k : ℕ} (hk : 2 ≤ k) :
    ∃ n₀ : ℕ, ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S →
      (∀ v ∈ S, (δ + 3 * ε) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ P : Finset (Finset V), IsKDeltaPartition k (δ + ε) P E S ∧ ∀ W ∈ P, W ⊆ S := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (131072 * (k : ℝ) ^ 6 / ε ^ 4)
  refine ⟨max N (2 * k) + 1, ?_⟩
  intro V _ E S hcard hES hdeg
  have hk0 : 0 < k := by omega
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set n : ℕ := S.card with hndef
  have hn2k : 2 * k + 1 ≤ n := le_trans (by omega) hcard
  have hnN : N < n := lt_of_lt_of_le (by omega) hcard
  have hn0 : 0 < n := by omega
  have hnR0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hnbig : 131072 * (k : ℝ) ^ 6 / ε ^ 4 < (n : ℝ) := by
    refine lt_of_lt_of_le hN ?_
    exact_mod_cast hnN.le
  -- the prescribed sizes
  set q : ℕ := n / k with hqdef
  set r : ℕ := n % k with hrdef
  have hqk : k * q + r = n := Nat.div_add_mod n k
  have hrk : r < k := Nat.mod_lt _ hk0
  have hq2 : 2 ≤ q := by
    rw [hqdef]
    have : 2 * k ≤ n := by omega
    exact (Nat.le_div_iff_mul_le hk0).2 (by omega)
  set L : List ℕ := List.replicate (k - r) q ++ List.replicate r (q + 1) with hLdef
  have hLsum : L.sum = n := by
    rw [hLdef, List.sum_append, List.sum_replicate, List.sum_replicate, smul_eq_mul, smul_eq_mul]
    obtain ⟨d, hd⟩ : ∃ d, k = r + d := ⟨k - r, by omega⟩
    have hkr : k - r = d := by omega
    rw [hkr]
    calc d * q + r * (q + 1) = (r + d) * q + r := by ring
      _ = k * q + r := by rw [hd]
      _ = n := hqk
  have hLlen : L.length = k := by
    rw [hLdef, List.length_append, List.length_replicate, List.length_replicate]
    omega
  have hLmem : ∀ c ∈ L, q ≤ c ∧ c ≤ q + 1 := by
    intro c hc
    rw [hLdef, List.mem_append] at hc
    rcases hc with hc | hc
    · have := List.eq_of_mem_replicate hc
      omega
    · have := List.eq_of_mem_replicate hc
      omega
  have hLpos : ∀ c ∈ L, 0 < c := fun c hc => lt_of_lt_of_le (by omega) (hLmem c hc).1
  have hLupper : ∀ c ∈ L, c * k ≤ n + k - 1 := by
    intro c hc
    rw [hLdef, List.mem_append] at hc
    rcases hc with hc | hc
    · have hcq := List.eq_of_mem_replicate hc
      have hcm : c * k = k * q := by rw [hcq, Nat.mul_comm]
      omega
    · have hr0 : 0 < r := by
        rcases Nat.eq_zero_or_pos r with h | h
        · rw [h] at hc; simp at hc
        · exact h
      have hcq := List.eq_of_mem_replicate hc
      have hcm : c * k = k * q + k := by rw [hcq]; ring
      omega
  have hLsorted : L.Pairwise (· ≤ ·) := by
    rw [hLdef]
    refine List.pairwise_append.2 ⟨?_, ?_, ?_⟩
    · exact List.pairwise_replicate.2 (Or.inr le_rfl)
    · exact List.pairwise_replicate.2 (Or.inr le_rfl)
    · intro a ha b hb
      rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
      omega
  -- the sampling parameter
  set θ : ℝ := ε / (2 * (k : ℝ)) with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one (by linarith)]
    linarith
  -- every part is at least `n/(2k)`
  have hqn : (n : ℝ) ≤ 2 * (k : ℝ) * (q : ℝ) := by
    have h1 : n ≤ 2 * (k * q) := by omega
    have h2 : ((n : ℕ) : ℝ) ≤ ((2 * (k * q) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hLthr : ∀ c ∈ L, 2 * ((S.card : ℝ)) < (θ ^ 2 * (c : ℝ) / 32) ^ 2 := by
    intro c hc
    have hcq : (q : ℝ) ≤ (c : ℝ) := by exact_mod_cast (hLmem c hc).1
    refine sampling_threshold_arith hε0 hkR hθdef hnR0 ?_ hnbig
    have : 2 * (k : ℝ) * (q : ℝ) ≤ 2 * (k : ℝ) * (c : ℝ) := by nlinarith
    linarith [hqn]
  -- the split
  obtain ⟨Ps, hforall, hsub, hcover, hpair, hbound⟩ :=
    exists_balanced_parts (I := S) (T := fun v => nonAdjIn E S v) (n := n) hn0 θ hθ0 hθ1
      L S 0 le_rfl hLsum.symm hLsorted hLpos hLthr
      (by
        intro v _
        have hTS : nonAdjIn E S v ∩ S = nonAdjIn E S v :=
          Finset.inter_eq_left.2 nonAdjIn_subset
        rw [hTS, ← hndef]
        have hid : ((nonAdjIn E S v).card : ℝ) * (n : ℝ) / (n : ℝ)
            = ((nonAdjIn E S v).card : ℝ) := by
          field_simp
        rw [hid]
        linarith)
  -- the parts are pairwise distinct
  have hPsne : ∀ Q ∈ Ps, Q.Nonempty := by
    intro Q hQ
    obtain ⟨c, hc, hQc⟩ := card_mem_of_forall₂ hforall Q hQ
    have := (hLmem c hc).1
    exact Finset.card_pos.1 (by omega)
  have hnodup : Ps.Nodup := by
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) hpair
    intro heq
    subst heq
    obtain ⟨x, hx⟩ := hPsne a ha
    exact (Finset.disjoint_left.1 hab hx) hx
  set P : Finset (Finset V) := Ps.toFinset with hPdef
  have hmemP : ∀ Q, Q ∈ P ↔ Q ∈ Ps := by intro Q; rw [hPdef, List.mem_toFinset]
  have hPcard : P.card = k := by
    rw [hPdef, List.toFinset_card_of_nodup hnodup, hforall.length_eq, hLlen]
  have hPsizes : ∀ Q ∈ P, q ≤ Q.card ∧ Q.card ≤ q + 1 := by
    intro Q hQ
    rw [hmemP] at hQ
    obtain ⟨c, hc, hQc⟩ := card_mem_of_forall₂ hforall Q hQ
    rw [hQc]
    exact hLmem c hc
  refine ⟨P, ⟨⟨hPcard, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · -- pairwise disjoint
    intro W hW W' hW' hne
    rw [hmemP] at hW hW'
    exact hpair.forall (fun _ _ h => h.symm) hW hW' hne
  · -- cover
    ext a
    simp only [Finset.mem_biUnion, id]
    constructor
    · rintro ⟨W, hW, haW⟩
      rw [hmemP] at hW
      exact hsub W hW haW
    · intro ha
      obtain ⟨Q, hQ, haQ⟩ := hcover a ha
      exact ⟨Q, (hmemP Q).2 hQ, haQ⟩
  · -- size lower bound
    intro W hW
    exact (hPsizes W hW).1
  · -- size upper bound
    intro W hW
    refine (Nat.le_div_iff_mul_le hk0).2 ?_
    rw [hmemP] at hW
    obtain ⟨c, hc, hWc⟩ := card_mem_of_forall₂ hforall W hW
    rw [hWc]
    exact hLupper c hc
  · -- the degree condition
    intro x hx W hW
    have hWS : W ⊆ S := by
      rw [hmemP] at hW; exact hsub W hW
    have hWcard : ((W.card : ℝ)) ≥ (q : ℝ) := by exact_mod_cast (hPsizes W hW).1
    have hbnd := hbound W ((hmemP W).1 hW) x hx
    -- the non-neighbourhood of `x` is small
    have hTx : ((nonAdjIn E S x).card : ℝ) ≤ (1 - δ - 3 * ε) * (n : ℝ) := by
      have h1 : degTo E x S + (nonAdjIn E S x).card = n := by
        have h := degTo_add_card_nonAdjIn (E := E) (S := S) (W := S) (Finset.Subset.refl S) x
        have h2 : nonAdjIn E S x ∩ S = nonAdjIn E S x :=
          Finset.inter_eq_left.2 nonAdjIn_subset
        rw [h2] at h
        exact h
      have h2 : edeg E x ≤ degTo E x S := edeg_le_degTo hES x
      have h3 : (δ + 3 * ε) * (n : ℝ) ≤ (edeg E x : ℝ) := hdeg x hx
      have h4 : ((edeg E x : ℕ) : ℝ) ≤ ((degTo E x S : ℕ) : ℝ) := by exact_mod_cast h2
      have h5 : ((degTo E x S : ℕ) : ℝ) + ((nonAdjIn E S x).card : ℝ) = (n : ℝ) := by
        exact_mod_cast h1
      linarith
    -- hence the non-neighbourhood inside `W` is small
    have hshare : ((nonAdjIn E S x).card : ℝ) * (W.card : ℝ) / (n : ℝ)
        ≤ (1 - δ - 3 * ε) * (W.card : ℝ) := by
      have hW0 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
      have h1 : ((nonAdjIn E S x).card : ℝ) * (W.card : ℝ)
          ≤ ((1 - δ - 3 * ε) * (n : ℝ)) * (W.card : ℝ) :=
        mul_le_mul_of_nonneg_right hTx hW0
      rw [div_le_iff₀ hnR0]
      linarith only [h1]
    have hsplit : (degTo E x W : ℝ) + ((nonAdjIn E S x ∩ W).card : ℝ) = (W.card : ℝ) := by
      exact_mod_cast degTo_add_card_nonAdjIn hWS x
    -- the error term is small
    have herr : θ * (S.card : ℝ) ≤ 2 * ε * (W.card : ℝ) := by
      have h1 : θ * (n : ℝ) = ε * (n : ℝ) / (2 * (k : ℝ)) := by rw [hθdef]; ring
      have h2 : ε * (n : ℝ) / (2 * (k : ℝ)) ≤ ε * (q : ℝ) := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * (k : ℝ))]
        linarith only [mul_le_mul_of_nonneg_left hqn hε0.le]
      have h3 : ε * (q : ℝ) ≤ ε * (W.card : ℝ) :=
        mul_le_mul_of_nonneg_left hWcard hε0.le
      rw [← hndef]
      linarith only [h1, h2, h3,
        mul_nonneg hε0.le (Nat.cast_nonneg W.card : (0:ℝ) ≤ (W.card : ℝ))]
    rw [← hndef] at hbnd
    linarith only [hbnd, hshare, hsplit, herr]
  · intro W hW
    rw [hmemP] at hW
    exact hsub W hW

/-! ### The one-level partition sequence -/

/-- A `(k, c)`-partition of `S` is a one-level `(k, c, ⌈|S|/k⌉)`-partition sequence. -/
theorem partSeq_of_isKDeltaPartition {k : ℕ} {c δ ε : ℝ} {P : Finset (Finset V)}
    {E : Finset (Sym2 V)} {S : Finset V} (h : IsKDeltaPartition k c P E S) :
    PartSeq k c δ ε ((S.card + k - 1) / k) [] P E S := by
  classical
  have hres : restrictParts P S = P := by
    ext W
    rw [mem_restrictParts]
    exact ⟨fun hw => hw.1, fun hw => ⟨hw, h.1.subset_of_mem hw⟩⟩
  refine ⟨by rw [hres]; exact h, ?_⟩
  intro W hW
  rw [hres] at hW
  refine ⟨?_, h.1.size_upper W hW⟩
  have hlow := h.1.size_lower W hW
  have hup : (S.card + k - 1) / k ≤ S.card / k + 1 := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk]
    · calc (S.card + k - 1) / k ≤ (S.card + k) / k := Nat.div_le_div_right (by omega)
        _ = S.card / k + 1 := Nat.add_div_right _ hk
  omega

/-- **The partition sequence of BKLO §10 exists in a dense graph.**  For `|S|` large, a graph on `S`
of minimum degree `(δ + 3ε)|S|` carries a one-level `(k, δ+ε, m)`-partition sequence whose parts all
have `m - 1` or `m` vertices, `m = ⌈|S|/k⌉`. -/
theorem exists_partSeq_dense {δ ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {k : ℕ} (hk : 2 ≤ k) :
    ∃ n₀ : ℕ, ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S →
      (∀ v ∈ S, (δ + 3 * ε) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ (Pl : Finset (Finset V)) (m : ℕ),
        S.card / k ≤ m ∧ m ≤ S.card / k + 1 ∧
        PartSeq k (δ + ε) δ ε m [] Pl E S ∧
        (∀ W ∈ restrictParts Pl S, W.card ≤ m) ∧
        (∀ W ∈ restrictParts Pl S, ∀ W' ∈ restrictParts Pl S, W ≠ W' → Disjoint W W') := by
  classical
  obtain ⟨n₀, hn₀⟩ := exists_kDeltaPartition_dense (δ := δ) hε0 hε1 hk
  have hk0 : 0 < k := by omega
  refine ⟨n₀, ?_⟩
  intro V _ E S hcard hES hdeg
  obtain ⟨P, hP, hPS⟩ := hn₀ E S hcard hES hdeg
  have hres : restrictParts P S = P := by
    ext W
    rw [mem_restrictParts]
    exact ⟨fun hw => hw.1, fun hw => ⟨hw, hPS W hw⟩⟩
  refine ⟨P, (S.card + k - 1) / k, ?_, ?_, partSeq_of_isKDeltaPartition (δ := δ) (ε := ε) hP,
    ?_, ?_⟩
  · exact Nat.div_le_div_right (by omega)
  · calc (S.card + k - 1) / k ≤ (S.card + k) / k := Nat.div_le_div_right (by omega)
      _ = S.card / k + 1 := Nat.add_div_right _ hk0
  · intro W hW
    rw [hres] at hW
    exact hP.1.size_upper W hW
  · intro W hW W' hW' hne
    rw [hres] at hW hW'
    exact hP.1.pairwise_disjoint W hW W' hW' hne

end BKLO
