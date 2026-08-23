/-
# BKLO Lemma 7.2 for `r = 2`: the `ρ`-random sparse subgraph.

This file discharges the hypothesis `BKLO.Lemma72K3'` of the assembly of Lemma 10.12: given an
equitable `k`-partition `P` of `S` and graphs `G`, `Hg` on `S`, there is a subgraph `R ⊆ G` with,
for every part `W ∈ P`,

* `d_R(x, W) ≤ ρ d_G(x, W) + γ|W|`;
* `d_R({x,y}, W) ≤ ρ² d_G({x,y}, W) + γ|W|` for `x ≠ y`;
* `d_{Hg}(y, N_R(x, W)) ≥ ρ d_{Hg}(y, N_G(x, W)) - γ|S|`.

The proof is the paper's: `R` is the `ρ`-random subgraph of `G`, each of the three quantities is a
sum of independent indicators of pairwise disjoint *blocks* of edges (one edge for a degree, two
edges for a codegree), the Chernoff–Hoeffding bounds of `BKLO/FiniteBernoulli.lean` bound the
probability that any one of them deviates by more than `γ`-times the relevant size, and a union
bound over the `O(kn²)` events leaves a positive probability of success.

The main results are

* `BKLO.lemma72K3'_holds : Lemma72K3'`;
* `BKLO.not_lemma72K3 : ¬ Lemma72K3` — the uncorrected transcription of Lemma 7.2 is false;
* `BKLO.lemma1012K3'_of_three_inputs`, `BKLO.paperIII_ax2_dense_of_four_inputs` — Lemma 10.12 and
  the AX2 half of Paper III with the Lemma 7.2 hypothesis discharged.

Everything here is `sorry`-free.
-/
import BKLO.Section1012Defs
import BKLO.FiniteBernoulli

open Finset BKLO.Bern

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### Generalities -/

theorem sum_union_le_real {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have h2 : 0 ≤ ∑ x ∈ s ∩ t, f x := Finset.sum_nonneg fun x _ => hf x
  linarith only [h, h2]

theorem sum_biUnion_le_real {ι α : Type*} [DecidableEq α] (s : Finset ι) (t : ι → Finset α)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) : ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (sum_union_le_real _ _ f hf).trans (by linarith)

/-- A crude cubic lower bound for the exponential, enough to beat any polynomial. -/
theorem cube_le_exp {u : ℝ} (hu : 0 ≤ u) : u ^ 3 / 27 ≤ Real.exp u := by
  have h1 : (0:ℝ) ≤ u / 3 := by linarith only [hu]
  have h2 : u / 3 ≤ Real.exp (u / 3) := by
    have := Real.add_one_le_exp (u / 3)
    linarith only [this]
  have h3 : (u / 3) ^ 3 ≤ Real.exp (u / 3) ^ 3 := by
    exact pow_le_pow_left₀ h1 h2 3
  have h4 : Real.exp (u / 3) ^ 3 = Real.exp u := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc u ^ 3 / 27 = (u / 3) ^ 3 := by ring
    _ ≤ Real.exp (u / 3) ^ 3 := h3
    _ = Real.exp u := h4

/-- If `E` lives on `S` then a vertex outside `S` has no `E`-neighbours. -/
theorem nbhdIn_eq_empty_of_notMem {E : Finset (Sym2 V)} {S : Finset V} (hE : E ⊆ cliqueEdges S)
    {x : V} (hx : x ∉ S) (W : Finset V) : nbhdIn E x W = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
  have hmem := (mem_nbhdIn.1 hz).2
  have := (mem_cliqueEdgesV.1 (hE hmem)).1 x (by simp)
  exact hx this

theorem degTo_empty (E : Finset (Sym2 V)) (x : V) : degTo E x ∅ = 0 := by
  simp [degTo, nbhdIn]

/-! ### The edge blocks -/

/-- The one-edge block `{xz}`. -/
def blk1 (x : V) : V → Finset (Sym2 V) := fun z => {s(x, z)}

/-- The two-edge block `{xz, yz}`. -/
def blk2 (x y : V) : V → Finset (Sym2 V) := fun z => {s(x, z), s(y, z)}

theorem blk1_subset_of_mem_nbhd {G : Finset (Sym2 V)} {x : V} {W : Finset V} :
    ∀ z ∈ nbhdIn G x W, blk1 x z ⊆ G := by
  intro z hz
  simp only [blk1, Finset.singleton_subset_iff]
  exact (mem_nbhdIn.1 hz).2

omit [DecidableEq V] in
theorem blk1_disj (x : V) : ∀ z z' : V, z ≠ z' → Disjoint (blk1 x z) (blk1 x z') := by
  intro z z' hne
  simp only [blk1, Finset.disjoint_singleton, ne_eq, Sym2.eq_iff]
  rintro (⟨-, h⟩ | ⟨h1, h2⟩)
  · exact hne h
  · exact hne (h2.trans h1)

theorem blk2_card {x y : V} (hxy : x ≠ y) (z : V) : (blk2 x y z).card = 2 := by
  have hnm : s(x, z) ∉ ({s(y, z)} : Finset (Sym2 V)) := by
    simp only [Finset.mem_singleton, Sym2.eq_iff]
    rintro (⟨h, -⟩ | ⟨h1, h2⟩)
    · exact hxy h
    · exact hxy (h1.trans h2)
  simp only [blk2]
  rw [Finset.card_insert_of_notMem hnm, Finset.card_singleton]

theorem blk2_disj {x y : V} (hxy : x ≠ y) {z z' : V} (hzx : z ≠ x) (hzy : z ≠ y) (hz'x : z' ≠ x)
    (hz'y : z' ≠ y) (hne : z ≠ z') : Disjoint (blk2 x y z) (blk2 x y z') := by
  rw [Finset.disjoint_left]
  intro e he he'
  simp only [blk2, Finset.mem_insert, Finset.mem_singleton] at he he'
  rcases he with rfl | rfl <;> rcases he' with h | h <;>
      rw [Sym2.eq_iff] at h <;> rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst_vars <;> simp_all

/-- The index set of the codegree blocks of the pair `x, y` inside `W`. -/
def codIdx (G : Finset (Sym2 V)) (x y : V) (W : Finset V) : Finset V :=
  ((nbhdIn G x W ∩ nbhdIn G y W).erase x).erase y

theorem mem_codIdx {G : Finset (Sym2 V)} {x y z : V} {W : Finset V} :
    z ∈ codIdx G x y W ↔ z ≠ y ∧ z ≠ x ∧ z ∈ W ∧ s(x, z) ∈ G ∧ s(y, z) ∈ G := by
  simp only [codIdx, Finset.mem_erase, Finset.mem_inter, mem_nbhdIn]
  tauto

theorem codIdx_subset {G : Finset (Sym2 V)} (x y : V) (W : Finset V) : codIdx G x y W ⊆ W :=
  fun _ hz => (mem_codIdx.1 hz).2.2.1

theorem blk2_subset_of_mem_codIdx {G : Finset (Sym2 V)} {x y : V} {W : Finset V} :
    ∀ z ∈ codIdx G x y W, blk2 x y z ⊆ G := by
  intro z hz
  rw [mem_codIdx] at hz
  simp only [blk2, Finset.insert_subset_iff, Finset.singleton_subset_iff]
  exact ⟨hz.2.2.2.1, hz.2.2.2.2⟩

/-! ### The three statistics as block counts -/

theorem blockCount_blk1 {A G : Finset (Sym2 V)} (hA : A ⊆ G) (x : V) (W : Finset V) :
    blockCount (nbhdIn G x W) (blk1 x) A = degTo A x W := by
  unfold blockCount degTo
  congr 1
  ext z
  simp only [Finset.mem_filter, mem_nbhdIn, blk1, Finset.singleton_subset_iff]
  constructor
  · rintro ⟨⟨hz, _⟩, hmem⟩; exact ⟨hz, hmem⟩
  · rintro ⟨hz, hmem⟩; exact ⟨⟨hz, hA hmem⟩, hmem⟩

omit [DecidableEq V] in
theorem blockMean_blk1 (ρ : ℝ) (K : Finset V) (x : V) :
    blockMean ρ K (blk1 x) = ρ * (K.card : ℝ) := by
  unfold blockMean blk1
  simp [mul_comm]

theorem blockCount_blk1_hg {A G Hg : Finset (Sym2 V)} (hA : A ⊆ G) (x y : V) (W : Finset V) :
    blockCount (nbhdIn Hg y (nbhdIn G x W)) (blk1 x) A = degTo Hg y (nbhdIn A x W) := by
  unfold blockCount degTo
  congr 1
  ext z
  simp only [Finset.mem_filter, mem_nbhdIn, blk1, Finset.singleton_subset_iff]
  constructor
  · rintro ⟨⟨⟨hz, _⟩, hHg⟩, hmem⟩; exact ⟨⟨hz, hmem⟩, hHg⟩
  · rintro ⟨⟨hz, hmem⟩, hHg⟩; exact ⟨⟨⟨hz, hA hmem⟩, hHg⟩, hmem⟩

theorem codegTo_le_blockCount {A G : Finset (Sym2 V)} (hA : A ⊆ G) (x y : V) (W : Finset V) :
    codegTo A x y W ≤ blockCount (codIdx G x y W) (blk2 x y) A + 2 := by
  set T := nbhdIn A x W ∩ nbhdIn A y W with hT
  have hsub : (T.erase x).erase y ⊆ (codIdx G x y W).filter (fun z => blk2 x y z ⊆ A) := by
    intro z hz
    simp only [Finset.mem_erase] at hz
    obtain ⟨hzy, hzx, hzT⟩ := hz
    rw [hT, Finset.mem_inter, mem_nbhdIn, mem_nbhdIn] at hzT
    refine Finset.mem_filter.2 ⟨mem_codIdx.2 ⟨hzy, hzx, hzT.1.1, hA hzT.1.2, hA hzT.2.2⟩, ?_⟩
    simp only [blk2, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hzT.1.2, hzT.2.2⟩
  have h1 : ((T.erase x).erase y).card ≤ blockCount (codIdx G x y W) (blk2 x y) A :=
    Finset.card_le_card hsub
  have h2 : T.card - 1 ≤ (T.erase x).card := Finset.pred_card_le_card_erase
  have h3 : (T.erase x).card - 1 ≤ ((T.erase x).erase y).card := Finset.pred_card_le_card_erase
  have h4 : codegTo A x y W = T.card := rfl
  omega

theorem blockMean_blk2 {ρ : ℝ} {G : Finset (Sym2 V)} {x y : V} (hxy : x ≠ y)
    (W : Finset V) :
    blockMean ρ (codIdx G x y W) (blk2 x y) ≤ ρ ^ 2 * (codegTo G x y W : ℝ) := by
  have hcard : ∀ z ∈ codIdx G x y W, ρ ^ (blk2 x y z).card = ρ ^ 2 := by
    intro z _; rw [blk2_card hxy]
  rw [blockMean, Finset.sum_congr rfl hcard, Finset.sum_const, nsmul_eq_mul]
  have hsub : codIdx G x y W ⊆ nbhdIn G x W ∩ nbhdIn G y W :=
    (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hle : ((codIdx G x y W).card : ℝ) ≤ (codegTo G x y W : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  nlinarith [sq_nonneg ρ]

/-! ### The three bad events -/

/-- The degree upper-tail event has small weight. -/
theorem sum_badA_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (G : Finset (Sym2 V)) (x : V)
    (W : Finset V) {t m : ℝ} (hm0 : 0 < m) (hW : (W.card : ℝ) ≤ m) (ht : 0 < t)
    {Bad : Finset (Finset (Sym2 V))} (hsub : Bad ⊆ G.powerset)
    (hbad : ∀ A ∈ Bad, ρ * (degTo G x W : ℝ) + t < (degTo A x W : ℝ)) :
    ∑ A ∈ Bad, wt ρ G A ≤ Real.exp (-(t ^ 2 / (4 * m))) := by
  refine tail_upper ρ hρ0 hρ1 (K := nbhdIn G x W) (B := blk1 x)
    (fun z hz => blk1_subset_of_mem_nbhd z hz) (fun z _ z' _ hne => blk1_disj x z z' hne)
    hm0 ?_ ht hsub ?_
  · exact le_trans (by exact_mod_cast Finset.card_le_card (nbhdIn_subset G x W)) hW
  · intro A hA
    have hAG : A ⊆ G := Finset.mem_powerset.1 (hsub hA)
    rw [blockMean_blk1, blockCount_blk1 hAG]
    have : ρ * ((nbhdIn G x W).card : ℝ) = ρ * (degTo G x W : ℝ) := rfl
    rw [this]
    exact (hbad A hA).le

/-- The codegree upper-tail event has small weight. -/
theorem sum_badB_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (G : Finset (Sym2 V)) {x y : V}
    (hxy : x ≠ y) (W : Finset V) {t m : ℝ} (hm0 : 0 < m) (hW : (W.card : ℝ) ≤ m) (ht : 0 < t)
    {Bad : Finset (Finset (Sym2 V))} (hsub : Bad ⊆ G.powerset)
    (hbad : ∀ A ∈ Bad, ρ ^ 2 * (codegTo G x y W : ℝ) + t + 2 < (codegTo A x y W : ℝ)) :
    ∑ A ∈ Bad, wt ρ G A ≤ Real.exp (-(t ^ 2 / (4 * m))) := by
  refine tail_upper ρ hρ0 hρ1 (K := codIdx G x y W) (B := blk2 x y)
    (fun z hz => blk2_subset_of_mem_codIdx z hz) ?_ hm0 ?_ ht hsub ?_
  · intro z hz z' hz' hne
    rw [mem_codIdx] at hz hz'
    exact blk2_disj hxy hz.2.1 hz.1 hz'.2.1 hz'.1 hne
  · exact le_trans (by exact_mod_cast Finset.card_le_card (codIdx_subset x y W)) hW
  · intro A hA
    have hAG : A ⊆ G := Finset.mem_powerset.1 (hsub hA)
    have h1 := codegTo_le_blockCount hAG x y W
    have h1' : (codegTo A x y W : ℝ) ≤ (blockCount (codIdx G x y W) (blk2 x y) A : ℝ) + 2 := by
      exact_mod_cast h1
    have h2 := blockMean_blk2 (ρ := ρ) (G := G) hxy W
    have h3 := hbad A hA
    linarith only [h1', h2, h3]

/-- The neighbourhood lower-tail event has small weight. -/
theorem sum_badC_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (G Hg : Finset (Sym2 V)) (x y : V)
    (W : Finset V) {t m : ℝ} (hm0 : 0 < m) (hW : (W.card : ℝ) ≤ m) (ht : 0 < t)
    {Bad : Finset (Finset (Sym2 V))} (hsub : Bad ⊆ G.powerset)
    (hbad : ∀ A ∈ Bad, (degTo Hg y (nbhdIn A x W) : ℝ)
      < ρ * (degTo Hg y (nbhdIn G x W) : ℝ) - t) :
    ∑ A ∈ Bad, wt ρ G A ≤ Real.exp (-(t ^ 2 / (4 * m))) := by
  refine tail_lower ρ hρ0 hρ1 (K := nbhdIn Hg y (nbhdIn G x W)) (B := blk1 x)
    (fun z hz => blk1_subset_of_mem_nbhd z (nbhdIn_subset _ _ _ hz))
    (fun z _ z' _ hne => blk1_disj x z z' hne) hm0 ?_ ht hsub ?_
  · refine le_trans ?_ hW
    have h1 : nbhdIn Hg y (nbhdIn G x W) ⊆ W :=
      (nbhdIn_subset _ _ _).trans (nbhdIn_subset _ _ _)
    exact_mod_cast Finset.card_le_card h1
  · intro A hA
    have hAG : A ⊆ G := Finset.mem_powerset.1 (hsub hA)
    rw [blockMean_blk1, blockCount_blk1_hg hAG]
    have hmean : ρ * ((nbhdIn Hg y (nbhdIn G x W)).card : ℝ)
        = ρ * (degTo Hg y (nbhdIn G x W) : ℝ) := rfl
    rw [hmean]
    exact (hbad A hA).le


/-! ### The union bound -/

theorem exp_tail_mono {m t0 t : ℝ} (hm : 0 < m) (h0 : 0 < t0) (h : t0 ≤ t) :
    Real.exp (-(t ^ 2 / (4 * m))) ≤ Real.exp (-(t0 ^ 2 / (4 * m))) := by
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  gcongr

theorem poly_lt_exp {c : ℝ} (hc : 0 < c) {k n : ℕ} (hk : 0 < k)
    (hn : 5184 * (k:ℝ) / c ^ 6 < (n:ℝ)) :
    3 * (n:ℝ) ^ 2 * (k:ℝ) * Real.exp (-(c ^ 2 * (n:ℝ) / 4)) < 1 := by
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hnR : (0:ℝ) < (n:ℝ) := lt_trans (by positivity) hn
  set u : ℝ := c ^ 2 * (n:ℝ) / 4 with hu
  have hu0 : 0 ≤ u := by positivity
  have hexp := cube_le_exp hu0
  have hcube : u ^ 3 / 27 = c ^ 6 * (n:ℝ) ^ 3 / 1728 := by rw [hu]; ring
  have h1 : 5184 * (k:ℝ) < c ^ 6 * (n:ℝ) := by
    rw [div_lt_iff₀ (by positivity)] at hn
    linarith only [hn]
  have h2 : (n:ℝ) ^ 2 * (5184 * (k:ℝ)) < (n:ℝ) ^ 2 * (c ^ 6 * (n:ℝ)) :=
    mul_lt_mul_of_pos_left h1 (by positivity)
  have hbig : 3 * (n:ℝ) ^ 2 * (k:ℝ) < c ^ 6 * (n:ℝ) ^ 3 / 1728 := by linarith only [h2]
  have hlt : 3 * (n:ℝ) ^ 2 * (k:ℝ) < Real.exp u := by rw [hcube] at hexp; linarith only [hexp, hbig]
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos u)]
  exact hlt

/-! ### BKLO Lemma 7.2 for `r = 2` -/

set_option maxHeartbeats 1600000 in
/-- **BKLO Lemma 7.2, p. 13, for `r = 2`** (in the corrected form `BKLO.Lemma72K3'`): the
`ρ`-random subgraph of `G` has the required degree, codegree and neighbourhood statistics. -/
theorem lemma72K3'_holds : Lemma72K3' := by
  classical
  intro k γ ρ hk0 hγ hρ0 hρ1
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk0
  set c : ℝ := γ / (4 * (k:ℝ)) with hcdef
  have hc0 : 0 < c := by positivity
  refine ⟨⌈2 * (k:ℝ) + 8 * (k:ℝ) / γ + 5184 * (k:ℝ) / c ^ 6⌉₊ + 1, ?_⟩
  intro V _ G Hg S P hcard hGS hHgS hpart
  set n : ℕ := S.card with hndef
  -- the consequences of `n ≥ n₀`
  have hnbig : 2 * (k:ℝ) + 8 * (k:ℝ) / γ + 5184 * (k:ℝ) / c ^ 6 < (n:ℝ) := by
    have h1 : ⌈2 * (k:ℝ) + 8 * (k:ℝ) / γ + 5184 * (k:ℝ) / c ^ 6⌉₊ < n := by omega
    have h2 : ((⌈2 * (k:ℝ) + 8 * (k:ℝ) / γ + 5184 * (k:ℝ) / c ^ 6⌉₊ : ℕ) : ℝ) < (n:ℝ) := by
      exact_mod_cast h1
    exact lt_of_le_of_lt (Nat.le_ceil _) h2
  have hpos1 : (0:ℝ) < 8 * (k:ℝ) / γ := by positivity
  have hpos2 : (0:ℝ) < 5184 * (k:ℝ) / c ^ 6 := by positivity
  have h2k : 2 * (k:ℝ) < (n:ℝ) := by linarith only [hnbig, hpos1, hpos2]
  have h8k : 8 * (k:ℝ) / γ < (n:ℝ) := by linarith only [hnbig, hpos2]
  have h5184 : 5184 * (k:ℝ) / c ^ 6 < (n:ℝ) := by linarith only [hnbig, hpos1]
  have hn0 : (0:ℝ) < (n:ℝ) := by linarith only [h2k]
  have hnpos : 0 < n := by exact_mod_cast hn0
  -- `c n ≥ 2`
  have hcn2 : 2 ≤ c * (n:ℝ) := by
    rw [hcdef]
    rw [div_lt_iff₀ hγ] at h8k
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith only [h8k]
  -- the sizes of the parts
  have hWS : ∀ W ∈ P, W ⊆ S := fun W hW => hpart.subset_of_mem hW
  have hWn : ∀ W ∈ P, (W.card : ℝ) ≤ (n:ℝ) := by
    intro W hW
    exact_mod_cast Finset.card_le_card (hWS W hW)
  have hWlow : ∀ W ∈ P, (n:ℝ) / (k:ℝ) - 1 ≤ (W.card : ℝ) := by
    intro W hW
    have h1 : (n / k : ℕ) ≤ W.card := hpart.size_lower W hW
    have h2 : ((n / k : ℕ) : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast h1
    have h3 : (n : ℝ) < ((n / k : ℕ) : ℝ) * (k : ℝ) + (k : ℝ) := by
      have := Nat.lt_div_mul_add hk0 (a := n)
      exact_mod_cast this
    rw [sub_le_iff_le_add, div_le_iff₀ hkR]
    nlinarith only [h2, h3]
  have htA : ∀ W ∈ P, 2 * (c * (n:ℝ)) ≤ γ * (W.card : ℝ) := by
    intro W hW
    have h1 : γ * ((n:ℝ) / (k:ℝ) - 1) ≤ γ * (W.card : ℝ) :=
      mul_le_mul_of_nonneg_left (hWlow W hW) hγ.le
    have h2 : (n:ℝ) / (k:ℝ) - 1 - (n:ℝ) / (2 * (k:ℝ)) = ((n:ℝ) - 2 * (k:ℝ)) / (2 * (k:ℝ)) := by
      field_simp
      ring
    have h3 : (0:ℝ) ≤ ((n:ℝ) - 2 * (k:ℝ)) / (2 * (k:ℝ)) := by
      apply div_nonneg (by linarith) (by positivity)
    have h4 : (n:ℝ) / (2 * (k:ℝ)) ≤ (n:ℝ) / (k:ℝ) - 1 := by linarith only [h2, h3]
    have h5 : 2 * (c * (n:ℝ)) = γ * ((n:ℝ) / (2 * (k:ℝ))) := by
      rw [hcdef]; field_simp; ring
    have h6 : γ * ((n:ℝ) / (2 * (k:ℝ))) ≤ γ * ((n:ℝ) / (k:ℝ) - 1) :=
      mul_le_mul_of_nonneg_left h4 hγ.le
    linarith only [h1, h5, h6]
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk0
  have hργ : c ≤ γ := by
    rw [hcdef, div_le_iff₀ (by positivity)]
    nlinarith only [hγ, hk1]
  -- the failure probability of a single event
  set Q : ℝ := Real.exp (-((c * (n:ℝ)) ^ 2 / (4 * (n:ℝ)))) with hQdef
  have hQ0 : 0 < Q := Real.exp_pos _
  -- the good samples
  set Good : Finset (Sym2 V) → Prop := fun A =>
    ∀ x ∈ S, ∀ y ∈ S, ∀ W ∈ P,
      ((degTo A x W : ℝ) ≤ ρ * (degTo G x W : ℝ) + γ * (W.card : ℝ))
      ∧ (x ≠ y → (codegTo A x y W : ℝ) ≤ ρ ^ 2 * (codegTo G x y W : ℝ) + γ * (W.card : ℝ))
      ∧ (ρ * (degTo Hg y (nbhdIn G x W) : ℝ) - γ * (n : ℝ)
          ≤ (degTo Hg y (nbhdIn A x W) : ℝ)) with hGooddef
  set bad : (V × V) × Finset V → Finset (Finset (Sym2 V)) := fun q =>
    G.powerset.filter (fun A => ¬ (
      ((degTo A q.1.1 q.2 : ℝ) ≤ ρ * (degTo G q.1.1 q.2 : ℝ) + γ * (q.2.card : ℝ))
      ∧ (q.1.1 ≠ q.1.2 → (codegTo A q.1.1 q.1.2 q.2 : ℝ)
          ≤ ρ ^ 2 * (codegTo G q.1.1 q.1.2 q.2 : ℝ) + γ * (q.2.card : ℝ))
      ∧ (ρ * (degTo Hg q.1.2 (nbhdIn G q.1.1 q.2) : ℝ) - γ * (n : ℝ)
          ≤ (degTo Hg q.1.2 (nbhdIn A q.1.1 q.2) : ℝ)))) with hbaddef
  set Bad : Finset (Finset (Sym2 V)) := G.powerset.filter (fun A => ¬ Good A) with hBaddef
  -- every bad sample is bad for some triple
  have hBadsub : Bad ⊆ ((S ×ˢ S) ×ˢ P).biUnion bad := by
    intro A hA
    rw [hBaddef, Finset.mem_filter] at hA
    obtain ⟨hAmem, hAbad⟩ := hA
    rw [hGooddef] at hAbad
    simp only [not_forall] at hAbad
    obtain ⟨x, hx, y, hy, W, hW, hfail⟩ := hAbad
    refine Finset.mem_biUnion.2 ⟨((x, y), W), ?_, ?_⟩
    · exact Finset.mem_product.2 ⟨Finset.mem_product.2 ⟨hx, hy⟩, hW⟩
    · exact Finset.mem_filter.2 ⟨hAmem, hfail⟩
  -- each triple fails with probability at most `3Q`
  have hper : ∀ q ∈ (S ×ˢ S) ×ˢ P, ∑ A ∈ bad q, wt ρ G A ≤ 3 * Q := by
    intro q hq
    obtain ⟨⟨x, y⟩, W⟩ := q
    obtain ⟨hq1, hW⟩ := Finset.mem_product.1 hq
    have hWmem : W ∈ P := hW
    have hWcard : (W.card : ℝ) ≤ (n:ℝ) := hWn W hWmem
    have htApos : 0 < γ * (W.card : ℝ) := by
      have := htA W hWmem
      nlinarith [mul_pos hc0 hn0]
    set bA : Finset (Finset (Sym2 V)) := G.powerset.filter
      (fun A => ¬ ((degTo A x W : ℝ) ≤ ρ * (degTo G x W : ℝ) + γ * (W.card : ℝ))) with hbA
    set bB : Finset (Finset (Sym2 V)) := G.powerset.filter
      (fun A => ¬ (x ≠ y → (codegTo A x y W : ℝ)
        ≤ ρ ^ 2 * (codegTo G x y W : ℝ) + γ * (W.card : ℝ))) with hbB
    set bC : Finset (Finset (Sym2 V)) := G.powerset.filter
      (fun A => ¬ (ρ * (degTo Hg y (nbhdIn G x W) : ℝ) - γ * (n : ℝ)
        ≤ (degTo Hg y (nbhdIn A x W) : ℝ))) with hbC
    have hsplit : bad ((x, y), W) ⊆ bA ∪ bB ∪ bC := by
      intro A hA
      simp only [hbaddef, Finset.mem_filter] at hA
      obtain ⟨hAmem, hAbad⟩ := hA
      by_cases h1 : (degTo A x W : ℝ) ≤ ρ * (degTo G x W : ℝ) + γ * (W.card : ℝ)
      · by_cases h2 : x ≠ y → (codegTo A x y W : ℝ)
            ≤ ρ ^ 2 * (codegTo G x y W : ℝ) + γ * (W.card : ℝ)
        · have h3 : ¬ (ρ * (degTo Hg y (nbhdIn G x W) : ℝ) - γ * (n : ℝ)
              ≤ (degTo Hg y (nbhdIn A x W) : ℝ)) := fun h => hAbad ⟨h1, h2, h⟩
          exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hAmem, h3⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.2 ⟨hAmem, h2⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨hAmem, h1⟩))
    have hnn : ∀ A : Finset (Sym2 V), 0 ≤ wt ρ G A := fun A => wt_nonneg hρ0.le hρ1.le G A
    have hA1 : ∑ A ∈ bA, wt ρ G A ≤ Q := by
      refine le_trans (sum_badA_le hρ0.le hρ1.le G x W hn0 hWcard htApos
        (Finset.filter_subset _ _) ?_) ?_
      · intro A hA
        have := (Finset.mem_filter.1 hA).2
        push_neg at this
        exact this
      · rw [hQdef]
        exact exp_tail_mono hn0 (by positivity) (by linarith [htA W hWmem])
    have hC1 : ∑ A ∈ bC, wt ρ G A ≤ Q := by
      refine le_trans (sum_badC_le hρ0.le hρ1.le G Hg x y W hn0 hWcard
        (t := γ * (n:ℝ)) (by positivity) (Finset.filter_subset _ _) ?_) ?_
      · intro A hA
        have := (Finset.mem_filter.1 hA).2
        push_neg at this
        linarith only [this]
      · rw [hQdef]
        refine exp_tail_mono hn0 (by positivity) ?_
        nlinarith only [hργ]
    have hB1 : ∑ A ∈ bB, wt ρ G A ≤ Q := by
      rcases eq_or_ne x y with rfl | hxy
      · have hempty : bB = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun A hA => ?_
          have h := (Finset.mem_filter.1 hA).2
          exact h (fun hne => absurd rfl hne)
        rw [hempty, Finset.sum_empty]
        exact hQ0.le
      · refine le_trans (sum_badB_le hρ0.le hρ1.le G hxy W hn0 hWcard
          (t := γ * (W.card : ℝ) - 2) (by linarith [htA W hWmem]) (Finset.filter_subset _ _) ?_) ?_
        · intro A hA
          have h := (Finset.mem_filter.1 hA).2
          push_neg at h
          have := h.2
          linarith only [this]
        · rw [hQdef]
          refine exp_tail_mono hn0 (by positivity) ?_
          linarith [htA W hWmem]
    calc ∑ A ∈ bad ((x, y), W), wt ρ G A ≤ ∑ A ∈ bA ∪ bB ∪ bC, wt ρ G A :=
          Finset.sum_le_sum_of_subset_of_nonneg hsplit (fun A _ _ => hnn A)
      _ ≤ (∑ A ∈ bA ∪ bB, wt ρ G A) + ∑ A ∈ bC, wt ρ G A := sum_union_le_real _ _ _ hnn
      _ ≤ ((∑ A ∈ bA, wt ρ G A) + ∑ A ∈ bB, wt ρ G A) + ∑ A ∈ bC, wt ρ G A := by
          have := sum_union_le_real bA bB (wt ρ G) hnn
          linarith only [this]
      _ ≤ 3 * Q := by linarith only [hA1, hC1, hB1]
  -- the union bound
  have htotal : ∑ A ∈ Bad, wt ρ G A < 1 := by
    have hnn : ∀ A : Finset (Sym2 V), 0 ≤ wt ρ G A := fun A => wt_nonneg hρ0.le hρ1.le G A
    have h1 : ∑ A ∈ Bad, wt ρ G A ≤ ∑ A ∈ ((S ×ˢ S) ×ˢ P).biUnion bad, wt ρ G A :=
      Finset.sum_le_sum_of_subset_of_nonneg hBadsub (fun A _ _ => hnn A)
    have h2 : ∑ A ∈ ((S ×ˢ S) ×ˢ P).biUnion bad, wt ρ G A
        ≤ ∑ q ∈ (S ×ˢ S) ×ˢ P, ∑ A ∈ bad q, wt ρ G A :=
      sum_biUnion_le_real _ _ _ hnn
    have h3 : ∑ q ∈ (S ×ˢ S) ×ˢ P, ∑ A ∈ bad q, wt ρ G A
        ≤ ∑ _q ∈ (S ×ˢ S) ×ˢ P, 3 * Q := Finset.sum_le_sum hper
    have h4 : ∑ _q ∈ (S ×ˢ S) ×ˢ P, (3 * Q) = ((n * n * k : ℕ) : ℝ) * (3 * Q) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 2
      rw [Finset.card_product, Finset.card_product, hpart.card_parts, ← hndef]
    have h5 : ((n * n * k : ℕ) : ℝ) * (3 * Q) = 3 * (n:ℝ) ^ 2 * (k:ℝ) * Q := by
      push_cast
      ring
    have h6 : Q = Real.exp (-(c ^ 2 * (n:ℝ) / 4)) := by
      rw [hQdef]
      congr 1
      field_simp
    have h7 : 3 * (n:ℝ) ^ 2 * (k:ℝ) * Q < 1 := by
      rw [h6]
      exact poly_lt_exp hc0 hk0 h5184
    linarith only [h1, h2, h3, h4, h5, h7]
  -- the probabilistic method
  obtain ⟨R, hRG, hRbad⟩ := exists_of_sum_lt_one (ρ := ρ) G (Finset.filter_subset _ _) htotal
  have hGoodR : Good R := by
    by_contra hcon
    exact hRbad (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hRG, hcon⟩)
  rw [hGooddef] at hGoodR
  -- from `S`-vertices to all vertices
  have hnbA : ∀ x : V, x ∉ S → ∀ W : Finset V, nbhdIn R x W = ∅ := fun x hx W =>
    nbhdIn_eq_empty_of_notMem (hRG.trans hGS) hx W
  have hnbG : ∀ x : V, x ∉ S → ∀ W : Finset V, nbhdIn G x W = ∅ := fun x hx W =>
    nbhdIn_eq_empty_of_notMem hGS hx W
  have hnbHg : ∀ y : V, y ∉ S → ∀ T : Finset V, nbhdIn Hg y T = ∅ := fun y hy T =>
    nbhdIn_eq_empty_of_notMem hHgS hy T
  refine ⟨R, hRG, ?_, ?_, ?_⟩
  · intro x W hW
    by_cases hx : x ∈ S
    · exact (hGoodR x hx x hx W hW).1
    · have h0 : degTo R x W = 0 := by
        unfold degTo
        rw [hnbA x hx W]
        exact Finset.card_empty
      rw [h0]
      have : (0:ℝ) ≤ ρ * (degTo G x W : ℝ) := by positivity
      have : (0:ℝ) ≤ γ * (W.card : ℝ) := by positivity
      push_cast
      linarith
  · intro x y W hxy hW
    by_cases hx : x ∈ S
    · by_cases hy : y ∈ S
      · exact (hGoodR x hx y hy W hW).2.1 hxy
      · have h0 : codegTo R x y W = 0 := by
          unfold codegTo
          rw [hnbA y hy W, Finset.inter_empty]
          exact Finset.card_empty
        rw [h0]
        have h1 : (0:ℝ) ≤ ρ ^ 2 * (codegTo G x y W : ℝ) := by positivity
        have h2 : (0:ℝ) ≤ γ * (W.card : ℝ) := by positivity
        push_cast
        linarith only [h1, h2]
    · have h0 : codegTo R x y W = 0 := by
        unfold codegTo
        rw [hnbA x hx W, Finset.empty_inter]
        exact Finset.card_empty
      rw [h0]
      have h1 : (0:ℝ) ≤ ρ ^ 2 * (codegTo G x y W : ℝ) := by positivity
      have h2 : (0:ℝ) ≤ γ * (W.card : ℝ) := by positivity
      push_cast
      linarith only [h1, h2]
  · intro x y W hW
    by_cases hx : x ∈ S
    · by_cases hy : y ∈ S
      · exact (hGoodR x hx y hy W hW).2.2
      · have h1 : degTo Hg y (nbhdIn G x W) = 0 := by
          unfold degTo; rw [hnbHg y hy _]; exact Finset.card_empty
        have h2 : degTo Hg y (nbhdIn R x W) = 0 := by
          unfold degTo; rw [hnbHg y hy _]; exact Finset.card_empty
        rw [h1, h2]
        have : (0:ℝ) ≤ γ * (n:ℝ) := by positivity
        push_cast
        linarith only [this]
    · have h1 : degTo Hg y (nbhdIn G x W) = 0 := by
        rw [hnbG x hx W, degTo_empty]
      have h2 : degTo Hg y (nbhdIn R x W) = 0 := by
        rw [hnbA x hx W, degTo_empty]
      rw [h1, h2]
      have : (0:ℝ) ≤ γ * (n:ℝ) := by positivity
      push_cast
      linarith only [this]

/-! ### The uncorrected transcription of Lemma 7.2 is false -/

theorem nbhdIn_cliqueEdges {S T : Finset V} {x : V} (hx : x ∈ S) (hT : T ⊆ S) :
    nbhdIn (cliqueEdges S) x T = T.erase x := by
  ext z
  simp only [mem_nbhdIn, Finset.mem_erase, mem_cliqueEdgesV, Sym2.mem_iff,
    Sym2.isDiag_iff_proj_eq]
  constructor
  · rintro ⟨hz, -, hne⟩
    exact ⟨fun h => hne (h ▸ rfl), hz⟩
  · rintro ⟨hne, hz⟩
    refine ⟨hz, ?_, fun h => hne h.symm⟩
    rintro u (rfl | rfl)
    · exact hx
    · exact hT hz

/-- `{S}` is an equitable partition of `S` into `1` part. -/
theorem equitable_singleton (S : Finset V) : IsEquitablePartition 1 {S} S where
  card_parts := Finset.card_singleton _
  pairwise_disjoint := by
    intro W hW W' hW' hne
    rw [Finset.mem_singleton] at hW hW'
    exact absurd (hW.trans hW'.symm) hne
  cover := by simp
  size_lower := by
    intro W hW; rw [Finset.mem_singleton] at hW; simp [hW]
  size_upper := by
    intro W hW; rw [Finset.mem_singleton] at hW; simp [hW]

/-- **The transcription `BKLO.Lemma72K3` of Lemma 7.2 is false.**

With `k = 1`, `ρ = 1/2`, `γ = 1/100`, take for `G` and for `Hg` the complete graph on a set `S` of
`n ≥ 5` vertices, partitioned into the single part `W = S`.  The codegree clause applied to
`x = y = 0` says `d_R(0, S) ≤ (1/4)(n-1) + n/100`, while the neighbourhood clause applied to
`x = 0`, `y = 1` says `d_R(0, S) ≥ (1/2)(n-2) - n/100`; the two are incompatible for `n ≥ 5`.

The point is that the paper's estimate concerns a *set* `{x, y}` of at most two vertices, so its
codegree case is about `x ≠ y`; this is restored in `BKLO.Lemma72K3'`. -/
theorem not_lemma72K3 : ¬ Lemma72K3 := by
  intro h
  obtain ⟨n₀, H⟩ := h 1 (1/100) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  set N : ℕ := max n₀ 5 with hNdef
  have hN5 : 5 ≤ N := le_max_right _ _
  have hNn₀ : n₀ ≤ N := le_max_left _ _
  set S : Finset ℕ := Finset.range N with hSdef
  have hScard : S.card = N := Finset.card_range N
  have hcard : n₀ ≤ S.card := by rw [hScard]; exact hNn₀
  obtain ⟨R, hRG, h1, h2, h3⟩ :=
    H (cliqueEdges S) (cliqueEdges S) S {S} hcard (equitable_singleton S)
  have hSmem : S ∈ ({S} : Finset (Finset ℕ)) := Finset.mem_singleton_self _
  have hx0 : (0:ℕ) ∈ S := by rw [hSdef, Finset.mem_range]; omega
  have hx1 : (1:ℕ) ∈ S := by rw [hSdef, Finset.mem_range]; omega
  have hnb0 : nbhdIn (cliqueEdges S) 0 S = S.erase 0 :=
    nbhdIn_cliqueEdges hx0 (Finset.Subset.refl _)
  have hdeg0 : degTo (cliqueEdges S) 0 S = N - 1 := by
    rw [degTo, hnb0, Finset.card_erase_of_mem hx0, hScard]
  have h1mem : (1:ℕ) ∈ S.erase 0 := Finset.mem_erase.2 ⟨by norm_num, hx1⟩
  have hnb1 : nbhdIn (cliqueEdges S) 1 (S.erase 0) = (S.erase 0).erase 1 :=
    nbhdIn_cliqueEdges hx1 (Finset.erase_subset _ _)
  have hdeg1 : degTo (cliqueEdges S) 1 (nbhdIn (cliqueEdges S) 0 S) = N - 2 := by
    rw [hnb0, degTo, hnb1, Finset.card_erase_of_mem h1mem, Finset.card_erase_of_mem hx0, hScard]
    omega
  have hcod : codegTo R 0 0 S = degTo R 0 S := by rw [codegTo, Finset.inter_self, degTo]
  have hcodG : codegTo (cliqueEdges S) 0 0 S = degTo (cliqueEdges S) 0 S := by
    rw [codegTo, Finset.inter_self, degTo]
  have hb := h2 0 0 S hSmem
  rw [hcod, hcodG, hdeg0, hScard] at hb
  have hc := h3 0 1 S hSmem
  rw [hdeg1, hScard] at hc
  have hle : (degTo (cliqueEdges S) 1 (nbhdIn R 0 S) : ℝ) ≤ (degTo R 0 S : ℝ) := by
    have hcc : degTo (cliqueEdges S) 1 (nbhdIn R 0 S) ≤ degTo R 0 S :=
      Finset.card_le_card (nbhdIn_subset _ _ _)
    exact_mod_cast hcc
  have hNR : (5:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN5
  have hc1 : ((N - 1 : ℕ) : ℝ) = (N:ℝ) - 1 := by
    have h : (1:ℕ) ≤ N := by omega
    push_cast [Nat.cast_sub h]
    ring
  have hc2 : ((N - 2 : ℕ) : ℝ) = (N:ℝ) - 2 := by
    have h : (2:ℕ) ≤ N := by omega
    push_cast [Nat.cast_sub h]
    ring
  rw [hc1] at hb
  rw [hc2] at hc
  linarith

end BKLO
