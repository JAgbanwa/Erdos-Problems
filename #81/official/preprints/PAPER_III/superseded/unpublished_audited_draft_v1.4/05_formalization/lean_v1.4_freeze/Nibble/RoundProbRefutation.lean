/-
# Nibble — REFUTATION of the probabilistic round `NibbleRoundProb`

`Nibble.RoundOracleKernel.NibbleRoundProb` (the "probabilistic half" of one nibble round) is
**false**, and this file proves it: `Nibble.not_nibbleRoundProb`.

The obstruction is purely combinatorial — no probability is involved.  `NibbleRoundProb` asks, for
an `r`-uniform `K` whose degrees all lie in `[L, U]` with `U ≤ 8L`, for a retained set `R' ⊆ K`
whose round matching simultaneously

* leaves all but a `δlow`-fraction of the uncovered vertices with residual degree `≥ (1/2-ε/2)L`,
  and
* leaves at most a `blow`-fraction of the vertices with residual degree `> (1/2+ε)U`.

The degree ceiling clause is relative to the GLOBAL upper scale `U`, while the degree floor clause
is relative to the GLOBAL lower scale `L`; when the degrees genuinely spread over the whole allowed
range `[L, 8L]`, no set of edges can do both.  The witness is the complete bipartite graph
`K_{m, 8m}` (so `r = 2`):

* `m` "hubs" of degree `8m = U`, and `8m` "leaves" of degree `m = L`; the ratio `U = 8L` is exactly
  the one the statement allows, the codegree is `≤ 1 ≤ ecod·L`, and `|V| = 9m`.
* Any round matching `M` has `|M| ≤ m` (each of its edges uses up a distinct hub), so it covers at
  most `m` leaves; an uncovered hub therefore keeps residual degree `≥ 8m - m = 7m > 5m = (1/2+ε)U`
  and is *high*.  Forcing the high set below `blow·|V|` therefore forces almost every hub to be
  covered, i.e. `|M| ≥ m(1 - 9·blow)`.
* But then an uncovered leaf has residual degree `m - |M| ≤ 9·blow·m`, far below
  `(1/2-ε/2)L = (7/16)m`; and there are at least `8m - |M| ≥ 7m` uncovered leaves, which is much
  more than the allowed `δlow·|V| = 9·δlow·m` exceptions.

Taking `δlow = blow = 1/1000` and `ε = 1/8` makes the two requirements contradictory for every
`m ≥ 1`, hence for arbitrarily large degree scales `L = m`; since `NibbleRoundProb` promises
thresholds `ecod, L₀` *before* seeing the hypergraph, this refutes it.

Note that the deterministic consumer `NibbleRoundStep` is NOT refuted by this example: it may prune
the residual (`K' ⊆ residual K R'`) before the degree ceiling is imposed, and a *balanced* pruning
of the hubs down to `5m` costs each leaf only about `(3/8)m` of its `m` edges, leaving it above
`(1/2-ε)L = (3/8)m`.  What the example does show is that the probabilistic input to the round has to
be stated with the pruning already in place (or with the excess-degree mass controlled), rather than
by asking the raw residual to satisfy the global ceiling.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.RoundOracleKernel

open Finset Hypergraph

namespace Nibble

namespace BipRef

/-! ## The complete bipartite witness `K_{m, 8m}` -/

/-- Vertex set: `m` hubs and `8m` leaves. -/
abbrev BV (m : ℕ) : Type := Sum (Fin m) (Fin (8 * m))

/-- The edge joining hub `i` to leaf `j`. -/
def bipEdge {m : ℕ} (i : Fin m) (j : Fin (8 * m)) : Finset (BV m) := {Sum.inl i, Sum.inr j}

/-- The complete bipartite graph `K_{m,8m}`, viewed as a `2`-uniform hypergraph. -/
def bipK (m : ℕ) : Finset (Finset (BV m)) :=
  Finset.image (fun q : Fin m × Fin (8 * m) => bipEdge q.1 q.2) Finset.univ

/-- The hub side. -/
def hubs (m : ℕ) : Finset (BV m) := Finset.univ.image Sum.inl

/-- The leaf side. -/
def leaves (m : ℕ) : Finset (BV m) := Finset.univ.image Sum.inr

theorem mem_bipK {m : ℕ} {e : Finset (BV m)} : e ∈ bipK m ↔ ∃ i j, e = bipEdge i j := by
  simp [bipK, eq_comm]

theorem bipEdge_card {m : ℕ} (i : Fin m) (j : Fin (8 * m)) : (bipEdge i j).card = 2 := by
  simp [bipEdge]

@[simp] theorem inl_mem_hubs {m : ℕ} (i : Fin m) : Sum.inl i ∈ hubs m := by simp [hubs]
@[simp] theorem inr_not_mem_hubs {m : ℕ} (j : Fin (8 * m)) : Sum.inr j ∉ hubs m := by simp [hubs]
@[simp] theorem inr_mem_leaves {m : ℕ} (j : Fin (8 * m)) : Sum.inr j ∈ leaves m := by simp [leaves]
@[simp] theorem inl_not_mem_leaves {m : ℕ} (i : Fin m) : Sum.inl i ∉ leaves m := by simp [leaves]

theorem card_hubs (m : ℕ) : (hubs m).card = m := by
  simp [hubs, Finset.card_image_of_injective _ Sum.inl_injective]

theorem card_leaves (m : ℕ) : (leaves m).card = 8 * m := by
  simp [leaves, Finset.card_image_of_injective _ Sum.inr_injective]

theorem card_univ_BV (m : ℕ) : Fintype.card (BV m) = 9 * m := by
  simp [BV]; ring

theorem bipK_uniform (m : ℕ) : IsUniform (bipK m) 2 := by
  intro e he
  obtain ⟨i, j, rfl⟩ := mem_bipK.1 he
  exact bipEdge_card i j

theorem disjoint_bipEdge {m : ℕ} (i : Fin m) (j : Fin (8 * m)) (D : Finset (BV m)) :
    Disjoint (bipEdge i j) D ↔ Sum.inl i ∉ D ∧ Sum.inr j ∉ D := by
  simp [bipEdge, Finset.disjoint_left]

theorem bipEdge_inter_hubs {m : ℕ} (i : Fin m) (j : Fin (8 * m)) :
    bipEdge i j ∩ hubs m = {Sum.inl i} := by
  ext v
  simp only [bipEdge, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h | h, hv⟩
    · exact h
    · exact absurd (h ▸ hv) (by simp)
  · rintro rfl; exact ⟨Or.inl rfl, by simp⟩

theorem bipEdge_inter_leaves {m : ℕ} (i : Fin m) (j : Fin (8 * m)) :
    bipEdge i j ∩ leaves m = {Sum.inr j} := by
  ext v
  simp only [bipEdge, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h | h, hv⟩
    · exact absurd (h ▸ hv) (by simp)
    · exact h
  · rintro rfl; exact ⟨Or.inr rfl, by simp⟩

/-! ## Degrees in the residual -/

/-- Residual edges through an uncovered hub `i` are exactly the edges to the uncovered leaves. -/
theorem hub_res_filter {m : ℕ} (i : Fin m) (D : Finset (BV m)) (hi : Sum.inl i ∉ D) :
    (((bipK m).filter (fun e => Disjoint e D)).filter (fun e => Sum.inl i ∈ e))
      = (leaves m \ D).image (fun v => insert (Sum.inl i) ({v} : Finset (BV m))) := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨he, hd⟩, hie⟩
    obtain ⟨i', j, rfl⟩ := mem_bipK.1 he
    have hii : i' = i := by
      simp only [bipEdge, Finset.mem_insert, Finset.mem_singleton] at hie
      rcases hie with h | h
      · exact (Sum.inl_injective h).symm
      · exact absurd h (by simp)
    subst hii
    rw [disjoint_bipEdge] at hd
    exact ⟨Sum.inr j, ⟨by simp, hd.2⟩, rfl⟩
  · rintro ⟨v, ⟨hv, hvD⟩, rfl⟩
    obtain ⟨j, rfl⟩ : ∃ j, v = Sum.inr j := by
      simp only [leaves, Finset.mem_image] at hv
      obtain ⟨j, _, rfl⟩ := hv
      exact ⟨j, rfl⟩
    refine ⟨⟨mem_bipK.2 ⟨i, j, rfl⟩, ?_⟩, by simp⟩
    rw [show insert (Sum.inl i) ({Sum.inr j} : Finset (BV m)) = bipEdge i j from rfl,
      disjoint_bipEdge]
    exact ⟨hi, hvD⟩

/-- Residual edges through an uncovered leaf `j` are exactly the edges to the uncovered hubs. -/
theorem leaf_res_filter {m : ℕ} (j : Fin (8 * m)) (D : Finset (BV m)) (hj : Sum.inr j ∉ D) :
    (((bipK m).filter (fun e => Disjoint e D)).filter (fun e => Sum.inr j ∈ e))
      = (hubs m \ D).image (fun v => insert v ({Sum.inr j} : Finset (BV m))) := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨he, hd⟩, hje⟩
    obtain ⟨i, j', rfl⟩ := mem_bipK.1 he
    have hjj : j' = j := by
      simp only [bipEdge, Finset.mem_insert, Finset.mem_singleton] at hje
      rcases hje with h | h
      · exact absurd h.symm (by simp)
      · exact (Sum.inr_injective h).symm
    subst hjj
    rw [disjoint_bipEdge] at hd
    exact ⟨Sum.inl i, ⟨by simp, hd.1⟩, rfl⟩
  · rintro ⟨v, ⟨hv, hvD⟩, rfl⟩
    obtain ⟨i, rfl⟩ : ∃ i, v = Sum.inl i := by
      simp only [hubs, Finset.mem_image] at hv
      obtain ⟨i, _, rfl⟩ := hv
      exact ⟨i, rfl⟩
    refine ⟨⟨mem_bipK.2 ⟨i, j, rfl⟩, ?_⟩, by simp⟩
    rw [show insert (Sum.inl i) ({Sum.inr j} : Finset (BV m)) = bipEdge i j from rfl,
      disjoint_bipEdge]
    exact ⟨hvD, hj⟩

theorem hub_res_deg {m : ℕ} (i : Fin m) (D : Finset (BV m)) (hi : Sum.inl i ∉ D) :
    (((bipK m).filter (fun e => Disjoint e D)).filter (fun e => Sum.inl i ∈ e)).card
      = (leaves m \ D).card := by
  rw [hub_res_filter i D hi]
  refine Finset.card_image_of_injOn (fun v hv v' _ h => ?_)
  have hvl : v ∈ leaves m := (Finset.mem_sdiff.1 (Finset.mem_coe.1 hv)).1
  have h' : ({Sum.inl i, v} : Finset (BV m)) = {Sum.inl i, v'} := h
  have hmem : v ∈ ({Sum.inl i, v'} : Finset (BV m)) := by rw [← h']; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1
  · rw [h1] at hvl; exact absurd hvl (by simp)
  · exact h1

theorem leaf_res_deg {m : ℕ} (j : Fin (8 * m)) (D : Finset (BV m)) (hj : Sum.inr j ∉ D) :
    (((bipK m).filter (fun e => Disjoint e D)).filter (fun e => Sum.inr j ∈ e)).card
      = (hubs m \ D).card := by
  rw [leaf_res_filter j D hj]
  refine Finset.card_image_of_injOn (fun v hv v' _ h => ?_)
  have hvl : v ∈ hubs m := (Finset.mem_sdiff.1 (Finset.mem_coe.1 hv)).1
  have h' : ({v, Sum.inr j} : Finset (BV m)) = {v', Sum.inr j} := h
  have hmem : v ∈ ({v', Sum.inr j} : Finset (BV m)) := by rw [← h']; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1
  · exact h1
  · rw [h1] at hvl; exact absurd hvl (by simp)

/-- Degrees of `bipK`: a hub has degree `8m`. -/
theorem degree_bipK_inl {m : ℕ} (i : Fin m) : degree (bipK m) (Sum.inl i) = 8 * m := by
  have h := hub_res_deg i (∅ : Finset (BV m)) (by simp)
  simpa [degree, card_leaves] using h

/-- Degrees of `bipK`: a leaf has degree `m`. -/
theorem degree_bipK_inr {m : ℕ} (j : Fin (8 * m)) : degree (bipK m) (Sum.inr j) = m := by
  have h := leaf_res_deg j (∅ : Finset (BV m)) (by simp)
  simpa [degree, card_hubs] using h

/-- The codegree of `bipK` is at most `1` (it is a simple graph). -/
theorem codegree_bipK_le_one {m : ℕ} (x y : BV m) (hxy : x ≠ y) : codegree (bipK m) x y ≤ 1 := by
  rw [codegree, Finset.card_le_one]
  intro e he f hf
  simp only [Finset.mem_filter] at he hf
  obtain ⟨heK, hxe, hye⟩ := he
  obtain ⟨hfK, hxf, hyf⟩ := hf
  have hpair : ({x, y} : Finset (BV m)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
  have hsube : ({x, y} : Finset (BV m)) ⊆ e := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  have hsubf : ({x, y} : Finset (BV m)) ⊆ f := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  have hce : e.card = 2 := bipK_uniform m e heK
  have hcf : f.card = 2 := bipK_uniform m f hfK
  have h1 : ({x, y} : Finset (BV m)) = e := Finset.eq_of_subset_of_card_le hsube (by omega)
  have h2 : ({x, y} : Finset (BV m)) = f := Finset.eq_of_subset_of_card_le hsubf (by omega)
  rw [← h1, ← h2]

/-! ## Counting the matching -/

/-- If every edge of a pairwise-disjoint family `M` meets `W` in exactly one vertex, then the
support of `M` meets `W` in exactly `|M|` vertices. -/
theorem card_support_inter {V : Type*} [DecidableEq V] (M : Finset (Finset V))
    (hd : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) (W : Finset V)
    (h1 : ∀ e ∈ M, (e ∩ W).card = 1) : (support M ∩ W).card = M.card := by
  have hrw : support M ∩ W = M.biUnion (fun e => e ∩ W) := by
    ext v
    simp only [support, Finset.mem_inter, Finset.mem_biUnion, id_eq]
    tauto
  rw [hrw, Finset.card_biUnion (fun e he f hf hef =>
    (hd e he f hf hef).mono Finset.inter_subset_left Finset.inter_subset_left),
    Finset.sum_congr rfl h1]
  simp

end BipRef

/-! ## The refutation -/

open BipRef in
/-- **`NibbleRoundProb` is false.**  See the file header: the complete bipartite graph `K_{m,8m}`
satisfies every hypothesis (`2`-uniform, codegree `≤ 1`, degrees in `[L, U]` with `L = m`,
`U = 8m = 8L`) yet admits no retained set whose round matching keeps both the residual degree floor
`(1/2-ε/2)L` off all but a `δlow`-fraction of the uncovered vertices and the residual degree ceiling
`(1/2+ε)U` off all but a `blow`-fraction of the vertices. -/
theorem not_nibbleRoundProb : ¬ NibbleRoundProb := by
  intro hprob
  obtain ⟨ecod, hecod, L₀, hL₀, hmain⟩ :=
    hprob 2 le_rfl (1 / 1000) (1 / 1000) (1 / 8) (by norm_num) (by norm_num) (by norm_num) le_rfl
  -- choose a degree scale `m` beyond both thresholds
  set m : ℕ := max 1 (max ⌈L₀⌉₊ ⌈1 / ecod⌉₊) with hmdef
  have hm1 : 1 ≤ m := le_max_left _ _
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmL₀ : L₀ ≤ (m : ℝ) := by
    refine le_trans (Nat.le_ceil L₀) ?_
    exact_mod_cast le_trans (le_max_left _ _) (le_max_right 1 _)
  have hmecod : 1 ≤ ecod * (m : ℝ) := by
    have h1 : 1 / ecod ≤ (m : ℝ) := by
      refine le_trans (Nat.le_ceil (1 / ecod)) ?_
      exact_mod_cast le_trans (le_max_right _ _) (le_max_right 1 _)
    rw [div_le_iff₀ hecod] at h1
    linarith
  -- the hypotheses of the round
  have hcodeg : CodegreeBounded (bipK m) (ecod * (m : ℝ)) := by
    intro x y hxy
    have := codegree_bipK_le_one x y hxy
    have : (codegree (bipK m) x y : ℝ) ≤ 1 := by exact_mod_cast this
    linarith
  have hdegU : ∀ v : BV m, (degree (bipK m) v : ℝ) ≤ 8 * (m : ℝ) := by
    rintro (i | j)
    · rw [degree_bipK_inl]; push_cast; linarith
    · rw [degree_bipK_inr]; linarith
  have hdegL : ∀ v : BV m, v ∉ (∅ : Finset (BV m)) → v ∉ (∅ : Finset (BV m)) →
      (m : ℝ) ≤ (degree (bipK m) v : ℝ) := by
    rintro (i | j) _ _
    · rw [degree_bipK_inl]; push_cast; linarith
    · rw [degree_bipK_inr]
  obtain ⟨R', hR'K, -, ⟨Elow, hElow, hlow⟩, hhigh⟩ :=
    hmain (bipK m) ∅ ∅ (m : ℝ) (8 * (m : ℝ)) hmL₀ (by linarith) (by linarith)
      (bipK_uniform m) hcodeg (by simp) hdegU hdegL
  -- notation
  set M : Finset (Finset (BV m)) := roundMatching R' with hMdef
  set C : Finset (BV m) := support M with hCdef
  have hMdisj : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f :=
    (roundMatching_isMatching hR'K).disjoint
  have hMsub : M ⊆ bipK m := (roundMatching_subset R').trans hR'K
  -- the matching meets each side in exactly `|M|` vertices
  have hcA : (C ∩ hubs m).card = M.card := by
    refine card_support_inter M hMdisj (hubs m) (fun e he => ?_)
    obtain ⟨i, j, rfl⟩ := mem_bipK.1 (hMsub he)
    rw [bipEdge_inter_hubs]; simp
  have hcB : (C ∩ leaves m).card = M.card := by
    refine card_support_inter M hMdisj (leaves m) (fun e he => ?_)
    obtain ⟨i, j, rfl⟩ := mem_bipK.1 (hMsub he)
    rw [bipEdge_inter_leaves]; simp
  have hMm : M.card ≤ m := by
    have hle : (C ∩ hubs m).card ≤ (hubs m).card :=
      Finset.card_le_card Finset.inter_subset_right
    rw [card_hubs] at hle
    omega
  -- cardinalities of the uncovered sides
  have hunA : (hubs m \ C).card + M.card = m := by
    rw [← hcA, Finset.inter_comm]
    rw [Finset.card_sdiff_add_card_inter, card_hubs]
  have hunB : (leaves m \ C).card + M.card = 8 * m := by
    rw [← hcB, Finset.inter_comm]
    rw [Finset.card_sdiff_add_card_inter, card_leaves]
  have hunBge : 7 * m ≤ (leaves m \ C).card := by omega
  -- every uncovered hub is a high-degree vertex of the residual
  have hhubhigh : hubs m \ C ⊆ highDeg (Hypergraph.residual (bipK m) R') ((1 / 2 + 1 / 8) *
      (8 * (m : ℝ))) := by
    intro v hv
    obtain ⟨hvhub, hvC⟩ := Finset.mem_sdiff.1 hv
    obtain ⟨i, rfl⟩ : ∃ i, v = Sum.inl i := by
      simp only [hubs, Finset.mem_image] at hvhub
      obtain ⟨i, _, rfl⟩ := hvhub
      exact ⟨i, rfl⟩
    have hdeg : degree (Hypergraph.residual (bipK m) R') (Sum.inl i) = (leaves m \ C).card :=
      hub_res_deg i C hvC
    have h7 : (7 : ℝ) * (m : ℝ) ≤ ((leaves m \ C).card : ℝ) := by exact_mod_cast hunBge
    simp only [highDeg, Finset.mem_filter, Finset.mem_univ, true_and, hdeg]
    linarith
  -- hence almost every hub is covered
  have hAsmall : ((hubs m \ C).card : ℝ) ≤ 1 / 1000 * (9 * (m : ℝ)) := by
    refine le_trans ?_ (le_trans (Finset.card_le_card hhubhigh |> Nat.cast_le.2) ?_)
    · exact le_of_eq rfl
    · simpa [card_univ_BV m] using hhigh
  -- an uncovered leaf then has far too small a residual degree, so it must lie in `Elow`
  have hleaflow : leaves m \ C ⊆ Elow := by
    intro v hv
    obtain ⟨hvleaf, hvC⟩ := Finset.mem_sdiff.1 hv
    obtain ⟨j, rfl⟩ : ∃ j, v = Sum.inr j := by
      simp only [leaves, Finset.mem_image] at hvleaf
      obtain ⟨j, _, rfl⟩ := hvleaf
      exact ⟨j, rfl⟩
    by_contra hnot
    have hdeg : degree (Hypergraph.residual (bipK m) R') (Sum.inr j) = (hubs m \ C).card :=
      leaf_res_deg j C hvC
    have := hlow (Sum.inr j) (by simpa using hvC) (by simp) hnot
    rw [hdeg] at this
    linarith
  have hBsmall : ((leaves m \ C).card : ℝ) ≤ 1 / 1000 * (9 * (m : ℝ)) := by
    refine le_trans (Nat.cast_le.2 (Finset.card_le_card hleaflow)) ?_
    simpa [card_univ_BV m] using hElow
  have h7 : (7 : ℝ) * (m : ℝ) ≤ ((leaves m \ C).card : ℝ) := by exact_mod_cast hunBge
  linarith

end Nibble
