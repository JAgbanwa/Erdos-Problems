/-
# BKLO §10.1 — Lemma 10.6 for `r = 2` (`F = K₃`).

This file transcribes BKLO Lemma 10.6 ("Bounding the maximum degree of the remainder graph")
for `r = 2`, `F = K₃`, `f = 3`, and proves it from

* `BKLO.TransformStepK3` — the *first half* of the paper's proof of Lemma 10.6, transcribed as a
  hypothesis (see the docstring there for exactly which paper ingredients it packages), and
* `BKLO.Lemma104K3` — BKLO Lemma 10.4, which `BKLO.lemma104K3_of_lemma103K3` derives from
  Lemma 10.3.

Everything here is `sorry`-free.
-/
import BKLO.Section10Matchings
import BKLO.Section10Iteration

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Edges between two sets -/

theorem mem_edgesBtw {E : Finset (Sym2 V)} {S T : Finset V} {e : Sym2 V} :
    e ∈ edgesBtw E S T ↔ e ∈ E ∧ ∃ a ∈ S, ∃ b ∈ T, e = s(a, b) := by
  simp [edgesBtw]

theorem edgesBtw_subset (E : Finset (Sym2 V)) (S T : Finset V) : edgesBtw E S T ⊆ E :=
  Finset.filter_subset _ _

theorem edgesBtw_mono_left {E E' : Finset (Sym2 V)} (h : E ⊆ E') (S T : Finset V) :
    edgesBtw E S T ⊆ edgesBtw E' S T := by
  intro e he
  rw [mem_edgesBtw] at he ⊢
  exact ⟨h he.1, he.2⟩

/-! ### Making the degrees into a set even by deleting one edge per vertex

This is the step "*by removing at most `r − 1` edges incident to each `v ∈ B_i` from `H*_i` we
obtain a spanning subgraph `H'_i` of `H*_i` which has the property that `r` divides
`d_{H'_i}(v, V'_i)` for all `v ∈ B_i`*" in the proof of BKLO Lemma 10.6, for `r = 2`. -/

/-- An arbitrary neighbour of `v` inside `W` (or `v` itself if there is none). -/
noncomputable def pickNbr (H : Finset (Sym2 V)) (v : V) (W : Finset V) : V :=
  if h : (nbhdIn H v W).Nonempty then h.choose else v

theorem pickNbr_mem {H : Finset (Sym2 V)} {v : V} {W : Finset V}
    (h : (nbhdIn H v W).Nonempty) : pickNbr H v W ∈ nbhdIn H v W := by
  rw [pickNbr, dif_pos h]
  exact h.choose_spec

/-- For each vertex of `U` whose degree into `W` is odd, one edge from it into `W`. -/
noncomputable def oddFix (H : Finset (Sym2 V)) (U W : Finset V) : Finset (Sym2 V) :=
  (U.filter (fun v => ¬ 2 ∣ degTo H v W)).image (fun v => s(v, pickNbr H v W))

theorem nonempty_nbhd_of_odd {H : Finset (Sym2 V)} {v : V} {W : Finset V}
    (h : ¬ 2 ∣ degTo H v W) : (nbhdIn H v W).Nonempty := by
  rw [← Finset.card_pos]
  rcases Nat.eq_zero_or_pos (nbhdIn H v W).card with h0 | h0
  · exact absurd (by simp [degTo, h0]) h
  · exact h0

theorem mem_oddFix {H : Finset (Sym2 V)} {U W : Finset V} {e : Sym2 V}
    (he : e ∈ oddFix H U W) :
    ∃ v ∈ U, ¬ 2 ∣ degTo H v W ∧ e = s(v, pickNbr H v W) ∧ pickNbr H v W ∈ W ∧ e ∈ H := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
  obtain ⟨hvU, hvodd⟩ := Finset.mem_filter.1 hv
  have hp := pickNbr_mem (nonempty_nbhd_of_odd hvodd)
  rw [mem_nbhdIn] at hp
  exact ⟨v, hvU, hvodd, rfl, hp.1, hp.2⟩

theorem oddFix_subset (H : Finset (Sym2 V)) (U W : Finset V) : oddFix H U W ⊆ H := by
  intro e he
  obtain ⟨v, _, _, _, _, h⟩ := mem_oddFix he
  exact h

/-- The deleted edges all leave `W`, so they miss `H[W]` entirely. -/
theorem oddFix_disjoint_edgesIn {H E : Finset (Sym2 V)} {U W : Finset V}
    (hUW : Disjoint U W) : Disjoint (oddFix H U W) (edgesIn E W) := by
  refine Finset.disjoint_left.2 fun e he he' => ?_
  obtain ⟨v, hvU, _, rfl, _, _⟩ := mem_oddFix he
  have : v ∈ W := (mem_edgesIn.1 he').2 v (by simp)
  exact (Finset.disjoint_left.1 hUW hvU) this

/-- Every deleted edge at a vertex `u ∈ U` is *the* edge chosen at `u`. -/
theorem oddFix_edge_at {H : Finset (Sym2 V)} {U W : Finset V} (hUW : Disjoint U W)
    {u : V} (hu : u ∈ U) {e : Sym2 V} (he : e ∈ oddFix H U W) (hue : u ∈ e) :
    ¬ 2 ∣ degTo H u W ∧ e = s(u, pickNbr H u W) := by
  obtain ⟨v, hvU, hvodd, rfl, hpW, _⟩ := mem_oddFix he
  have huv : u = v := by
    rcases Sym2.mem_iff.1 hue with h | h
    · exact h
    · exact absurd (h ▸ hpW) (Finset.disjoint_left.1 hUW hu)
  subst huv
  exact ⟨hvodd, rfl⟩

theorem edeg_oddFix_le_one {H : Finset (Sym2 V)} {U W : Finset V} (hUW : Disjoint U W)
    {v : V} (hv : v ∉ W) : edeg (oddFix H U W) v ≤ 1 := by
  classical
  by_cases hvU : v ∈ U
  · have hsub : (oddFix H U W).filter (fun e => v ∈ e) ⊆ {s(v, pickNbr H v W)} := by
      intro e he
      obtain ⟨he1, he2⟩ := Finset.mem_filter.1 he
      exact Finset.mem_singleton.2 (oddFix_edge_at hUW hvU he1 he2).2
    calc edeg (oddFix H U W) v ≤ ({s(v, pickNbr H v W)} : Finset (Sym2 V)).card :=
          Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
  · have hempty : (oddFix H U W).filter (fun e => v ∈ e) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun e he => ?_
      obtain ⟨he1, he2⟩ := Finset.mem_filter.1 he
      obtain ⟨u, huU, _, rfl, hpW, _⟩ := mem_oddFix he1
      rcases Sym2.mem_iff.1 he2 with h | h
      · exact hvU (h ▸ huU)
      · exact hv (h ▸ hpW)
    simp [edeg, hempty]

/-- The neighbourhood of `u ∈ U` inside `W` after the deletion. -/
theorem nbhdIn_sdiff_oddFix {H : Finset (Sym2 V)} {U W : Finset V} (hUW : Disjoint U W)
    {u : V} (hu : u ∈ U) :
    nbhdIn (H \ oddFix H U W) u W =
      if 2 ∣ degTo H u W then nbhdIn H u W else (nbhdIn H u W).erase (pickNbr H u W) := by
  classical
  ext y
  by_cases hpar : 2 ∣ degTo H u W
  · simp only [hpar, if_true, mem_nbhdIn, Finset.mem_sdiff]
    constructor
    · rintro ⟨hyW, hy, -⟩; exact ⟨hyW, hy⟩
    · rintro ⟨hyW, hy⟩
      refine ⟨hyW, hy, fun hc => ?_⟩
      exact (oddFix_edge_at hUW hu hc (by simp)).1 hpar
  · simp only [hpar, if_false, mem_nbhdIn, Finset.mem_sdiff, Finset.mem_erase]
    constructor
    · rintro ⟨hyW, hy, hnot⟩
      refine ⟨fun hyp => hnot ?_, hyW, hy⟩
      subst hyp
      exact Finset.mem_image.2 ⟨u, Finset.mem_filter.2 ⟨hu, hpar⟩, rfl⟩
    · rintro ⟨hyne, hyW, hy⟩
      refine ⟨hyW, hy, fun hc => ?_⟩
      have := (oddFix_edge_at hUW hu hc (by simp)).2
      rw [Sym2.eq_iff] at this
      rcases this with ⟨-, h⟩ | ⟨-, h2⟩
      · exact hyne h
      · exact (Finset.disjoint_left.1 hUW hu) (h2 ▸ hyW)

theorem degTo_sdiff_oddFix_even {H : Finset (Sym2 V)} {U W : Finset V} (hUW : Disjoint U W)
    {u : V} (hu : u ∈ U) : 2 ∣ degTo (H \ oddFix H U W) u W := by
  classical
  rw [degTo, nbhdIn_sdiff_oddFix hUW hu]
  by_cases hpar : 2 ∣ degTo H u W
  · rw [if_pos hpar]; exact hpar
  · rw [if_neg hpar]
    have hmem : pickNbr H u W ∈ nbhdIn H u W := pickNbr_mem (nonempty_nbhd_of_odd hpar)
    rw [Finset.card_erase_of_mem hmem]
    have hpos : 0 < (nbhdIn H u W).card := Finset.card_pos.2 ⟨_, hmem⟩
    rw [degTo] at hpar
    omega

theorem degTo_sdiff_oddFix_ge {H : Finset (Sym2 V)} {U W : Finset V} (hUW : Disjoint U W)
    {u : V} (hu : u ∈ U) : degTo H u W ≤ degTo (H \ oddFix H U W) u W + 1 := by
  classical
  have h : degTo (H \ oddFix H U W) u W
      = (if 2 ∣ degTo H u W then nbhdIn H u W
          else (nbhdIn H u W).erase (pickNbr H u W)).card := by
    rw [degTo, nbhdIn_sdiff_oddFix hUW hu]
  rw [h]
  by_cases hpar : 2 ∣ degTo H u W
  · rw [if_pos hpar]; exact Nat.le_succ _
  · rw [if_neg hpar]
    have hmem : pickNbr H u W ∈ nbhdIn H u W := pickNbr_mem (nonempty_nbhd_of_odd hpar)
    rw [Finset.card_erase_of_mem hmem, degTo]
    omega

/-! ### The graphs `H*_i` and `H'_i` of the proof of Lemma 10.6 -/

/-- `H*_i := H'[B_i, V'_i] ∪ G[V'_i]`, where `B_i := B \ V_i` and `V'_i := V_i \ B`. -/
def starGraph (E H' : Finset (Sym2 V)) (B W : Finset V) : Finset (Sym2 V) :=
  edgesBtw H' (B \ W) (W \ B) ∪ edgesIn E (W \ B)

/-- `H'_i`: the graph `H*_i` with at most one (`= r - 1`) edge deleted at each vertex of `B_i`,
so that `2 = r` divides `d(v, V'_i)` for every `v ∈ B_i`. -/
noncomputable def evenStar (E H' : Finset (Sym2 V)) (B W : Finset V) : Finset (Sym2 V) :=
  starGraph E H' B W \ oddFix (starGraph E H' B W) (B \ W) (W \ B)

theorem disjoint_sdiff_sdiff (B W : Finset V) : Disjoint (B \ W) (W \ B) :=
  Finset.disjoint_left.2 fun _ ha hb => (Finset.mem_sdiff.1 ha).2 (Finset.mem_sdiff.1 hb).1

theorem starGraph_subset {E H' : Finset (Sym2 V)} (hH' : H' ⊆ E) (B W : Finset V) :
    starGraph E H' B W ⊆ E := by
  refine Finset.union_subset (fun e he => hH' (edgesBtw_subset _ _ _ he)) (edgesIn_subset _ _)

theorem evenStar_subset (E H' : Finset (Sym2 V)) (B W : Finset V) :
    evenStar E H' B W ⊆ starGraph E H' B W := Finset.sdiff_subset

/-- The edges of `H'_i` inside `V'_i` are exactly the edges of `G` inside `V'_i`. -/
theorem edgesIn_evenStar (E H' : Finset (Sym2 V)) (B W : Finset V) :
    edgesIn (evenStar E H' B W) (W \ B) = edgesIn E (W \ B) := by
  apply Finset.Subset.antisymm
  · intro e he
    rw [mem_edgesIn] at he ⊢
    obtain ⟨he1, he2⟩ := he
    have : e ∈ starGraph E H' B W := evenStar_subset E H' B W he1
    rcases Finset.mem_union.1 this with h | h
    · obtain ⟨-, a, ha, b, hb, rfl⟩ := mem_edgesBtw.1 h
      exact absurd (he2 a (by simp)) (fun hc => (Finset.mem_sdiff.1 hc).2 (Finset.mem_sdiff.1 ha).1)
    · exact ⟨(mem_edgesIn.1 h).1, he2⟩
  · intro e he
    rw [mem_edgesIn] at he ⊢
    refine ⟨?_, he.2⟩
    rw [evenStar, Finset.mem_sdiff]
    refine ⟨Finset.mem_union_right _ (mem_edgesIn.2 he), ?_⟩
    intro hc
    exact Finset.disjoint_left.1
      (oddFix_disjoint_edgesIn (E := E) (disjoint_sdiff_sdiff B W)) hc (mem_edgesIn.2 he)

theorem edgesBtw_evenStar_subset (E H' : Finset (Sym2 V)) (B W : Finset V) :
    edgesBtw (evenStar E H' B W) (B \ W) (W \ B) ⊆ H' := by
  intro e he
  have he' : e ∈ starGraph E H' B W :=
    evenStar_subset E H' B W (edgesBtw_subset _ _ _ he)
  rcases Finset.mem_union.1 he' with h | h
  · exact edgesBtw_subset _ _ _ h
  · exfalso
    obtain ⟨-, a, ha, b, hb, rfl⟩ := mem_edgesBtw.1 he
    have : a ∈ W \ B := (mem_edgesIn.1 h).2 a (by simp)
    exact (Finset.mem_sdiff.1 this).2 (Finset.mem_sdiff.1 ha).1

/-- Every edge of `H'_i` between `B_i` and `V'_i` joins a vertex of `B` to a vertex outside `B`,
and lies in `H'`. -/
theorem shape_edgesBtw_evenStar {E H' : Finset (Sym2 V)} {B W : Finset V} {e : Sym2 V}
    (he : e ∈ edgesBtw (evenStar E H' B W) (B \ W) (W \ B)) :
    ∃ b ∈ B \ W, ∃ w ∈ W \ B, e = s(b, w) := by
  obtain ⟨-, a, ha, b, hb, rfl⟩ := mem_edgesBtw.1 he
  exact ⟨a, ha, b, hb, rfl⟩

/-! ### The statement of Lemma 10.6, and the first half of its proof as a hypothesis -/

/-- **The first half of the proof of BKLO Lemma 10.6** (`r = 2`, `F = K₃`), transcribed as a
hypothesis.

In the paper (pp. 28–29) this is everything up to and including displays (10.1) and (10.2): one
chooses `η ≪ q ≪ γ`, takes a subgraph `G'` of `G[P]` satisfying

* (G1) `Δ(G') ≤ 2qn`;
* (G2) `d_{G'}(S, V(G)) ≥ q^r εn/2` for every `S ⊆ V(G)` with `|S| ≤ r`

(existence of `G'` is the probabilistic step: a `q`-random subgraph of `G[P]` works whp), applies
the definition of `δ_F^η` to `G[P] − G'` to get an `η`-approximate `F`-decomposition `F₀` with
uncovered graph `G₀`, sets `B := {v : d_{G₀}(v) > η^{1/2} n}` (so `|B| ≤ 2η^{1/2}n`) and
`A := V(G) \ B`, and then uses **BKLO Lemma 5.2** (the rooted embedding lemma, p. 10) to replace
every copy of `F` in `F₀` meeting `B` by a copy inside `A`, obtaining an `F`-decomposition `F₁` of
`G[P] − H'` where `H' := G[P] − ⋃F₁` satisfies

* `N_{H'}(v) = N_{G[P]}(v)` for all `v ∈ B`   (10.1);
* `d_{H'}(v) ≤ 3qn` for all `v ∈ A`           (10.2).

Here `|B| ≤ βn` and `3qn ≤ γn` are the two bounds carried as parameters: the paper's hierarchy
`1/n ≪ η ≪ q ≪ γ` lets `β` and `γ` be prescribed in advance (`η` is chosen last).  The three
ingredients that this hypothesis packages — the existence of `G'` with (G1) and (G2), the
approximate-decomposition threshold `δ_F^η`, and Lemma 5.2 — are exactly the inputs of §10.1 that
are *not* available in this development. -/
def TransformStepK3 (δ : ℝ) : Prop :=
  ∀ (γ β ε : ℝ) (k : ℕ), 0 < γ → 0 < β → 0 < ε → 0 < k → ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V)) (P : Finset (Finset V)),
      n₀ ≤ Fintype.card V → (∀ e ∈ E, ¬ e.IsDiag) →
      IsKDeltaPartition k (δ + ε) P E Finset.univ →
      ∃ (B : Finset V) (H' : Finset (Sym2 V)),
        (B.card : ℝ) ≤ β * (Fintype.card V : ℝ) ∧
        H' ⊆ crossParts E P ∧
        TriDecomp (crossParts E P \ H') ∧
        (∀ e ∈ crossParts E P, (∃ v ∈ B, v ∈ e) → e ∈ H') ∧
        (∀ v : V, v ∉ B → (edeg H' v : ℝ) ≤ γ * (Fintype.card V : ℝ))

/-- **The transformation step for a single pair `(ε, k)`**: the body of `BKLO.TransformStepK3`
with `ε` and `k` fixed.  This is the form in which the second half of the proof of Lemma 10.6
actually consumes it, and it is what allows the *repaired* transformation step
`BKLO.TransformStepK3Res` (which, unlike `BKLO.TransformStepK3`, restores the paper's `1/k ≪ ε`
and is true) to be fed into `BKLO.lemma106K3_core`. -/
def TransformStepK3At (δ ε : ℝ) (k : ℕ) : Prop :=
  ∀ (γ β : ℝ), 0 < γ → 0 < β → ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V)) (P : Finset (Finset V)),
      n₀ ≤ Fintype.card V → (∀ e ∈ E, ¬ e.IsDiag) →
      IsKDeltaPartition k (δ + ε) P E Finset.univ →
      ∃ (B : Finset V) (H' : Finset (Sym2 V)),
        (B.card : ℝ) ≤ β * (Fintype.card V : ℝ) ∧
        H' ⊆ crossParts E P ∧
        TriDecomp (crossParts E P \ H') ∧
        (∀ e ∈ crossParts E P, (∃ v ∈ B, v ∈ e) → e ∈ H') ∧
        (∀ v : V, v ∉ B → (edeg H' v : ℝ) ≤ γ * (Fintype.card V : ℝ))

theorem transformStepK3At_of_transformStepK3 {δ ε : ℝ} {k : ℕ} (h : TransformStepK3 δ)
    (hε : 0 < ε) (hk : 0 < k) : TransformStepK3At δ ε k :=
  fun γ β hγ hβ => h γ β ε k hγ hβ hε hk

/-- **BKLO Lemma 10.6, for `r = 2` and `F = K₃`.**

*Let `r, f, k, n ∈ ℕ` and let `γ, η, ε > 0` with `1/n ≪ η ≪ γ ≪ 1/k ≪ ε, 1/r, 1/f`.  Let `F` be an
`r`-regular graph on `f` vertices and let `G` be a graph on `n` vertices.  Let
`δ := max{δ_F^η, 1 − 1/(r+1)}`.  Suppose that `P = {V₁, …, V_k}` is a `(k, δ+ε)`-partition for `G`.
Then there is a subgraph `H` of `G` such that*

* *(a) `G − H` has an `F`-decomposition;*
* *(b) `Δ(H[P]) ≤ γn`;*
* *(c) for each `1 ≤ i ≤ k`, `Δ(G[Vᵢ] − H[Vᵢ]) ≤ 2γ|Vᵢ|`.*

For `r = 2`: an `F`-decomposition is a `TriDecomp`, `H[P] = crossParts H P`, and
`G[Vᵢ] − H[Vᵢ] = edgesIn E Vᵢ \ edgesIn H Vᵢ`.  The part `γ ≪ ε` of the hierarchy is transcribed
as `γ ≤ ε/4`; `1/n ≪ γ` is transcribed as a threshold `n₀`.  The bound `ε ≤ 1/3` is implicit in
the paper: `δ + ε ≤ 1` and `δ ≥ 1 - 1/(r+1) = 2/3`. -/
def Lemma106K3 (δ : ℝ) : Prop :=
  ∀ (γ ε : ℝ) (k : ℕ), 0 < γ → γ ≤ ε / 4 → 0 < ε → ε ≤ 1 / 3 → 0 < k → ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V)) (P : Finset (Finset V)),
      n₀ ≤ Fintype.card V → (∀ e ∈ E, ¬ e.IsDiag) →
      IsKDeltaPartition k (δ + ε) P E Finset.univ →
      ∃ H : Finset (Sym2 V), H ⊆ E ∧
        TriDecomp (E \ H) ∧
        (∀ v : V, (edeg (crossParts H P) v : ℝ) ≤ γ * (Fintype.card V : ℝ)) ∧
        (∀ W ∈ P, ∀ v : V, (edeg (edgesIn E W \ edgesIn H W) v : ℝ) ≤ 2 * γ * (W.card : ℝ))


/-! ### Auxiliary facts about partitions -/

theorem eq_of_mem_parts {k : ℕ} {P : Finset (Finset V)} {S : Finset V}
    (hEq : IsEquitablePartition k P S) {W W₂ : Finset V} (hW : W ∈ P) (hW₂ : W₂ ∈ P)
    {x : V} (hx : x ∈ W) (hx₂ : x ∈ W₂) : W = W₂ := by
  by_contra hne
  exact (Finset.disjoint_left.1 (hEq.pairwise_disjoint W hW W₂ hW₂ hne)) hx hx₂

theorem edgesIn_disjoint_of_ne {E : Finset (Sym2 V)} {S T : Finset V}
    (h : ∀ x, x ∈ S → x ∈ T → False) : Disjoint (edgesIn E S) (edgesIn E T) := by
  refine Finset.disjoint_left.2 ?_
  intro e
  induction e using Sym2.ind with
  | _ a b =>
    intro he he'
    exact h a ((mem_edgesIn.1 he).2 a (by simp)) ((mem_edgesIn.1 he').2 a (by simp))


/-! ### Lemma 10.6 from the transformation step and Lemma 10.4 -/

/-- **BKLO Lemma 10.6 for `r = 2`**, from the first half of its proof (`TransformStepK3`) and
Lemma 10.4 (`Lemma104K3`, which follows from Lemma 10.3 by `lemma104K3_of_lemma103K3`).

This is the second half of the paper's proof (pp. 29–30): for each `1 ≤ i ≤ k` one sets
`B_i := B \ V_i`, `V'_i := V_i \ B` and `H*_i := H'[B_i, V'_i] ∪ G[V'_i]`, deletes at most
`r - 1 = 1` edge at each vertex of `B_i` to make `d(v, V'_i)` even (`oddFix`), checks conditions
(i)–(iv) of Lemma 10.4 for the resulting graph `H'_i = evenStar E H' B V_i` — condition (ii) via
Proposition 10.5 — and puts
`H := H' ∪ (G − G[P]) − ⋃ᵢ (H'_i[B_i,V'_i] ∪ H_i) = G − ⋃F₁ − ⋃F₂`. -/
theorem lemma106K3_core {δ : ℝ} (hδ : (2 : ℝ) / 3 ≤ δ) (h104 : Lemma104K3)
    {γ ε : ℝ} {k : ℕ} (hγ : 0 < γ) (hγε : γ ≤ ε / 4) (hε : 0 < ε) (hε1 : ε ≤ 1 / 3)
    (hk : 0 < k) (htr : TransformStepK3At δ ε k) :
    ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V)) (P : Finset (Finset V)),
        n₀ ≤ Fintype.card V → (∀ e ∈ E, ¬ e.IsDiag) →
        IsKDeltaPartition k (δ + ε) P E Finset.univ →
        ∃ H : Finset (Sym2 V), H ⊆ E ∧
          TriDecomp (E \ H) ∧
          (∀ v : V, (edeg (crossParts H P) v : ℝ) ≤ γ * (Fintype.card V : ℝ)) ∧
          (∀ W ∈ P, ∀ v : V,
            (edeg (edgesIn E W \ edgesIn H W) v : ℝ) ≤ 2 * γ * (W.card : ℝ)) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  obtain ⟨η₀, hη₀pos, h104'⟩ := h104 γ (2 * k) hγ (by omega)
  obtain ⟨n₁, hn₁⟩ := h104' η₀ hη₀pos (le_refl _)
  obtain ⟨γ', hγ'pos, hγ'γ, hγ'η⟩ : ∃ x : ℝ, 0 < x ∧ x ≤ γ ∧ x ≤ η₀ / (4 * (k : ℝ)) :=
    ⟨min γ (η₀ / (4 * (k : ℝ))), lt_min hγ (by positivity), min_le_left _ _, min_le_right _ _⟩
  obtain ⟨β, hβpos, hβγ, hβε⟩ : ∃ x : ℝ, 0 < x ∧ x ≤ γ / 2 ∧ x ≤ ε / (16 * (k : ℝ)) :=
    ⟨min (γ / 2) (ε / (16 * (k : ℝ))), lt_min (by positivity) (by positivity),
      min_le_left _ _, min_le_right _ _⟩
  obtain ⟨n₂, hn₂⟩ := htr γ' β hγ'pos hβpos
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge (2 * (k : ℝ) / γ)
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (16 * (k : ℝ))
  obtain ⟨N₃, hN₃⟩ := exists_nat_ge (16 * (k : ℝ) / ε)
  refine ⟨max (max n₁ n₂) (max N₁ (max N₂ N₃)), ?_⟩
  intro V _ _ E P hn hloop hpart
  simp only [Nat.max_le] at hn
  obtain ⟨⟨hn1, hn2⟩, hna, hnb, hnc⟩ := hn
  set n : ℕ := Fintype.card V with hndef
  have hR1 : 2 * (k : ℝ) / γ ≤ (n : ℝ) := le_trans hN₁ (by exact_mod_cast hna)
  have hR2 : 16 * (k : ℝ) ≤ (n : ℝ) := le_trans hN₂ (by exact_mod_cast hnb)
  have hR3 : 16 * (k : ℝ) / ε ≤ (n : ℝ) := le_trans hN₃ (by exact_mod_cast hnc)
  have hnR : (0 : ℝ) < (n : ℝ) := by linarith only [hR2, hkR]
  -- the transformation step
  obtain ⟨B, H', hBcard, hH'cross, hH'dec, hH'B, hH'deg⟩ := hn₂ E P hn2 hloop hpart
  have hH'E : H' ⊆ E := fun e he => crossParts_subset E P (hH'cross he)
  have hEq := hpart.1
  have hPdeg := hpart.2
  have hPcard : P.card = k := hEq.card_parts
  -- the basic size estimates, in terms of `u = n/k`
  obtain ⟨u, hudef⟩ : ∃ x : ℝ, x = (n : ℝ) / (k : ℝ) := ⟨_, rfl⟩
  have huk : 16 ≤ u := by rw [hudef, le_div_iff₀ hkR]; linarith only [hR2]
  have hu0 : (0 : ℝ) < u := by linarith only [huk]
  have hεu : (16 : ℝ) ≤ ε * u := by
    rw [div_le_iff₀ hε] at hR3
    have hre : ε * u = ε * (n : ℝ) / (k : ℝ) := by rw [hudef]; ring
    rw [hre, le_div_iff₀ hkR]
    linarith only [hR3]
  have hkn : (k : ℝ) ≤ γ * (n : ℝ) / 2 := by
    rw [div_le_iff₀ hγ] at hR1
    linarith only [hR1]
  have hBu : (B.card : ℝ) ≤ ε * u / 16 := by
    have heq : ε / (16 * (k : ℝ)) * (n : ℝ) = ε * u / 16 := by rw [hudef]; field_simp
    have h1 : β * (n : ℝ) ≤ ε / (16 * (k : ℝ)) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hβε hnR.le
    linarith only [hBcard, h1, heq]
  have hBu' : (B.card : ℝ) ≤ u / 48 := by
    have h1 : ε * u ≤ u / 3 := by
      have := mul_le_mul_of_nonneg_right hε1 hu0.le
      linarith only [this]
    linarith only [hBu, h1]
  have hBγ : (B.card : ℝ) ≤ γ * (n : ℝ) / 2 := by
    have h1 : β * (n : ℝ) ≤ γ / 2 * (n : ℝ) := mul_le_mul_of_nonneg_right hβγ hnR.le
    linarith only [hBcard, h1]
  have hWlow : ∀ W ∈ P, 15 / 16 * u ≤ (W.card : ℝ) := by
    intro W hW
    have h1 : (Finset.univ : Finset V).card / k ≤ W.card := hEq.size_lower W hW
    have h2 := sub_one_le_cast_div (Finset.univ : Finset V).card k hk
    have h3 : ((Finset.univ : Finset V).card : ℝ) = (n : ℝ) := by
      simp [hndef, Finset.card_univ]
    have h4 : (((Finset.univ : Finset V).card / k : ℕ) : ℝ) ≤ (W.card : ℝ) := by
      exact_mod_cast h1
    rw [h3, ← hudef] at h2
    linarith only [h2, h4, huk]
  have hW'card : ∀ W ∈ P, u / 2 ≤ ((W \ B).card : ℝ) := by
    intro W hW
    have h1 : W.card ≤ (W \ B).card + B.card := by
      calc W.card ≤ ((W \ B) ∪ B).card := by
            refine Finset.card_le_card fun x hx => ?_
            by_cases hxB : x ∈ B
            · exact Finset.mem_union_right _ hxB
            · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hx, hxB⟩)
        _ ≤ (W \ B).card + B.card := Finset.card_union_le _ _
    have h1' : (W.card : ℝ) ≤ ((W \ B).card : ℝ) + (B.card : ℝ) := by exact_mod_cast h1
    have h2 := hWlow W hW
    linarith only [h1', h2, hBu']
  have hW'cardNat : ∀ W ∈ P, n / (2 * k) ≤ (W \ B).card := by
    intro W hW
    have h1 : ((n / (2 * k) : ℕ) : ℝ) ≤ (n : ℝ) / ((2 * k : ℕ) : ℝ) :=
      cast_div_le n (2 * k) (by omega)
    have h2 : (((2 * k : ℕ)) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
    have h3 : (n : ℝ) / (2 * (k : ℝ)) = u / 2 := by rw [hudef]; field_simp
    rw [h2, h3] at h1
    have h4 := le_trans h1 (hW'card W hW)
    exact_mod_cast h4
  have hHpE : ∀ W : Finset V, evenStar E H' B W ⊆ E := fun W =>
    Finset.Subset.trans (evenStar_subset E H' B W) (starGraph_subset hH'E B W)
  -- an edge from `B \ W` to `W` is a crossing edge
  have hcross : ∀ W ∈ P, ∀ x ∈ B \ W, ∀ z ∈ W, s(x, z) ∈ E → s(x, z) ∈ crossParts E P := by
    intro W hW x hx z hz hE
    rw [mem_crossParts]
    refine ⟨hE, ?_⟩
    rintro ⟨W₀, hW₀, hall⟩
    have hzW₀ : z ∈ W₀ := hall z (by simp)
    have hxW₀ : x ∈ W₀ := hall x (by simp)
    exact (Finset.mem_sdiff.1 hx).2 ((eq_of_mem_parts hEq hW hW₀ hz hzW₀) ▸ hxW₀)
  -- edges inside `W \ B` are the same in `E` and in `H'_i`
  have hnbhdEq : ∀ W : Finset V, ∀ y ∈ W \ B, ∀ S : Finset V, S ⊆ W \ B →
      nbhdIn (evenStar E H' B W) y S = nbhdIn E y S := by
    intro W y hy S hS
    apply Finset.Subset.antisymm
    · exact nbhdIn_mono_left (hHpE W) y S
    · intro z hz
      rw [mem_nbhdIn] at hz ⊢
      refine ⟨hz.1, ?_⟩
      have hin : s(y, z) ∈ edgesIn E (W \ B) := by
        rw [mem_edgesIn]
        refine ⟨hz.2, ?_⟩
        intro v hv
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · exact hy
        · exact hS hz.1
      have h2 : s(y, z) ∈ edgesIn (evenStar E H' B W) (W \ B) := by
        rw [edgesIn_evenStar]; exact hin
      exact (mem_edgesIn.1 h2).1
  -- apply Lemma 10.4 to each part
  have key : ∀ W ∈ P, ∃ HV : Finset (Sym2 V),
      HV ⊆ edgesIn (evenStar E H' B W) (W \ B) ∧
      TriDecomp (edgesBtw (evenStar E H' B W) (B \ W) (W \ B) ∪ HV) ∧
      ∀ v : V, (edeg HV v : ℝ) ≤ 2 * γ * ((W \ B).card : ℝ) := by
    intro W hW
    have hdisj : Disjoint (B \ W) (W \ B) := disjoint_sdiff_sdiff B W
    have hWc := hW'card W hW
    have hWlo := hWlow W hW
    have hWle : ((W \ B).card : ℝ) ≤ (W.card : ℝ) :=
      Nat.cast_le.2 (Finset.card_le_card Finset.sdiff_subset)
    have hW'nn : (0 : ℝ) ≤ ((W \ B).card : ℝ) := Nat.cast_nonneg _
    have hWnn : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
    -- (i)
    have hdvd : ∀ x ∈ B \ W, 2 ∣ degTo (evenStar E H' B W) x (W \ B) := fun x hx =>
      degTo_sdiff_oddFix_even hdisj hx
    -- (iii)
    have hiii : ∀ y ∈ W \ B,
        (degTo (evenStar E H' B W) y (B \ W) : ℝ) ≤ η₀ * ((W \ B).card : ℝ) := by
      intro y hy
      have hsub : nbhdIn (evenStar E H' B W) y (B \ W) ⊆ nbhdIn H' y (B \ W) := by
        intro z hz
        rw [mem_nbhdIn] at hz ⊢
        refine ⟨hz.1, ?_⟩
        have hst := evenStar_subset E H' B W hz.2
        rcases Finset.mem_union.1 hst with h | h
        · exact edgesBtw_subset _ _ _ h
        · exact absurd ((mem_edgesIn.1 h).2 z (by simp))
            (fun hc => (Finset.mem_sdiff.1 hc).2 (Finset.mem_sdiff.1 hz.1).1)
      have h1 : (degTo (evenStar E H' B W) y (B \ W) : ℝ) ≤ (edeg H' y : ℝ) := by
        have hle := Finset.card_le_card hsub
        have h3 : degTo H' y (B \ W) ≤ edeg H' y := card_filter_edge_le_edeg H' y (B \ W)
        exact_mod_cast le_trans hle h3
      have h4 : (edeg H' y : ℝ) ≤ γ' * (n : ℝ) := hH'deg y (Finset.mem_sdiff.1 hy).2
      have h6 : γ' * (n : ℝ) ≤ (η₀ / (4 * (k : ℝ))) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hγ'η hnR.le
      have h7 : (η₀ / (4 * (k : ℝ))) * (n : ℝ) = η₀ * u / 4 := by rw [hudef]; field_simp
      have h8 : η₀ * (u / 2) ≤ η₀ * ((W \ B).card : ℝ) :=
        mul_le_mul_of_nonneg_left hWc hη₀pos.le
      linarith only [h1, h4, h6, h7, h8]
    -- (iv)
    have hiv : ∀ y ∈ W \ B, ((1 : ℝ) / 2 + 2 * γ) * ((W \ B).card : ℝ)
        ≤ (degTo (evenStar E H' B W) y (W \ B) : ℝ) := by
      intro y hy
      have hd : degTo (evenStar E H' B W) y (W \ B) = degTo E y (W \ B) := by
        rw [degTo, hnbhdEq W y hy (W \ B) (Finset.Subset.refl _), degTo]
      rw [hd]
      have h1 : degTo E y W ≤ degTo E y (W \ B) + B.card := by
        have hsub : nbhdIn E y W ⊆ nbhdIn E y (W \ B) ∪ B := by
          intro z hz
          rw [mem_nbhdIn] at hz
          by_cases hzB : z ∈ B
          · exact Finset.mem_union_right _ hzB
          · exact Finset.mem_union_left _ (mem_nbhdIn.2 ⟨Finset.mem_sdiff.2 ⟨hz.1, hzB⟩, hz.2⟩)
        calc degTo E y W ≤ (nbhdIn E y (W \ B) ∪ B).card := Finset.card_le_card hsub
          _ ≤ degTo E y (W \ B) + B.card := Finset.card_union_le _ _
      have h1' : (degTo E y W : ℝ) ≤ (degTo E y (W \ B) : ℝ) + (B.card : ℝ) := by
        exact_mod_cast h1
      have h2 : (δ + ε) * (W.card : ℝ) ≤ (degTo E y W : ℝ) :=
        hPdeg y (Finset.mem_univ y) W hW
      have h3 : ((2 : ℝ) / 3 + ε) * (W.card : ℝ) ≤ (degTo E y W : ℝ) := by
        have := mul_le_mul_of_nonneg_right (by linarith only [hδ] : (2 : ℝ) / 3 + ε ≤ δ + ε) hWnn
        linarith only [this, h2]
      -- `(1/2 + 2γ)|W'| ≤ (1/2 + ε/2)|W| ≤ (2/3 + ε)|W| − |B|`
      have hA : ((1 : ℝ) / 2 + 2 * γ) * ((W \ B).card : ℝ) ≤ ((1 : ℝ) / 2 + ε / 2) * (W.card : ℝ) := by
        have h5 : ((1 : ℝ) / 2 + 2 * γ) * ((W \ B).card : ℝ)
            ≤ ((1 : ℝ) / 2 + 2 * γ) * (W.card : ℝ) :=
          mul_le_mul_of_nonneg_left hWle (by linarith only [hγ])
        have h6 : (0 : ℝ) ≤ (ε / 4 - γ) * (W.card : ℝ) :=
          mul_nonneg (by linarith only [hγε]) hWnn
        linarith only [h5, h6]
      have hB : ((1 : ℝ) / 2 + ε / 2) * (W.card : ℝ) + (B.card : ℝ)
          ≤ ((2 : ℝ) / 3 + ε) * (W.card : ℝ) := by
        have h7 : (0 : ℝ) ≤ ε * (W.card : ℝ) := mul_nonneg hε.le hWnn
        linarith only [h7, hBu', hWlo]
      linarith only [hA, hB, h1', h3]
    -- (ii)
    have hii : ∀ x ∈ B \ W, ∀ y ∈ nbhdIn (evenStar E H' B W) x (W \ B),
        (1 / 2 : ℝ) * (degTo (evenStar E H' B W) x (W \ B) : ℝ) + γ * ((W \ B).card : ℝ)
          ≤ (degTo (evenStar E H' B W) y (nbhdIn (evenStar E H' B W) x (W \ B)) : ℝ) := by
      intro x hx y hy
      set N : Finset V := nbhdIn (evenStar E H' B W) x (W \ B) with hNdef
      have hNsubW' : N ⊆ W \ B := nbhdIn_subset _ _ _
      have hNsubM : N ⊆ nbhdIn E x W := by
        intro z hz
        rw [hNdef, mem_nbhdIn] at hz
        exact mem_nbhdIn.2 ⟨(Finset.mem_sdiff.1 hz.1).1, hHpE W hz.2⟩
      have hMsub : nbhdIn E x W ⊆ N ∪ B ∪ {pickNbr (starGraph E H' B W) x (W \ B)} := by
        intro z hz
        rw [mem_nbhdIn] at hz
        by_cases hzB : z ∈ B
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hzB)
        · have hzW' : z ∈ W \ B := Finset.mem_sdiff.2 ⟨hz.1, hzB⟩
          have hc : s(x, z) ∈ crossParts E P := hcross W hW x hx z hz.1 hz.2
          have hH : s(x, z) ∈ H' := hH'B _ hc ⟨x, (Finset.mem_sdiff.1 hx).1, by simp⟩
          have hst : s(x, z) ∈ starGraph E H' B W :=
            Finset.mem_union_left _ (mem_edgesBtw.2 ⟨hH, x, hx, z, hzW', rfl⟩)
          have hzst : z ∈ nbhdIn (starGraph E H' B W) x (W \ B) := mem_nbhdIn.2 ⟨hzW', hst⟩
          have hNeq := nbhdIn_sdiff_oddFix (H := starGraph E H' B W) (U := B \ W) (W := W \ B)
            (disjoint_sdiff_sdiff B W) hx
          by_cases hpar : 2 ∣ degTo (starGraph E H' B W) x (W \ B)
          · rw [if_pos hpar] at hNeq
            refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
            rw [hNdef, evenStar, hNeq]
            exact hzst
          · rw [if_neg hpar] at hNeq
            by_cases hzp : z = pickNbr (starGraph E H' B W) x (W \ B)
            · exact Finset.mem_union_right _ (Finset.mem_singleton.2 hzp)
            · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
              rw [hNdef, evenStar, hNeq]
              exact Finset.mem_erase.2 ⟨hzp, hzst⟩
      have hMcard : ((nbhdIn E x W).card : ℝ) ≤ (N.card : ℝ) + (B.card : ℝ) + 1 := by
        have h1 : (nbhdIn E x W).card ≤ N.card + B.card + 1 := by
          have hu1 : (nbhdIn E x W).card
              ≤ (N ∪ B ∪ {pickNbr (starGraph E H' B W) x (W \ B)}).card :=
            Finset.card_le_card hMsub
          have hu2 := Finset.card_union_le (N ∪ B)
            ({pickNbr (starGraph E H' B W) x (W \ B)} : Finset V)
          have hu3 := Finset.card_union_le N B
          simp only [Finset.card_singleton] at hu2
          omega
        exact_mod_cast h1
      have hyW' : y ∈ W \ B := hNsubW' hy
      have hdegy : degTo (evenStar E H' B W) y N = degTo E y N := by
        rw [degTo, hnbhdEq W y hyW' N hNsubW', degTo]
      -- Proposition 10.5
      have hprop : ∀ z ∈ nbhdIn E x W,
          (1 - 1 / (2 : ℝ)) * (degTo E x W : ℝ) + ε * (W.card : ℝ)
            ≤ (degTo E z (nbhdIn E x W) : ℝ) := by
        have hxdeg : (1 - 1 / (((2 : ℕ) : ℝ) + 1) + ε) * (W.card : ℝ) ≤ (degTo E x W : ℝ) := by
          have h := hPdeg x (Finset.mem_univ x) W hW
          have h2 := mul_le_mul_of_nonneg_right
            (by push_cast; linarith only [hδ] :
              (1 - 1 / (((2 : ℕ) : ℝ) + 1) + ε) ≤ δ + ε) hWnn
          linarith only [h, h2]
        have hydeg : ∀ z ∈ W, (1 - 1 / (((2 : ℕ) : ℝ) + 1) + ε) * (W.card : ℝ)
            ≤ (degTo E z W : ℝ) := by
          intro z _
          have h := hPdeg z (Finset.mem_univ z) W hW
          have h2 := mul_le_mul_of_nonneg_right
            (by push_cast; linarith only [hδ] :
              (1 - 1 / (((2 : ℕ) : ℝ) + 1) + ε) ≤ δ + ε) hWnn
          linarith only [h, h2]
        have hp := prop_10_5 (E := E) (W := W) (r := 2) (by norm_num) (le_of_lt hε) hxdeg hydeg
        intro z hz
        have h := hp z hz
        push_cast at h ⊢
        linarith only [h]
      have hrestrict : (degTo E y (nbhdIn E x W) : ℝ)
          ≤ (degTo E y N : ℝ) + (((nbhdIn E x W).card : ℝ) - (N.card : ℝ)) := by
        have hsub : nbhdIn E y (nbhdIn E x W) ⊆ nbhdIn E y N ∪ (nbhdIn E x W \ N) := by
          intro z hz
          rw [mem_nbhdIn] at hz
          by_cases hzN : z ∈ N
          · exact Finset.mem_union_left _ (mem_nbhdIn.2 ⟨hzN, hz.2⟩)
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hz.1, hzN⟩)
        have h1 : degTo E y (nbhdIn E x W) ≤ degTo E y N + (nbhdIn E x W \ N).card := by
          calc degTo E y (nbhdIn E x W) ≤ (nbhdIn E y N ∪ (nbhdIn E x W \ N)).card :=
                Finset.card_le_card hsub
            _ ≤ degTo E y N + (nbhdIn E x W \ N).card := Finset.card_union_le _ _
        have h2 : (nbhdIn E x W \ N).card = (nbhdIn E x W).card - N.card := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.2 hNsubM]
        have h3 : N.card ≤ (nbhdIn E x W).card := Finset.card_le_card hNsubM
        have h1' : (degTo E y (nbhdIn E x W) : ℝ)
            ≤ (degTo E y N : ℝ) + ((nbhdIn E x W \ N).card : ℝ) := by exact_mod_cast h1
        rw [h2] at h1'
        have h4 : (((nbhdIn E x W).card - N.card : ℕ) : ℝ)
            = ((nbhdIn E x W).card : ℝ) - (N.card : ℝ) := by
          push_cast [h3]
          ring
        rw [h4] at h1'
        linarith only [h1']
      have hNcardle : (N.card : ℝ) ≤ (degTo E x W : ℝ) :=
        Nat.cast_le.2 (Finset.card_le_card hNsubM)
      have hdegxN : (degTo (evenStar E H' B W) x (W \ B) : ℝ) = (N.card : ℝ) := by
        rw [hNdef, degTo]
      have hpy := hprop y (hNsubM hy)
      have hMeq : (degTo E x W : ℝ) = ((nbhdIn E x W).card : ℝ) := by rw [degTo]
      rw [hdegy, hdegxN]
      -- the slack: `γ|W'| + |B| + 1 ≤ ε|W|`
      have hslack : γ * ((W \ B).card : ℝ) + (B.card : ℝ) + 1 ≤ ε * (W.card : ℝ) := by
        have ha : (0 : ℝ) ≤ (ε / 4 - γ) * ((W \ B).card : ℝ) :=
          mul_nonneg (by linarith only [hγε]) hW'nn
        have hb : (0 : ℝ) ≤ (ε / 4) * ((W.card : ℝ) - ((W \ B).card : ℝ)) :=
          mul_nonneg (by linarith only [hε]) (by linarith only [hWle])
        have hc : (0 : ℝ) ≤ ε * ((W.card : ℝ) - 15 / 16 * u) :=
          mul_nonneg hε.le (by linarith only [hWlo])
        have hd : (1 : ℝ) ≤ ε * u / 16 := by linarith only [hεu]
        linarith only [ha, hb, hc, hd, hBu]
      linarith only [hpy, hrestrict, hMcard, hNcardle, hMeq, hslack, hdegy]
    -- Lemma 10.4
    have hloopHp : ∀ e ∈ evenStar E H' B W, ¬ e.IsDiag := fun e he => hloop e (hHpE W he)
    obtain ⟨HV, h1, h2, h3⟩ := hn₁ (evenStar E H' B W) (B \ W) (W \ B) hn1 hloopHp hdisj
      (by simpa [hndef] using hW'cardNat W hW) hdvd hii hiii hiv
    exact ⟨HV, h1, h2, h3⟩
  choose! HV hHV1 hHV2 hHV3 using key
  -- the union of the two families `F₁` and `F₂`
  set T : Finset V → Finset (Sym2 V) :=
    fun W => edgesBtw (evenStar E H' B W) (B \ W) (W \ B) ∪ HV W with hTdef
  set Dec : Finset (Sym2 V) := (crossParts E P \ H') ∪ P.biUnion T with hDecdef
  have hHVin : ∀ W ∈ P, HV W ⊆ edgesIn E (W \ B) := by
    intro W hW
    have h := hHV1 W hW
    rwa [edgesIn_evenStar] at h
  have hTsub : ∀ W ∈ P, T W ⊆ E := by
    intro W hW
    refine Finset.union_subset (fun e he => hH'E (edgesBtw_evenStar_subset E H' B W he)) ?_
    exact fun e he => edgesIn_subset _ _ (hHVin W hW he)
  have hDecsub : Dec ⊆ E := by
    refine Finset.union_subset (fun e he => crossParts_subset E P (Finset.mem_sdiff.1 he).1) ?_
    exact Finset.biUnion_subset.2 hTsub
  -- edge-disjointness of the pieces
  have hdisjA : ∀ W ∈ P, Disjoint (crossParts E P \ H') (T W) := by
    intro W hW
    refine Finset.disjoint_left.2 fun e he heT => ?_
    rcases Finset.mem_union.1 heT with h | h
    · exact (Finset.mem_sdiff.1 he).2 (edgesBtw_evenStar_subset E H' B W h)
    · have hin := hHVin W hW h
      refine (mem_crossParts.1 (Finset.mem_sdiff.1 he).1).2 ⟨W, hW, fun v hv => ?_⟩
      exact (Finset.mem_sdiff.1 ((mem_edgesIn.1 hin).2 v hv)).1
  have hdisjT : ∀ W ∈ P, ∀ W₂ ∈ P, W ≠ W₂ → Disjoint (T W) (T W₂) := by
    intro W hW W₂ hW₂ hne
    refine Finset.disjoint_left.2 fun e he he₂ => ?_
    rcases Finset.mem_union.1 he with h | h <;> rcases Finset.mem_union.1 he₂ with h2 | h2
    · obtain ⟨b, hb, w, hw, rfl⟩ := shape_edgesBtw_evenStar h
      obtain ⟨b₂, hb₂, w₂, hw₂, hEq2⟩ := shape_edgesBtw_evenStar h2
      rw [Sym2.eq_iff] at hEq2
      rcases hEq2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne (eq_of_mem_parts hEq hW hW₂ (Finset.mem_sdiff.1 hw).1
          (Finset.mem_sdiff.1 hw₂).1)
      · exact (Finset.mem_sdiff.1 hw).2 (Finset.mem_sdiff.1 hb₂).1
    · obtain ⟨b, hb, w, hw, rfl⟩ := shape_edgesBtw_evenStar h
      have hin := hHVin W₂ hW₂ h2
      have hbW₂ : b ∈ W₂ \ B := (mem_edgesIn.1 hin).2 b (by simp)
      exact (Finset.mem_sdiff.1 hbW₂).2 (Finset.mem_sdiff.1 hb).1
    · obtain ⟨b, hb, w, hw, rfl⟩ := shape_edgesBtw_evenStar h2
      have hin := hHVin W hW h
      have hbW : b ∈ W \ B := (mem_edgesIn.1 hin).2 b (by simp)
      exact (Finset.mem_sdiff.1 hbW).2 (Finset.mem_sdiff.1 hb).1
    · refine Finset.disjoint_left.1
        (edgesIn_disjoint_of_ne (E := E) (S := W \ B) (T := W₂ \ B) fun x hx hx₂ => ?_)
        (hHVin W hW h) (hHVin W₂ hW₂ h2)
      exact hne (eq_of_mem_parts hEq hW hW₂ (Finset.mem_sdiff.1 hx).1 (Finset.mem_sdiff.1 hx₂).1)
  have hdec : TriDecomp Dec := by
    rw [hDecdef]
    refine TriDecomp.union ?_ hH'dec (TriDecomp.biUnion hHV2 hdisjT)
    rw [Finset.disjoint_biUnion_right]
    exact hdisjA
  refine ⟨E \ Dec, Finset.sdiff_subset, ?_, ?_, ?_⟩
  · rwa [Finset.sdiff_sdiff_eq_self hDecsub]
  · -- (b)  `Δ(H[P]) ≤ γn`
    intro v
    have hcrossH : crossParts (E \ Dec) P ⊆ H' := by
      intro e he
      have he1 : e ∈ E \ Dec := crossParts_subset _ _ he
      have he2 : e ∈ crossParts E P := by
        rw [mem_crossParts] at he ⊢
        exact ⟨(Finset.mem_sdiff.1 he1).1, he.2⟩
      by_contra hH
      exact (Finset.mem_sdiff.1 he1).2
        (Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨he2, hH⟩))
    by_cases hvB : v ∈ B
    · -- vertices of `B`: only edges to `B` and the `≤ k` deleted edges survive
      have hsub : (crossParts (E \ Dec) P).filter (fun e => v ∈ e)
          ⊆ (P.biUnion (fun W => oddFix (starGraph E H' B W) (B \ W) (W \ B))).filter
              (fun e => v ∈ e) ∪ B.image (fun x => s(v, x)) := by
        intro e he
        obtain ⟨he1, hve⟩ := Finset.mem_filter.1 he
        obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hve
        by_cases hwB : w ∈ B
        · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, hwB, rfl⟩)
        · have hwU : w ∈ (Finset.univ : Finset V) := Finset.mem_univ w
          rw [← hEq.cover] at hwU
          obtain ⟨W, hW, hwW⟩ := Finset.mem_biUnion.1 hwU
          have hvW : v ∉ W := by
            intro hvW
            exact (mem_crossParts.1 he1).2 ⟨W, hW, fun z hz => by
              rcases Sym2.mem_iff.1 hz with rfl | rfl
              · exact hvW
              · exact hwW⟩
          have hvBW : v ∈ B \ W := Finset.mem_sdiff.2 ⟨hvB, hvW⟩
          have hwW' : w ∈ W \ B := Finset.mem_sdiff.2 ⟨hwW, hwB⟩
          have heD : s(v, w) ∈ E \ Dec := crossParts_subset _ _ he1
          have heE : s(v, w) ∈ crossParts E P := by
            rw [mem_crossParts] at he1 ⊢
            exact ⟨(Finset.mem_sdiff.1 heD).1, he1.2⟩
          have hH : s(v, w) ∈ H' := hH'B _ heE ⟨v, hvB, by simp⟩
          have hst : s(v, w) ∈ starGraph E H' B W :=
            Finset.mem_union_left _ (mem_edgesBtw.2 ⟨hH, v, hvBW, w, hwW', rfl⟩)
          by_cases hdel : s(v, w) ∈ oddFix (starGraph E H' B W) (B \ W) (W \ B)
          · exact Finset.mem_union_left _
              (Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨W, hW, hdel⟩, hve⟩)
          · exfalso
            have hev : s(v, w) ∈ evenStar E H' B W := Finset.mem_sdiff.2 ⟨hst, hdel⟩
            have hbtw : s(v, w) ∈ edgesBtw (evenStar E H' B W) (B \ W) (W \ B) :=
              mem_edgesBtw.2 ⟨hev, v, hvBW, w, hwW', rfl⟩
            refine (Finset.mem_sdiff.1 heD).2 ?_
            rw [hDecdef]
            exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨W, hW,
              Finset.mem_union_left _ hbtw⟩)
      have hDcard : ((P.biUnion (fun W => oddFix (starGraph E H' B W) (B \ W) (W \ B))).filter
          (fun e => v ∈ e)).card ≤ k := by
        rw [Finset.filter_biUnion]
        refine le_trans (Finset.card_biUnion_le) ?_
        calc ∑ W ∈ P, ((oddFix (starGraph E H' B W) (B \ W) (W \ B)).filter
                (fun e => v ∈ e)).card
            ≤ ∑ _W ∈ P, 1 := by
              refine Finset.sum_le_sum fun W hW => ?_
              have hvW : v ∉ W \ B := fun hc => (Finset.mem_sdiff.1 hc).2 hvB
              exact edeg_oddFix_le_one (disjoint_sdiff_sdiff B W) hvW
          _ = k := by simp [hPcard]
      have hfin : edeg (crossParts (E \ Dec) P) v ≤ k + B.card := by
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_union_le
          ((P.biUnion (fun W => oddFix (starGraph E H' B W) (B \ W) (W \ B))).filter
            (fun e => v ∈ e)) (B.image (fun x => s(v, x)))
        have h3 : (B.image (fun x => s(v, x))).card ≤ B.card := Finset.card_image_le
        have h4 : edeg (crossParts (E \ Dec) P) v
            = ((crossParts (E \ Dec) P).filter (fun e => v ∈ e)).card := rfl
        omega
      have hfin' : (edeg (crossParts (E \ Dec) P) v : ℝ) ≤ (k : ℝ) + (B.card : ℝ) := by
        exact_mod_cast hfin
      linarith only [hfin', hkn, hBγ]
    · -- vertices outside `B`: the remainder is contained in `H'`
      have h1 : (edeg (crossParts (E \ Dec) P) v : ℝ) ≤ (edeg H' v : ℝ) :=
        Nat.cast_le.2 (edeg_mono hcrossH v)
      have h2 : (edeg H' v : ℝ) ≤ γ' * (n : ℝ) := hH'deg v hvB
      have h3 : γ' * (n : ℝ) ≤ γ * (n : ℝ) := mul_le_mul_of_nonneg_right hγ'γ hnR.le
      linarith only [h1, h2, h3]
  · -- (c)  `Δ(G[Vᵢ] − H[Vᵢ]) ≤ 2γ|Vᵢ|`
    intro W hW v
    have hsub : edgesIn E W \ edgesIn (E \ Dec) W ⊆ HV W := by
      intro e he
      obtain ⟨he1, he2⟩ := Finset.mem_sdiff.1 he
      obtain ⟨heE, heW⟩ := mem_edgesIn.1 he1
      have heDec : e ∈ Dec := by
        by_contra hc
        exact he2 (mem_edgesIn.2 ⟨Finset.mem_sdiff.2 ⟨heE, hc⟩, heW⟩)
      rw [hDecdef] at heDec
      rcases Finset.mem_union.1 heDec with h | h
      · exact absurd ⟨W, hW, heW⟩ (mem_crossParts.1 (Finset.mem_sdiff.1 h).1).2
      · obtain ⟨W₂, hW₂, hmem⟩ := Finset.mem_biUnion.1 h
        rcases Finset.mem_union.1 hmem with h2 | h2
        · exfalso
          obtain ⟨b, hb, w, hw, rfl⟩ := shape_edgesBtw_evenStar h2
          have hwW : w ∈ W := heW w (by simp)
          have hWW₂ : W = W₂ := eq_of_mem_parts hEq hW hW₂ hwW (Finset.mem_sdiff.1 hw).1
          exact (Finset.mem_sdiff.1 hb).2 (hWW₂ ▸ heW b (by simp))
        · have hin := hHVin W₂ hW₂ h2
          have hWW₂ : W = W₂ := by
            revert hin heW
            induction e using Sym2.ind with
            | _ a b =>
              intro heW hin
              exact eq_of_mem_parts hEq hW hW₂ (heW a (by simp))
                (Finset.mem_sdiff.1 ((mem_edgesIn.1 hin).2 a (by simp))).1
          rw [hWW₂]
          exact h2
    have h1 : (edeg (edgesIn E W \ edgesIn (E \ Dec) W) v : ℝ) ≤ (edeg (HV W) v : ℝ) :=
      Nat.cast_le.2 (edeg_mono hsub v)
    have h2 := hHV3 W hW v
    have h3 : ((W \ B).card : ℝ) ≤ (W.card : ℝ) :=
      Nat.cast_le.2 (Finset.card_le_card Finset.sdiff_subset)
    have h4 : 2 * γ * ((W \ B).card : ℝ) ≤ 2 * γ * (W.card : ℝ) :=
      mul_le_mul_of_nonneg_left h3 (by linarith only [hγ])
    linarith only [h1, h2, h4]

/-- **BKLO Lemma 10.6 for `r = 2`**, from the first half of its proof (`TransformStepK3`) and
Lemma 10.4.  This is `BKLO.lemma106K3_core` with the transformation step supplied for every
`(ε, k)` at once.

Note that the hypothesis `TransformStepK3 δ` is *false* as stated (see
`BKLO.not_transformStepK3`): it omits the paper's `1/k ≪ ε`.  The repaired chain, ending in
`BKLO.Lemma106K3Res`, is in `BKLO/Section10TransformStepProof.lean`. -/
theorem lemma106K3_of_transformStep {δ : ℝ} (hδ : (2 : ℝ) / 3 ≤ δ)
    (htr : TransformStepK3 δ) (h104 : Lemma104K3) : Lemma106K3 δ :=
  fun _ _ _ hγ hγε hε hε1 hk =>
    lemma106K3_core hδ h104 hγ hγε hε hε1 hk (transformStepK3At_of_transformStepK3 htr hε hk)

end BKLO
