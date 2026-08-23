/-
# BKLO §10.3 — the iteration: Lemma 10.13 (hence Lemma 10.1) from Lemma 10.12, for `r = 2`.

BKLO's Lemma 10.1 (the output of §10) is deduced in §10.3 from the "strengthened `(†)`"
statement Lemma 10.12 by iterating it down a partition sequence `P₁, …, P_ℓ`.  This file carries
out that iteration for `r = 2` (`F = K₃`): Lemma 10.12 is transcribed as the hypothesis
`Lemma1012K3 δ`, and `BKLO.lemma_10_13_K3` proves BKLO Lemma 10.13 (which immediately implies
Lemma 10.1) from it.

The partition sequence is encoded as a list `L` of partitions followed by the last partition `Pl`
(so `ℓ = |L| + 1`), with `P[W] := restrictParts P W` the parts of `P` contained in `W`, exactly as
in the paper.  The predicate `PartSeq k c δ ε m L Pl E S` says:

* the first partition is a `(k, c)`-partition for `E` (paper: `(k, δ+ε)`-partition for `G`);
* for every part `W` of it, the rest of the sequence, restricted to `W`, is a partition sequence
  for `E[W]` whose first partition is a `(k, δ+2ε)`-partition (paper: condition (ii));
* every part of the last partition has size `m-1` or `m` (paper: condition (iii)).

Everything here is `sorry`-free.
-/
import BKLO.Section10Defs
import Mathlib.Data.Int.Star

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Restricting a partition to a subset -/

/-- `P[W]`: the parts of `P` contained in `W`. -/
def restrictParts (Q : Finset (Finset V)) (W : Finset V) : Finset (Finset V) :=
  Q.filter (fun R => R ⊆ W)

theorem mem_restrictParts {Q : Finset (Finset V)} {W R : Finset V} :
    R ∈ restrictParts Q W ↔ R ∈ Q ∧ R ⊆ W := by simp [restrictParts]

theorem restrictParts_mono {Q : Finset (Finset V)} {W W' : Finset V} (h : W ⊆ W') :
    restrictParts Q W ⊆ restrictParts Q W' := by
  intro R hR
  rw [mem_restrictParts] at hR ⊢
  exact ⟨hR.1, hR.2.trans h⟩

/-! ### Elementary facts about induced edge sets -/

/-- All edges of `E` at `x` lie inside `W`, so `x` has at most `|W|` of them. -/
theorem edeg_le_card_of_within {E : Finset (Sym2 V)} {x : V} {W : Finset V}
    (h : ∀ e ∈ E, x ∈ e → ∀ v ∈ e, v ∈ W) : edeg E x ≤ W.card := by
  classical
  have hsub : E.filter (fun e => x ∈ e) ⊆ W.image (fun y => s(x, y)) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 he.2
    exact Finset.mem_image.2 ⟨y, h _ he.1 he.2 y (by simp), rfl⟩
  exact le_trans (Finset.card_le_card hsub) (Finset.card_image_le)

theorem edgesIn_sdiff (E D : Finset (Sym2 V)) (W : Finset V) :
    edgesIn (E \ D) W = edgesIn E W \ D := by
  ext e
  simp only [mem_edgesIn, Finset.mem_sdiff]
  tauto

theorem edgesIn_edgesIn (E : Finset (Sym2 V)) {U W : Finset V} (h : W ⊆ U) :
    edgesIn (edgesIn E U) W = edgesIn E W := by
  ext e
  simp only [mem_edgesIn]
  constructor
  · rintro ⟨⟨he, _⟩, hW⟩
    exact ⟨he, hW⟩
  · rintro ⟨he, hW⟩
    exact ⟨⟨he, fun v hv => h (hW v hv)⟩, hW⟩

theorem insideParts_eq_biUnion (E : Finset (Sym2 V)) (P : Finset (Finset V)) :
    insideParts E P = P.biUnion (fun W => edgesIn E W) := by
  ext e
  simp only [mem_insideParts, Finset.mem_biUnion, mem_edgesIn]
  constructor
  · rintro ⟨he, W, hW, hsub⟩
    exact ⟨W, hW, he, hsub⟩
  · rintro ⟨W, hW, he, hsub⟩
    exact ⟨he, W, hW, hsub⟩

theorem edgesIn_subset_insideParts {E : Finset (Sym2 V)} {P : Finset (Finset V)} {W : Finset V}
    (hW : W ∈ P) : edgesIn E W ⊆ insideParts E P := by
  intro e he
  rw [mem_edgesIn] at he
  exact mem_insideParts.2 ⟨he.1, W, hW, he.2⟩

/-- Edges inside two disjoint sets are different edges. -/
theorem disjoint_edgesIn {E : Finset (Sym2 V)} {U U' : Finset V} (h : Disjoint U U') :
    Disjoint (edgesIn E U) (edgesIn E U') := by
  refine Finset.disjoint_left.2 fun e he he' => ?_
  rw [mem_edgesIn] at he he'
  obtain ⟨x, hx⟩ : ∃ x, x ∈ e := ⟨e.out.1, by simp [Sym2.out_fst_mem]⟩
  exact (Finset.disjoint_left.1 h) (he.2 x hx) (he'.2 x hx)

/-- An edge inside a part is not a crossing edge. -/
theorem disjoint_edgesIn_crossParts {E : Finset (Sym2 V)} {P : Finset (Finset V)} {W : Finset V}
    (hW : W ∈ P) : Disjoint (edgesIn E W) (crossParts E P) := by
  refine Finset.disjoint_left.2 fun e he he' => ?_
  rw [mem_edgesIn] at he
  exact (mem_crossParts.1 he').2 ⟨W, hW, he.2⟩

/-! ### Nat division, in `ℝ` -/

theorem cast_div_le (a k : ℕ) (hk : 0 < k) : ((a / k : ℕ) : ℝ) ≤ (a : ℝ) / (k : ℝ) := by
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [le_div_iff₀ hk']
  exact_mod_cast Nat.div_mul_le_self a k

theorem sub_one_le_cast_div (a k : ℕ) (hk : 0 < k) :
    (a : ℝ) / (k : ℝ) - 1 ≤ ((a / k : ℕ) : ℝ) := by
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h : a < (a / k + 1) * k := by
    have h1 := Nat.div_add_mod a k
    have h2 := Nat.mod_lt a hk
    linarith only [h1, h2]
  have h' : (a : ℝ) < ((a / k : ℕ) + 1) * (k : ℝ) := by exact_mod_cast h
  rw [sub_le_iff_le_add, div_le_iff₀ hk']
  linarith only [h']

theorem cast_ceil_div_le (a k : ℕ) (hk : 0 < k) :
    (((a + k - 1) / k : ℕ) : ℝ) ≤ (a : ℝ) / (k : ℝ) + 1 := by
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h1 : ((a + k - 1) / k : ℕ) * k ≤ a + k - 1 := Nat.div_mul_le_self _ _
  have h2 : a + k - 1 ≤ a + k := by omega
  have h3 : ((a + k - 1) / k : ℕ) * k ≤ a + k := le_trans h1 h2
  have h4 : (((a + k - 1) / k : ℕ) : ℝ) * (k : ℝ) ≤ (a : ℝ) + (k : ℝ) := by exact_mod_cast h3
  rw [← le_div_iff₀ hk'] at h4
  refine le_trans h4 ?_
  rw [add_div]
  simp [div_self (ne_of_gt hk')]

/-! ### Degrees under edge deletion -/

theorem edeg_sdiff_add_edeg_eq {D E : Finset (Sym2 V)} (h : D ⊆ E) (x : V) :
    edeg (E \ D) x + edeg D x = edeg E x := by
  classical
  have h1 : (E \ D).filter (fun e => x ∈ e) = E.filter (fun e => x ∈ e) \ D.filter (fun e => x ∈ e) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have h2 : D.filter (fun e => x ∈ e) ⊆ E.filter (fun e => x ∈ e) :=
    Finset.filter_subset_filter _ h
  unfold edeg
  rw [h1]
  exact Finset.card_sdiff_add_card_eq_card h2

theorem evenDegrees_sdiff {D E : Finset (Sym2 V)} (h : D ⊆ E) (hE : EvenDegrees E)
    (hD : EvenDegrees D) : EvenDegrees (E \ D) := by
  intro v
  have := edeg_sdiff_add_edeg_eq h v
  rcases hE v with ⟨a, ha⟩
  rcases hD v with ⟨b, hb⟩
  exact ⟨a - b, by omega⟩

theorem evenDegrees_of_triDecomp {D : Finset (Sym2 V)} (h : TriDecomp D) : EvenDegrees D :=
  fun v => (h.triDivisible).1 v

theorem edgesIn_subset_cliqueEdges {E : Finset (Sym2 V)} {U : Finset V}
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) : edgesIn E U ⊆ cliqueEdges U := by
  intro e he
  rw [mem_edgesIn] at he
  exact mem_cliqueEdgesV.2 ⟨he.2, hloop e he.1⟩

/-! ### Partition sequences -/

/-- The first partition of the sequence `L`, `Pl`. -/
def headParts : List (Finset (Finset V)) → Finset (Finset V) → Finset (Finset V)
  | [], Pl => Pl
  | (P :: _), _ => P

/-- **`(k, δ+ε, m)`-partition sequence** (BKLO Lemma 10.13 (i)–(iii)), relative to a top-level
density `c`.  The sequence is `P₁, …, P_ℓ` with `L = [P₁, …, P_{ℓ-1}]` and `Pl = P_ℓ`:

* the first partition, restricted to the current vertex set `S`, is a `(k, c)`-partition for `E`;
* for each of its parts `W`, the remaining partitions form such a sequence for `E[W]` on `W`,
  with top-level density `δ + 2ε`;
* every part of the last partition has `m - 1` or `m` vertices. -/
def PartSeq (k : ℕ) (c δ ε : ℝ) (m : ℕ) :
    List (Finset (Finset V)) → Finset (Finset V) → Finset (Sym2 V) → Finset V → Prop
  | [], Pl, E, S =>
      IsKDeltaPartition k c (restrictParts Pl S) E S ∧
        ∀ W ∈ restrictParts Pl S, m ≤ W.card + 1 ∧ W.card ≤ m
  | (P :: rest), Pl, E, S =>
      IsKDeltaPartition k c (restrictParts P S) E S ∧
        ∀ W ∈ restrictParts P S, PartSeq k (δ + 2 * ε) δ ε m rest Pl (edgesIn E W) W

theorem PartSeq.head {k : ℕ} {c δ ε : ℝ} {m : ℕ} {L : List (Finset (Finset V))}
    {Pl : Finset (Finset V)} {E : Finset (Sym2 V)} {S : Finset V}
    (h : PartSeq k c δ ε m L Pl E S) :
    IsKDeltaPartition k c (restrictParts (headParts L Pl) S) E S := by
  cases L with
  | nil => exact h.1
  | cons P rest => exact h.1

/-- Every vertex set carrying a partition sequence has at least `m - 1` vertices. -/
theorem PartSeq.card_ge {k : ℕ} {δ ε : ℝ} {m : ℕ} (hk : 0 < k) :
    ∀ (L : List (Finset (Finset V))) (c : ℝ) (Pl : Finset (Finset V)) (E : Finset (Sym2 V))
      (S : Finset V), PartSeq k c δ ε m L Pl E S → m ≤ S.card + 1 := by
  intro L
  induction L with
  | nil =>
    intro c Pl E S h
    obtain ⟨W, hW⟩ : (restrictParts Pl S).Nonempty := by
      rw [← Finset.card_pos, h.1.1.card_parts]; exact hk
    have hsize := (h.2 W hW).1
    have hsub : W ⊆ S := (mem_restrictParts.1 hW).2
    have := Finset.card_le_card hsub
    omega
  | cons P rest ih =>
    intro c Pl E S h
    obtain ⟨W, hW⟩ : (restrictParts P S).Nonempty := by
      rw [← Finset.card_pos, h.1.1.card_parts]; exact hk
    have hsub : W ⊆ S := (mem_restrictParts.1 hW).2
    have := ih (δ + 2 * ε) Pl (edgesIn E W) W (h.2 W hW)
    have := Finset.card_le_card hsub
    omega

/-- **Deleting a low-degree graph from the top level of a partition sequence.**  If `H` has small
maximum degree and avoids all the edges inside the parts of the first partition, then the sequence
remains a partition sequence for `E - H`, with the top-level density degraded from `c` to `c'`. -/
theorem PartSeq.sdiff_head {k : ℕ} {c c' δ ε cc : ℝ} {m : ℕ} {L : List (Finset (Finset V))}
    {Pl : Finset (Finset V)} {E H : Finset (Sym2 V)} {S : Finset V}
    (hseq : PartSeq k c δ ε m L Pl E S)
    (hH : ∀ v : V, (edeg H v : ℝ) ≤ cc)
    (hc : ∀ W ∈ restrictParts (headParts L Pl) S, cc ≤ (c - c') * (W.card : ℝ))
    (hdisj : ∀ W ∈ restrictParts (headParts L Pl) S, Disjoint H (edgesIn E W)) :
    PartSeq k c' δ ε m L Pl (E \ H) S := by
  cases L with
  | nil =>
    exact ⟨hseq.1.sdiff hH hc, hseq.2⟩
  | cons P rest =>
    refine ⟨hseq.1.sdiff hH hc, fun W hW => ?_⟩
    have heq : edgesIn (E \ H) W = edgesIn E W := by
      rw [edgesIn_sdiff]
      exact Finset.sdiff_eq_self_of_disjoint (hdisj W hW).symm
    rw [heq]
    exact hseq.2 W hW

/-! ### Lemma 10.12 -/

/-- **BKLO Lemma 10.12, for `r = 2` and `F = K₃`** (the formal version of the statement `(†)` at
the beginning of §10), transcribed as a hypothesis.

*Let `r, f, k, n ∈ ℕ` and let `η, ε > 0` with `1/n ≪ η ≪ 1/k ≪ ε, 1/r, 1/f`.  Let `F` be an
`r`-regular graph on `f` vertices.  Let `G` be an `r`-divisible graph on `n` vertices and let `G₀`
be a subgraph of `G - G[P]`.  Let `δ := max{δ_F^η, 1 - 1/(r+1)}`.  Suppose that
`P = {V₁, …, V_k}` is a `(k, δ+3ε)`-partition for `G - G₀`.  Then there is a subgraph `H` of
`G - G[P] - G₀` such that `G[P] ∪ H` has an `F`-decomposition and `Δ(H) ≤ εn/2k²`.*

For `r = 2`: `r`-divisible means all degrees are even, and an `F`-decomposition is a `TriDecomp`.
The threshold `δ` (which depends on `η`, hence on `k` and `ε`) is carried as a parameter. -/
def Lemma1012K3 (δ : ℝ) : Prop :=
  ∀ (k : ℕ) (ε : ℝ), 0 < k → 0 < ε → ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E G₀ : Finset (Sym2 V)) (S : Finset V)
      (P : Finset (Finset V)),
      n₀ ≤ S.card → (∀ e ∈ E, ¬ e.IsDiag) → E ⊆ cliqueEdges S → EvenDegrees E →
      G₀ ⊆ insideParts E P →
      IsKDeltaPartition k (δ + 3 * ε) P (E \ G₀) S →
      ∃ H : Finset (Sym2 V), H ⊆ insideParts E P \ G₀ ∧
        TriDecomp (crossParts E P ∪ H) ∧
        ∀ v : V, (edeg H v : ℝ) ≤ ε * (S.card : ℝ) / (2 * (k : ℝ) ^ 2)

/-! ### Lemma 10.13: the iteration -/

/-- **BKLO Lemma 10.13 for `r = 2`, the induction.**  Iterating Lemma 10.12 down the partition
sequence.  `N` is the threshold: it must be at least the `n₀` of Lemma 10.12 (used with `ε/6` in
place of `ε`), and large enough for the two size estimates collected in `hgap`. -/
theorem lemma_10_13_aux {δ ε : ℝ} {k m N : ℕ} (hk : 0 < k) (hε : 0 < ε)
    (h12 : ∀ (E G₀ : Finset (Sym2 V)) (S : Finset V) (P : Finset (Finset V)),
      N ≤ S.card → (∀ e ∈ E, ¬ e.IsDiag) → E ⊆ cliqueEdges S → EvenDegrees E →
      G₀ ⊆ insideParts E P → IsKDeltaPartition k (δ + 3 * (ε / 6)) P (E \ G₀) S →
      ∃ H : Finset (Sym2 V), H ⊆ insideParts E P \ G₀ ∧
        TriDecomp (crossParts E P ∪ H) ∧
        ∀ v : V, (edeg H v : ℝ) ≤ (ε / 6) * (S.card : ℝ) / (2 * (k : ℝ) ^ 2))
    (hgap : ∀ s : ℝ, (N : ℝ) ≤ s →
      s / (k : ℝ) ^ 2 + 2 ≤ (ε / 2) * (s / (k : ℝ) - 1) ∧ 3 * (k : ℝ) ^ 2 ≤ s)
    (hmN : N + 1 ≤ m) :
    ∀ (L : List (Finset (Finset V))) (Pl : Finset (Finset V)) (E : Finset (Sym2 V))
      (S : Finset V), (∀ e ∈ E, ¬ e.IsDiag) → E ⊆ cliqueEdges S → EvenDegrees E →
      PartSeq k (δ + ε) δ ε m L Pl E S →
      ∃ Hstar : Finset (Sym2 V), Hstar ⊆ insideParts E (restrictParts Pl S) ∧
        TriDecomp (E \ Hstar) := by
  classical
  intro L
  induction L with
  | nil =>
    intro Pl E S hloop hES hev hseq
    have hcardS : N ≤ S.card := by
      have := PartSeq.card_ge (δ := δ) (ε := ε) hk [] (δ + ε) Pl E S hseq
      omega
    obtain ⟨H, hHsub, hHdec, -⟩ :=
      h12 E ∅ S (restrictParts Pl S) hcardS hloop hES hev (by simp)
        (by rw [Finset.sdiff_empty]; exact hseq.1.mono (by linarith))
    have hHin : H ⊆ insideParts E (restrictParts Pl S) := by
      simpa using hHsub
    refine ⟨insideParts E (restrictParts Pl S) \ H, Finset.sdiff_subset, ?_⟩
    have hEeq : E \ (insideParts E (restrictParts Pl S) \ H)
        = crossParts E (restrictParts Pl S) ∪ H := by
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_union, mem_crossParts, mem_insideParts]
      constructor
      · rintro ⟨he, h⟩
        by_cases hi : ∃ W ∈ restrictParts Pl S, ∀ v ∈ e, v ∈ W
        · right
          by_contra hH
          exact h ⟨⟨he, hi⟩, hH⟩
        · exact Or.inl ⟨he, hi⟩
      · rintro (⟨he, hi⟩ | hH)
        · exact ⟨he, fun hc => hi hc.1.2⟩
        · have hmem := hHin hH
          rw [mem_insideParts] at hmem
          exact ⟨hmem.1, fun hc => hc.2 hH⟩
    rw [hEeq]
    exact hHdec
  | cons P rest ih =>
    intro Pl E S hloop hES hev hseq
    -- notation
    set Pp := restrictParts P S with hPpdef
    set Q := headParts rest Pl with hQdef
    have hpart : IsEquitablePartition k Pp S := hseq.1.1
    have hchild : ∀ U ∈ Pp, PartSeq k (δ + 2 * ε) δ ε m rest Pl (edgesIn E U) U := hseq.2
    have hQpart : ∀ U ∈ Pp, IsEquitablePartition k (restrictParts Q U) U := fun U hU =>
      ((hchild U hU).head).1
    have hcardS : N ≤ S.card := by
      have := PartSeq.card_ge (δ := δ) (ε := ε) hk (P :: rest) (δ + ε) Pl E S hseq
      omega
    have hcardSR : (N : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcardS
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    -- the edges inside the second-level parts
    set G₀ := Pp.biUnion (fun U => insideParts (edgesIn E U) (restrictParts Q U)) with hG₀def
    have hG₀sub : G₀ ⊆ insideParts E Pp := by
      intro e he
      obtain ⟨U, hU, heU⟩ := Finset.mem_biUnion.1 he
      have h1 := (mem_insideParts.1 heU).1
      rw [mem_edgesIn] at h1
      exact mem_insideParts.2 ⟨h1.1, U, hU, h1.2⟩
    have hG₀mem : ∀ U ∈ Pp, ∀ W ∈ restrictParts Q U, edgesIn E W ⊆ G₀ := by
      intro U hU W hW e he
      have hWU : W ⊆ U := (mem_restrictParts.1 hW).2
      rw [mem_edgesIn] at he
      refine Finset.mem_biUnion.2 ⟨U, hU, mem_insideParts.2 ⟨?_, W, hW, he.2⟩⟩
      exact mem_edgesIn.2 ⟨he.1, fun v hv => hWU (he.2 v hv)⟩
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hinvk : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one hkR]; exact hk1
    -- the degree of `G₀`
    have hdegG₀ : ∀ x ∈ S, (edeg G₀ x : ℝ) ≤ (S.card : ℝ) / (k : ℝ) ^ 2 + 2 := by
      intro x hx
      obtain ⟨U, hU, hxU⟩ : ∃ U ∈ Pp, x ∈ U := by
        have hcov := hpart.cover
        rw [← hcov] at hx
        obtain ⟨U, hU, hxU⟩ := Finset.mem_biUnion.1 hx
        exact ⟨U, hU, hxU⟩
      obtain ⟨Vx, hVx, hxVx⟩ : ∃ W ∈ restrictParts Q U, x ∈ W := by
        have hcov := (hQpart U hU).cover
        rw [← hcov] at hxU
        obtain ⟨W, hW, hxW⟩ := Finset.mem_biUnion.1 hxU
        exact ⟨W, hW, hxW⟩
      have hxU' : x ∈ U := (mem_restrictParts.1 hVx).2 hxVx
      have hwithin : ∀ e ∈ G₀, x ∈ e → ∀ v ∈ e, v ∈ Vx := by
        intro e he hxe v hv
        obtain ⟨U', hU', heU'⟩ := Finset.mem_biUnion.1 he
        obtain ⟨hein, W, hW, hsub⟩ := mem_insideParts.1 heU'
        have hWU' : W ⊆ U' := (mem_restrictParts.1 hW).2
        have hxW : x ∈ W := hsub x hxe
        have hUU' : U = U' := by
          by_contra hne
          exact (Finset.disjoint_left.1 (hpart.pairwise_disjoint U hU U' hU' hne)) hxU'
            (hWU' hxW)
        subst hUU'
        have hWVx : W = Vx := by
          by_contra hne
          exact (Finset.disjoint_left.1
            ((hQpart U hU).pairwise_disjoint W hW Vx hVx hne)) hxW hxVx
        rw [← hWVx]
        exact hsub v hv
      have h1 : edeg G₀ x ≤ Vx.card := edeg_le_card_of_within hwithin
      have h2 : (Vx.card : ℝ) ≤ (U.card : ℝ) / (k : ℝ) + 1 := by
        refine le_trans ?_ (cast_ceil_div_le U.card k hk)
        exact_mod_cast (hQpart U hU).size_upper Vx hVx
      have h3 : (U.card : ℝ) ≤ (S.card : ℝ) / (k : ℝ) + 1 := by
        refine le_trans ?_ (cast_ceil_div_le S.card k hk)
        exact_mod_cast hpart.size_upper U hU
      have h5 : (U.card : ℝ) / (k : ℝ) ≤ ((S.card : ℝ) / (k : ℝ) + 1) / (k : ℝ) := by
        gcongr
      have h6 : ((S.card : ℝ) / (k : ℝ) + 1) / (k : ℝ)
          = (S.card : ℝ) / (k : ℝ) ^ 2 + 1 / (k : ℝ) := by
        field_simp
        try ring
      have h7 : (edeg G₀ x : ℝ) ≤ (Vx.card : ℝ) := by exact_mod_cast h1
      linarith only [hinvk, h2, h5, h6, h7]
    -- the size of a part
    have hpartsize : ∀ W ∈ Pp, (S.card : ℝ) / (k : ℝ) - 1 ≤ (W.card : ℝ) := by
      intro W hW
      refine le_trans (sub_one_le_cast_div S.card k hk) ?_
      exact_mod_cast hpart.size_lower W hW
    -- (d): the partition survives the removal of `G₀`
    have hF3 : IsKDeltaPartition k (δ + 3 * (ε / 6)) Pp (E \ G₀) S := by
      refine ⟨hpart, fun x hx W hW => ?_⟩
      have h1 : (degTo E x W : ℝ) ≤ (degTo (E \ G₀) x W : ℝ) + (edeg G₀ x : ℝ) := by
        exact_mod_cast Nat.cast_le.2 (degTo_sdiff_ge E G₀ x W)
      have h2 := hseq.1.2 x hx W hW
      have h3 := hdegG₀ x hx
      have h4 := (hgap _ hcardSR).1
      have h5 := hpartsize W hW
      have h6 : (ε / 2) * ((S.card : ℝ) / (k : ℝ) - 1) ≤ (ε / 2) * (W.card : ℝ) := by
        exact mul_le_mul_of_nonneg_left h5 (by linarith)
      have : (δ + 3 * (ε / 6)) * (W.card : ℝ) = (δ + ε) * (W.card : ℝ) - (ε / 2) * (W.card : ℝ) := by
        ring
      rw [this]
      linarith only [h1, h2, h3, h4, h6]
    obtain ⟨H, hHsub, hHdec, hHdeg⟩ := h12 E G₀ S Pp hcardS hloop hES hev hG₀sub hF3
    have hHinside : H ⊆ insideParts E Pp := (Finset.subset_sdiff.1 hHsub).1
    have hHG₀ : Disjoint H G₀ := (Finset.subset_sdiff.1 hHsub).2
    have hHE : H ⊆ E := hHinside.trans (insideParts_subset _ _)
    have hDE : crossParts E Pp ∪ H ⊆ E :=
      Finset.union_subset (crossParts_subset _ _) hHE
    have hevD : EvenDegrees (crossParts E Pp ∪ H) := evenDegrees_of_triDecomp hHdec
    have hevG' : EvenDegrees (E \ (crossParts E Pp ∪ H)) := evenDegrees_sdiff hDE hev hevD
    -- the leftover inside a part
    have hEU : ∀ U ∈ Pp, edgesIn (E \ (crossParts E Pp ∪ H)) U = edgesIn E U \ H := by
      intro U hU
      rw [edgesIn_sdiff]
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨he, h⟩
        exact ⟨he, fun hH => h (Or.inr hH)⟩
      · rintro ⟨he, hH⟩
        refine ⟨he, ?_⟩
        rintro (hc | hh)
        · exact (Finset.disjoint_left.1 (disjoint_edgesIn_crossParts hU)) he hc
        · exact hH hh
    -- the inductive hypothesis, applied inside each part
    have hmain : ∀ U ∈ Pp, ∃ Hu : Finset (Sym2 V),
        Hu ⊆ insideParts (edgesIn E U \ H) (restrictParts Pl U) ∧
        TriDecomp ((edgesIn E U \ H) \ Hu) := by
      intro U hU
      have hUS : U ⊆ S := hpart.subset_of_mem hU
      have hloopU : ∀ e ∈ edgesIn E U \ H, ¬ e.IsDiag := fun e he =>
        hloop e (edgesIn_subset _ _ (Finset.mem_sdiff.1 he).1)
      have hclique : edgesIn E U \ H ⊆ cliqueEdges U :=
        (Finset.sdiff_subset).trans (edgesIn_subset_cliqueEdges hloop)
      -- even degrees
      have hevU : EvenDegrees (edgesIn E U \ H) := by
        rw [← hEU U hU]
        intro x
        by_cases hxU : x ∈ U
        · have hfil : edeg (edgesIn (E \ (crossParts E Pp ∪ H)) U) x
              = edeg (E \ (crossParts E Pp ∪ H)) x := by
            unfold edeg
            congr 1
            refine Finset.Subset.antisymm (Finset.filter_subset_filter _ (edgesIn_subset _ _)) ?_
            intro e he
            rw [Finset.mem_filter] at he ⊢
            refine ⟨mem_edgesIn.2 ⟨he.1, ?_⟩, he.2⟩
            have he' := he.1
            rw [Finset.mem_sdiff] at he'
            have hncross : e ∉ crossParts E Pp := fun hc => he'.2 (Finset.mem_union_left _ hc)
            have hex : ∃ W ∈ Pp, ∀ v ∈ e, v ∈ W := by
              by_contra hcon
              exact hncross (mem_crossParts.2 ⟨he'.1, hcon⟩)
            obtain ⟨W, hW, hsub⟩ := hex
            have hxW : x ∈ W := hsub x he.2
            have hWU : W = U := by
              by_contra hne
              exact (Finset.disjoint_left.1 (hpart.pairwise_disjoint W hW U hU hne)) hxW hxU
            rw [← hWU]
            exact hsub
          rw [hfil]
          exact hevG' x
        · have hzero : edeg (edgesIn (E \ (crossParts E Pp ∪ H)) U) x = 0 := by
            unfold edeg
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro e he hxe
            exact hxU ((mem_edgesIn.1 he).2 x hxe)
          rw [hzero]
          exact ⟨0, rfl⟩
      -- the partition sequence survives
      have hseqU : PartSeq k (δ + ε) δ ε m rest Pl (edgesIn E U \ H) U := by
        refine PartSeq.sdiff_head (hchild U hU) hHdeg ?_ ?_
        · intro W hW
          rw [← hQdef] at hW
          have hWU : W ⊆ U := (mem_restrictParts.1 hW).2
          have hU1 : (S.card : ℝ) / (k : ℝ) - 1 ≤ (U.card : ℝ) := hpartsize U hU
          have hW1 : (U.card : ℝ) / (k : ℝ) - 1 ≤ (W.card : ℝ) := by
            refine le_trans (sub_one_le_cast_div U.card k hk) ?_
            exact_mod_cast (hQpart U hU).size_lower W hW
          have hstep : ((S.card : ℝ) / (k : ℝ) - 1) / (k : ℝ) ≤ (U.card : ℝ) / (k : ℝ) := by
            gcongr
          have he1 : ((S.card : ℝ) / (k : ℝ) - 1) / (k : ℝ)
              = (S.card : ℝ) / (k : ℝ) ^ 2 - 1 / (k : ℝ) := by
            field_simp
            try ring
          have hWs : (S.card : ℝ) / (k : ℝ) ^ 2 - 2 ≤ (W.card : ℝ) := by
            rw [he1] at hstep
            linarith only [hinvk, hW1, hstep]
          have h3k := (hgap _ hcardSR).2
          have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
          have hSk : 3 ≤ (S.card : ℝ) / (k : ℝ) ^ 2 := by
            rw [le_div_iff₀ hk2]
            linarith only [h3k]
          have hmid : (ε / 6) * (S.card : ℝ) / (2 * (k : ℝ) ^ 2)
              ≤ ε * ((S.card : ℝ) / (k : ℝ) ^ 2 - 2) := by
            have hdiv : (ε / 6) * (S.card : ℝ) / (2 * (k : ℝ) ^ 2)
                = (ε / 12) * ((S.card : ℝ) / (k : ℝ) ^ 2) := by
              field_simp
              try ring
            rw [hdiv]
            nlinarith only [hSk, hε]
          have hlast : ε * ((S.card : ℝ) / (k : ℝ) ^ 2 - 2) ≤ ε * (W.card : ℝ) :=
            mul_le_mul_of_nonneg_left hWs (le_of_lt hε)
          have hdd : (δ + 2 * ε) - (δ + ε) = ε := by ring
          rw [hdd]
          linarith only [hmid, hlast]
        · intro W hW
          rw [← hQdef] at hW
          have hWU : W ⊆ U := (mem_restrictParts.1 hW).2
          rw [edgesIn_edgesIn E hWU]
          exact Finset.disjoint_left.2 fun e heH heW =>
            (Finset.disjoint_left.1 hHG₀) heH (hG₀mem U hU W hW heW)
      exact ih Pl (edgesIn E U \ H) U hloopU hclique hevU hseqU
    choose! f hf1 hf2 using hmain
    have hfsub : ∀ U ∈ Pp, f U ⊆ edgesIn E U \ H := by
      intro U hU e he
      exact (mem_insideParts.1 (hf1 U hU he)).1
    refine ⟨Pp.biUnion f, ?_, ?_⟩
    · -- the leftover lies inside the parts of the last partition
      intro e he
      obtain ⟨U, hU, hfe⟩ := Finset.mem_biUnion.1 he
      obtain ⟨heU, W, hW, hsub⟩ := mem_insideParts.1 (hf1 U hU hfe)
      have hUS : U ⊆ S := hpart.subset_of_mem hU
      have heE : e ∈ E := edgesIn_subset _ _ (Finset.mem_sdiff.1 heU).1
      refine mem_insideParts.2 ⟨heE, W, ?_, hsub⟩
      exact mem_restrictParts.2 ⟨(mem_restrictParts.1 hW).1,
        (mem_restrictParts.1 hW).2.trans hUS⟩
    · -- the decomposition
      have hsplit : E \ Pp.biUnion f
          = (crossParts E Pp ∪ H) ∪ Pp.biUnion (fun U => (edgesIn E U \ H) \ f U) := by
        ext e
        constructor
        · intro he
          rw [Finset.mem_sdiff] at he
          obtain ⟨heE, hnot⟩ := he
          by_cases hc : e ∈ crossParts E Pp
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
          · have hins : e ∈ insideParts E Pp := by
              have := crossParts_union_insideParts E Pp
              rw [← this] at heE
              rcases Finset.mem_union.1 heE with h | h
              · exact absurd h hc
              · exact h
            by_cases hH : e ∈ H
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ hH)
            · obtain ⟨heE', U, hU, hsub⟩ := mem_insideParts.1 hins
              refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨U, hU, ?_⟩)
              refine Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨mem_edgesIn.2 ⟨heE', hsub⟩, hH⟩, ?_⟩
              intro hf
              exact hnot (Finset.mem_biUnion.2 ⟨U, hU, hf⟩)
        · intro he
          rcases Finset.mem_union.1 he with h | h
          · rcases Finset.mem_union.1 h with hc | hH
            · refine Finset.mem_sdiff.2 ⟨crossParts_subset _ _ hc, ?_⟩
              intro hb
              obtain ⟨U, hU, hfU⟩ := Finset.mem_biUnion.1 hb
              have := (Finset.mem_sdiff.1 (hfsub U hU hfU)).1
              exact (Finset.disjoint_left.1 (disjoint_edgesIn_crossParts hU)) this hc
            · refine Finset.mem_sdiff.2 ⟨hHE hH, ?_⟩
              intro hb
              obtain ⟨U, hU, hfU⟩ := Finset.mem_biUnion.1 hb
              exact (Finset.mem_sdiff.1 (hfsub U hU hfU)).2 hH
          · obtain ⟨U, hU, hfU⟩ := Finset.mem_biUnion.1 h
            obtain ⟨hmem, hnf⟩ := Finset.mem_sdiff.1 hfU
            refine Finset.mem_sdiff.2 ⟨edgesIn_subset _ _ (Finset.mem_sdiff.1 hmem).1, ?_⟩
            intro hb
            obtain ⟨U', hU', hfU'⟩ := Finset.mem_biUnion.1 hb
            by_cases hUU' : U = U'
            · exact hnf (hUU' ▸ hfU')
            · have h1 := (Finset.mem_sdiff.1 hmem).1
              have h2 := (Finset.mem_sdiff.1 (hfsub U' hU' hfU')).1
              exact (Finset.disjoint_left.1
                (disjoint_edgesIn (hpart.pairwise_disjoint U hU U' hU' hUU'))) h1 h2
      rw [hsplit]
      refine TriDecomp.union ?_ hHdec (TriDecomp.biUnion (fun U hU => hf2 U hU) ?_)
      · refine Finset.disjoint_left.2 ?_
        intro e he hb
        obtain ⟨U, hU, hfU⟩ := Finset.mem_biUnion.1 hb
        obtain ⟨hmem, -⟩ := Finset.mem_sdiff.1 hfU
        rcases Finset.mem_union.1 he with hc | hH
        · exact (Finset.disjoint_left.1 (disjoint_edgesIn_crossParts hU))
            (Finset.mem_sdiff.1 hmem).1 hc
        · exact (Finset.mem_sdiff.1 hmem).2 hH
      · intro U hU U' hU' hne
        refine Finset.disjoint_left.2 fun e he he' => ?_
        have h1 := (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 he).1).1
        have h2 := (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 he').1).1
        exact (Finset.disjoint_left.1
          (disjoint_edgesIn (hpart.pairwise_disjoint U hU U' hU' hne))) h1 h2

/-- The threshold needed by the iteration: a single `N` beyond the `n₀` of Lemma 10.12 for which
both size estimates hold. -/
theorem exists_iteration_threshold (k : ℕ) (ε : ℝ) (hk : 0 < k) (hε : 0 < ε)
    (hkε : 1 / (k : ℝ) ≤ ε / 8) (n₀ : ℕ) :
    ∃ N : ℕ, n₀ ≤ N ∧ ∀ s : ℝ, (N : ℝ) ≤ s →
      s / (k : ℝ) ^ 2 + 2 ≤ (ε / 2) * (s / (k : ℝ) - 1) ∧ 3 * (k : ℝ) ^ 2 ≤ s := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set A : ℝ := (8 * (k : ℝ) / (3 * ε)) * (2 + ε / 2) with hA
  refine ⟨max n₀ (max ⌈A⌉₊ (3 * k ^ 2)), le_max_left _ _, fun s hs => ?_⟩
  have hs1 : (⌈A⌉₊ : ℝ) ≤ s := by
    refine le_trans ?_ hs
    exact_mod_cast le_trans (le_max_left _ _) (le_max_right n₀ _)
  have hs2 : ((3 * k ^ 2 : ℕ) : ℝ) ≤ s := by
    refine le_trans ?_ hs
    exact_mod_cast le_trans (le_max_right _ _) (le_max_right n₀ _)
  have hAs : A ≤ s := le_trans (Nat.le_ceil A) hs1
  have h3k : 3 * (k : ℝ) ^ 2 ≤ s := by
    refine le_trans ?_ hs2
    push_cast
    linarith only []
  refine ⟨?_, h3k⟩
  have hspos : (0 : ℝ) ≤ s := by nlinarith [sq_nonneg (k : ℝ)]
  -- `s/k² = (1/k)(s/k) ≤ (ε/8)(s/k)`
  have hsk : (0 : ℝ) ≤ s / (k : ℝ) := div_nonneg hspos (le_of_lt hkR)
  have hsplit : s / (k : ℝ) ^ 2 = (1 / (k : ℝ)) * (s / (k : ℝ)) := by
    field_simp
    try ring
  have h1 : s / (k : ℝ) ^ 2 ≤ (ε / 8) * (s / (k : ℝ)) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hkε hsk
  -- `s ≥ A` gives `(3ε/8)(s/k) ≥ 2 + ε/2`
  have h2 : 2 + ε / 2 ≤ (3 * ε / 8) * (s / (k : ℝ)) := by
    have hA' : (8 * (k : ℝ) / (3 * ε)) * (2 + ε / 2) ≤ s := hAs
    rw [← sub_nonneg]
    have hkey : (3 * ε / 8) * (s / (k : ℝ)) - (2 + ε / 2)
        = (3 * ε / (8 * (k : ℝ))) * (s - (8 * (k : ℝ) / (3 * ε)) * (2 + ε / 2)) := by
      field_simp
      try ring
    rw [hkey]
    have : (0 : ℝ) ≤ s - (8 * (k : ℝ) / (3 * ε)) * (2 + ε / 2) := by linarith only [hA']
    positivity
  linarith only [h1, h2]

/-- **BKLO Lemma 10.13 for `r = 2`** (which immediately implies Lemma 10.1).

*Let `r, f, m, k, ℓ ∈ ℕ` and let `ε, η > 0` with `1/m ≪ η ≪ 1/k ≪ ε, 1/r, 1/f`.  Let `F` be an
`r`-regular graph on `f` vertices and let `G` be an `r`-divisible graph.  Let
`δ := max{δ_F^η, 1 - 1/(r+1)}`.  Suppose that `P₁, …, P_ℓ` is a sequence of partitions of `V(G)`
such that (i) `P₁` is a `(k, δ+ε)`-partition for `G`; (ii) for each `2 ≤ i ≤ ℓ` and each
`V ∈ P_{i-1}`, `P_i[V]` is a `(k, δ+2ε)`-partition for `G[V]`; (iii) each `V ∈ P_ℓ` has size `m-1`
or `m`.  Then there exists a subgraph `H*` of `⋃_{V ∈ P_ℓ} G[V]` such that `G - H*` has an
`F`-decomposition.*

The hierarchy `1/m ≪ 1/k ≪ ε` is transcribed as: `1/k ≤ ε/8`, and `m` at least a threshold `m₀`
(which depends on `k`, `ε` and the `n₀` of Lemma 10.12). -/
theorem lemma_10_13_K3 {δ ε : ℝ} {k : ℕ} (hk : 0 < k) (hε : 0 < ε) (hkε : 1 / (k : ℝ) ≤ ε / 8)
    (h12 : Lemma1012K3 δ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ {V : Type} [DecidableEq V] (L : List (Finset (Finset V))) (Pl : Finset (Finset V))
        (E : Finset (Sym2 V)) (S : Finset V),
        (∀ e ∈ E, ¬ e.IsDiag) → E ⊆ cliqueEdges S → EvenDegrees E →
        PartSeq k (δ + ε) δ ε m L Pl E S →
        ∃ Hstar : Finset (Sym2 V), Hstar ⊆ insideParts E (restrictParts Pl S) ∧
          TriDecomp (E \ Hstar) := by
  obtain ⟨n₀, hn₀⟩ := h12 k (ε / 6) hk (by linarith)
  obtain ⟨N, hNn₀, hgap⟩ := exists_iteration_threshold k ε hk hε hkε n₀
  refine ⟨N + 1, fun m hm V _ L Pl E S hloop hES hev hseq => ?_⟩
  refine lemma_10_13_aux (N := N) hk hε ?_ hgap hm L Pl E S hloop hES hev hseq
  intro E' G₀ S' P hcard hloop' hES' hev' hG₀ hpart
  exact hn₀ E' G₀ S' P (le_trans hNn₀ hcard) hloop' hES' hev' hG₀ hpart

/-- **The "in particular" of BKLO Lemma 10.1**: if `G` is `F`-divisible (here: triangle-divisible),
then so is the remainder `H*`. -/
theorem triDivisible_remainder {E Hstar : Finset (Sym2 V)} (hsub : Hstar ⊆ E)
    (hE : TriDivisible E) (hdec : TriDecomp (E \ Hstar)) : TriDivisible Hstar := by
  have h1 : TriDivisible (E \ (E \ Hstar)) :=
    TriDivisible.sdiff (Finset.sdiff_subset) hE hdec.triDivisible
  have h2 : E \ (E \ Hstar) = Hstar := by
    ext e
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨he, h⟩
      by_contra hH
      exact h ⟨he, hH⟩
    · intro hH
      exact ⟨hsub hH, fun hc => hc.2 hH⟩
  rwa [h2] at h1

end BKLO
