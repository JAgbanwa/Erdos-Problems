/-
# BKLO §10.13 — the vortex: a partition sequence with CONSTANT-size bottom cells

`BKLO.exists_partSeq_dense` (`BKLO/PartSeqDenseProof.lean`) produces a *one-level* partition
sequence, whose parts have `≈ |S|/k = Θ(n)` vertices.  The §8 absorber, however, can only be run on
parts of **bounded** size (the within-a-part counting obstruction of
`BKLO/AbsorberPartsInterface.lean`), so the §10 remainder must be confined to cells of constant
size.  That is what BKLO's *vortex* does: a nested sequence of partitions
`P₁ ≻ P₂ ≻ … ≻ P_ℓ` of `S`, of depth `ℓ ≈ log_k(n)`, whose bottom cells have `O(1)` vertices.

The obstruction to iterating `BKLO.exists_kDeltaPartition_dense` naively is that it degrades the
density by `2ε` per level, while only `O(1)` levels' worth of density is available.  The repair —
this is the quantitative heart of the vortex — is that the density loss of a *random* refinement is
not a fixed `2ε`, but `2ε_j` where `ε_j` may be taken as small as the sampling threshold
`131072 k⁶ / ε_j⁴ < (cell size)` allows.  Since cell sizes grow by a factor `k` as one moves up the
vortex, the affordable `ε_j` *shrinks geometrically* going up, and the total loss
`∑_j 2 ε_j = O(ε₀)` is dominated by the bottom level.  Choosing the bottom cell size
`≈ 131072 k⁶/ε₀⁴ = O(1)` therefore keeps the total density loss below `ε` no matter how deep the
vortex is.

Contents:

* `BKLO.exists_kDeltaPartition_dense_explicit` — the `(k, δ)`-partition lemma with an *explicit*
  size threshold and the density parameter quantified *inside*, so that it can be applied with a
  different `ε_j` at every level of the vortex;
* `BKLO.GoodChain` — a nested chain of global level-partitions, and
  `BKLO.partSeq_of_goodChain` — such a chain is a `BKLO.PartSeq`;
* `BKLO.vortexBuild` — the recursion that builds the chain, maintaining the density on every core;
* `BKLO.exists_partSeq_dense_bounded` — the vortex: a partition sequence for a dense graph whose
  bottom cells have constant size.

Everything here is `sorry`-free.
-/
import BKLO.PartSeqDenseProof
import Mathlib.Data.Finset.Functor

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The `(k, δ)`-partition lemma with an explicit threshold -/

/-- The size condition of the sampling lemma, in real arithmetic (a copy of the corresponding
private lemma of `BKLO/PartSeqDenseProof.lean`). -/
private theorem sampling_threshold_arith' {ε θ nR cR kR : ℝ} (hε0 : 0 < ε)
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

set_option maxHeartbeats 1000000 in
/-- **A `(k, c - 2ε)`-partition exists in a graph of minimum degree `c|S|`.**

This is `BKLO.exists_kDeltaPartition_dense` with two changes, both needed to run it down a vortex:
the size threshold is *explicit* (`|S| > 131072k⁶/ε⁴` and `|S| ≥ 2k+1`), and the density `c` is
quantified after it, so that a *single* statement covers all the densities occurring at the
different levels.  The density loss is `2ε`, and `ε` may be taken as small as the size of the
current cell allows. -/
theorem exists_kDeltaPartition_dense_explicit {ε c : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {k : ℕ}
    (hk : 2 ≤ k) (E : Finset (Sym2 V)) (S : Finset V)
    (hn1 : 2 * k + 1 ≤ S.card) (hn2 : 131072 * (k : ℝ) ^ 6 / ε ^ 4 < (S.card : ℝ))
    (hES : E ⊆ cliqueEdges S) (hdeg : ∀ v ∈ S, c * (S.card : ℝ) ≤ (edeg E v : ℝ)) :
    ∃ P : Finset (Finset V), IsKDeltaPartition k (c - 2 * ε) P E S ∧ ∀ W ∈ P, W ⊆ S := by
  classical
  set δ : ℝ := c - 3 * ε with hδdef
  have hdeg' : ∀ v ∈ S, (δ + 3 * ε) * (S.card : ℝ) ≤ (edeg E v : ℝ) := by
    intro v hv
    have := hdeg v hv
    have hcc : δ + 3 * ε = c := by rw [hδdef]; ring
    rw [hcc]; exact this
  have hgoal : δ + ε = c - 2 * ε := by rw [hδdef]; ring
  rw [← hgoal]
  clear_value δ
  clear hdeg hδdef
  have hk0 : 0 < k := by omega
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set n : ℕ := S.card with hndef
  have hn2k : 2 * k + 1 ≤ n := hn1
  have hn0 : 0 < n := by omega
  have hnR0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hnbig : 131072 * (k : ℝ) ^ 6 / ε ^ 4 < (n : ℝ) := hn2
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
  have hqn : (n : ℝ) ≤ 2 * (k : ℝ) * (q : ℝ) := by
    have h1 : n ≤ 2 * (k * q) := by omega
    have h2 : ((n : ℕ) : ℝ) ≤ ((2 * (k * q) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hLthr : ∀ c ∈ L, 2 * ((S.card : ℝ)) < (θ ^ 2 * (c : ℝ) / 32) ^ 2 := by
    intro c hc
    have hcq : (q : ℝ) ≤ (c : ℝ) := by exact_mod_cast (hLmem c hc).1
    refine sampling_threshold_arith' hε0 hkR hθdef hnR0 ?_ hnbig
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
  · intro W hW W' hW' hne
    rw [hmemP] at hW hW'
    exact hpair.forall (fun _ _ h => h.symm) hW hW' hne
  · ext a
    simp only [Finset.mem_biUnion, id]
    constructor
    · rintro ⟨W, hW, haW⟩
      rw [hmemP] at hW
      exact hsub W hW haW
    · intro ha
      obtain ⟨Q, hQ, haQ⟩ := hcover a ha
      exact ⟨Q, (hmemP Q).2 hQ, haQ⟩
  · intro W hW
    exact (hPsizes W hW).1
  · intro W hW
    refine (Nat.le_div_iff_mul_le hk0).2 ?_
    rw [hmemP] at hW
    obtain ⟨c, hc, hWc⟩ := card_mem_of_forall₂ hforall W hW
    rw [hWc]
    exact hLupper c hc
  · intro x hx W hW
    have hWS : W ⊆ S := by
      rw [hmemP] at hW; exact hsub W hW
    have hWcard : ((W.card : ℝ)) ≥ (q : ℝ) := by exact_mod_cast (hPsizes W hW).1
    have hbnd := hbound W ((hmemP W).1 hW) x hx
    have hTx : ((nonAdjIn E S x).card : ℝ) ≤ (1 - δ - 3 * ε) * (n : ℝ) := by
      have h1 : degTo E x S + (nonAdjIn E S x).card = n := by
        have h := degTo_add_card_nonAdjIn (E := E) (S := S) (W := S) (Finset.Subset.refl S) x
        have h2 : nonAdjIn E S x ∩ S = nonAdjIn E S x :=
          Finset.inter_eq_left.2 nonAdjIn_subset
        rw [h2] at h
        exact h
      have h2 : edeg E x ≤ degTo E x S := edeg_le_degTo hES x
      have h3 : (δ + 3 * ε) * (n : ℝ) ≤ (edeg E x : ℝ) := hdeg' x hx
      have h4 : ((edeg E x : ℕ) : ℝ) ≤ ((degTo E x S : ℕ) : ℝ) := by exact_mod_cast h2
      have h5 : ((degTo E x S : ℕ) : ℝ) + ((nonAdjIn E S x).card : ℝ) = (n : ℝ) := by
        exact_mod_cast h1
      linarith
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

/-! ### Degrees inside a cell -/

/-- Inside a cell, the degree of the induced graph is the degree into the cell. -/
theorem degTo_le_edeg_edgesIn_cell {E : Finset (Sym2 V)} {W : Finset V} {x : V} (hx : x ∈ W) :
    degTo E x W ≤ edeg (edgesIn E W) x := by
  classical
  have hset : W.filter (fun y => s(x, y) ∈ edgesIn E W) = nbhdIn E x W := by
    ext y
    simp only [Finset.mem_filter, mem_nbhdIn, mem_edgesIn]
    constructor
    · rintro ⟨hy, he, _⟩; exact ⟨hy, he⟩
    · rintro ⟨hy, he⟩
      refine ⟨hy, he, ?_⟩
      intro v hv
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact hx
      · exact hy
  have := card_filter_edge_le_edeg (edgesIn E W) x W
  rwa [hset] at this

/-- Inside a cell, the degree into the cell is at most the degree of the clique-restricted graph. -/
theorem degTo_le_edeg_inter_cliqueEdges {E : Finset (Sym2 V)} {P : Finset V} {v : V} (hv : v ∈ P)
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) : degTo E v P ≤ edeg (E ∩ cliqueEdges P) v := by
  classical
  have hset : P.filter (fun y => s(v, y) ∈ E ∩ cliqueEdges P) = nbhdIn E v P := by
    ext y
    simp only [Finset.mem_filter, mem_nbhdIn, Finset.mem_inter]
    constructor
    · rintro ⟨hy, he, _⟩; exact ⟨hy, he⟩
    · rintro ⟨hy, he⟩
      refine ⟨hy, he, mem_cliqueEdgesV.2 ⟨?_, hloop _ he⟩⟩
      intro z hz
      rcases Sym2.mem_iff.1 hz with rfl | rfl
      · exact hv
      · exact hy
  have := card_filter_edge_le_edeg (E ∩ cliqueEdges P) v P
  rwa [hset] at this

/-- A graph spanned by `S` is its own restriction to `S`. -/
theorem edgesIn_self {E : Finset (Sym2 V)} {S : Finset V} (hE : E ⊆ cliqueEdges S) :
    edgesIn E S = E := by
  refine Finset.Subset.antisymm (edgesIn_subset E S) fun e he => ?_
  exact mem_edgesIn.2 ⟨he, (mem_cliqueEdgesV.1 (hE he)).1⟩

/-! ### Chains of nested partitions -/

/-- **A nested chain of global level-partitions.**  `GoodChain k d m E₀ L Pl` says that, for each
consecutive pair of levels of the list `L ++ [Pl]`, every cell `W` of the earlier level is split by
the later level into a `(k, d)`-partition of the graph induced on `W`, that every cell of every
level has at least `m-1` vertices, and that the cells of the last level `Pl` have `m-1` or `m`
vertices.

Unlike `BKLO.PartSeq`, this is a statement about *global* families of cells, which is what the
vortex recursion produces: it never has to merge the branches of the vortex tree.  It also carries
the density `d` as an explicit parameter, which is what lets a chain be *degraded* by deleting a
low-degree graph (`BKLO.GoodChain.sdiff`) -- the step that makes room for an absorber. -/
def GoodChain (k : ℕ) (d : ℝ) (m : ℕ) (E₀ : Finset (Sym2 V)) :
    List (Finset (Finset V)) → Finset (Finset V) → Prop
  | [], Pl => ∀ W ∈ Pl, m ≤ W.card + 1 ∧ W.card ≤ m
  | (P :: rest), Pl =>
      (∀ W ∈ P, m ≤ W.card + 1 ∧
        IsKDeltaPartition k d (restrictParts (headParts rest Pl) W) (edgesIn E₀ W) W) ∧
      GoodChain k d m E₀ rest Pl

/-- **A chain of nested partitions is a partition sequence.** -/
theorem partSeq_of_goodChain {k m : ℕ} {δ ε : ℝ} {E₀ : Finset (Sym2 V)} :
    ∀ (L : List (Finset (Finset V))) (Pl : Finset (Finset V)) (c : ℝ) (E : Finset (Sym2 V))
      (S : Finset V), GoodChain k (δ + 2 * ε) m E₀ L Pl →
      IsKDeltaPartition k c (restrictParts (headParts L Pl) S) E S →
      (∀ W ∈ restrictParts (headParts L Pl) S, edgesIn E W = edgesIn E₀ W) →
      PartSeq k c δ ε m L Pl E S := by
  intro L
  induction L with
  | nil =>
    intro Pl c E S hgc hhead _
    refine ⟨hhead, fun W hW => hgc W (mem_restrictParts.1 hW).1⟩
  | cons P rest ih =>
    intro Pl c E S hgc hhead hcompat
    refine ⟨hhead, fun W hW => ?_⟩
    have hWP : W ∈ P := (mem_restrictParts.1 hW).1
    have hWS : W ⊆ S := (mem_restrictParts.1 hW).2
    have hEW : edgesIn E W = edgesIn E₀ W := hcompat W hW
    refine ih Pl (δ + 2 * ε) (edgesIn E W) W hgc.2 ?_ ?_
    · rw [hEW]; exact (hgc.1 W hWP).2
    · intro W' hW'
      have hW'W : W' ⊆ W := (mem_restrictParts.1 hW').2
      rw [edgesIn_edgesIn _ hW'W, ← edgesIn_edgesIn E hW'W, hEW, edgesIn_edgesIn _ hW'W]

/-! ### One step of the vortex -/

set_option maxHeartbeats 1000000 in
/-- **One level of the vortex.**  Every cell of the current level `Cur` (all of size `a` or `a+1`,
pairwise disjoint, and of internal minimum degree `c` times its size) is split into `k` cells of
size `⌊a/k⌋` or `⌊a/k⌋ + 1`, in such a way that the internal minimum degree of every new cell is
still `c - 2ε_j` times its size.

This is the *density-maintenance* step: the loss `2ε_j` is not a fixed proportion of the density,
but may be taken as small as the size of the current cells allows (`131072k⁶/ε_j⁴ < a`). -/
theorem vortex_step {k : ℕ} (hk : 2 ≤ k) {ej c : ℝ} (hej0 : 0 < ej) (hej1 : ej ≤ 1)
    {E₀ : Finset (Sym2 V)} (hloop : ∀ e ∈ E₀, ¬ e.IsDiag) {Cur : Finset (Finset V)} {a : ℕ}
    (hthr1 : 2 * k + 1 ≤ a) (hthr2 : 131072 * (k : ℝ) ^ 6 / ej ^ 4 < (a : ℝ))
    (hsize : ∀ W ∈ Cur, a ≤ W.card ∧ W.card ≤ a + 1)
    (hdisj : ∀ W ∈ Cur, ∀ W' ∈ Cur, W ≠ W' → Disjoint W W')
    (hdens : ∀ W ∈ Cur, ∀ x ∈ W, c * (W.card : ℝ) ≤ (degTo E₀ x W : ℝ)) :
    ∃ Next : Finset (Finset V),
      (∀ W ∈ Cur, IsKDeltaPartition k (c - 2 * ej) (restrictParts Next W) (edgesIn E₀ W) W) ∧
      (∀ X ∈ Next, ∃ W ∈ Cur, X ⊆ W) ∧
      (∀ W ∈ Cur, ∀ x ∈ W, ∃ X ∈ Next, x ∈ X) ∧
      (∀ X ∈ Next, ∀ X' ∈ Next, X ≠ X' → Disjoint X X') ∧
      (∀ X ∈ Next, a / k ≤ X.card ∧ X.card ≤ a / k + 1) ∧
      (∀ X ∈ Next, ∀ x ∈ X, (c - 2 * ej) * (X.card : ℝ) ≤ (degTo E₀ x X : ℝ)) := by
  classical
  have hk0 : 0 < k := by omega
  have hak : 2 ≤ a / k := (Nat.le_div_iff_mul_le hk0).2 (by omega)
  -- the partition of each current cell
  have hex : ∀ W ∈ Cur, ∃ Q : Finset (Finset V),
      IsKDeltaPartition k (c - 2 * ej) Q (edgesIn E₀ W) W ∧ ∀ X ∈ Q, X ⊆ W := by
    intro W hW
    have h1 : 2 * k + 1 ≤ W.card := le_trans hthr1 (hsize W hW).1
    have h2 : 131072 * (k : ℝ) ^ 6 / ej ^ 4 < (W.card : ℝ) := by
      refine lt_of_lt_of_le hthr2 ?_
      exact_mod_cast (hsize W hW).1
    refine exists_kDeltaPartition_dense_explicit hej0 hej1 hk (edgesIn E₀ W) W h1 h2
      (edgesIn_subset_cliqueEdges hloop) ?_
    intro v hv
    refine le_trans (hdens W hW v hv) ?_
    exact_mod_cast degTo_le_edeg_edgesIn_cell hv
  choose! f hf1 hf2 using hex
  -- sizes of the new cells
  have hcards : ∀ W ∈ Cur, ∀ X ∈ f W, a / k ≤ X.card ∧ X.card ≤ a / k + 1 := by
    intro W hW X hX
    have hlow : W.card / k ≤ X.card := (hf1 W hW).1.size_lower X hX
    have hup : X.card ≤ (W.card + k - 1) / k := (hf1 W hW).1.size_upper X hX
    have h1 : a / k ≤ W.card / k := Nat.div_le_div_right (hsize W hW).1
    have h2 : (W.card + k - 1) / k ≤ (a + k) / k := by
      refine Nat.div_le_div_right ?_
      have := (hsize W hW).2
      omega
    have h3 : (a + k) / k = a / k + 1 := Nat.add_div_right a hk0
    omega
  have hXne : ∀ W ∈ Cur, ∀ X ∈ f W, X.Nonempty := by
    intro W hW X hX
    exact Finset.card_pos.1 (by have := (hcards W hW X hX).1; omega)
  -- the new level
  set Next : Finset (Finset V) := Cur.biUnion f with hNext
  have hmemNext : ∀ X, X ∈ Next ↔ ∃ W ∈ Cur, X ∈ f W := by
    intro X; rw [hNext, Finset.mem_biUnion]
  have hres : ∀ W ∈ Cur, restrictParts Next W = f W := by
    intro W hW
    ext X
    rw [mem_restrictParts]
    constructor
    · rintro ⟨hX, hXW⟩
      obtain ⟨W', hW', hXW'⟩ := (hmemNext X).1 hX
      obtain ⟨x, hx⟩ := hXne W' hW' X hXW'
      by_cases hWW : W = W'
      · rwa [hWW]
      · exact absurd (Finset.disjoint_left.1 (hdisj W hW W' hW' hWW) (hXW hx))
          (not_not.2 (hf2 W' hW' X hXW' hx))
    · intro hX
      exact ⟨(hmemNext X).2 ⟨W, hW, hX⟩, hf2 W hW X hX⟩
  refine ⟨Next, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W hW
    rw [hres W hW]
    exact hf1 W hW
  · intro X hX
    obtain ⟨W, hW, hXW⟩ := (hmemNext X).1 hX
    exact ⟨W, hW, hf2 W hW X hXW⟩
  · intro W hW x hx
    have hcover := (hf1 W hW).1.cover
    have : x ∈ (f W).biUnion id := by rw [hcover]; exact hx
    obtain ⟨X, hX, hxX⟩ := Finset.mem_biUnion.1 this
    exact ⟨X, (hmemNext X).2 ⟨W, hW, hX⟩, hxX⟩
  · intro X hX X' hX' hne
    obtain ⟨W, hW, hXW⟩ := (hmemNext X).1 hX
    obtain ⟨W', hW', hXW'⟩ := (hmemNext X').1 hX'
    by_cases hWW : W = W'
    · subst hWW
      exact (hf1 W hW).1.pairwise_disjoint X hXW X' hXW' hne
    · exact Finset.disjoint_of_subset_left (hf2 W hW X hXW)
        (Finset.disjoint_of_subset_right (hf2 W' hW' X' hXW') (hdisj W hW W' hW' hWW))
  · intro X hX
    obtain ⟨W, hW, hXW⟩ := (hmemNext X).1 hX
    exact hcards W hW X hXW
  · intro X hX x hx
    obtain ⟨W, hW, hXW⟩ := (hmemNext X).1 hX
    have hxW : x ∈ W := hf2 W hW X hXW hx
    have h := (hf1 W hW).2 x hxW X hXW
    refine le_trans h ?_
    exact_mod_cast degTo_mono_left (edgesIn_subset E₀ W) x X

/-- The cells of the last level of a `BKLO.GoodChain` have `m-1` or `m` vertices. -/
theorem GoodChain.sizes {k m : ℕ} {d : ℝ} {E₀ : Finset (Sym2 V)} :
    ∀ (L : List (Finset (Finset V))) (Pl : Finset (Finset V)), GoodChain k d m E₀ L Pl →
      ∀ W ∈ Pl, m ≤ W.card + 1 ∧ W.card ≤ m := by
  intro L
  induction L with
  | nil => intro Pl h; exact h
  | cons P rest ih => intro Pl h; exact ih Pl h.2

/-- Every cell of the first level of a `BKLO.GoodChain` has at least `m-1` vertices. -/
theorem GoodChain.head_sizes {k m : ℕ} {d : ℝ} {E₀ : Finset (Sym2 V)}
    (L : List (Finset (Finset V))) (Pl : Finset (Finset V)) (h : GoodChain k d m E₀ L Pl) :
    ∀ W ∈ headParts L Pl, m ≤ W.card + 1 := by
  cases L with
  | nil => intro W hW; exact (h W hW).1
  | cons P rest => intro W hW; exact (h.1 W hW).1

/-- **A chain survives the deletion of a low-degree graph**, at the price of `(d - d')` of density.
Since every cell of every level of the chain has at least `m-1` vertices, a *global* degree bound
`Δ(H) ≤ c ≤ (d-d')(m-1)` suffices at every level at once -- this is what makes the vortex
compatible with reserving an absorber of bounded degree. -/
theorem GoodChain.sdiff {k m : ℕ} {d d' c : ℝ} {E₀ H : Finset (Sym2 V)}
    (hdd : d' ≤ d) (hH : ∀ v : V, (edeg H v : ℝ) ≤ c) (hc : c ≤ (d - d') * ((m : ℝ) - 1)) :
    ∀ (L : List (Finset (Finset V))) (Pl : Finset (Finset V)), GoodChain k d m E₀ L Pl →
      GoodChain k d' m (E₀ \ H) L Pl := by
  intro L
  induction L with
  | nil => intro Pl h; exact h
  | cons P rest ih =>
    intro Pl h
    refine ⟨fun W hW => ⟨(h.1 W hW).1, ?_⟩, ih Pl h.2⟩
    have hcells : ∀ X ∈ restrictParts (headParts rest Pl) W, c ≤ (d - d') * (X.card : ℝ) := by
      intro X hX
      have hsz : m ≤ X.card + 1 :=
        GoodChain.head_sizes rest Pl h.2 X (mem_restrictParts.1 hX).1
      have hszR : (m : ℝ) - 1 ≤ (X.card : ℝ) := by
        have : ((m : ℝ)) ≤ (X.card : ℝ) + 1 := by exact_mod_cast hsz
        linarith
      have := mul_le_mul_of_nonneg_left hszR (by linarith : (0:ℝ) ≤ d - d')
      linarith
    have := ((h.1 W hW).2).sdiff hH hcells
    rwa [← edgesIn_sdiff] at this

/-! ### The depth of the vortex -/

/-- The vortex has a well-defined depth: iterating division by `k` from `n` lands exactly once in
the window `[M, kM)`. -/
theorem div_pow_succ_eq (n k l : ℕ) : n / k ^ (l + 1) = n / k / k ^ l := by
  rw [Nat.div_div_eq_div_mul, pow_succ']

theorem exists_vortex_depth (k M : ℕ) (hk : 2 ≤ k) (hM : 1 ≤ M) :
    ∀ n : ℕ, M ≤ n → ∃ l : ℕ, M ≤ n / k ^ l ∧ n / k ^ (l + 1) < M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hsmall : n / k < M
    · exact ⟨0, by simpa using hn, by simpa using hsmall⟩
    · push_neg at hsmall
      have hlt : n / k < n := Nat.div_lt_self (by omega) (by omega)
      obtain ⟨l, h1, h2⟩ := ih (n / k) hlt hsmall
      exact ⟨l + 1, by rwa [div_pow_succ_eq], by rwa [div_pow_succ_eq]⟩

/-! ### The vortex -/

/-- The sampling threshold survives the geometric choice `ε_j = ε₀ 2^{-j}` of the per-level loss,
because the cells grow by a factor `k ≥ 16` as one moves up the vortex. -/
theorem vortex_threshold {k M j : ℕ} {eps0 : ℝ} (hk : 16 ≤ k) (heps0 : 0 < eps0)
    (hM2 : 131072 * (k : ℝ) ^ 6 / eps0 ^ 4 < (M : ℝ)) {a : ℕ} (ha : M * k ^ j ≤ a) :
    131072 * (k : ℝ) ^ 6 / (eps0 * (1 / 2 : ℝ) ^ j) ^ 4 < (a : ℝ) := by
  have heps4 : (0 : ℝ) < eps0 ^ 4 := by positivity
  have hej : (0 : ℝ) < eps0 * (1 / 2 : ℝ) ^ j := by positivity
  have he4 : (eps0 * (1 / 2 : ℝ) ^ j) ^ 4 = eps0 ^ 4 * (1 / 16 : ℝ) ^ j := by
    rw [mul_pow, ← pow_mul, mul_comm j 4, pow_mul]
    norm_num
  have hmul : (16 : ℝ) ^ j * (1 / 16 : ℝ) ^ j = 1 := by
    rw [← mul_pow]; norm_num
  have hbase : 131072 * (k : ℝ) ^ 6 < (M : ℝ) * eps0 ^ 4 := by
    rw [div_lt_iff₀ heps4] at hM2; linarith
  have h16k : (16 : ℝ) ^ j ≤ (k : ℝ) ^ j := by
    refine pow_le_pow_left₀ (by norm_num) ?_ j
    exact_mod_cast hk
  have haR : (M : ℝ) * (k : ℝ) ^ j ≤ (a : ℝ) := by
    have : ((M * k ^ j : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    push_cast at this; linarith
  have hM0 : (0 : ℝ) < (M : ℝ) := by
    have : (0 : ℝ) < 131072 * (k : ℝ) ^ 6 / eps0 ^ 4 := by
      have : (0 : ℝ) < (k : ℝ) := by
        have : (16 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        linarith
      positivity
    linarith
  have hstep : (M : ℝ) * eps0 ^ 4 ≤ (a : ℝ) * (eps0 * (1 / 2 : ℝ) ^ j) ^ 4 := by
    rw [he4]
    have h1 : (M : ℝ) * (16 : ℝ) ^ j ≤ (a : ℝ) := by nlinarith only [h16k, haR, hM0.le]
    have h2 : (0 : ℝ) < eps0 ^ 4 * (1 / 16 : ℝ) ^ j := by positivity
    have h3 := mul_le_mul_of_nonneg_right h1 h2.le
    have h4 : (M : ℝ) * (16 : ℝ) ^ j * (eps0 ^ 4 * (1 / 16 : ℝ) ^ j) = (M : ℝ) * eps0 ^ 4 := by
      calc (M : ℝ) * (16 : ℝ) ^ j * (eps0 ^ 4 * (1 / 16 : ℝ) ^ j)
          = (M : ℝ) * eps0 ^ 4 * ((16 : ℝ) ^ j * (1 / 16 : ℝ) ^ j) := by ring
        _ = (M : ℝ) * eps0 ^ 4 := by rw [hmul, mul_one]
    linarith
  rw [div_lt_iff₀ (by positivity : (0:ℝ) < (eps0 * (1 / 2 : ℝ) ^ j) ^ 4)]
  linarith

set_option maxHeartbeats 1000000 in
/-- **The vortex.**  Starting from a family `Cur` of disjoint cells of size `a` or `a+1`, each of
internal minimum degree `(δ+2ε+t)` times its size, the vortex refines it `j+1` further times, each
time dividing the cell sizes by `k` and losing only `2ε₀ 2^{-i}` of density at the `i`-th level from
the bottom, so that the *total* loss stays below `4ε₀ ≤ t`.  The bottom cells all have `m-1` or `m`
vertices, with `m = ⌊a/k^{j+1}⌋ + 1`, and still have internal minimum degree `(δ+2ε)` times their
size.  The output is a `BKLO.GoodChain`, i.e. a partition sequence (`BKLO.partSeq_of_goodChain`). -/
theorem vortexBuild {k : ℕ} (hk : 16 ≤ k) {d eps0 : ℝ} (heps0 : 0 < eps0) (heps1 : eps0 ≤ 1)
    {M : ℕ} (hM1 : 2 * k + 1 ≤ M) (hM2 : 131072 * (k : ℝ) ^ 6 / eps0 ^ 4 < (M : ℝ))
    {E₀ : Finset (Sym2 V)} (hloop : ∀ e ∈ E₀, ¬ e.IsDiag) :
    ∀ (j a m : ℕ) (t : ℝ) (Cur : Finset (Finset V)),
      M * k ^ j ≤ a → a / k ^ (j + 1) + 1 = m →
      4 * eps0 - 2 * eps0 * (1 / 2 : ℝ) ^ j ≤ t →
      (∀ W ∈ Cur, a ≤ W.card ∧ W.card ≤ a + 1) →
      (∀ W ∈ Cur, ∀ W' ∈ Cur, W ≠ W' → Disjoint W W') →
      (∀ W ∈ Cur, ∀ x ∈ W, (d + t) * (W.card : ℝ) ≤ (degTo E₀ x W : ℝ)) →
      ∃ (L : List (Finset (Finset V))) (Pl : Finset (Finset V)),
        GoodChain k d m E₀ L Pl ∧
        (∀ W ∈ Cur, IsKDeltaPartition k d (restrictParts (headParts L Pl) W) (edgesIn E₀ W) W) ∧
        (∀ X ∈ Pl, ∃ W ∈ Cur, X ⊆ W) ∧
        (∀ W ∈ Cur, ∀ x ∈ W, ∃ X ∈ Pl, x ∈ X) ∧
        (∀ X ∈ Pl, ∀ X' ∈ Pl, X ≠ X' → Disjoint X X') ∧
        (∀ X ∈ Pl, ∀ x ∈ X, d * (X.card : ℝ) ≤ (degTo E₀ x X : ℝ)) := by
  have hk2 : 2 ≤ k := by omega
  have hk0 : 0 < k := by omega
  intro j
  induction j with
  | zero =>
    intro a m t Cur ha hm ht hsize hdisj hdens
    have hpow : (1 / 2 : ℝ) ^ (0 : ℕ) = 1 := pow_zero _
    have hthr1 : 2 * k + 1 ≤ a := by
      have : M ≤ a := by simpa using ha
      omega
    have hthr2 : 131072 * (k : ℝ) ^ 6 / (eps0 * (1 / 2 : ℝ) ^ (0 : ℕ)) ^ 4 < (a : ℝ) :=
      vortex_threshold hk heps0 hM2 ha
    obtain ⟨Next, hpart, hsub, hcover, hdisjN, hcardN, hdensN⟩ :=
      vortex_step (c := d + t) hk2 (by positivity) (by
        rw [hpow, mul_one]; exact heps1) hloop hthr1 hthr2 hsize hdisj hdens
    have hslack : d ≤ d + t - 2 * (eps0 * (1 / 2 : ℝ) ^ (0 : ℕ)) := by
      rw [hpow, mul_one]; rw [hpow, mul_one] at ht; linarith
    refine ⟨[], Next, ?_, ?_, hsub, hcover, hdisjN, ?_⟩
    · intro X hX
      have h := hcardN X hX
      have hmk : a / k ^ (0 + 1) = a / k := by norm_num
      omega
    · intro W hW
      exact (hpart W hW).mono hslack
    · intro X hX x hx
      refine le_trans ?_ (hdensN X hX x hx)
      exact mul_le_mul_of_nonneg_right hslack (Nat.cast_nonneg _)
  | succ j ih =>
    intro a m t Cur ha hm ht hsize hdisj hdens
    set ej : ℝ := eps0 * (1 / 2 : ℝ) ^ (j + 1) with hejdef
    have hej0 : 0 < ej := by rw [hejdef]; positivity
    have hej1 : ej ≤ 1 := by
      rw [hejdef]
      have h1 : (1 / 2 : ℝ) ^ (j + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have h2 : eps0 * (1 / 2 : ℝ) ^ (j + 1) ≤ 1 * 1 :=
        mul_le_mul heps1 h1 (by positivity) zero_le_one
      linarith only [h2]
    have hthr1 : 2 * k + 1 ≤ a := by
      have h1 : M * 1 ≤ M * k ^ (j + 1) :=
        Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ hk0)
      omega
    have hthr2 : 131072 * (k : ℝ) ^ 6 / ej ^ 4 < (a : ℝ) := vortex_threshold hk heps0 hM2 ha
    obtain ⟨Next, hpart, hsub, hcover, hdisjN, hcardN, hdensN⟩ :=
      vortex_step (c := d + t) hk2 hej0 hej1 hloop hthr1 hthr2 hsize hdisj hdens
    -- the surplus left for the levels below
    set t' : ℝ := t - 2 * ej with ht'def
    have hhalf : (1 / 2 : ℝ) ^ (j + 1) = (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) := pow_succ _ _
    have ht' : 4 * eps0 - 2 * eps0 * (1 / 2 : ℝ) ^ j ≤ t' := by
      rw [ht'def, hejdef, hhalf]
      rw [hhalf] at ht
      linarith
    have ht'0 : 0 ≤ t' := by
      have h1 : (0:ℝ) < (1 / 2 : ℝ) ^ j := by positivity
      have h2 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have h3 : 2 * eps0 * (1 / 2 : ℝ) ^ j ≤ 2 * eps0 * 1 :=
        mul_le_mul_of_nonneg_left h2 (by linarith only [heps0])
      linarith only [ht', h3, heps0]
    have hdens' : ∀ X ∈ Next, ∀ x ∈ X, (d + t') * (X.card : ℝ) ≤ (degTo E₀ x X : ℝ) := by
      intro X hX x hx
      have := hdensN X hX x hx
      have heq : d + t - 2 * ej = d + t' := by rw [ht'def]; ring
      rwa [heq] at this
    -- every cell of the next level is at least as large as a bottom cell
    have hmsize : ∀ X ∈ Next, m ≤ X.card + 1 := by
      intro X hX
      have h1 : a / k ≤ X.card := (hcardN X hX).1
      have h2 : a / k ^ (j + 1 + 1) ≤ a / k := by
        refine Nat.div_le_div_left ?_ hk0
        calc k = k ^ 1 := (pow_one k).symm
          _ ≤ k ^ (j + 1 + 1) := Nat.pow_le_pow_right hk0 (by omega)
      omega
    obtain ⟨L', Pl', hgc', hhead', hsub', hcover', hdisj', hdensPl'⟩ :=
      ih (a / k) m t' Next
        ((Nat.le_div_iff_mul_le hk0).2 (by
          have : M * k ^ j * k = M * k ^ (j + 1) := by ring
          omega))
        (by rw [← hm, div_pow_succ_eq a k (j + 1)])
        ht' hcardN hdisjN hdens'
    refine ⟨Next :: L', Pl', ⟨fun W hW => ⟨hmsize W hW, hhead' W hW⟩, hgc'⟩, ?_, ?_, ?_, hdisj',
      hdensPl'⟩
    · intro W hW
      have hslack : d ≤ d + t - 2 * ej := by rw [ht'def] at ht'0; linarith
      exact (hpart W hW).mono hslack
    · intro X hX
      obtain ⟨W, hW, hXW⟩ := hsub' X hX
      obtain ⟨U, hU, hWU⟩ := hsub W hW
      exact ⟨U, hU, hXW.trans hWU⟩
    · intro W hW x hx
      obtain ⟨X, hX, hxX⟩ := hcover W hW x hx
      exact hcover' X hX x hxX

/-! ### The bounded vortex -/

set_option maxHeartbeats 1000000 in
/-- **The vortex of BKLO §10.13, with CONSTANT-size bottom cells.**

For `k ≥ 16`, a maintained density `d`, a budget `ε` and every prescribed `M₁` there are constants
`Mmax, n₀` (independent of the host) such that every graph `E` on a vertex set `S` of size at least
`n₀` with minimum degree `(d+ε)|S|` carries a nested chain of partitions `BKLO.GoodChain k d m E`
whose bottom cells have `m-1` or `m` vertices with `M₁ ≤ m ≤ Mmax`, whose top level is a
`(k, d)`-partition of `S`, and whose bottom cells are pairwise disjoint, cover `S` and have internal
minimum degree `d` times their size.

The density `d` is *maintained*, not degraded per level: the loss at the `i`-th level from the
bottom is only `2ε₀2^{-i}` with `ε₀ = ε/4`, and the bottom cells have constant size
`≈ 131072k⁶/ε₀⁴`. -/
theorem exists_goodChain_dense_bounded {d ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {k : ℕ} (hk : 16 ≤ k)
    (M₁ : ℕ) :
    ∃ Mmax n₀ : ℕ, ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S →
      (∀ v ∈ S, (d + ε) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ (m : ℕ) (L : List (Finset (Finset V))) (Pl : Finset (Finset V)),
        M₁ ≤ m ∧ m ≤ Mmax ∧
        GoodChain k d m E L Pl ∧
        IsKDeltaPartition k d (restrictParts (headParts L Pl) S) E S ∧
        (∀ P ∈ restrictParts Pl S, P ⊆ S) ∧
        (∀ P ∈ restrictParts Pl S, ∀ Q ∈ restrictParts Pl S, P ≠ Q → Disjoint P Q) ∧
        S ⊆ (restrictParts Pl S).biUnion id ∧
        (∀ P ∈ restrictParts Pl S, m - 1 ≤ P.card ∧ P.card ≤ m) ∧
        (∀ P ∈ restrictParts Pl S, ∀ v ∈ P, d * (P.card : ℝ) ≤ (edeg (E ∩ cliqueEdges P) v : ℝ)) ∧
        restrictParts Pl S = Pl := by
  classical
  have hk2 : 2 ≤ k := by omega
  have hk0 : 0 < k := by omega
  set eps0 : ℝ := ε / 4 with heps0def
  have heps0 : 0 < eps0 := by rw [heps0def]; linarith
  have heps1 : eps0 ≤ 1 := by rw [heps0def]; linarith
  set M : ℕ := max (2 * k + 1) (max (⌈131072 * (k : ℝ) ^ 6 / eps0 ^ 4⌉₊ + 1) (k * M₁)) with hMdef
  have hM1 : 2 * k + 1 ≤ M := le_max_left _ _
  have hMceil : ⌈131072 * (k : ℝ) ^ 6 / eps0 ^ 4⌉₊ + 1 ≤ M :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hMk : k * M₁ ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hM2 : 131072 * (k : ℝ) ^ 6 / eps0 ^ 4 < (M : ℝ) := by
    have h1 : 131072 * (k : ℝ) ^ 6 / eps0 ^ 4 ≤ (⌈131072 * (k : ℝ) ^ 6 / eps0 ^ 4⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : ((⌈131072 * (k : ℝ) ^ 6 / eps0 ^ 4⌉₊ + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast hMceil
    push_cast at h2
    linarith
  refine ⟨M, M, ?_⟩
  intro V _ E S hcard hES hdeg
  have hloop : ∀ e ∈ E, ¬ e.IsDiag := fun e he => (mem_cliqueEdgesV.1 (hES he)).2
  -- the depth of the vortex
  obtain ⟨l, hl1, hl2⟩ := exists_vortex_depth k M hk2 (by omega) S.card hcard
  set m : ℕ := S.card / k ^ (l + 1) + 1 with hmdef
  have hpowl : 0 < k ^ l := pow_pos hk0 l
  have hMkl : M * k ^ l ≤ S.card := (Nat.le_div_iff_mul_le hpowl).1 hl1
  -- the vortex
  obtain ⟨L, Pl, hgc, hhead, hsub, hcover, hdisjPl, hdensPl⟩ :=
    vortexBuild (d := d) hk heps0 heps1 hM1 hM2 hloop l S.card m ε {S} hMkl rfl
      (by
        have h1 : (0:ℝ) < (1 / 2 : ℝ) ^ l := by positivity
        rw [heps0def]; nlinarith)
      (by intro W hW; rw [Finset.mem_singleton] at hW; subst hW; omega)
      (by
        intro W hW W' hW' hne
        rw [Finset.mem_singleton] at hW hW'
        exact absurd (hW.trans hW'.symm) hne)
      (by
        intro W hW x hx
        rw [Finset.mem_singleton] at hW
        subst hW
        have h1 : (d + ε) * (W.card : ℝ) ≤ (edeg E x : ℝ) := hdeg x hx
        have h2 : (edeg E x : ℝ) ≤ (degTo E x W : ℝ) := by
          exact_mod_cast edeg_le_degTo hES x
        linarith)
  have hSmem : S ∈ ({S} : Finset (Finset V)) := Finset.mem_singleton_self S
  -- the bottom cells
  have hsizes : ∀ W ∈ Pl, m ≤ W.card + 1 ∧ W.card ≤ m := GoodChain.sizes L Pl hgc
  have hPlS : ∀ X ∈ Pl, X ⊆ S := by
    intro X hX
    obtain ⟨W, hW, hXW⟩ := hsub X hX
    rw [Finset.mem_singleton] at hW
    exact hXW.trans (le_of_eq hW)
  have hrestr : restrictParts Pl S = Pl := by
    ext X
    rw [mem_restrictParts]
    exact ⟨fun h => h.1, fun h => ⟨h, hPlS X h⟩⟩
  refine ⟨m, L, Pl, ?_, ?_, hgc, ?_, ?_, ?_, ?_, ?_, ?_, hrestr⟩
  · -- `m` is at least the prescribed bound
    have h1 : M / k ≤ S.card / k ^ l / k := Nat.div_le_div_right hl1
    have h2 : S.card / k ^ l / k = S.card / k ^ (l + 1) := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have h3 : M₁ ≤ M / k := (Nat.le_div_iff_mul_le hk0).2 (by rw [Nat.mul_comm]; exact hMk)
    omega
  · -- and at most the constant `M`
    omega
  · -- the top level
    have h := hhead S hSmem
    rwa [edgesIn_self hES] at h
  · intro P hP; exact (mem_restrictParts.1 hP).2
  · intro P hP Q hQ hne
    exact hdisjPl P (mem_restrictParts.1 hP).1 Q (mem_restrictParts.1 hQ).1 hne
  · intro x hx
    obtain ⟨X, hX, hxX⟩ := hcover S hSmem x hx
    exact Finset.mem_biUnion.2 ⟨X, by rw [hrestr]; exact hX, hxX⟩
  · intro P hP
    have := hsizes P (mem_restrictParts.1 hP).1
    omega
  · intro P hP v hv
    have h1 := hdensPl P (mem_restrictParts.1 hP).1 v hv
    have h2 : (degTo E v P : ℝ) ≤ (edeg (E ∩ cliqueEdges P) v : ℝ) := by
      exact_mod_cast degTo_le_edeg_inter_cliqueEdges hv hloop
    linarith

/-- **The partition sequence of BKLO §10 with CONSTANT-size bottom cells.**

For `k ≥ 16` and every prescribed `M₁` there are constants `Mmax, n₀` (independent of the host) such
that every graph `E` on a vertex set `S` of size at least `n₀` with minimum degree `(δ+3ε)|S|`
carries a `(k, δ+ε, m)`-partition sequence `BKLO.PartSeq k (δ+ε) δ ε m L Pl E S` whose bottom cells
have `m-1` or `m` vertices with `M₁ ≤ m ≤ Mmax`; moreover the bottom cells are pairwise disjoint,
cover `S`, and each vertex of a bottom cell `P` has at least `(δ+2ε)|P|` neighbours inside `P`.

This is exactly the input the bounded §8 absorber needs: in contrast with
`BKLO.exists_partSeq_dense`, whose single level has parts of size `Θ(n)`, the parts here have
*constant* size. -/
theorem exists_partSeq_dense_bounded {δ ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {k : ℕ} (hk : 16 ≤ k)
    (M₁ : ℕ) :
    ∃ Mmax n₀ : ℕ, ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S →
      (∀ v ∈ S, (δ + 3 * ε) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ (m : ℕ) (L : List (Finset (Finset V))) (Pl : Finset (Finset V)),
        M₁ ≤ m ∧ m ≤ Mmax ∧
        PartSeq k (δ + ε) δ ε m L Pl E S ∧
        (∀ P ∈ restrictParts Pl S, P ⊆ S) ∧
        (∀ P ∈ restrictParts Pl S, ∀ Q ∈ restrictParts Pl S, P ≠ Q → Disjoint P Q) ∧
        S ⊆ (restrictParts Pl S).biUnion id ∧
        (∀ P ∈ restrictParts Pl S, m - 1 ≤ P.card ∧ P.card ≤ m) ∧
        (∀ P ∈ restrictParts Pl S, ∀ v ∈ P,
          (δ + 2 * ε) * (P.card : ℝ) ≤ (edeg (E ∩ cliqueEdges P) v : ℝ)) := by
  obtain ⟨Mmax, n₀, h⟩ :=
    exists_goodChain_dense_bounded (d := δ + 2 * ε) (ε := ε) hε0 hε1 hk M₁
  refine ⟨Mmax, n₀, ?_⟩
  intro V _ E S hcard hES hdeg
  obtain ⟨m, L, Pl, hm1, hm2, hgc, hhead, hPS, hPdisj, hPcover, hPcard, hPdeg, _⟩ :=
    h E S hcard hES (by intro v hv; have := hdeg v hv; linarith only [this])
  exact ⟨m, L, Pl, hm1, hm2,
    partSeq_of_goodChain L Pl (δ + ε) E S hgc (hhead.mono (by linarith)) (fun W _ => rfl),
    hPS, hPdisj, hPcover, hPcard, hPdeg⟩

end BKLO