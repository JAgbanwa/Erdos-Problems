/-
# The dense decomposition theorem from the vortex and a bounded-leftover absorber

This file composes the pieces of BKLO's proof of the dense triangle-decomposition theorem in the
form this project has them:

* the **vortex** `BKLO.exists_partSeq_dense_bounded` (`BKLO/VortexPartition.lean`, proved) — a
  partition sequence whose bottom cells have *constant* size `m ≤ Mmax`, `Mmax` depending on the
  parameters only and **not** on `|S|`, obtained from a nested chain of partitions on whose cores
  the density is maintained rather than degraded per level;
* the **§10 iteration** `BKLO.lemma_10_13_K3'` (`BKLO/Section1012Repaired.lean`) — from the
  repaired Lemma 10.12 `BKLO.Lemma1012K3' (9/10)` it decomposes all of the host but a remainder
  `Hstar` confined to the cells of the last partition of a partition sequence;
* an **absorber**, as the interface `BKLO.AbsorberDenseK3BoundedLeftover` below.

`BKLO.triDecompDense_vortex` is the composition: reserve the absorber `R` *first*, run the vortex on
`E \ R`, run the §10 iteration on the resulting partition sequence, and absorb the remainder — which
lives inside cells of constant size and therefore has *constant* maximum degree.

## What the vortex buys

The point of the vortex is exactly the strength of the absorber that the composition needs.

* `BKLO.triDecompDense_faithful` (`BKLO/NearOptimalFaithful.lean`) runs the same composition on the
  single-level partition `BKLO.exists_partSeq_dense`, whose cells have `Θ(|S|/k)` vertices.  Its
  remainder therefore has maximum degree `Θ(|S|/k)`, and the absorber it consumes,
  `BKLO.AbsorberDenseK3`, must swallow leftovers of degree up to `γ'|S|` — a *linear* amount.
* With the vortex the cells have at most `Mmax = O(1)` vertices, so the remainder has maximum degree
  at most the constant `Mmax`.  The composition below therefore needs only
  `BKLO.AbsorberDenseK3BoundedLeftover`: an absorber for leftovers of **bounded** maximum degree.

`BKLO.absorberDenseK3BoundedLeftover_of_absorberDenseK3` records that this is indeed a weakening:
the interface consumed here follows from the one consumed by `triDecompDense_faithful`.

## Why the proved §8 parts-absorber cannot be used instead

`BKLO.absorberDenseK3PartsBounded_holds` (`BKLO/AbsorberPartsInterface.lean`) proves a
parts-confined absorber for bounded parts, but it cannot discharge the absorber used here, and the
reason is not a technicality.  The absorber it constructs is the edge-disjoint triangle cover of
*all* part-internal edges of the host; consequently

* the only leftover `H ⊆ E \ A` confined to the parts is `H = ∅`, so its absorption clause carries
  no information about a genuinely non-empty remainder (this is stated in that file's own
  docstring), and
* deleting it removes every edge inside a cell, so the bottom level of any partition sequence built
  on `E \ A` has internal minimum degree `0` and is destroyed.

Exchanging the quantifiers to demand a *global* degree bound `Δ(A) ≤ r` with `r` fixed before the
cell size — so that the deletion could be survived — produces an interface that is **false**: a
bipartite (hence triangle-free) confined leftover `H` forces `e(H) ≤ 2 e(A)` (this is
`BKLO.card_le_two_mul_of_bipartite`), while `Δ(A) ≤ r = O(1)` gives `e(A) = O(|S|)` and a dense host
admits confined bipartite even-degree leftovers with `Θ(m|S|)` edges.  So no absorber can both be
deletable from the vortex and absorb an arbitrary confined leftover; the leftover must instead be
controlled by its degree, which is what `AbsorberDenseK3BoundedLeftover` does and what the vortex
makes possible.

Everything in this file is `sorry`-free.
-/
import BKLO.VortexPartition
import BKLO.NearOptimalFaithful
import BKLO.BoundedLeftoverInterface

open Finset

namespace BKLO

/-! ### The absorber interface consumed by the vortex -/

-- `AbsorberDenseK3BoundedLeftover` is now defined once in `BKLO.BoundedLeftoverInterface`
-- (imported above), shared with the absorber-side files (`CoreAbsorberExists`, `ApexCover`, the
-- cluster/Fano route).  The definition is unchanged.

/-- The bounded-leftover absorber is a weakening of the §11 absorber `BKLO.AbsorberDenseK3`: once
the host is large enough, `D ≤ γ'|S|`. -/
theorem absorberDenseK3BoundedLeftover_of_absorberDenseK3 (h : AbsorberDenseK3) :
    AbsorberDenseK3BoundedLeftover := by
  intro γ hγ D
  obtain ⟨γ', n₀, hγ', habs⟩ := h γ hγ
  refine ⟨max n₀ (⌈(D : ℝ) / γ'⌉₊), ?_⟩
  intro V _ E S hcard hES hdiv hdeg
  obtain ⟨R, hRE, hRev, hRdeg, hRabs⟩ :=
    habs E S (le_trans (le_max_left _ _) hcard) hES hdiv hdeg
  refine ⟨R, hRE, hRev, hRdeg, ?_⟩
  intro H hHE hHev hHdeg hdvd
  refine hRabs H hHE hHev (fun v => ?_) hdvd
  have h1 : ((D : ℝ) / γ') ≤ (⌈(D : ℝ) / γ'⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ((⌈(D : ℝ) / γ'⌉₊ : ℕ) : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast le_trans (le_max_right n₀ _) hcard
  have h3 : (D : ℝ) / γ' ≤ (S.card : ℝ) := le_trans h1 h2
  rw [div_le_iff₀ hγ'] at h3
  have h4 : (edeg H v : ℝ) ≤ (D : ℝ) := by exact_mod_cast hHdeg v
  linarith

/-! ### The composition -/

set_option maxHeartbeats 1000000 in
/-- **The triangle decomposition theorem for dense divisible graphs, from the vortex.**

Given the repaired §10 input `BKLO.Lemma1012K3' (9/10)` and the bounded-leftover absorber
`BKLO.AbsorberDenseK3BoundedLeftover`, every sufficiently large triangle-divisible graph with
`δ(G) ≥ (9/10 + ε)|S|` has a triangle decomposition.

Reserve the absorber `R`; the vortex `BKLO.exists_partSeq_dense_bounded` supplies, for `E \ R`, a
partition sequence whose bottom cells have at most `Mmax = O(1)` vertices; the §10 iteration
`BKLO.lemma_10_13_K3'` decomposes all of `E \ R` but a remainder confined to those cells, whose
maximum degree is therefore at most the constant `Mmax`; the absorber swallows it. -/
theorem triDecompDense_vortex (h12 : Lemma1012K3' (9 / 10))
    (habs : AbsorberDenseK3BoundedLeftover) : TriDecompDense := by
  classical
  intro ε hε
  -- a small parameter, below `ε/8` and below `1/100`
  set e : ℝ := min (ε / 8) (1 / 100) with hedef
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have he1 : e ≤ ε / 8 := min_le_left _ _
  have he100 : e ≤ 1 / 100 := min_le_right _ _
  have heps : e ≤ 1 := by linarith
  -- the number of parts, large enough for the hierarchy `1/k ≤ e/8` and for the vortex
  set k : ℕ := max 16 (⌈8 / e⌉₊ + 1) with hkdef
  have hk16 : 16 ≤ k := le_max_left _ _
  have hk0 : 0 < k := by omega
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hk8 : 8 / e ≤ (k : ℝ) := by
    have h1 : 8 / e ≤ (⌈8 / e⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈8 / e⌉₊ + 1 ≤ k := le_max_right _ _
    have h3 : ((⌈8 / e⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans (Nat.le_succ _) h2
    linarith
  have hkε : 1 / (k : ℝ) ≤ e / 8 := by
    rw [div_le_div_iff₀ hkpos (by norm_num)]
    have := (div_le_iff₀ he).1 hk8
    linarith
  -- the §10 iteration, from the repaired Lemma 10.12
  obtain ⟨m₀, h10⟩ := lemma_10_13_K3' (δ := 9 / 10) (ε := e) hk0 he hkε h12
  -- the vortex: bottom cells of size at most the constant `Mmax`
  obtain ⟨Mmax, nv, hvor⟩ :=
    exists_partSeq_dense_bounded (δ := 9 / 10) (ε := e) he heps hk16 (max m₀ 3)
  -- the absorber, for leftovers of degree at most `Mmax`
  obtain ⟨n₁, habs'⟩ := habs e he Mmax
  refine ⟨max nv n₁, ?_⟩
  intro V _ S E hcard hES hdiv hdeg
  have hnv : nv ≤ S.card := le_trans (le_max_left _ _) hcard
  have hn₁ : n₁ ≤ S.card := le_trans (le_max_right _ _) hcard
  have hScard : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  -- reserve the absorber
  obtain ⟨R, hRE, hRev, hRdeg, hRabs⟩ :=
    habs' E S hn₁ hES hdiv (by
      intro v hv
      have := hdeg v hv
      nlinarith)
  set E₁ : Finset (Sym2 V) := E \ R with hE₁def
  have hE₁E : E₁ ⊆ E := Finset.sdiff_subset
  have hE₁S : E₁ ⊆ cliqueEdges S := hE₁E.trans hES
  have hloop : ∀ f ∈ E₁, ¬ f.IsDiag := fun f hf => (mem_cliqueEdgesV.1 (hE₁S hf)).2
  have hEev : EvenDegrees E := fun v => hdiv.1 v
  have hE₁ev : EvenDegrees E₁ := evenDegrees_sdiff hRE hEev hRev
  -- the minimum degree survives the reservation
  have hE₁deg : ∀ v ∈ S, (9 / 10 + 3 * e) * (S.card : ℝ) ≤ (edeg E₁ v : ℝ) := by
    intro v hv
    have h1 : (edeg E v : ℝ) ≤ (edeg E₁ v : ℝ) + (edeg R v : ℝ) := by
      exact_mod_cast edeg_le_edeg_sdiff_add_edeg E R v
    have h2 := hdeg v hv
    have h3 := hRdeg v
    nlinarith
  -- the vortex partition sequence of the reserved graph
  obtain ⟨m, L, Pl, hm1, hm2, hps, _hPS, hPdisj, _hPcover, hPcard, _hPdeg⟩ :=
    hvor E₁ S hnv hE₁S hE₁deg
  have hmm₀ : m₀ ≤ m := le_trans (le_max_left _ _) hm1
  -- the §10 output
  obtain ⟨Hstar, hHsub, hHdec⟩ := h10 m hmm₀ L Pl E₁ S hloop hE₁S hE₁ev hps
  have hHE₁ : Hstar ⊆ E₁ := hHsub.trans (insideParts_subset _ _)
  have hHev : EvenDegrees Hstar :=
    evenDegrees_of_sdiff hHE₁ hE₁ev (fun v => (hHdec.triDivisible).1 v)
  -- the remainder has *constant* maximum degree: it lives inside the bounded cells
  have hHdeg : ∀ v : V, edeg Hstar v ≤ Mmax := by
    intro v
    refine le_trans (edeg_mono hHsub v) ?_
    exact edeg_insideParts_le hPdisj (fun P hP => le_trans (hPcard P hP).2 hm2) v
  -- the divisibility of the absorbed graph
  have hHR : Disjoint R Hstar := by
    refine Finset.disjoint_left.2 fun f hfR hfH => ?_
    exact (Finset.mem_sdiff.1 (hHE₁ hfH)).2 hfR
  have hcards : (E₁ \ Hstar).card + Hstar.card + R.card = E.card := by
    have h1 : (E₁ \ Hstar).card + Hstar.card = E₁.card :=
      Finset.card_sdiff_add_card_eq_card hHE₁
    have h2 : E₁.card + R.card = E.card := Finset.card_sdiff_add_card_eq_card hRE
    omega
  have hdvd : 3 ∣ (R ∪ Hstar).card := by
    have h1 : (R ∪ Hstar).card = R.card + Hstar.card := Finset.card_union_of_disjoint hHR
    obtain ⟨a, ha⟩ := hdiv.2
    obtain ⟨b, hb⟩ := (hHdec.triDivisible).2
    exact ⟨a - b, by omega⟩
  -- absorb
  have hAbs : TriDecomp (R ∪ Hstar) := hRabs Hstar hHE₁ hHev hHdeg hdvd
  -- and assemble
  have hsplit : (E₁ \ Hstar) ∪ (R ∪ Hstar) = E := by
    refine Finset.Subset.antisymm (fun f hf => ?_) (fun f hf => ?_)
    · rcases Finset.mem_union.1 hf with h | h
      · exact hE₁E (Finset.mem_sdiff.1 h).1
      · rcases Finset.mem_union.1 h with h' | h'
        · exact hRE h'
        · exact hE₁E (hHE₁ h')
    · by_cases hfR : f ∈ R
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ hfR)
      · by_cases hfH : f ∈ Hstar
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ hfH)
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨hf, hfR⟩, hfH⟩)
  have hdisj2 : Disjoint (E₁ \ Hstar) (R ∪ Hstar) := by
    refine Finset.disjoint_left.2 fun f hf hf' => ?_
    rw [Finset.mem_sdiff, hE₁def, Finset.mem_sdiff] at hf
    rcases Finset.mem_union.1 hf' with h | h
    · exact hf.1.2 h
    · exact hf.2 h
  have hEdec : TriDecomp E := by
    have := TriDecomp.union hdisj2 hHdec hAbs
    rwa [hsplit] at this
  obtain ⟨P, hP3, hPd, hPfam⟩ := hEdec
  refine ⟨P, ⟨hP3, ?_, hPd⟩, ?_⟩
  · intro t ht
    rw [← hPfam]
    exact Finset.subset_biUnion_of_mem cliqueEdges ht
  · rw [hPfam]

/-- **The dense triangle-decomposition theorem, from the vortex and the bounded-leftover absorber.**
Every sufficiently large triangle-divisible graph with `δ(G) ≥ (9/10 + ε)|V|` has a triangle
decomposition. -/
theorem triangleDecomposable_dense_vortex (h12 : Lemma1012K3' (9 / 10))
    (habs : AbsorberDenseK3BoundedLeftover) (ε : ℝ) (hε : 0 < ε) : ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → 3 ∣ G.edgeFinset.card → (∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G := by
  classical
  obtain ⟨n₀, hn₀⟩ := triDecompDense_vortex h12 habs ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hcard hdvd heven hdeg
  have hES : G.edgeFinset ⊆ cliqueEdges (Finset.univ : Finset V) := by
    intro f hf
    exact mem_cliqueEdgesV.2 ⟨fun x _ => Finset.mem_univ x,
      G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.1 hf)⟩
  have hdivis : TriDivisible G.edgeFinset := by
    refine ⟨fun v => ?_, hdvd⟩
    have h := heven v
    rwa [← edeg_edgeFinset_eq_degree] at h
  have hdegE : ∀ v ∈ (Finset.univ : Finset V),
      (9 / 10 + ε) * ((Finset.univ : Finset V).card : ℝ) ≤ (edeg G.edgeFinset v : ℝ) := by
    intro v _
    have h1 : (G.minDegree : ℝ) ≤ (G.degree v : ℝ) := by exact_mod_cast G.minDegree_le_degree v
    have h2 : (edeg G.edgeFinset v : ℝ) = (G.degree v : ℝ) := by rw [edeg_edgeFinset_eq_degree]
    rw [Finset.card_univ, h2]
    linarith
  obtain ⟨P, hfam, hcov⟩ :=
    hn₀ (Finset.univ : Finset V) G.edgeFinset (by rw [Finset.card_univ]; exact hcard) hES hdivis
      hdegE
  refine triangleDecomposable_of_triDecomp G ⟨P, hfam.1, hfam.2.2, ?_⟩
  exact Finset.Subset.antisymm (famEdges_subset_of_triFamilyIn hfam) hcov

end BKLO
