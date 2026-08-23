/-
# From the faithful §10 output to `BKLO.NearOptimalConclusion`

The faithful §10 core of this project is `BKLO.lemma_10_13_K3'` (BKLO Lemma 10.13, hence Lemma 10.1,
for `r = 2`), which from the single remaining paper input `BKLO.Lemma1012K3'` produces, for a
partition sequence `P₁, …, P_ℓ` of the host graph, a triangle decomposition of everything except a
remainder `Hstar` confined to the parts of the last partition `P_ℓ`.

`BKLO.NearOptimalConclusion` (`BKLO/NearOptimal.lean`) asks for something different in one crucial
respect: the remainder must be confined to a **single bounded** vertex set `U`, chosen before the
reserved edge set `A`.  The §10 remainder is *not* of that shape — it is spread over **all**
`≈ |S|/m` parts of the last partition, and no choice of the partition sequence can change that: the
partitions of a partition sequence are equitable and every vertex is required to have `(δ+ε)|W|`
neighbours in every part `W`, so every part carries a dense induced graph and, in general, a
nonempty remainder.  Passing from the §10 output to a vortex-shaped statement is the business of
BKLO §11 (absorption); this file carries out that passage, isolating exactly what §11 has to
supply, and proving everything else.

Two further ingredients are needed on top of the §10 core.  The first is *proved* here (in
`BKLO/PartSeqDenseProof.lean`), the second is stated as a named, self-contained interface:

* **the partition sequence exists** — `BKLO.exists_partSeq_dense`.  A graph on `S` of minimum degree
  `(δ + 3ε)|S|` carries, for `|S|` large, a one-level `(k, δ+ε, m)`-partition sequence with
  `m = ⌈|S|/k⌉`.  This is obtained by splitting `S` into `k` almost equal parts in which no vertex
  has more than its share of non-neighbours, using the project's own second-moment bound.  One
  level suffices: §10 only needs the bottom parts to be a small fraction of `|S|`, which `k ≥ 2/γ`
  already gives, while `BKLO.Lemma1012K3'` only puts a *lower* bound on `k`.
* `BKLO.AbsorberDenseK3` — **the §11 absorbing structure.**  A dense triangle-divisible graph
  contains a sparse `R` (an absorber) which swallows *every* sparse even-degree leftover disjoint
  from it: `R ∪ H` is triangle-decomposable for every such `H` with `3 ∣ |R ∪ H|`.  This is BKLO
  §8.1 / §11 (absorption), for `F = K₃`.

From these two together with `Lemma1012K3'` the whole dense decomposition theorem follows —
`BKLO.triDecompDense_faithful` — and hence `BKLO.NearOptimalConclusion` with `C = 0`, `U = ∅`
(`BKLO.nearOptimalConclusion_faithful`).  The route is BKLO's own: reserve the absorber, run the
faithful §10 iteration on what is left, and absorb the §10 remainder.

Everything here is `sorry`-free and uses no `axiom`.
-/
import BKLO.Section1012Repaired
import BKLO.CoverDownFromDecomp
import BKLO.PartSeqDenseProof
import Mathlib.Data.Nat.Cast.Order.Field

open Finset

namespace BKLO

/-! ### Two small facts about the §10 remainder -/

variable {V : Type*} [DecidableEq V]

/-- The remainder of §10 lives inside the parts of the last partition, so its degree at any vertex
is at most the size of the part containing that vertex. -/
theorem edeg_insideParts_le {E : Finset (Sym2 V)} {Q : Finset (Finset V)} {m : ℕ}
    (hdisj : ∀ W ∈ Q, ∀ W' ∈ Q, W ≠ W' → Disjoint W W') (hcard : ∀ W ∈ Q, W.card ≤ m) (v : V) :
    edeg (insideParts E Q) v ≤ m := by
  classical
  by_cases h : ∃ W ∈ Q, v ∈ W
  · obtain ⟨W, hW, hvW⟩ := h
    refine le_trans (edeg_le_card_of_within ?_) (hcard W hW)
    intro e he hve u hue
    rw [mem_insideParts] at he
    obtain ⟨-, W', hW', hsub⟩ := he
    have hvW' : v ∈ W' := hsub v hve
    have : W' = W := by
      by_contra hne
      exact (Finset.disjoint_left.1 (hdisj W' hW' W hW hne)) hvW' hvW
    subst this
    exact hsub u hue
  · have hempty : (insideParts E Q).filter (fun e => v ∈ e) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun e he hve => h ?_
      rw [mem_insideParts] at he
      obtain ⟨-, W', hW', hsub⟩ := he
      exact ⟨W', hW', hsub v hve⟩
    have : edeg (insideParts E Q) v = 0 := by
      unfold edeg; rw [hempty]; rfl
    omega

/-- If `E` and `E \ H` have even degrees and `H ⊆ E`, then so has `H`. -/
theorem evenDegrees_of_sdiff {E H : Finset (Sym2 V)} (hHE : H ⊆ E) (hE : EvenDegrees E)
    (hEH : EvenDegrees (E \ H)) : EvenDegrees H := by
  intro v
  have h1 := edeg_sdiff_add_edeg_eq hHE v
  obtain ⟨a, ha⟩ := hE v
  obtain ⟨b, hb⟩ := hEH v
  exact ⟨a - b, by omega⟩

/-! ### The two interfaces that BKLO §10 and §11 supply -/

/-- **The absorbing structure of BKLO §8.1 / §11, for `F = K₃` in the dense regime.**

For every `γ > 0` there is a `γ' > 0` and a threshold beyond which every large dense
triangle-divisible edge set `E` contains an *absorber* `R`: an even-degree subgraph of maximum
degree at most `γ|S|` such that `R ∪ H` is triangle-decomposable for **every** even-degree
`H ⊆ E \ R` of maximum degree at most `γ'|S|` for which `R ∪ H` is 3-divisible.

This is exactly the property the §10 remainder is fed to in BKLO §11: the remainder is even-degree,
sparse, and disjoint from the reserved absorber, and the absorber turns it into a decomposition.
The divisibility side condition `3 ∣ |R ∪ H|` is necessary (a triangle decomposition has a number of
edges divisible by three) and is automatic at the point of use. -/
def AbsorberDenseK3 : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ (γ' : ℝ) (n₀ : ℕ), 0 < γ' ∧
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → TriDivisible E →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ R : Finset (Sym2 V), R ⊆ E ∧ EvenDegrees R ∧
        (∀ v : V, (edeg R v : ℝ) ≤ γ * (S.card : ℝ)) ∧
        ∀ H : Finset (Sym2 V), H ⊆ E \ R → EvenDegrees H →
          (∀ v : V, (edeg H v : ℝ) ≤ γ' * (S.card : ℝ)) →
          3 ∣ (R ∪ H).card → TriDecomp (R ∪ H)

/-! ### The dense decomposition theorem, from the faithful §10 core -/

/-- **The triangle decomposition theorem for dense divisible graphs, from the faithful §10 core.**

Reserve the §11 absorber `R`, run the faithful §10 iteration (`BKLO.lemma_10_13_K3'`, i.e. BKLO
Lemma 10.13 from the repaired Lemma 10.12) on `E \ R`, and absorb the remainder — which the §10
output places inside the bottom parts of the partition sequence, hence is sparse and even. -/
theorem triDecompDense_faithful (h12 : Lemma1012K3' (9 / 10)) (habs : AbsorberDenseK3) :
    TriDecompDense := by
  classical
  intro ε hε
  -- a small parameter, below `ε/8` and below `1/100`
  set e : ℝ := min (ε / 8) (1 / 100) with hedef
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have he1 : e ≤ ε / 8 := min_le_left _ _
  have he100 : e ≤ 1 / 100 := min_le_right _ _
  -- the §11 absorber: its sparsity parameter `γ'` fixes how fine the partition has to be
  obtain ⟨γ', n₁, hγ', habs'⟩ := habs e he
  -- the number of parts, large enough both for the hierarchy `1/k ≤ e/8` and for the bottom parts
  -- to be a `γ'`-fraction of the whole
  set k : ℕ := max 2 (max (⌈8 / e⌉₊ + 1) (⌈2 / γ'⌉₊ + 1)) with hkdef
  have hk2 : 2 ≤ k := le_max_left _ _
  have hk0 : 0 < k := by omega
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hk8 : 8 / e ≤ (k : ℝ) := by
    have h1 : 8 / e ≤ (⌈8 / e⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈8 / e⌉₊ + 1 ≤ k := le_trans (le_max_left _ _) (le_max_right 2 _)
    have h3 : ((⌈8 / e⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans (Nat.le_succ _) h2
    linarith
  have hkγ : 2 / γ' ≤ (k : ℝ) := by
    have h1 : 2 / γ' ≤ (⌈2 / γ'⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈2 / γ'⌉₊ + 1 ≤ k := le_trans (le_max_right _ _) (le_max_right 2 _)
    have h3 : ((⌈2 / γ'⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans (Nat.le_succ _) h2
    linarith
  have hγk : 2 ≤ γ' * (k : ℝ) := by
    rw [div_le_iff₀ hγ'] at hkγ
    linarith
  have hkε : 1 / (k : ℝ) ≤ e / 8 := by
    rw [div_le_div_iff₀ hkpos (by norm_num)]
    have := (div_le_iff₀ he).1 hk8
    linarith
  -- the §10 iteration, from the repaired Lemma 10.12
  obtain ⟨m₀, h10⟩ := lemma_10_13_K3' (δ := 9 / 10) (ε := e) hk0 he hkε h12
  -- the partition sequence
  obtain ⟨n₂, hseq'⟩ := exists_partSeq_dense (δ := 9 / 10) (ε := e) he (by linarith) hk2
  refine ⟨max (max 1 n₁) (max n₂ (max (m₀ * k) ⌈2 / γ'⌉₊)), ?_⟩
  intro V _ S E hcard hES hdiv hdeg
  have hn₁ : n₁ ≤ S.card := le_trans (le_trans (le_max_right 1 _) (le_max_left _ _)) hcard
  have hn₂ : n₂ ≤ S.card := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hcard
  have hnm₀ : m₀ * k ≤ S.card :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hcard
  have hnγ : ⌈2 / γ'⌉₊ ≤ S.card :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hcard
  have hScard : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hnγR : 2 ≤ γ' * (S.card : ℝ) := by
    have h1 : 2 / γ' ≤ (⌈2 / γ'⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈2 / γ'⌉₊ : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hnγ
    have h3 : 2 / γ' ≤ (S.card : ℝ) := le_trans h1 h2
    rw [div_le_iff₀ hγ'] at h3
    linarith
  -- reserve the absorber
  obtain ⟨R, hRE, hRev, hRdeg, hRabs⟩ :=
    habs' E S hn₁ hES hdiv (by
      intro v hv
      have := hdeg v hv
      nlinarith [min_le_left (ε / 8) (1 / 100)])
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
    have h4 : e ≤ ε / 8 := he1
    nlinarith
  -- the partition sequence of the reserved graph
  obtain ⟨Pl, m, hmlow, hmup, hps, hsize, hdisj⟩ := hseq' E₁ S hn₂ hE₁S hE₁deg
  have hm₀ : m₀ ≤ m := le_trans ((Nat.le_div_iff_mul_le hk0).2 hnm₀) hmlow
  have hmγ : (m : ℝ) ≤ γ' * (S.card : ℝ) := by
    have h1 : (m : ℝ) ≤ ((S.card / k : ℕ) : ℝ) + 1 := by exact_mod_cast hmup
    have h2 : ((S.card / k : ℕ) : ℝ) ≤ (S.card : ℝ) / (k : ℝ) := Nat.cast_div_le
    have h3 : (S.card : ℝ) / (k : ℝ) ≤ γ' * (S.card : ℝ) / 2 := by
      rw [div_le_iff₀ hkpos]
      nlinarith
    linarith
  set L : List (Finset (Finset V)) := [] with hLdef
  -- the §10 output
  obtain ⟨Hstar, hHsub, hHdec⟩ := h10 m hm₀ L Pl E₁ S hloop hE₁S hE₁ev hps
  have hHE₁ : Hstar ⊆ E₁ := hHsub.trans (insideParts_subset _ _)
  have hHev : EvenDegrees Hstar :=
    evenDegrees_of_sdiff hHE₁ hE₁ev (fun v => (hHdec.triDivisible).1 v)
  -- the remainder is sparse
  have hHdeg : ∀ v : V, (edeg Hstar v : ℝ) ≤ γ' * (S.card : ℝ) := by
    intro v
    have h1 : edeg Hstar v ≤ edeg (insideParts E₁ (restrictParts Pl S)) v :=
      edeg_mono hHsub v
    have h2 : edeg (insideParts E₁ (restrictParts Pl S)) v ≤ m :=
      edeg_insideParts_le hdisj hsize v
    have h3 : (edeg Hstar v : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_trans h1 h2
    linarith
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

/-! ### `NearOptimalConclusion` -/

/-- The degree of a vertex in a graph, in edge-set language. -/
theorem edeg_edgeFinset_eq_degree {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (v : W) : edeg G.edgeFinset v = G.degree v := by
  rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter v, edeg]

/-- **`BKLO.NearOptimalConclusion` from the dense decomposition theorem**, with `C = 0` and
`U = ∅`: deleting a bounded edge set from a graph of minimum degree `(9/10 + ε)n` leaves, for `n`
large, a divisible graph of minimum degree `(9/10 + ε/2)n`, which is decomposed outright. -/
theorem nearOptimalConclusion_of_triDecompDense (h : TriDecompDense) : NearOptimalConclusion := by
  classical
  intro ε hε
  obtain ⟨n₁, hn₁⟩ := h (ε / 2) (by linarith)
  refine ⟨0, ?_⟩
  intro K
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (K : ℝ) / ε)
  refine ⟨max 1 (max n₁ N), ?_⟩
  intro V _ _ G _ hn hdeg
  have hn1 : 1 ≤ Fintype.card V := le_trans (le_max_left _ _) hn
  have hnn₁ : n₁ ≤ Fintype.card V := le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hn
  have hnN : N ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hn
  have hKsmall : (K : ℝ) ≤ ε / 2 * (Fintype.card V : ℝ) := by
    have h1 : 2 * (K : ℝ) / ε < (Fintype.card V : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hnN)
    rw [div_lt_iff₀ hε] at h1
    linarith
  refine ⟨∅, by simp, ?_⟩
  intro A hAsub hAcard hAdisj hAdiv
  set E : Finset (Sym2 V) := G.edgeFinset \ A with hEdef
  have hES : E ⊆ cliqueEdges (Finset.univ : Finset V) := by
    intro f hf
    have hfG : f ∈ G.edgeFinset := (Finset.mem_sdiff.1 hf).1
    refine mem_cliqueEdgesV.2 ⟨fun x _ => Finset.mem_univ x, ?_⟩
    exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.1 hfG)
  have hcardU : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
  have hdegE : ∀ v ∈ (Finset.univ : Finset V),
      (9 / 10 + ε / 2) * ((Finset.univ : Finset V).card : ℝ) ≤ (edeg E v : ℝ) := by
    intro v _
    have h1 : (G.minDegree : ℝ) ≤ (G.degree v : ℝ) := by exact_mod_cast G.minDegree_le_degree v
    have h2 : (edeg G.edgeFinset v : ℝ) ≤ (edeg E v : ℝ) + (edeg A v : ℝ) := by
      exact_mod_cast edeg_le_edeg_sdiff_add_edeg G.edgeFinset A v
    have h3 : edeg A v ≤ A.card := Finset.card_le_card (Finset.filter_subset _ _)
    have h4 : (edeg A v : ℝ) ≤ (K : ℝ) := by
      have : edeg A v ≤ K := le_trans h3 hAcard
      exact_mod_cast this
    have h5 : (edeg G.edgeFinset v : ℝ) = (G.degree v : ℝ) := by
      rw [edeg_edgeFinset_eq_degree]
    rw [hcardU]
    linarith [hdeg]
  obtain ⟨P, hP, hcover⟩ :=
    hn₁ (Finset.univ : Finset V) E (by rw [hcardU]; exact hnn₁) hES hAdiv hdegE
  refine ⟨P, hP.1, hP.2.1, hP.2.2, ?_⟩
  intro f hf
  exact absurd (hcover (Finset.mem_sdiff.1 hf).1) (Finset.mem_sdiff.1 hf).2

/-- **The near-optimal decomposition, faithfully.**  `BKLO.NearOptimalConclusion` from the faithful
§10 core (the repaired Lemma 10.12 `Lemma1012K3'`, through BKLO Lemma 10.13) together with the §11
absorbing structure; the partition sequence it is run on is constructed in
`BKLO.exists_partSeq_dense`. -/
theorem nearOptimalConclusion_faithful (h12 : Lemma1012K3' (9 / 10)) (habs : AbsorberDenseK3) :
    NearOptimalConclusion :=
  nearOptimalConclusion_of_triDecompDense (triDecompDense_faithful h12 habs)

/-! ### The dense case of the decomposition theorem -/

/-- **The dense triangle-decomposition theorem, from the faithful §10 core.**  Every sufficiently
large triangle-divisible graph with `δ(G) ≥ (9/10 + ε)|V|` has a triangle decomposition — the
conclusion of BKLO Theorem 1.3 / 6.3 for `F = K₃` in the range `δ ≥ 9/10`, from the repaired
Lemma 10.12 and the §11 absorbing structure. -/
theorem triangleDecomposable_dense_faithful (h12 : Lemma1012K3' (9 / 10)) (habs : AbsorberDenseK3)
    (ε : ℝ) (hε : 0 < ε) : ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → 3 ∣ G.edgeFinset.card → (∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G := by
  classical
  obtain ⟨n₀, hn₀⟩ := triDecompDense_faithful h12 habs ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hcard hdvd heven hdeg
  have hES : G.edgeFinset ⊆ cliqueEdges (Finset.univ : Finset V) := by
    intro f hf
    exact mem_cliqueEdgesV.2 ⟨fun x _ => Finset.mem_univ x,
      G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.1 hf)⟩
  have hdiv : TriDivisible G.edgeFinset := by
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
    hn₀ (Finset.univ : Finset V) G.edgeFinset (by rw [Finset.card_univ]; exact hcard) hES hdiv
      hdegE
  refine triangleDecomposable_of_triDecomp G ⟨P, hfam.1, hfam.2.2, ?_⟩
  exact Finset.Subset.antisymm (famEdges_subset_of_triFamilyIn hfam) hcov

end BKLO
