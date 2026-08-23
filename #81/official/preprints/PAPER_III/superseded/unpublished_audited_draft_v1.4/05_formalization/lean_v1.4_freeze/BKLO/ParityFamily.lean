/-
# Parity graphs from edge-disjoint triangle families

This file provides the reduction that makes BKLO §9 (for `r = 2`, `F = K₃`) a purely combinatorial
construction problem:

> Let `𝒯` be a family of pairwise edge-disjoint triangles.  If, for **every** triangle `T₀` on the
> vertex set `⋃ P` of the partition, some subfamily `𝒮 ⊆ 𝒯` has the same parity vector as `T₀`
> (i.e. `d_{famEdges 𝒮}(x, W) ≡ d_{T₀}(x, W) (mod 2)` for every part `W` and every `x ∈ V_{<W}`),
> then `famEdges 𝒯` is a parity graph in the sense of `BKLO.IsParityGraphK3S`.

The point is that every `2`-divisible `Gstar` on `⋃ P` is an `F₂`-sum of triangles
(`BKLO.even_graph_triSum`), and the parity vector is additive over `F₂`-sums.

Everything here is `sorry`-free.
-/
import BKLO.TriangleSums

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- **Parity graph (BKLO §9, Lemma 9.3 form).**  `Ppar` is triangle-decomposable and, for every
`2`-divisible `Gstar` on `⋃ P` edge-disjoint from it, some `P' ⊆ Ppar` fixes every before-part
parity of `Gstar`.  (Restored here after a version drift: this def lived in an older
`Section1012Defs`; all its dependencies — `beforeParts`, `degTo`, `TriDecomp` — are in the tree.) -/
def IsParityGraphK3S (P : Finset (Finset V)) (idx : Finset V → ℕ) (Ppar : Finset (Sym2 V)) :
    Prop :=
  TriDecomp Ppar ∧
    ∀ Gstar : Finset (Sym2 V), Gstar ⊆ cliqueEdges (P.biUnion id) → Disjoint Gstar Ppar →
      EvenDegrees Gstar →
      ∃ P' : Finset (Sym2 V), P' ⊆ Ppar ∧ TriDecomp (Ppar \ P') ∧
        ∀ W ∈ P, ∀ x ∈ beforeParts P idx W, Even (degTo (Gstar ∪ P') x W)

/-- **BKLO Lemma 9.3 (r=2, F=K₃), repaired form on the partition's vertex set.**  The parity graph
is required to work for every `2`-divisible `Gstar` on `⋃ P` (not outside `S`).  (Restored here
after the same version drift as `IsParityGraphK3S`.) -/
def Lemma93K3S : Prop :=
  ∀ (k : ℕ) (γ : ℝ), 0 < k → 0 < γ → ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (G : Finset (Sym2 V)) (S : Finset V) (P : Finset (Finset V))
      (idx : Finset V → ℕ) (d : ℝ),
      n₀ ≤ S.card → (∀ e ∈ G, ¬ e.IsDiag) → G ⊆ cliqueEdges S →
      1 / 2 + γ ≤ d → IsKDeltaPartition k d P G S →
      ∃ Ppar : Finset (Sym2 V), Ppar ⊆ G ∧ IsParityGraphK3S P idx Ppar ∧
        ∀ v : V, (edeg Ppar v : ℝ) ≤ γ * (S.card : ℝ)

/-! ### Sums over symmetric differences in characteristic two -/

theorem sum_symmDiff_zmod {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ZMod 2) :
    ∑ a ∈ symmDiff s t, f a = (∑ a ∈ s, f a) + ∑ a ∈ t, f a := by
  classical
  have hsd : symmDiff s t = (s \ t) ∪ (t \ s) := rfl
  have hdisj : Disjoint (s \ t) (t \ s) :=
    Finset.disjoint_left.2 fun a ha ha' => (Finset.mem_sdiff.1 ha).2 (Finset.mem_sdiff.1 ha').1
  have h1 : ∑ a ∈ symmDiff s t, f a = (∑ a ∈ s \ t, f a) + ∑ a ∈ t \ s, f a := by
    rw [hsd, Finset.sum_union hdisj]
  have h2 : (∑ a ∈ s ∩ t, f a) + ∑ a ∈ s \ t, f a = ∑ a ∈ s, f a :=
    Finset.sum_inter_add_sum_diff s t f
  have h3 : (∑ a ∈ t ∩ s, f a) + ∑ a ∈ t \ s, f a = ∑ a ∈ t, f a :=
    Finset.sum_inter_add_sum_diff t s f
  rw [Finset.inter_comm t s] at h3
  rw [h1, ← h2, ← h3]
  have h4 : (2 : ZMod 2) = 0 := by decide
  have : (∑ a ∈ s ∩ t, f a) + (∑ a ∈ s ∩ t, f a) = 0 := by
    have : (∑ a ∈ s ∩ t, f a) + (∑ a ∈ s ∩ t, f a) = 2 * ∑ a ∈ s ∩ t, f a := by ring
    rw [this, h4, zero_mul]
  linear_combination (norm := ring_nf) -this

/-! ### Edge-disjoint triangle families -/

/-- An edge-disjoint family of triangles. -/
structure IsTriFamily (𝒯 : Finset (Finset V)) : Prop where
  card_three : ∀ T ∈ 𝒯, T.card = 3
  edge_disjoint : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → Disjoint (cliqueEdges T) (cliqueEdges T')

theorem IsTriFamily.mono {𝒯 𝒮 : Finset (Finset V)} (h : IsTriFamily 𝒯) (hs : 𝒮 ⊆ 𝒯) :
    IsTriFamily 𝒮 :=
  ⟨fun T hT => h.card_three T (hs hT), fun T hT T' hT' hne =>
    h.edge_disjoint T (hs hT) T' (hs hT') hne⟩

theorem IsTriFamily.triDecomp {𝒯 : Finset (Finset V)} (h : IsTriFamily 𝒯) :
    TriDecomp (famEdges 𝒯) :=
  ⟨𝒯, h.card_three, h.edge_disjoint, rfl⟩

theorem famEdges_mono {𝒮 𝒯 : Finset (Finset V)} (h : 𝒮 ⊆ 𝒯) : famEdges 𝒮 ⊆ famEdges 𝒯 :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

/-- For an edge-disjoint family, removing a subfamily removes exactly its edges. -/
theorem famEdges_sdiff {𝒯 𝒮 : Finset (Finset V)} (h : IsTriFamily 𝒯) (hs : 𝒮 ⊆ 𝒯) :
    famEdges 𝒯 \ famEdges 𝒮 = famEdges (𝒯 \ 𝒮) := by
  ext e
  simp only [famEdges, Finset.mem_sdiff, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨T, hT, heT⟩, hno⟩
    exact ⟨T, ⟨hT, fun hc => hno ⟨T, hc, heT⟩⟩, heT⟩
  · rintro ⟨T, ⟨hT𝒯, hTn⟩, heT⟩
    refine ⟨⟨T, hT𝒯, heT⟩, ?_⟩
    rintro ⟨T', hT', heT'⟩
    have hne : T ≠ T' := fun hc => hTn (hc ▸ hT')
    exact (Finset.disjoint_left.1 (h.edge_disjoint T hT𝒯 T' (hs hT') hne) heT) heT'

/-- Degrees into a set are additive over an edge-disjoint triangle family. -/
theorem degTo_famEdges {𝒮 : Finset (Finset V)} (h : IsTriFamily 𝒮) (x : V) (W : Finset V) :
    degTo (famEdges 𝒮) x W = ∑ T ∈ 𝒮, degTo (cliqueEdges T) x W := by
  classical
  have hnb : nbhdIn (famEdges 𝒮) x W = 𝒮.biUnion (fun T => nbhdIn (cliqueEdges T) x W) := by
    ext y
    simp only [mem_nbhdIn, famEdges, Finset.mem_biUnion]
    constructor
    · rintro ⟨hyW, T, hT, heT⟩
      exact ⟨T, hT, hyW, heT⟩
    · rintro ⟨T, hT, hyW, heT⟩
      exact ⟨hyW, T, hT, heT⟩
  have hpd : ∀ T ∈ 𝒮, ∀ T' ∈ 𝒮, T ≠ T' →
      Disjoint (nbhdIn (cliqueEdges T) x W) (nbhdIn (cliqueEdges T') x W) := by
    intro T hT T' hT' hne
    refine Finset.disjoint_left.2 fun y hy hy' => ?_
    exact (Finset.disjoint_left.1 (h.edge_disjoint T hT T' hT' hne) (mem_nbhdIn.1 hy).2)
      (mem_nbhdIn.1 hy').2
  rw [degTo, hnb, Finset.card_biUnion hpd]
  rfl

/-- The parity vector of a subfamily. -/
def flipv (𝒮 : Finset (Finset V)) (x : V) (W : Finset V) : ZMod 2 :=
  ((degTo (famEdges 𝒮) x W : ℕ) : ZMod 2)

theorem flipv_eq_sum {𝒮 : Finset (Finset V)} (h : IsTriFamily 𝒮) (x : V) (W : Finset V) :
    flipv 𝒮 x W = ∑ T ∈ 𝒮, ((degTo (cliqueEdges T) x W : ℕ) : ZMod 2) := by
  rw [flipv, degTo_famEdges h]
  push_cast
  rfl

/-- The parity vector is additive over symmetric differences of subfamilies. -/
theorem flipv_symmDiff {𝒯 𝒮₁ 𝒮₂ : Finset (Finset V)} (h : IsTriFamily 𝒯)
    (h₁ : 𝒮₁ ⊆ 𝒯) (h₂ : 𝒮₂ ⊆ 𝒯) (x : V) (W : Finset V) :
    flipv (symmDiff 𝒮₁ 𝒮₂) x W = flipv 𝒮₁ x W + flipv 𝒮₂ x W := by
  have hsub : symmDiff 𝒮₁ 𝒮₂ ⊆ 𝒯 := by
    intro T hT
    rcases Finset.mem_symmDiff.1 hT with ⟨hT1, -⟩ | ⟨hT2, -⟩
    · exact h₁ hT1
    · exact h₂ hT2
  rw [flipv_eq_sum (h.mono hsub), flipv_eq_sum (h.mono h₁), flipv_eq_sum (h.mono h₂),
    sum_symmDiff_zmod]

/-! ### The reduction -/

/-- **Reduction of BKLO §9 to a combinatorial construction.**  If an edge-disjoint triangle family
`𝒯` can reproduce, modulo `2`, the part-degree vector of every triangle on `⋃ P`, then its edge set
is a parity graph. -/
theorem isParityGraphK3S_of_realizable {P : Finset (Finset V)} {idx : Finset V → ℕ}
    {𝒯 : Finset (Finset V)} (hfam : IsTriFamily 𝒯)
    (hreal : ∀ T₀ : Finset V, T₀.card = 3 → T₀ ⊆ P.biUnion id →
      ∃ 𝒮 : Finset (Finset V), 𝒮 ⊆ 𝒯 ∧ ∀ W ∈ P, ∀ x ∈ beforeParts P idx W,
        flipv 𝒮 x W = ((degTo (cliqueEdges T₀) x W : ℕ) : ZMod 2)) :
    IsParityGraphK3S P idx (famEdges 𝒯) := by
  classical
  refine ⟨hfam.triDecomp, ?_⟩
  intro Gstar hGS hdisj heven
  -- every `2`-divisible graph on `⋃ P` is an `F₂`-sum of triangles
  obtain ⟨L, hL, hLeq⟩ := even_graph_triSum (S := P.biUnion id) Gstar.card Gstar le_rfl hGS heven
  -- realize the sum of their parity vectors
  have hmain : ∀ L' : List (Finset V), (∀ T ∈ L', T.card = 3 ∧ T ⊆ P.biUnion id) →
      ∃ 𝒮 : Finset (Finset V), 𝒮 ⊆ 𝒯 ∧ ∀ W ∈ P, ∀ x ∈ beforeParts P idx W,
        flipv 𝒮 x W = ((degTo (triSum L') x W : ℕ) : ZMod 2) := by
    intro L'
    induction L' with
    | nil =>
      intro _
      refine ⟨∅, Finset.empty_subset _, fun W hW x hx => ?_⟩
      simp [flipv, famEdges, degTo, nbhdIn]
    | cons T L' ih =>
      intro hall
      obtain ⟨𝒮₁, h₁sub, h₁⟩ := hreal T (hall T (by simp)).1 (hall T (by simp)).2
      obtain ⟨𝒮₂, h₂sub, h₂⟩ := ih fun T' hT' => hall T' (by simp [hT'])
      refine ⟨symmDiff 𝒮₁ 𝒮₂, ?_, fun W hW x hx => ?_⟩
      · intro T' hT'
        rcases Finset.mem_symmDiff.1 hT' with ⟨hT1, -⟩ | ⟨hT2, -⟩
        · exact h₁sub hT1
        · exact h₂sub hT2
      · rw [flipv_symmDiff hfam h₁sub h₂sub, h₁ W hW x hx, h₂ W hW x hx, triSum_cons,
          degTo_symmDiff_zmod]
  obtain ⟨𝒮, h𝒮sub, h𝒮⟩ := hmain L hL
  refine ⟨famEdges 𝒮, famEdges_mono h𝒮sub, ?_, ?_⟩
  · rw [famEdges_sdiff hfam h𝒮sub]
    exact (hfam.mono Finset.sdiff_subset).triDecomp
  · intro W hW x hx
    have hdisj' : Disjoint Gstar (famEdges 𝒮) :=
      Finset.disjoint_of_subset_right (famEdges_mono h𝒮sub) hdisj
    have hsplit : degTo (Gstar ∪ famEdges 𝒮) x W
        = degTo Gstar x W + degTo (famEdges 𝒮) x W := degTo_union_edges hdisj' x W
    have hflip : flipv 𝒮 x W = ((degTo Gstar x W : ℕ) : ZMod 2) := by
      rw [h𝒮 W hW x hx, hLeq]
    rw [even_iff_natCast_zmod, hsplit]
    push_cast
    rw [← flipv, hflip]
    ring_nf
    rw [show ((2 : ZMod 2)) = 0 by decide]
    ring

end BKLO
