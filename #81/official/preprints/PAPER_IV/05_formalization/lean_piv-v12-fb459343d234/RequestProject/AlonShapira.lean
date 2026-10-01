module

public import RequestProject.AS.Lemma42
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Alon–Shapira, Lemma 4.2

Formalization of Lemma 4.2 of N. Alon and A. Shapira,
*A characterization of the (natural) graph properties testable with one-sided error*:

> For every (possibly infinite) family of graphs `𝓕`, there are functions `N_𝓕(ε)`, `f_𝓕(ε)`
> and `δ_𝓕(ε)` such that the following holds for any `ε > 0`: if a graph `G` on `n ≥ N_𝓕(ε)`
> vertices is `ε`-far from being induced `𝓕`-free, then `G` contains `δ n^f` induced copies of a
> graph `F ∈ 𝓕` of size `f`, where `f ≤ f_𝓕(ε)` and `δ ≥ δ_𝓕(ε)`.

We then specialise it to the hereditary property "being chordal", whose family of forbidden
induced subgraphs is `{C₄, C₅, C₆, …}`, and derive the "reversed" form used to show that a graph
with few induced cycles of every bounded length is `εn²`-close (in edit distance) to a chordal
graph.

## Conventions

* A family of graphs is `𝓕 : ∀ k, Set (SimpleGraph (Fin k))`: `𝓕 k` are the members with
  exactly `k` vertices (so "size `f`" of the paper is the index `k`).
* The input graph `G` has vertex set `Fin n`.
* "ε-far" means: every induced-`𝓕`-free graph `G'` on the same vertex set differs from `G` in at
  least `ε n²` pairs (edges added or removed), exactly as in the paper.
* "Induced copies" are counted as *labelled* induced embeddings `H ↪g G` (injective maps that
  preserve both adjacency and non-adjacency), i.e. ordered `k`-tuples of vertices spanning an
  induced copy of `H`. This differs from the count of unlabelled copies by a factor between `1`
  and `k! ≤ f_𝓕(ε)!`, so the two versions of the lemma are equivalent up to changing `δ_𝓕`.
-/

@[expose] public section

open SimpleGraph

open scoped Classical

namespace AlonShapira

/-- **Lemma 4.2 of Alon–Shapira**, for every (possibly infinite) family of graphs.
The proof (`lemma42_holds`, in `RequestProject/AS/Lemma42.lean`) follows Section 5 of the paper,
using Lemma 3.8 (`AFKS.corollary_4_2`), Lemma 3.5 (`lemma_3_5`), the induced counting lemma
Lemma 3.2 (`counting_lemma`) and colored homomorphisms (`Psi`). -/
theorem lemma_4_2 (𝓕 : GraphFamily) : Lemma42 𝓕 :=
  lemma42_holds 𝓕

/-! ## Specialisation to chordal graphs -/

/-- The forbidden induced subgraphs of chordality: the cycles `C_k` with `k ≥ 4`. -/
def chordalFamily : GraphFamily := fun k => {H | 4 ≤ k ∧ H = cycleGraph k}

/-- A graph is *chordal* if it contains no induced cycle of length at least `4`
(equivalently: every cycle of length `≥ 4` has a chord). -/
def IsChordal {V : Type*} (G : SimpleGraph V) : Prop :=
  IndFree chordalFamily G

/-- Chordality is hereditary: if `G'` is an induced subgraph of a chordal graph `G`, then `G'`
is chordal. -/
theorem IsChordal.of_embedding {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}
    (hG : IsChordal G) (e : G' ↪g G) : IsChordal G' := by
  intro k H hH
  refine ⟨fun e' => ?_⟩
  exact (hG k H hH).false (e.comp e')

/-- Every induced subgraph of a chordal graph is chordal. -/
theorem IsChordal.induce {V : Type*} {G : SimpleGraph V} (hG : IsChordal G) (s : Set V) :
    IsChordal (G.induce s) :=
  hG.of_embedding (Embedding.induce s)

/-- Sanity check: the cycle `C_k` with `k ≥ 4` is not chordal. -/
theorem not_isChordal_cycleGraph {k : ℕ} (hk : 4 ≤ k) : ¬ IsChordal (cycleGraph k) :=
  fun h => (h k (cycleGraph k) ⟨hk, rfl⟩).false (Embedding.refl)

/-- `G` is `ε`-far from chordal: any way of making it chordal needs at least `ε n²` edits. -/
def FarFromChordal (ε : ℝ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  FarFromIndFree chordalFamily ε G

/-- **Lemma 4.2 for chordality.** For every `ε > 0` there are `K(ε)`, `N(ε)` and
`δ(ε) > 0` such that every graph on `n ≥ N(ε)` vertices that is `ε`-far from chordal contains at
least `δ(ε) n^k` induced copies of the cycle `C_k` for some `4 ≤ k ≤ K(ε)`. -/
theorem chordal_far_many_induced_cycles (h : Lemma42 chordalFamily) :
    ∃ N : ℝ → ℕ, ∃ K : ℝ → ℕ, ∃ δ : ℝ → ℝ,
      ∀ ε > 0, 0 < δ ε ∧
        ∀ n ≥ N ε, ∀ G : SimpleGraph (Fin n), FarFromChordal ε G →
          ∃ k, 4 ≤ k ∧ k ≤ K ε ∧ δ ε * (n : ℝ) ^ k ≤ indCopies (cycleGraph k) G := by
  obtain ⟨N, f, δ, hδ⟩ := h
  refine ⟨N, f, δ, fun ε hε => ⟨(hδ ε hε).1, fun n hn G hG => ?_⟩⟩
  obtain ⟨k, hk, H, ⟨h4, rfl⟩, hc⟩ := (hδ ε hε).2 n hn G hG
  exact ⟨k, h4, hk, hc⟩

/-- **Lemma 4.2 for chordality, used in reverse.** For every `ε > 0` there are `K(ε)`, `N(ε)` and
`δ(ε) > 0` such that every graph on `n ≥ N(ε)` vertices having fewer than `δ(ε) n^k` induced
copies of `C_k` for every `4 ≤ k ≤ K(ε)` is at edit distance `< ε n²` from a chordal graph. -/
theorem near_chordal_of_few_induced_cycles (h : Lemma42 chordalFamily) :
    ∃ N : ℝ → ℕ, ∃ K : ℝ → ℕ, ∃ δ : ℝ → ℝ,
      ∀ ε > 0, 0 < δ ε ∧
        ∀ n ≥ N ε, ∀ G : SimpleGraph (Fin n),
          (∀ k, 4 ≤ k → k ≤ K ε → (indCopies (cycleGraph k) G : ℝ) < δ ε * (n : ℝ) ^ k) →
            ∃ G' : SimpleGraph (Fin n), IsChordal G' ∧ (editDist G G' : ℝ) < ε * (n : ℝ) ^ 2 := by
  obtain ⟨N, K, δ, hδ⟩ := chordal_far_many_induced_cycles h
  refine ⟨N, K, δ, fun ε hε => ⟨(hδ ε hε).1, fun n hn G hG => ?_⟩⟩
  by_contra hne
  push_neg at hne
  obtain ⟨k, h4, hk, hc⟩ := (hδ ε hε).2 n hn G hne
  exact absurd hc (not_le.mpr (hG k h4 hk))

/-- **Asymptotic form of the reversed lemma.** Let `P` be any class of finite graphs
(`P n G` for `G` on `n` vertices) in which, for each fixed `k ≥ 4`, the number of induced `C_k`
is `o(n^k)`. Then for every `ε > 0`, every graph of `P` on sufficiently many vertices is at edit
distance `< ε n²` from a chordal graph. -/
theorem near_chordal_of_induced_cycles_littleO (h : Lemma42 chordalFamily)
    (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop)
    (hP : ∀ k, 4 ≤ k → ∀ δ > (0 : ℝ), ∃ M : ℕ, ∀ n ≥ M, ∀ G : SimpleGraph (Fin n), P n G →
      (indCopies (cycleGraph k) G : ℝ) < δ * (n : ℝ) ^ k) :
    ∀ ε > (0 : ℝ), ∃ M : ℕ, ∀ n ≥ M, ∀ G : SimpleGraph (Fin n), P n G →
      ∃ G' : SimpleGraph (Fin n), IsChordal G' ∧ (editDist G G' : ℝ) < ε * (n : ℝ) ^ 2 := by
  obtain ⟨N, K, δ, hδ⟩ := near_chordal_of_few_induced_cycles h
  intro ε hε
  obtain ⟨hδpos, hmain⟩ := hδ ε hε
  -- a threshold for each `k`
  let Mk : ℕ → ℕ := fun k => if hk : 4 ≤ k then Classical.choose (hP k hk (δ ε) hδpos) else 0
  refine ⟨max (N ε) ((Finset.range (K ε + 1)).sup Mk), fun n hn G hG => ?_⟩
  refine hmain n (le_trans (le_max_left _ _) hn) G fun k h4 hk => ?_
  have hMk : Mk k ≤ n := by
    refine le_trans ?_ (le_trans (le_max_right _ _) hn)
    exact Finset.le_sup (f := Mk) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hspec := Classical.choose_spec (hP k h4 (δ ε) hδpos)
  simp only [Mk, dif_pos h4] at hMk
  exact hspec n hMk G hG

/-! ## Unconditional versions (using the proof of Lemma 4.2) -/

/-- Lemma 4.2 for chordality, unconditionally. -/
theorem chordal_far_many_induced_cycles' :
    ∃ N : ℝ → ℕ, ∃ K : ℝ → ℕ, ∃ δ : ℝ → ℝ,
      ∀ ε > 0, 0 < δ ε ∧
        ∀ n ≥ N ε, ∀ G : SimpleGraph (Fin n), FarFromChordal ε G →
          ∃ k, 4 ≤ k ∧ k ≤ K ε ∧ δ ε * (n : ℝ) ^ k ≤ indCopies (cycleGraph k) G :=
  chordal_far_many_induced_cycles (lemma_4_2 chordalFamily)

/-- Lemma 4.2 for chordality used in reverse, unconditionally. -/
theorem near_chordal_of_few_induced_cycles' :
    ∃ N : ℝ → ℕ, ∃ K : ℝ → ℕ, ∃ δ : ℝ → ℝ,
      ∀ ε > 0, 0 < δ ε ∧
        ∀ n ≥ N ε, ∀ G : SimpleGraph (Fin n),
          (∀ k, 4 ≤ k → k ≤ K ε → (indCopies (cycleGraph k) G : ℝ) < δ ε * (n : ℝ) ^ k) →
            ∃ G' : SimpleGraph (Fin n), IsChordal G' ∧ (editDist G G' : ℝ) < ε * (n : ℝ) ^ 2 :=
  near_chordal_of_few_induced_cycles (lemma_4_2 chordalFamily)

/-- Asymptotic reversed form, unconditionally: in any class of graphs with `o(n^k)` induced
`C_k` for every fixed `k ≥ 4`, large graphs are `< εn²` edits away from a chordal graph. -/
theorem near_chordal_of_induced_cycles_littleO'
    (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop)
    (hP : ∀ k, 4 ≤ k → ∀ δ > (0 : ℝ), ∃ M : ℕ, ∀ n ≥ M, ∀ G : SimpleGraph (Fin n), P n G →
      (indCopies (cycleGraph k) G : ℝ) < δ * (n : ℝ) ^ k) :
    ∀ ε > (0 : ℝ), ∃ M : ℕ, ∀ n ≥ M, ∀ G : SimpleGraph (Fin n), P n G →
      ∃ G' : SimpleGraph (Fin n), IsChordal G' ∧ (editDist G G' : ℝ) < ε * (n : ℝ) ^ 2 :=
  near_chordal_of_induced_cycles_littleO (lemma_4_2 chordalFamily) P hP

end AlonShapira
