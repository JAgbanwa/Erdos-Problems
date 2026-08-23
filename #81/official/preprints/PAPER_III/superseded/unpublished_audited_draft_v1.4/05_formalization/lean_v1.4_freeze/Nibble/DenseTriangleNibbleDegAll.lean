/-
# Nibble — `DenseTriangleNibbleDeg` for **every** `β > 0`

The known route to the per-vertex bound (`Nibble.denseTriangleNibbleDeg_final`) runs the length-one
swap engine and walls at `β > 1/10`.  This file removes the wall.

The argument is a *global potential* argument.  Take a packing `M` minimising

  `Nibble.uncoveredPot G M = ∑_v |uncoveredAt G M v|²`

over **all** packings.  Its potential is at most that of the global-leftover packing `M₀` supplied
by `Nibble.denseGlobalSmallLeftover_final`, so `Φ(M) ≤ |V| · uncoveredTot(M₀) ≤ ε₀|V|³`.  Hence the
*expensive* vertices `Zexp` (uncovered star bigger than `d/64`) are few, and
`Nibble.exists_pot_decrease` then produces a strictly improving move at any vertex whose uncovered
star exceeds `β|V|` — contradicting minimality.  Choosing `ε₀ = β³/(5·10⁹)` makes the counting work
for every `β > 0`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.StarAugment
import Nibble.DrossCutCert

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A packing minimising the potential among **all** packings (no leftover constraint). -/
theorem exists_min_pot_all (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
      ∀ M' : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M' →
        uncoveredPot G M ≤ uncoveredPot G M' := by
  classical
  set S : Finset (Finset (Finset (EdgeV G))) :=
    (Finset.univ : Finset (Finset (Finset (EdgeV G)))).filter
      (fun M => IsMatching (triangleHypergraphSub G) M) with hS
  have hne : S.Nonempty := by
    refine ⟨(∅ : Finset (Finset (EdgeV G))), ?_⟩
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Finset.empty_subset _, fun e he => absurd he (Finset.notMem_empty e)⟩
  obtain ⟨M, hM, hmin⟩ := S.exists_min_image (uncoveredPot G) hne
  obtain ⟨-, hMmatch⟩ := Finset.mem_filter.mp hM
  refine ⟨M, hMmatch, fun M' hM' => hmin M' ?_⟩
  rw [hS, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hM'⟩

/-- The potential is at most `|V|` times the total uncovered incidence count. -/
theorem uncoveredPot_le_card_mul_tot (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset (EdgeV G))) :
    uncoveredPot G M ≤ Fintype.card V * uncoveredTot G M := by
  classical
  rw [uncoveredPot, uncoveredTot, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro u _
  have := unDeg_le_card G M u
  nlinarith [Nat.zero_le (unDeg G M u)]

/-- **Expensive vertices are heavy.**  Each `u ∈ Zexp G M dd` contributes at least `(dd/64)²` to the
potential, so `|Zexp| · dd² ≤ 4096 · Φ`. -/
theorem card_Zexp_mul_sq_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset (EdgeV G))) (dd : ℕ) :
    (Zexp G M dd).card * dd ^ 2 ≤ 4096 * uncoveredPot G M := by
  classical
  have hterm : ∀ u ∈ Zexp G M dd, dd ^ 2 ≤ 4096 * (unDeg G M u) ^ 2 := by
    intro u hu
    have h := (mem_Zexp G).mp hu
    push_neg at h
    nlinarith only [h.le]
  calc (Zexp G M dd).card * dd ^ 2
      = ∑ _u ∈ Zexp G M dd, dd ^ 2 := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ u ∈ Zexp G M dd, 4096 * (unDeg G M u) ^ 2 := Finset.sum_le_sum hterm
    _ ≤ ∑ u : V, 4096 * (unDeg G M u) ^ 2 :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 4096 * uncoveredPot G M := by rw [uncoveredPot, Finset.mul_sum]

/-- **The per-vertex star bound with no wall**: at the Dross density every `β > 0` is achievable. -/
theorem denseTriangleNibbleDeg_all : DenseTriangleNibbleDeg := by
  intro β hβ
  classical
  set ε₀ : ℝ := β ^ 3 / (5 * 10 ^ 9) with hε₀def
  have hε₀ : 0 < ε₀ := by positivity
  obtain ⟨n₁, hglob⟩ := denseGlobalSmallLeftover_final ε₀ hε₀
  refine ⟨max n₁ (Nat.ceil (4000 / β)), ?_⟩
  intro V _ _ G _ hV hdense
  obtain ⟨M₀, hM₀, hM₀tot⟩ := hglob G (le_trans (le_max_left _ _) hV) hdense
  obtain ⟨M, hM, hmin⟩ := exists_min_pot_all G
  refine ⟨M, hM, ?_⟩
  intro v
  by_contra hcon
  push_neg at hcon
  set n := Fintype.card V with hn
  set d := unDeg G M v with hd
  have hdcon : β * (n : ℝ) < (d : ℝ) := by
    rw [hd, unDeg]; exact hcon
  -- `n` is large enough that `β n ≥ 4000`
  have hnbig : (4000 : ℝ) / β ≤ (n : ℝ) := by
    have h1 : (Nat.ceil (4000 / β) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (le_max_right n₁ _) hV
    exact le_trans (Nat.le_ceil _) h1
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℝ) < 4000 / β := by positivity
    linarith
  have hbigR : (4000 : ℝ) < (d : ℝ) := by
    have : (4000 : ℝ) ≤ β * (n : ℝ) := by
      rw [div_le_iff₀ hβ] at hnbig
      linarith
    linarith
  have hbig : 4000 ≤ d := by
    have : (4000 : ℕ) < d := by exact_mod_cast hbigR
    omega
  -- the expensive vertices are few
  have hZ : 1000000 * (Zexp G M d).card ≤ d := by
    have h1 : ((Zexp G M d).card : ℝ) * (d : ℝ) ^ 2 ≤ 4096 * (uncoveredPot G M : ℝ) := by
      exact_mod_cast card_Zexp_mul_sq_le G M d
    have h2 : (uncoveredPot G M : ℝ) ≤ (uncoveredPot G M₀ : ℝ) := by
      exact_mod_cast hmin M₀ hM₀
    have h3 : (uncoveredPot G M₀ : ℝ) ≤ (n : ℝ) * (uncoveredTot G M₀ : ℝ) := by
      exact_mod_cast uncoveredPot_le_card_mul_tot G M₀
    have h4 : (uncoveredTot G M₀ : ℝ) ≤ ε₀ * (n : ℝ) ^ 2 := hM₀tot
    have hD : (0 : ℝ) < (d : ℝ) := by linarith
    have hZc : (0 : ℝ) ≤ ((Zexp G M d).card : ℝ) := Nat.cast_nonneg _
    have hcube : β ^ 3 * (n : ℝ) ^ 3 < (d : ℝ) ^ 3 := by
      have hbn : (0 : ℝ) ≤ β * (n : ℝ) := by positivity
      have h := pow_lt_pow_left₀ hdcon hbn (n := 3) (by norm_num)
      rwa [mul_pow] at h
    have hkey : (1000000 * ((Zexp G M d).card : ℝ)) * (d : ℝ) ^ 2 < (d : ℝ) * (d : ℝ) ^ 2 := by
      have hstep : (1000000 : ℝ) * (((Zexp G M d).card : ℝ) * (d : ℝ) ^ 2)
          ≤ (4096 / 5000) * (β ^ 3 * (n : ℝ) ^ 3) := by
        have hb : (uncoveredTot G M₀ : ℝ) ≤ β ^ 3 * (n : ℝ) ^ 2 / (5 * 10 ^ 9) := by
          rw [hε₀def] at h4; linarith only [h4]
        have h5 : (uncoveredPot G M : ℝ) ≤ (n : ℝ) * (β ^ 3 * (n : ℝ) ^ 2 / (5 * 10 ^ 9)) := by
          have := mul_le_mul_of_nonneg_left hb (le_of_lt hn0)
          linarith
        linarith
      have hlt : (4096 / 5000 : ℝ) * (β ^ 3 * (n : ℝ) ^ 3)
          < (4096 / 5000 : ℝ) * ((d : ℝ) ^ 3) := by
        have : (0 : ℝ) < 4096 / 5000 := by norm_num
        exact mul_lt_mul_of_pos_left hcube this
      have hle2 : (4096 / 5000 : ℝ) * ((d : ℝ) ^ 3) ≤ (d : ℝ) * (d : ℝ) ^ 2 := by
        linarith only [pow_pos hD 3]
      linarith
    have hfinal : 1000000 * ((Zexp G M d).card : ℝ) < (d : ℝ) :=
      lt_of_mul_lt_mul_right hkey (le_of_lt (pow_pos hD 2))
    have : (1000000 * (Zexp G M d).card : ℕ) < d := by exact_mod_cast hfinal
    omega
  obtain ⟨M', hM', hlt⟩ := exists_pot_decrease G hdense hM v hbig (by rw [← hd]; exact hZ)
  exact absurd (hmin M' hM') (not_le.mpr hlt)

/-- **The degree-bounded approximate triangle decomposition at density `9/10`, unconditionally.**
Every `β > 0` is achievable: the residual `Nibble.DenseTriangleNibbleDeg` is now a theorem. -/
theorem dense_approx_deg_bounded_all (β : ℝ) (hβ : 0 < β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ (P : Finset (Finset V)) (L : Finset (Sym2 V)),
        (∀ t ∈ P, G.IsNClique 3 t) ∧
        (P : Set (Finset V)).Pairwise (fun s t => Disjoint (edgesOf s) (edgesOf t)) ∧
        L = G.edgeFinset \ (P.biUnion edgesOf) ∧
        (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 ∧
        (∀ v : V, (L.filter (fun e => v ∈ e)).card ≤ ⌈β * (Fintype.card V : ℝ)⌉₊) :=
  dense_approx_deg_bounded denseTriangleNibbleDeg_all β hβ

end Nibble
