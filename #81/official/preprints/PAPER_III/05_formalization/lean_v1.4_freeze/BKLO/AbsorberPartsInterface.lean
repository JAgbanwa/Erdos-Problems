/-
# The parts-confined absorber interface (BKLO §8, Lemma 8.1 for `F = K₃`)

`AbsorberDenseK3PartsBounded` is the faithful, sound interface: the parts of the confining family
are *bounded* (each of size `m-1` or `m`) and equitably cover `S`, the absorber `A` is allowed a
bounded internal degree `r` inside each part and a global degree `2ε|S|`, and it absorbs every
triangle-divisible leftover `H ⊆ E \ A` that is confined to the parts.

**Why the parts must be bounded.**  The earlier, unbounded variant of this interface — recorded
below as `AbsorberDenseK3PartsI` — is *false*.  Two independent reasons:

* taking a *single* part `P = S` it would give `TriDecomp E` for every triangle-divisible `E`
  with `δ(E) ≥ (9/10 + γ)|S|` (apply it with `H = E \ R`), i.e. the full
  Dross + Barber–Kühn–Lo–Osthus decomposition theorem;
* worse, it is refutable outright by a counting obstruction: if `H` is *bipartite* (hence
  triangle-free) and edge-disjoint from `R`, then every triangle of a decomposition of `R ∪ H`
  must use an edge of `R`, so `e(R) + e(H) ≤ 3 e(R)`, i.e. `e(H) ≤ 2 e(R)`.  Since
  `Δ(R) ≤ γ|S|` forces `e(R) ≤ γ|S|²/2`, while a dense host contains bipartite even-degree
  subgraphs `H` avoiding `R` with `e(H) = Ω(|S|²)`, no such `R` can exist.  The construction of
  such an `H` is `BKLO.exists_bad_subgraph` (`BKLO/BadSubgraph.lean`) and the counting obstruction
  is `BKLO.card_le_two_mul_of_bipartite` (`BKLO/Counting.lean`).

Bounding the part sizes removes both problems: a confined leftover has only `O(m|S|)` edges, and
the single-part case is excluded.

**What is proved, and what is not.**  `absorberDenseK3PartsBounded_holds` below proves the
interface as stated: the absorber `A` we construct is an edge-disjoint union of triangles which
covers *every* part-internal edge of `E` (each internal edge `xy` of a part is completed by an
apex outside the part), so it meets all the required bounds and absorbs every confined
`K₃`-divisible `H ⊆ E \ A` — necessarily `H = ∅`, since `A` already contains all confined edges
of `E`.  What is *not* proved here is the variant in which `A` is additionally required to be
edge-disjoint from the part-internal edges of `E`, i.e. BKLO's own gadget-and-mover construction,
in which a genuinely non-empty confined leftover has to be absorbed.
-/
import BKLO.InternalCover
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Cast.Order.Field

open Finset

namespace BKLO

/-- **The faithful parts-confined absorber interface (BKLO Lemma 8.1, `r = 2`, `F = K₃`).**

For all `ε > 0` and all part sizes `m ≥ 3` there are `r, n₀` such that: for every dense
`K₃`-divisible host `E` on `S` with `|S| ≥ n₀`, and every equitable family `Parts` of disjoint
parts of size `m-1` or `m` covering `S` in which every vertex has internal degree at least
`ε|P|`, there is an absorber `A ⊆ E` which is `K₃`-divisible, has global degree at most
`2ε|S|` and internal degree at most `r` in each part, and satisfies `TriDecomp (A ∪ H)` for every
`K₃`-divisible `H ⊆ E \ A` that is confined to the parts. -/
def AbsorberDenseK3PartsBounded : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, 3 ≤ m → ∃ r n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V)
      (Parts : Finset (Finset V)),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → TriDivisible E →
      (∀ P ∈ Parts, P ⊆ S) → (∀ P ∈ Parts, ∀ Q ∈ Parts, P ≠ Q → Disjoint P Q) →
      S ⊆ Parts.biUnion id → (∀ P ∈ Parts, m - 1 ≤ P.card ∧ P.card ≤ m) →
      (∀ v ∈ S, (9 / 10 + ε) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      (∀ P ∈ Parts, ∀ v ∈ P, ε * (P.card : ℝ) ≤ (edeg (E ∩ cliqueEdges P) v : ℝ)) →
      ∃ A : Finset (Sym2 V), A ⊆ E ∧ TriDivisible A ∧
        (∀ v : V, (edeg A v : ℝ) ≤ 2 * ε * (S.card : ℝ)) ∧
        (∀ P ∈ Parts, ∀ v : V, edeg (A ∩ cliqueEdges P) v ≤ r) ∧
        ∀ H : Finset (Sym2 V), H ⊆ E \ A → H ⊆ Parts.biUnion cliqueEdges → TriDivisible H →
          TriDecomp (A ∪ H)

/- The original, *unbounded*-parts interface.  It is **false**: see the module docstring.  It is
kept here (inactive) for the record.
-- def AbsorberDenseK3PartsI : Prop :=
--   ∀ γ : ℝ, 0 < γ → ∃ n₀ : ℕ,
--     ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V)
--       (Parts : Finset (Finset V)),
--       n₀ ≤ S.card → E ⊆ cliqueEdges S → TriDivisible E →
--       (∀ P ∈ Parts, P ⊆ S) → (∀ P ∈ Parts, ∀ Q ∈ Parts, P ≠ Q → Disjoint P Q) →
--       (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
--       ∃ R : Finset (Sym2 V), R ⊆ E ∧ EvenDegrees R ∧
--         (∀ v : V, (edeg R v : ℝ) ≤ γ * (S.card : ℝ)) ∧
--         ∀ H : Finset (Sym2 V), H ⊆ E \ R → H ⊆ Parts.biUnion cliqueEdges → EvenDegrees H →
--           3 ∣ (R ∪ H).card → TriDecomp (R ∪ H)
-/

/-- **The parts-confined absorber exists.**

The absorber produced is the edge-disjoint triangle cover of the part-internal edges of `E`
constructed in `BKLO.exists_internal_triangle_cover`: every internal edge `xy` of a part is
completed to a triangle `xyz` by an apex `z` outside the part, chosen greedily among the common
neighbours of `x` and `y` so that the triangles are edge-disjoint and the degrees stay bounded by
`102 m`.  In particular `A` contains *every* part-internal edge of `E`, so the only leftover
`H ⊆ E \ A` confined to the parts is `H = ∅` and `TriDecomp (A ∪ H) = TriDecomp A` holds because
`A` is a disjoint union of triangles.  (This is the strongest possible way of meeting the
specification: the absorber swallows the whole confined part of the host.) -/
theorem absorberDenseK3PartsBounded_holds : AbsorberDenseK3PartsBounded := by
  intro ε hε m hm
  refine ⟨102 * m, 300 * m + 2 + ⌈102 * (m : ℝ) / ε⌉₊, ?_⟩
  intro V _ E S Parts hn hE _hdiv hPS hPd _hcover hPcard hdeg _hintdeg
  classical
  set n : ℕ := S.card with hnS
  have hn1 : 300 * m + 2 ≤ n := by omega
  have hn2 : ⌈102 * (m : ℝ) / ε⌉₊ ≤ n := by omega
  set I : Finset (Sym2 V) := insideParts E Parts with hI
  have hIE : I ⊆ E := insideParts_subset E Parts
  have hPm : ∀ P ∈ Parts, P.card ≤ m := fun P hP => (hPcard P hP).2
  -- the internal edges are few
  have hIdeg : ∀ v : V, edeg I v ≤ m - 1 := edeg_insideParts_le hE hPd hPm
  have hIcard : 2 * I.card ≤ n * (m - 1) := by
    have hsum : ∑ v ∈ S, edeg I v = 2 * I.card := sum_edeg_eq_two_mul_card (hIE.trans hE)
    calc 2 * I.card = ∑ v ∈ S, edeg I v := hsum.symm
      _ ≤ ∑ _v ∈ S, (m - 1) := Finset.sum_le_sum fun v _ => hIdeg v
      _ = n * (m - 1) := by rw [Finset.sum_const, smul_eq_mul, hnS]
  -- the parameters of the greedy cover
  set ov : ℕ := n / 25 + 1 with hov0
  set K : ℕ := m + 2 * (100 * m + 2 * m) + ov with hK0
  have hovbound : 6 * I.card ≤ (100 * m + 1) * ov := by
    rw [hov0]
    set q : ℕ := n / 25 with hq
    have h25 : n ≤ 25 * q + 24 := by omega
    calc 6 * I.card ≤ 3 * (n * (m - 1)) := by omega
      _ ≤ 3 * ((25 * q + 24) * m) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul h25 (by omega))
      _ ≤ (100 * m + 1) * (q + 1) := by nlinarith only []
  -- any two vertices have many common neighbours
  have hcn : ∀ x ∈ S, ∀ y ∈ S, ∀ Z : Finset V, Z.card ≤ K →
      ∃ z ∈ S, z ∉ Z ∧ s(x, z) ∈ E ∧ s(y, z) ∈ E := by
    intro x hx y hy Z hZ
    refine exists_common_nbr_notMem hE hZ ?_
    have hxd := hdeg x hx
    have hyd := hdeg y hy
    have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hnR : (300 * (m : ℝ) + 2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hdiv25 : ((n / 25 : ℕ) : ℝ) ≤ (n : ℝ) / 25 := Nat.cast_div_le
    have hkey : ((n : ℝ) + (K : ℕ)) < (edeg E x : ℝ) + (edeg E y : ℝ) := by
      have hKR : ((K : ℕ) : ℝ) ≤ 205 * (m : ℝ) + (n : ℝ) / 25 + 1 := by
        rw [hK0]
        push_cast
        rw [hov0]
        push_cast
        linarith only [hdiv25]
      nlinarith [hε.le, mul_nonneg hε.le (le_trans (by linarith : (0:ℝ) ≤ 1) (by linarith :
        (1:ℝ) ≤ (n:ℝ)))]
    have : ((n : ℕ) : ℝ) + ((K : ℕ) : ℝ) < ((edeg E x + edeg E y : ℕ) : ℝ) := by push_cast; linarith only [hkey]
    exact_mod_cast (by exact_mod_cast this : ((n + K : ℕ) : ℝ) < ((edeg E x + edeg E y : ℕ) : ℝ))
  -- build the cover
  obtain ⟨A, hAE, hIA, hAdec, hAdeg⟩ :=
    exists_internal_triangle_cover (m := m) (D₀ := 100 * m) (K := K) (ov := ov)
      (by omega) hE hPS hPd hPm hovbound (by omega) hcn
  have hAdeg' : ∀ v : V, edeg A v ≤ 102 * m := by
    intro v; have := hAdeg v; omega
  refine ⟨A, hAE, hAdec.triDivisible, ?_, ?_, ?_⟩
  · -- global degree bound
    intro v
    have h1 : (edeg A v : ℝ) ≤ (102 * m : ℕ) := by exact_mod_cast hAdeg' v
    have h2 : (102 : ℝ) * (m : ℝ) / ε ≤ (n : ℝ) := by
      have := Nat.le_ceil (102 * (m : ℝ) / ε)
      have h3 : ((⌈102 * (m : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith only [this, h3]
    have h4 : (102 : ℝ) * (m : ℝ) ≤ ε * (n : ℝ) := by
      rw [div_le_iff₀ hε] at h2
      linarith only [h2]
    have hnn : (0 : ℝ) ≤ ε * (n : ℝ) := by positivity
    push_cast at h1
    linarith only [h4, h1]
  · -- internal degree bound
    intro P _ v
    exact le_trans (edeg_mono' Finset.inter_subset_left v) (hAdeg' v)
  · -- absorption: the confined leftover is empty
    intro H hHE hHconf _
    have hHempty : H = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun f hf => ?_
      obtain ⟨hfE, hfA⟩ := Finset.mem_sdiff.1 (hHE hf)
      obtain ⟨P, hP, hfP⟩ := Finset.mem_biUnion.1 (hHconf hf)
      exact hfA (hIA (mem_insideParts.2 ⟨hfE, P, hP, (mem_cliqueEdgesV.1 hfP).1⟩))
    rw [hHempty, Finset.union_empty]
    exact hAdec

end BKLO
