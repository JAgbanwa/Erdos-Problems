/-
# Nibble — the per-vertex leftover bound at `1/2`, and the quadratic route below it

This file sharpens `Nibble.dense_uncoveredAt_le` (the unconditional `11/20` bound of
`Nibble.DenseTriangleNibbleDegProof`) to `1/2`, by a new double count on top of the same two local
moves.

The extra input is the following counting step.  Let `M` be a potential-minimal matching, let `v₀`
maximise the uncovered star size `D = |uncoveredAt M v₀|`, put `A = unNbr M v₀` (so `|A| = D`), let
`B = {z : D ≤ |uncoveredAt M z| + 2}` be the set of vertices with an almost maximal uncovered star,
and let `C` be the rest.  If `2D > |V| + 4` then:

* `A ∩ B = ∅` and `B` carries no uncovered edge, because two vertices joined by an uncovered edge
  have disjoint uncovered stars (`Nibble.unDeg_add_le_of_mem_unNbr`, from `no_free_triangle`);
* hence the uncovered star of any `z ∈ B` lies in `A ∪ C`, so `z` sends at most `|C| + 2` *covered*
  edges into `A` (`Nibble.card_sdiff_unNbr_le`);
* every `G`-edge inside `A` is covered by a packing triangle whose apex lies in `B`
  (`no_free_triangle` and `swap_stability`), and the map `(a, a') ↦ (apex, a)` is injective
  (`Nibble.card_adjPairs_le`), since a matching has at most one triangle through a given edge;
* the Dross density `9|V| ≤ 10 δ(G)` makes `A` dense: `10 · 2e(A) ≥ D(10D − |V|)`.

Together these give `10D² ≤ 10|B|(|C| + 2) + D|V|` with `D + |B| + |C| = |V|`, which is
inconsistent with `2D > |V| + 4`.  Hence:

* `Nibble.dense_uncoveredAt_le_half` — **the unconditional output**: at the Dross density
  `9|V| ≤ 10 δ(G)`, some edge-disjoint triangle family leaves at most `(|V| + 4)/2` uncovered edges
  at every vertex;
* `Nibble.denseTriangleNibbleDeg_of_half_lt` — the residual `Nibble.DenseTriangleNibbleDeg` holds
  for every `β > 1/2`;
* `Nibble.DenseTriangleNibbleDegVerySmall`, `Nibble.denseTriangleNibbleDeg_of_verySmall` — the
  narrowed residual (`0 < β ≤ 1/2`) and the machine-checked reduction to it.

The last section records the conditional route below `1/2`: with the global input
`Nibble.DenseGlobalSmallLeftover` (a triangle packing leaving `o(|V|²)` uncovered incidences at the
Dross density — an approximate triangle decomposition, which is *not* available in this library at
`δ(G) ≥ (9/10)|V|`; `Nibble.dense_approx_global` supplies it only in the near-complete regime), the
quadratic engine `Nibble.dense_uncoveredAt_quadratic` pushes the per-vertex bound all the way down
to `1/10`: `Nibble.denseTriangleNibbleDeg_of_tenth_lt`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DenseTriangleNibbleDegProof

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### A cardinality helper -/

/-- The number of adjacent pairs in a product, fibrewise. -/
theorem card_filter_product {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (p : α → β → Prop) [DecidableRel p] :
    ((s ×ˢ t).filter (fun q => p q.1 q.2)).card = ∑ a ∈ s, (t.filter (p a)).card := by
  rw [Finset.card_filter, Finset.sum_product]
  exact Finset.sum_congr rfl (fun a _ => (Finset.card_filter _ _).symm)

/-! ### Two vertices joined by an uncovered edge have disjoint uncovered stars -/

/-- **Uncovered stars along an uncovered edge are disjoint.**  If `w` is joined to `v` by an
uncovered edge of a potential-minimal matching, then the uncovered stars at `v` and at `w` are
disjoint (a common uncovered neighbour would complete a triangle with three uncovered edges), so
their sizes add up to at most `|V|`. -/
theorem unDeg_add_le_of_mem_unNbr (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    (hmin : ∀ M' : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M' →
      uncoveredTot G M' ≤ uncoveredTot G M → uncoveredPot G M ≤ uncoveredPot G M')
    {v w : V} (hw : w ∈ unNbr G M v) :
    unDeg G M v + unDeg G M w ≤ Fintype.card V := by
  classical
  obtain ⟨hvw, huvw⟩ := (mem_unNbr G).mp hw
  have hdisj : Disjoint (unNbr G M v) (unNbr G M w) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    obtain ⟨hvu, h1⟩ := (mem_unNbr G).mp hu
    obtain ⟨hwu, h2⟩ := (mem_unNbr G).mp hu'
    exact no_free_triangle G hM hmin hvw hwu hvu huvw h2 h1
  have hun := Finset.card_union_of_disjoint hdisj
  have hle : (unNbr G M v ∪ unNbr G M w).card ≤ Fintype.card V := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  rw [card_unNbr, card_unNbr] at hun
  omega

/-! ### The core double count -/

/-- **The core double count.**  A potential-minimal matching at the Dross density has no vertex
whose uncovered star exceeds `(|V| + 4)/2`. -/
theorem star_counting_contradiction (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree)
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    (hmin : ∀ M' : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M' →
      uncoveredTot G M' ≤ uncoveredTot G M → uncoveredPot G M ≤ uncoveredPot G M')
    (v₀ : V) (hbig : Fintype.card V + 5 ≤ 2 * unDeg G M v₀) : False := by
  classical
  set n := Fintype.card V with hn
  set D := unDeg G M v₀ with hD
  set A := unNbr G M v₀ with hA
  have hAcard : A.card = D := card_unNbr G M v₀
  set B := Finset.univ.filter (fun z : V => D ≤ unDeg G M z + 2) with hB
  set C := (Finset.univ : Finset V) \ (A ∪ B) with hC
  -- (1) an uncovered edge from `v₀` lands on a vertex with a small uncovered star
  have hABdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a haA haB
    have h1 := unDeg_add_le_of_mem_unNbr G hM hmin haA
    have h2 : D ≤ unDeg G M a + 2 := (Finset.mem_filter.mp haB).2
    omega
  -- (2) the three parts `A`, `B`, `C` count `|V|`
  have hcards : D + B.card + C.card = n := by
    have h1 : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hABdisj
    have h2 : C.card + (A ∪ B).card = n := by
      rw [hC, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ]
    omega
  -- (3) every `z ∈ B` sends at most `|C| + 2` covered edges into `A`
  have hzbound : ∀ z ∈ B, (A \ unNbr G M z).card ≤ C.card + 2 := by
    intro z hzB
    have hzD : D ≤ unDeg G M z + 2 := (Finset.mem_filter.mp hzB).2
    have hsub : unNbr G M z \ A ⊆ C := by
      intro u hu
      rw [Finset.mem_sdiff] at hu
      rw [hC, Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Finset.mem_union]
      rintro (h | h)
      · exact hu.2 h
      · have h1 := unDeg_add_le_of_mem_unNbr G hM hmin hu.1
        have h2 : D ≤ unDeg G M u + 2 := (Finset.mem_filter.mp h).2
        omega
    have hc1 : (unNbr G M z \ A).card ≤ C.card := Finset.card_le_card hsub
    have h2 : (unNbr G M z ∩ A).card + (unNbr G M z \ A).card = unDeg G M z := by
      rw [Finset.card_inter_add_card_sdiff]; exact card_unNbr G M z
    have h3 : (A ∩ unNbr G M z).card + (A \ unNbr G M z).card = A.card :=
      Finset.card_inter_add_card_sdiff A _
    have h4 : (A ∩ unNbr G M z).card = (unNbr G M z ∩ A).card := by rw [Finset.inter_comm]
    omega
  -- (4) the two sides of the double count
  set P : Finset (V × V) := (A ×ˢ A).filter (fun p => G.Adj p.1 p.2) with hP
  set Q : Finset (V × V) := (B ×ˢ A).filter (fun q => q.2 ∉ unNbr G M q.1) with hQ
  have hPsum : P.card = ∑ a ∈ A, (A.filter (fun b => G.Adj a b)).card :=
    card_filter_product A A (fun a b => G.Adj a b)
  have hQsum : Q.card = ∑ z ∈ B, (A.filter (fun a => a ∉ unNbr G M z)).card :=
    card_filter_product B A (fun z a => a ∉ unNbr G M z)
  have hQeq : ∀ z : V, A.filter (fun a => a ∉ unNbr G M z) = A \ unNbr G M z := by
    intro z; ext a; simp [Finset.mem_sdiff]
  -- (5) `A` is dense, by the Dross density
  have hterm : ∀ a ∈ A, 10 * D ≤ 10 * (A.filter (fun b => G.Adj a b)).card + n := by
    intro a _
    have heq : A.filter (fun b => G.Adj a b) = A ∩ G.neighborFinset a := by
      ext b; simp [SimpleGraph.mem_neighborFinset]
    have hunion := Finset.card_inter_add_card_union A (G.neighborFinset a)
    have hun_le : (A ∪ G.neighborFinset a).card ≤ n := by
      rw [hn, ← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
    have hdeg : 9 * n ≤ 10 * G.degree a :=
      le_trans hdense (Nat.mul_le_mul_left 10 (SimpleGraph.minDegree_le_degree G a))
    have hnb : (G.neighborFinset a).card = G.degree a := rfl
    rw [heq]
    omega
  have hPlow : 10 * D * D ≤ 10 * P.card + D * n := by
    calc 10 * D * D = ∑ _a ∈ A, 10 * D := by
          rw [Finset.sum_const, hAcard, smul_eq_mul]; ring
      _ ≤ ∑ a ∈ A, (10 * (A.filter (fun b => G.Adj a b)).card + n) := Finset.sum_le_sum hterm
      _ = 10 * P.card + D * n := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hPsum, Finset.sum_const, hAcard,
            smul_eq_mul]
  have hQle : Q.card ≤ B.card * (C.card + 2) := by
    rw [hQsum]
    calc ∑ z ∈ B, (A.filter (fun a => a ∉ unNbr G M z)).card
        ≤ ∑ _z ∈ B, (C.card + 2) :=
          Finset.sum_le_sum (fun z hz => by rw [hQeq z]; exact hzbound z hz)
      _ = B.card * (C.card + 2) := by rw [Finset.sum_const, smul_eq_mul]
  -- (6) every `G`-edge inside `A` is covered by a packing triangle with apex in `B`, and the
  -- apex together with one endpoint determines the edge
  have hPQ : P.card ≤ Q.card := by
    have hex : ∀ p : V × V, ∃ z : V, p ∈ P →
        (z, p.1) ∈ Q ∧ z ≠ p.1 ∧ z ≠ p.2 ∧
          ∃ (hab : G.Adj p.1 p.2) (hbz : G.Adj p.2 z) (haz : G.Adj p.1 z),
            triE G hab hbz haz ∈ M := by
      intro p
      by_cases hp : p ∈ P
      · obtain ⟨hmem, hadj⟩ := Finset.mem_filter.mp hp
        obtain ⟨haA, hbA⟩ := Finset.mem_product.mp hmem
        obtain ⟨hva, hua⟩ := (mem_unNbr G).mp haA
        obtain ⟨hvb, hub⟩ := (mem_unNbr G).mp hbA
        have hcov : ¬ UncE G M (edgeE G hadj) := fun hu =>
          no_free_triangle G hM hmin hva hadj hvb hua hu hub
        simp only [UncE, not_forall, not_not] at hcov
        obtain ⟨T, hT, hmemT⟩ := hcov
        obtain ⟨z, hbz, haz, hza, hzb, hTeq, hle⟩ :=
          swap_stability G hM hmin hva hvb hadj hua hub hT hmemT
        refine ⟨z, fun _ => ⟨?_, hza, hzb, hadj, hbz, haz, hTeq ▸ hT⟩⟩
        rw [hQ, Finset.mem_filter]
        refine ⟨Finset.mem_product.mpr ⟨?_, haA⟩, ?_⟩
        · rw [hB, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hle⟩
        · intro hmemU
          obtain ⟨hzu, huzu⟩ := (mem_unNbr G).mp hmemU
          have heq2 : edgeE G hzu = edgeE G haz := by
            rw [edgeE_eq_iff]; exact Finset.pair_comm z p.1
          refine huzu T hT ?_
          rw [heq2, hTeq, mem_triE]
          exact Or.inr (Or.inr rfl)
      · exact ⟨v₀, fun h => absurd h hp⟩
    choose f hf using hex
    refine Finset.card_le_card_of_injOn (fun p => (f p, p.1)) (fun p hp => (hf p hp).1) ?_
    rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hfeq, haa⟩ := heq
    subst haa
    obtain ⟨-, hza, hzb, hab, hbz, haz, hTmem⟩ := hf (a, b) hp
    have hd' := hf (a, b') hp'
    rw [← hfeq] at hd'
    obtain ⟨-, hza', hzb', hab', hb'z, haz', hT'mem⟩ := hd'
    have hE : edgeE G haz ∈ triE G hab hbz haz := by rw [mem_triE]; exact Or.inr (Or.inr rfl)
    have hE' : edgeE G haz ∈ triE G hab' hb'z haz' := by
      rw [mem_triE]
      exact Or.inr (Or.inr ((edgeE_eq_iff G haz haz').mpr rfl).symm)
    have hTT : triE G hab hbz haz = triE G hab' hb'z haz' := by
      by_contra hne
      exact Finset.disjoint_left.mp (hM.disjoint _ hTmem _ hT'mem hne) hE hE'
    have hmem' : edgeE G hab' ∈ triE G hab hbz haz := by
      rw [hTT, mem_triE]; exact Or.inl rfl
    rw [mem_triE] at hmem'
    have hbb : b' = b := by
      rcases hmem' with h | h | h
      · have hpair := (edgeE_eq_iff G hab' hab).mp h
        have hmm : b' ∈ ({a, b} : Finset V) := by rw [← hpair]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmm
        rcases hmm with rfl | rfl
        · exact absurd rfl hab'.ne'
        · rfl
      · have hpair := (edgeE_eq_iff G hab' hbz).mp h
        have hmm : a ∈ ({b, f (a, b)} : Finset V) := by rw [← hpair]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmm
        rcases hmm with h1 | h1
        · exact absurd h1 hab.ne
        · exact absurd h1.symm hza
      · have hpair := (edgeE_eq_iff G hab' haz).mp h
        have hmm : b' ∈ ({a, f (a, b)} : Finset V) := by rw [← hpair]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmm
        rcases hmm with rfl | rfl
        · exact absurd rfl hab'.ne'
        · exact absurd rfl hzb'
    rw [hbb]
  -- (7) the two bounds are incompatible with `2D > |V| + 4`
  have hfinal : 10 * D * D ≤ 10 * (B.card * (C.card + 2)) + D * n :=
    le_trans hPlow
      (Nat.add_le_add_right (Nat.mul_le_mul_left 10 (le_trans hPQ hQle)) _)
  zify at hfinal hcards hbig
  have hb : (0 : ℤ) ≤ (B.card : ℤ) := Int.natCast_nonneg _
  have hc : (0 : ℤ) ≤ (C.card : ℤ) := Int.natCast_nonneg _
  nlinarith [sq_nonneg ((B.card : ℤ) - C.card), mul_nonneg hb hc,
    mul_nonneg (by linarith : (0 : ℤ) ≤ (D : ℤ) - B.card - C.card - 5)
      (by linarith : (0 : ℤ) ≤ (D : ℤ) + B.card + C.card)]

/-- **The unconditional per-vertex leftover bound at `1/2`.**  Every graph with `9|V| ≤ 10 δ(G)`
has an edge-disjoint family of triangles whose uncovered star at every vertex has at most
`(|V| + 4)/2` edges. -/
theorem dense_uncoveredAt_le_half (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) :
    ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
      ∀ v : V, 2 * (uncoveredAt G M v).card ≤ Fintype.card V + 4 := by
  classical
  obtain ⟨M, hM, hmin⟩ := exists_min_pot G
  refine ⟨M, hM, fun v => ?_⟩
  have hne : (Finset.univ : Finset V).Nonempty := ⟨v, Finset.mem_univ v⟩
  obtain ⟨v₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (unDeg G M) hne
  have hkey : 2 * unDeg G M v₀ ≤ Fintype.card V + 4 := by
    by_contra hcon
    exact star_counting_contradiction G hdense hM hmin v₀ (by omega)
  have hvle : unDeg G M v ≤ unDeg G M v₀ := hmax v (Finset.mem_univ v)
  show 2 * unDeg G M v ≤ Fintype.card V + 4
  omega

/-- **The residual holds for every `β > 1/2`.** -/
theorem denseTriangleNibbleDeg_of_half_lt {β : ℝ} (hβ : 1 / 2 < β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) := by
  have hpos : 0 < 2 * β - 1 := by linarith
  refine ⟨⌈(4 : ℝ) / (2 * β - 1)⌉₊, ?_⟩
  intro V _ _ G _ hV hdense
  obtain ⟨M, hM, hbound⟩ := dense_uncoveredAt_le_half G hdense
  refine ⟨M, hM, fun v => ?_⟩
  have h1 : (2 : ℝ) * ((uncoveredAt G M v).card : ℝ) ≤ (Fintype.card V : ℝ) + 4 := by
    exact_mod_cast hbound v
  have h2 : (4 : ℝ) / (2 * β - 1) ≤ (Fintype.card V : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hV)
  have h3 : (4 : ℝ) ≤ (Fintype.card V : ℝ) * (2 * β - 1) := (div_le_iff₀ hpos).mp h2
  linarith

/-- **The narrowed residual**: the statement of `Nibble.DenseTriangleNibbleDeg` for `β ≤ 1/2`. -/
def DenseTriangleNibbleDegVerySmall : Prop :=
  ∀ β : ℝ, 0 < β → β ≤ 1 / 2 → ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ)

/-- **Machine-checked reduction**: the full residual follows from the narrowed one. -/
theorem denseTriangleNibbleDeg_of_verySmall (h : DenseTriangleNibbleDegVerySmall) :
    DenseTriangleNibbleDeg := by
  intro β hβ
  rcases le_or_gt β (1 / 2) with hle | hgt
  · exact h β hβ hle
  · exact denseTriangleNibbleDeg_of_half_lt hgt

/-- **Machine-checked reduction**: the previous residual (`β ≤ 11/20`) follows from the new one
(`β ≤ 1/2`). -/
theorem denseTriangleNibbleDegSmall_of_verySmall (h : DenseTriangleNibbleDegVerySmall) :
    DenseTriangleNibbleDegSmall := by
  intro β hβ _
  rcases le_or_gt β (1 / 2) with hle | hgt
  · exact h β hβ hle
  · exact denseTriangleNibbleDeg_of_half_lt hgt

/-! ### The conditional route below `1/2` -/

/-- **The global input.**  At the Dross density, triangle packings leaving `o(|V|²)` uncovered
incidences (equivalently, `o(|V|²)` uncovered edges: an approximate triangle decomposition).

This is *not* available in the present library at `δ(G) ≥ (9/10)|V|`: `Nibble.dense_approx_global`
proves the corresponding statement only in the near-complete regime `δ(G) ≥ (1 − μ/2)|V|`, where
`μ = μ(ε)` is the nibble's own band. -/
def DenseGlobalSmallLeftover : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        (uncoveredTot G M : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- **The quadratic route.**  Given the global input, the swap engine
`Nibble.dense_uncoveredAt_quadratic` pushes the per-vertex bound down to `1/10`: the residual
`Nibble.DenseTriangleNibbleDeg` holds for every `β > 1/10`. -/
theorem denseTriangleNibbleDeg_of_tenth_lt (hglob : DenseGlobalSmallLeftover) {β : ℝ}
    (hβ : 1 / 10 < β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) := by
  have hβpos : 0 < β := by linarith
  have h10 : 0 < 10 * β - 1 := by linarith
  have hεpos : 0 < β * (10 * β - 1) / 40 := by positivity
  obtain ⟨n₁, hmain⟩ := hglob (β * (10 * β - 1) / 40) hεpos
  refine ⟨max n₁ ⌈(40 : ℝ) / (10 * β - 1)⌉₊, ?_⟩
  intro V _ _ G _ hV hdense
  obtain ⟨M₀, hM₀, hK⟩ := hmain G (le_trans (le_max_left _ _) hV) hdense
  obtain ⟨M, hM, -, hquad⟩ :=
    dense_uncoveredAt_quadratic G hdense (uncoveredTot G M₀) hM₀ le_rfl
  refine ⟨M, hM, fun v => ?_⟩
  have hnbig : (40 : ℝ) / (10 * β - 1) ≤ (Fintype.card V : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hV)
  have hq : 10 * ((uncoveredAt G M v).card : ℝ) * ((uncoveredAt G M v).card : ℝ)
      ≤ 10 * (uncoveredTot G M₀ : ℝ) + (Fintype.card V : ℝ) * ((uncoveredAt G M v).card : ℝ)
        + 20 * ((uncoveredAt G M v).card : ℝ) := by
    exact_mod_cast hquad v
  have hd0 : (0 : ℝ) ≤ ((uncoveredAt G M v).card : ℝ) := Nat.cast_nonneg _
  set d : ℝ := ((uncoveredAt G M v).card : ℝ) with hd
  set n : ℝ := (Fintype.card V : ℝ) with hnn
  have hn40 : (40 : ℝ) ≤ n * (10 * β - 1) := (div_le_iff₀ h10).mp hnbig
  have hn0 : 0 < n := by nlinarith
  by_contra hcon
  push_neg at hcon
  have hgap : (10 * β - 1) * n - 20 ≥ (10 * β - 1) * n / 2 := by linarith
  have hgap0 : 0 < (10 * β - 1) * n / 2 := by positivity
  have hfac : (10 * β - 1) * n - 20 < 10 * d - n - 20 := by linarith
  have hβn : 0 ≤ β * n := by positivity
  have hprod : (β * n) * ((10 * β - 1) * n / 2) < d * (10 * d - n - 20) := by
    have h1 : (β * n) * ((10 * β - 1) * n / 2) ≤ (β * n) * (10 * d - n - 20) := by nlinarith
    have h2 : (β * n) * (10 * d - n - 20) < d * (10 * d - n - 20) := by nlinarith
    linarith
  nlinarith [hK, hq]

end Nibble
