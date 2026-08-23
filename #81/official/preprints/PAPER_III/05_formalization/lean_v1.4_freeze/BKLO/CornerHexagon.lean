/-
# An unlinked hexagon: the corner mechanism is dead in every form

`BKLO/CornerLimit.lean` refutes `BKLO.CornerReservoirExistence` using a leftover triangle, and one
might object that a triangle is a degenerate test case: it needs no reservoir at all, so the
corrected statement `BKLO.PartialCornerReservoirExistence` routes only a *part* `H'` of the
leftover.  This file removes the objection: it refutes the corrected statement as well.

The test leftover is a **hexagon** — a six-cycle `p₀p₁p₂p₃p₄p₅` — placed on six vertices which
the reservoir does not corner-link and between which it reserves no edge.  Such six vertices exist
by counting (`BKLO.exists_unlinked_hexagon`): with maximum reservoir degree `d ≤ n/1000` there are
at most `36n⁵` degenerate six-tuples, at most `36 d n⁵` with a reserved pair and at most
`74088 n⁴d²` with a corner-linked triple, all together fewer than the `n⁶` six-tuples.

On such a hexagon no part can be routed: a nonempty routed part would corner-link three of its
vertices (`BKLO.exists_cornerLinked_of_cornerRouting`), and the empty part leaves the whole hexagon
to decompose by itself, which it does not (`BKLO.not_triDecomp_hexagon`: a six-cycle contains no
triangle).

Everything in this file is `sorry`-free.
-/
import BKLO.CornerLimit

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Counting tuples by a restriction of their coordinates -/

/-- **Restriction bound.**  A set of `m`-tuples cut out by a condition on `k` of the coordinates has
at most `|A| · n^{m-k}` elements, where `A` is the set of admissible restrictions. -/
theorem card_filter_restrict_le [Fintype V] {k m : ℕ} (ι : Fin k → Fin m)
    (hι : Function.Injective ι) (A : Finset (Fin k → V)) :
    (Finset.univ.filter (fun p : Fin m → V => (fun i => p (ι i)) ∈ A)).card
      ≤ A.card * Fintype.card V ^ (m - k) := by
  classical
  set s : Finset (Fin m) := Finset.univ.filter (fun j => ∀ i, ι i ≠ j) with hs
  have hscard : s.card = m - k := by
    have h1 : (Finset.univ.image ι).card = k := by
      rw [Finset.card_image_of_injective _ hι, Finset.card_univ, Fintype.card_fin]
    have h2 : s = Finset.univ \ Finset.univ.image ι := by
      ext j
      simp [hs, Finset.mem_sdiff, Finset.mem_image, eq_comm]
    rw [h2, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, h1]
  have hmap : ∀ p ∈ Finset.univ.filter (fun p : Fin m → V => (fun i => p (ι i)) ∈ A),
      ((fun i => p (ι i)), (fun j : {x // x ∈ s} => p j.1)) ∈
        A ×ˢ (Finset.univ : Finset ({x // x ∈ s} → V)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact Finset.mem_product.2 ⟨hp.2, Finset.mem_univ _⟩
  have hinj : Set.InjOn
      (fun p : Fin m → V => ((fun i => p (ι i)), (fun j : {x // x ∈ s} => p j.1)))
      ↑(Finset.univ.filter (fun p : Fin m → V => (fun i => p (ι i)) ∈ A)) := by
    intro p _ q _ hpq
    have h1 := congrArg Prod.fst hpq
    have h2 := congrArg Prod.snd hpq
    funext j
    by_cases hj : j ∈ s
    · exact congrFun h2 ⟨j, hj⟩
    · rw [hs, Finset.mem_filter] at hj
      push_neg at hj
      obtain ⟨i, hi⟩ := hj (Finset.mem_univ j)
      rw [← hi]
      exact congrFun h1 i
  calc (Finset.univ.filter (fun p : Fin m → V => (fun i => p (ι i)) ∈ A)).card
      ≤ (A ×ˢ (Finset.univ : Finset ({x // x ∈ s} → V))).card :=
        Finset.card_le_card_of_injOn _ hmap hinj
    _ = A.card * Fintype.card V ^ (m - k) := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_coe, hscard]

/-! ### The three kinds of bad restrictions -/

variable {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}

theorem injective_two {i j : Fin 6} (h : i ≠ j) : Function.Injective ![i, j] := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

theorem injective_three {i j k : Fin 6} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Function.Injective ![i, j, k] := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

/-- Pairs of equal entries. -/
noncomputable def eqPairs [Fintype V] : Finset (Fin 2 → V) :=
  open Classical in Finset.univ.filter (fun g => g 0 = g 1)

/-- Pairs joined by a reserved edge. -/
noncomputable def resPairs [Fintype V] (R : Finset (Sym2 V)) : Finset (Fin 2 → V) :=
  open Classical in Finset.univ.filter (fun g => s(g 0, g 1) ∈ R)

/-- Corner-linked triples, as functions. -/
noncomputable def linkPairs [Fintype V] (𝒞 : Finset (Finset V)) : Finset (Fin 3 → V) :=
  open Classical in Finset.univ.filter (fun g => CornerLinked 𝒞 (g 0) (g 1) (g 2))

theorem card_eqPairs_le [Fintype V] : (eqPairs (V := V)).card ≤ Fintype.card V := by
  classical
  refine (Finset.card_le_card_of_injOn (fun g => g 0) (fun g _ => Finset.mem_univ _) ?_).trans
    (le_of_eq (Finset.card_univ))
  intro g hg h hh hgh
  have hg' : g 0 = g 1 := by simpa [eqPairs] using hg
  have hh' : h 0 = h 1 := by simpa [eqPairs] using hh
  funext i
  fin_cases i
  · exact hgh
  · exact hg'.symm.trans (hgh.trans hh')

theorem card_resPairs_le [Fintype V] {R : Finset (Sym2 V)} {d : ℕ} (hd : ∀ v, edeg R v ≤ d) :
    (resPairs R).card ≤ Fintype.card V * d := by
  classical
  have hsub : resPairs R ⊆ Finset.univ.biUnion
      (fun a : V => (resNbr R a).image (fun b => ![a, b])) := by
    intro g hg
    have hg' : s(g 0, g 1) ∈ R := by simpa [resPairs] using hg
    refine Finset.mem_biUnion.2 ⟨g 0, Finset.mem_univ _, Finset.mem_image.2 ⟨g 1, ?_, ?_⟩⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hg'⟩
    · funext i; fin_cases i <;> simp
  calc (resPairs R).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ _a : V, d := by
        refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum ?_)
        intro a _
        exact (Finset.card_image_le).trans ((card_resNbr_le a).trans (hd a))
    _ = Fintype.card V * d := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]

omit [DecidableEq V] in
theorem card_linkPairs_le [Fintype V] : (linkPairs 𝒞).card ≤ (linkedTriples 𝒞).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun g => (g 0, g 1, g 2)) ?_ ?_
  · intro g hg
    have hg' : CornerLinked 𝒞 (g 0) (g 1) (g 2) := by simpa [linkPairs] using hg
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hg'⟩
  · intro g _ h _ hgh
    have h0 : g 0 = h 0 := congrArg Prod.fst hgh
    have h1 : g 1 = h 1 := congrArg (fun q => q.2.1) hgh
    have h2 : g 2 = h 2 := congrArg (fun q => q.2.2) hgh
    funext i
    fin_cases i
    exacts [h0, h1, h2]

/-! ### Six vertices that the reservoir neither joins nor links -/

/-- **An unlinked hexagon exists.**  In a cluster reservoir of maximum degree `d` on `n` vertices
with `1000 d ≤ n` and `4000 ≤ n` there are six distinct vertices, no two joined by a reserved edge
and no three corner-linked. -/
theorem exists_unlinked_hexagon [Fintype V] {E : Finset (Sym2 V)} {C7 : Finset (Finset V)}
    (hfam : ClusterFamilyIn E C7) {d : ℕ} (hd : ∀ v, edeg (famEdges C7) v ≤ d)
    (hdn : 1000 * d ≤ Fintype.card V) (hn : 4000 ≤ Fintype.card V) :
    ∃ p : Fin 6 → V, (∀ i j : Fin 6, i ≠ j → p i ≠ p j) ∧
      (∀ i j : Fin 6, i ≠ j → s(p i, p j) ∉ famEdges C7) ∧
      (∀ i j k : Fin 6, i ≠ j → j ≠ k → i ≠ k → ¬ CornerLinked C7 (p i) (p j) (p k)) := by
  classical
  set n := Fintype.card V with hncard
  set R := famEdges C7 with hR
  set P2 : Finset (Fin 6 × Fin 6) := Finset.univ.filter (fun q => q.1 ≠ q.2) with hP2
  set P3 : Finset (Fin 6 × Fin 6 × Fin 6) :=
    Finset.univ.filter (fun q => q.1 ≠ q.2.1 ∧ q.2.1 ≠ q.2.2 ∧ q.1 ≠ q.2.2) with hP3
  have hP2card : P2.card ≤ 36 := by
    refine (Finset.card_filter_le _ _).trans ?_
    simp
  have hP3card : P3.card ≤ 216 := by
    refine (Finset.card_filter_le _ _).trans ?_
    simp
  set Beq : Finset (Fin 6 → V) := P2.biUnion (fun q =>
    Finset.univ.filter (fun p : Fin 6 → V => (fun t => p (![q.1, q.2] t)) ∈ eqPairs)) with hBeq
  set Bres : Finset (Fin 6 → V) := P2.biUnion (fun q =>
    Finset.univ.filter (fun p : Fin 6 → V => (fun t => p (![q.1, q.2] t)) ∈ resPairs R)) with hBres
  set Blk : Finset (Fin 6 → V) := P3.biUnion (fun q =>
    Finset.univ.filter (fun p : Fin 6 → V =>
      (fun t => p (![q.1, q.2.1, q.2.2] t)) ∈ linkPairs C7)) with hBlk
  -- the three counts
  have hcBeq : Beq.card ≤ 36 * (n * n ^ 4) := by
    refine (Finset.card_biUnion_le).trans ?_
    calc ∑ q ∈ P2, (Finset.univ.filter
            (fun p : Fin 6 → V => (fun t => p (![q.1, q.2] t)) ∈ eqPairs)).card
        ≤ ∑ _q ∈ P2, (n * n ^ 4) := by
          refine Finset.sum_le_sum ?_
          intro q hq
          have hne : q.1 ≠ q.2 := (Finset.mem_filter.1 hq).2
          have := card_filter_restrict_le (V := V) ![q.1, q.2] (injective_two hne) eqPairs
          exact this.trans (Nat.mul_le_mul (card_eqPairs_le) (le_of_eq (by rw [hncard])))
      _ = P2.card * (n * n ^ 4) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 36 * (n * n ^ 4) := Nat.mul_le_mul_right _ hP2card
  have hcBres : Bres.card ≤ 36 * ((n * d) * n ^ 4) := by
    refine (Finset.card_biUnion_le).trans ?_
    calc ∑ q ∈ P2, (Finset.univ.filter
            (fun p : Fin 6 → V => (fun t => p (![q.1, q.2] t)) ∈ resPairs R)).card
        ≤ ∑ _q ∈ P2, ((n * d) * n ^ 4) := by
          refine Finset.sum_le_sum ?_
          intro q hq
          have hne : q.1 ≠ q.2 := (Finset.mem_filter.1 hq).2
          have := card_filter_restrict_le (V := V) ![q.1, q.2] (injective_two hne) (resPairs R)
          exact this.trans (Nat.mul_le_mul (card_resPairs_le hd) (le_of_eq (by rw [hncard])))
      _ = P2.card * ((n * d) * n ^ 4) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 36 * ((n * d) * n ^ 4) := Nat.mul_le_mul_right _ hP2card
  have hLk : (linkedTriples C7).card ≤ 343 * (n * (d * d)) :=
    (card_linkedTriples_le hfam).trans (Nat.mul_le_mul_left _ (card_resTriangles_le hd))
  have hcBlk : Blk.card ≤ 216 * ((343 * (n * (d * d))) * n ^ 3) := by
    refine (Finset.card_biUnion_le).trans ?_
    calc ∑ q ∈ P3, (Finset.univ.filter
            (fun p : Fin 6 → V => (fun t => p (![q.1, q.2.1, q.2.2] t)) ∈ linkPairs C7)).card
        ≤ ∑ _q ∈ P3, ((343 * (n * (d * d))) * n ^ 3) := by
          refine Finset.sum_le_sum ?_
          intro q hq
          obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.1 hq).2
          have := card_filter_restrict_le (V := V) ![q.1, q.2.1, q.2.2]
            (injective_three h1 h2 h3) (linkPairs C7)
          exact this.trans (Nat.mul_le_mul (card_linkPairs_le.trans hLk) (le_of_eq (by rw [hncard])))
      _ = P3.card * ((343 * (n * (d * d))) * n ^ 3) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 216 * ((343 * (n * (d * d))) * n ^ 3) := Nat.mul_le_mul_right _ hP3card
  -- the union is not everything
  have hlt : (Beq ∪ Bres ∪ Blk).card < (Finset.univ : Finset (Fin 6 → V)).card := by
    have huniv : (Finset.univ : Finset (Fin 6 → V)).card = n ^ 6 := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hncard]
    have hsum : (Beq ∪ Bres ∪ Blk).card ≤ Beq.card + Bres.card + Blk.card :=
      le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have hbound : Beq.card + Bres.card + Blk.card
        ≤ 36 * (n * n ^ 4) + 36 * ((n * d) * n ^ 4) + 216 * ((343 * (n * (d * d))) * n ^ 3) :=
      Nat.add_le_add (Nat.add_le_add hcBeq hcBres) hcBlk
    rw [huniv]
    refine lt_of_le_of_lt (hsum.trans hbound) ?_
    -- `36n⁵ + 36dn⁵ + 74088 n⁴d² < n⁶`
    have hn5 : 4000 * n ^ 5 ≤ n ^ 6 := by
      calc 4000 * n ^ 5 ≤ n * n ^ 5 := Nat.mul_le_mul_right _ (by omega)
        _ = n ^ 6 := by ring
    have hd5 : 1000 * (d * n ^ 5) ≤ n ^ 6 := by
      calc 1000 * (d * n ^ 5) = (1000 * d) * n ^ 5 := by ring
        _ ≤ n * n ^ 5 := Nat.mul_le_mul_right _ hdn
        _ = n ^ 6 := by ring
    have hd4 : 1000000 * (n ^ 4 * (d * d)) ≤ n ^ 6 := by
      calc 1000000 * (n ^ 4 * (d * d)) = n ^ 4 * ((1000 * d) * (1000 * d)) := by ring
        _ ≤ n ^ 4 * (n * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hdn hdn)
        _ = n ^ 6 := by ring
    have hpos : 0 < n ^ 6 := by positivity
    have key : 1000000 * (36 * (n * n ^ 4) + 36 * ((n * d) * n ^ 4)
        + 216 * ((343 * (n * (d * d))) * n ^ 3)) < 1000000 * n ^ 6 := by
      have e1 : 1000000 * (36 * (n * n ^ 4)) ≤ 9000 * n ^ 6 := by
        calc 1000000 * (36 * (n * n ^ 4)) = 9000 * (4000 * n ^ 5) := by ring
          _ ≤ 9000 * n ^ 6 := Nat.mul_le_mul_left _ hn5
      have e2 : 1000000 * (36 * ((n * d) * n ^ 4)) ≤ 36000 * n ^ 6 := by
        calc 1000000 * (36 * ((n * d) * n ^ 4)) = 36000 * (1000 * (d * n ^ 5)) := by ring
          _ ≤ 36000 * n ^ 6 := Nat.mul_le_mul_left _ hd5
      have e3 : 1000000 * (216 * ((343 * (n * (d * d))) * n ^ 3)) ≤ 74088 * n ^ 6 := by
        calc 1000000 * (216 * ((343 * (n * (d * d))) * n ^ 3))
            = 74088 * (1000000 * (n ^ 4 * (d * d))) := by ring
          _ ≤ 74088 * n ^ 6 := Nat.mul_le_mul_left _ hd4
      have : 1000000 * (36 * (n * n ^ 4) + 36 * ((n * d) * n ^ 4)
          + 216 * ((343 * (n * (d * d))) * n ^ 3)) ≤ 119088 * n ^ 6 := by
        rw [Nat.mul_add, Nat.mul_add]
        omega
      have hlt' : 119088 * n ^ 6 < 1000000 * n ^ 6 :=
        Nat.mul_lt_mul_of_lt_of_le (by norm_num) (le_refl _) hpos
      exact lt_of_le_of_lt this hlt'
    exact lt_of_mul_lt_mul_left key (Nat.zero_le _)
  obtain ⟨p, hp⟩ : ∃ p : Fin 6 → V, p ∉ Beq ∪ Bres ∪ Blk := by
    by_contra hcon
    push_neg at hcon
    exact absurd (Finset.card_le_card (fun p _ => hcon p)) (not_le.2 hlt)
  simp only [Finset.mem_union, not_or] at hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  refine ⟨p, ?_, ?_, ?_⟩
  · intro i j hij hcon
    refine h1 ?_
    rw [hBeq]
    refine Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩, ?_⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simpa [eqPairs] using hcon
  · intro i j hij hcon
    refine h2 ?_
    rw [hBres]
    refine Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩, ?_⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simpa [resPairs] using hcon
  · intro i j k hij hjk hik hcon
    refine h3 ?_
    rw [hBlk]
    refine Finset.mem_biUnion.2 ⟨(i, j, k),
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hij, hjk, hik⟩, ?_⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simpa [linkPairs] using hcon

/-! ### The hexagon leftover -/

/-- The edge set of the six-cycle `p 0 p 1 p 2 p 3 p 4 p 5`. -/
noncomputable def hexEdges (p : Fin 6 → V) : Finset (Sym2 V) :=
  Finset.univ.image (fun i : Fin 6 => s(p i, p (i + 1)))

variable {p : Fin 6 → V}

omit [DecidableEq V] in
theorem hex_inj (hp : ∀ i j : Fin 6, i ≠ j → p i ≠ p j) : Function.Injective p := by
  intro i j h; by_contra hne; exact hp i j hne h

theorem mem_hexEdges {e : Sym2 V} : e ∈ hexEdges p ↔ ∃ i : Fin 6, e = s(p i, p (i + 1)) := by
  simp [hexEdges, eq_comm]

/-- Both endpoints of an edge of the hexagon are vertices of it, at cyclically adjacent indices. -/
theorem hex_adj {u v : V} (h : s(u, v) ∈ hexEdges p) :
    ∃ a b : Fin 6, u = p a ∧ v = p b ∧ (b = a + 1 ∨ a = b + 1) := by
  obtain ⟨i, hi⟩ := mem_hexEdges.1 h
  rw [Sym2.eq_iff] at hi
  rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨i, i + 1, h1, h2, Or.inl rfl⟩
  · exact ⟨i + 1, i, h1, h2, Or.inr rfl⟩

/-- Every vertex touched by the hexagon is one of its six vertices. -/
theorem hex_vertex {x : V} (h : ∃ e ∈ hexEdges p, x ∈ e) : ∃ i : Fin 6, x = p i := by
  obtain ⟨e, he, hx⟩ := h
  obtain ⟨i, rfl⟩ := mem_hexEdges.1 he
  rcases Sym2.mem_iff.1 hx with rfl | rfl
  exacts [⟨i, rfl⟩, ⟨i + 1, rfl⟩]

omit [DecidableEq V] in
theorem hexMap_inj (hp : ∀ i j : Fin 6, i ≠ j → p i ≠ p j) :
    Function.Injective (fun i : Fin 6 => s(p i, p (i + 1))) := by
  intro i j h
  simp only [Sym2.eq_iff] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact hex_inj hp h1
  · have a1 := hex_inj hp h1
    have a2 := hex_inj hp h2
    clear h1 h2
    revert a1 a2; revert i j; decide

theorem hexEdges_card (hp : ∀ i j : Fin 6, i ≠ j → p i ≠ p j) : (hexEdges p).card = 6 := by
  rw [hexEdges, Finset.card_image_of_injective _ (hexMap_inj hp)]; simp

theorem edeg_hexEdges (hp : ∀ i j : Fin 6, i ≠ j → p i ≠ p j) (k : Fin 6) :
    edeg (hexEdges p) (p k) = 2 := by
  classical
  have hk : k - 1 ≠ k := by revert k; decide
  have hfil : (hexEdges p).filter (fun e => p k ∈ e)
      = ((Finset.univ.filter (fun i : Fin 6 => i = k - 1 ∨ i = k)).image
          (fun i : Fin 6 => s(p i, p (i + 1)))) := by
    rw [hexEdges, Finset.filter_image]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff, (hex_inj hp).eq_iff]
    clear hk; revert i; revert k; decide
  rw [edeg, hfil, Finset.card_image_of_injective _ (hexMap_inj hp)]
  have h2 : (Finset.univ.filter (fun i : Fin 6 => i = k - 1 ∨ i = k)) = {k - 1, k} := by
    ext i; simp
  rw [h2, Finset.card_pair hk]

theorem edeg_hexEdges_of_notMem {v : V} (hv : ∀ i : Fin 6, v ≠ p i) :
    edeg (hexEdges p) v = 0 := by
  rw [edeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he
  obtain ⟨i, rfl⟩ := mem_hexEdges.1 he
  simp only [Sym2.mem_iff, not_or]
  exact ⟨hv i, hv (i + 1)⟩

theorem edeg_hexEdges_le (hp : ∀ i j : Fin 6, i ≠ j → p i ≠ p j) (v : V) :
    edeg (hexEdges p) v ≤ 2 := by
  by_cases h : ∃ i : Fin 6, v = p i
  · obtain ⟨i, rfl⟩ := h; exact (edeg_hexEdges hp i).le
  · push_neg at h; rw [edeg_hexEdges_of_notMem h]; omega

theorem evenDegrees_hexEdges (hp : ∀ i j : Fin 6, i ≠ j → p i ≠ p j) :
    EvenDegrees (hexEdges p) := by
  intro v
  by_cases h : ∃ i : Fin 6, v = p i
  · obtain ⟨i, rfl⟩ := h; rw [edeg_hexEdges hp i]; decide
  · push_neg at h; rw [edeg_hexEdges_of_notMem h]; decide

/-- **A six-cycle contains no triangle**, hence is not triangle-decomposable. -/
theorem not_triDecomp_hexEdges (hp : ∀ i j : Fin 6, i ≠ j → p i ≠ p j) :
    ¬ TriDecomp (hexEdges p) := by
  classical
  rintro ⟨P, hc, -, hE⟩
  have hne : P.Nonempty := by
    rcases Finset.eq_empty_or_nonempty P with rfl | h
    · rw [famEdges, Finset.biUnion_empty] at hE
      have h6 := hexEdges_card hp
      rw [← hE] at h6; simp at h6
    · exact h
  obtain ⟨t, ht⟩ := hne
  have hsub : cliqueEdges t ⊆ hexEdges p := by
    rw [← hE]; exact Finset.subset_biUnion_of_mem cliqueEdges ht
  obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := Finset.card_eq_three.1 (hc t ht)
  rw [cliqueEdgesV_triple huv hvw huw] at hsub
  obtain ⟨a, b, hua, hvb, hab⟩ := hex_adj (hsub (by simp) : s(u, v) ∈ hexEdges p)
  obtain ⟨b', c, hvb', hwc, hbc⟩ := hex_adj (hsub (by simp) : s(v, w) ∈ hexEdges p)
  obtain ⟨a', c', hua', hwc', hac⟩ := hex_adj (hsub (by simp) : s(u, w) ∈ hexEdges p)
  have hbb : b' = b := hex_inj hp (by rw [← hvb', ← hvb])
  have haa : a' = a := hex_inj hp (by rw [← hua', ← hua])
  have hcc : c' = c := hex_inj hp (by rw [← hwc', ← hwc])
  rw [hbb] at hbc
  rw [haa, hcc] at hac
  have hab' : a ≠ b := by rintro rfl; exact huv (by rw [hua, hvb])
  have hbc' : b ≠ c := by rintro rfl; exact hvw (by rw [hvb, hwc])
  have hac' : a ≠ c := by rintro rfl; exact huw (by rw [hua, hwc])
  clear hua hvb hwc hua' hwc' hvb' huv hvw huw hsub hE hc ht hbb haa hcc
  revert hab hbc hac hab' hbc' hac'
  clear a' b' c'
  revert a b c
  decide +kernel

/-! ### The corrected corner statement is false as well -/

theorem fin_six_ne_succ (i : Fin 6) : i ≠ i + 1 := by revert i; decide

/-- **`BKLO.PartialCornerReservoirExistence` is false.**

Take the host to be a complete graph on `n` vertices and `γ = 1/1000`, and let `D = 3`.  Whatever
cluster reservoir of maximum degree at most `γn` is reserved, `BKLO.exists_unlinked_hexagon`
produces six vertices between which no edge is reserved and no three of which are corner-linked.
The six-cycle `H` on them is an admissible leftover — even, of maximum degree `2`, with `3 ∣ |H|`
— and it lies entirely in the unreserved part of the host.

Neither alternative offered by a partial corner routing is available for it.  If the routed part
`H'` is empty then the whole hexagon has to be triangle-decomposable, which it is not
(`BKLO.not_triDecomp_hexEdges`).  If `H'` is nonempty then a corner routing of it corner-links
three of its vertices (`BKLO.exists_cornerLinked_of_cornerRouting`), and those are three distinct
vertices of the hexagon, which the reservoir does not link.

So the corner mechanism fails in every form: the obstruction is not an artefact of asking to route
the *whole* leftover. -/
theorem not_partialCornerReservoirExistence : ¬ PartialCornerReservoirExistence := by
  classical
  intro hCR
  obtain ⟨n₀, hres⟩ := hCR (1 / 1000 : ℝ) (by norm_num) 3
  set n := max n₀ 4000 with hndef
  have hn4000 : 4000 ≤ n := le_max_right _ _
  have hnn₀ : n₀ ≤ n := le_max_left _ _
  have hcardfin : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hdegE : ∀ v ∈ (Finset.univ : Finset (Fin n)),
      (9 / 10 + (1 / 1000 : ℝ)) * ((Finset.univ : Finset (Fin n)).card : ℝ) ≤
        (edeg (cliqueEdges (Finset.univ : Finset (Fin n))) v : ℝ) := by
    intro v _
    have hv : edeg (cliqueEdges (Finset.univ : Finset (Fin n))) v = n - 1 := by
      rw [edeg_cliqueEdges_card v, if_pos (Finset.mem_univ v), hcardfin]
    rw [hv, hcardfin]
    have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have : (1 : ℕ) ≤ n := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [h1]
    have hn : (4000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4000
    nlinarith
  obtain ⟨Cl, hfam, hdeg, hcorner⟩ :=
    hres (V := Fin n) (cliqueEdges (Finset.univ : Finset (Fin n))) Finset.univ
      (by rw [hcardfin]; exact hnn₀) (Finset.Subset.refl _) hdegE
  set d := n / 1000 with hddef
  have hd : ∀ v : Fin n, edeg (famEdges Cl) v ≤ d := by
    intro v
    have h := hdeg v
    rw [hcardfin] at h
    have h' : (1000 : ℝ) * (edeg (famEdges Cl) v : ℝ) ≤ (n : ℝ) := by nlinarith
    have h'' : 1000 * edeg (famEdges Cl) v ≤ n := by exact_mod_cast h'
    rw [hddef, Nat.le_div_iff_mul_le (by norm_num : 0 < 1000)]
    omega
  have hcardV : Fintype.card (Fin n) = n := by simp
  obtain ⟨p, hpne, hpres, hpunlinked⟩ :=
    exists_unlinked_hexagon hfam hd (by rw [hcardV, hddef]; omega) (by rw [hcardV]; exact hn4000)
  set H : Finset (Sym2 (Fin n)) := hexEdges p with hHdef
  have hHsub : H ⊆ cliqueEdges (Finset.univ : Finset (Fin n)) \ famEdges Cl := by
    intro e he
    obtain ⟨i, rfl⟩ := mem_hexEdges.1 he
    have hii : i ≠ i + 1 := fin_six_ne_succ i
    refine Finset.mem_sdiff.2 ⟨mem_cliqueEdgesV.2 ⟨fun w _ => Finset.mem_univ w, ?_⟩,
      hpres i (i + 1) hii⟩
    simpa [Sym2.isDiag_iff_proj_eq] using hpne i (i + 1) hii
  obtain ⟨H', f, Tr, cl, hH'sub, hrest, hroute⟩ :=
    hcorner H hHsub (evenDegrees_hexEdges hpne)
      (fun v => le_trans (edeg_hexEdges_le hpne v) (by norm_num))
      (by rw [hHdef, hexEdges_card hpne]; norm_num)
  rcases Finset.eq_empty_or_nonempty H' with rfl | hH'ne
  · exact not_triDecomp_hexEdges hpne (by simpa using hrest)
  · obtain ⟨x, y, z, hxy, hyz, hxz, hx, hy, hz, hlink⟩ :=
      exists_cornerLinked_of_cornerRouting hfam hroute hH'ne
    have hmem : ∀ u : Fin n, (∃ e ∈ H', u ∈ e) → ∃ i : Fin 6, u = p i := by
      rintro u ⟨e, he, hue⟩
      exact hex_vertex ⟨e, hH'sub he, hue⟩
    obtain ⟨i, rfl⟩ := hmem x hx
    obtain ⟨j, rfl⟩ := hmem y hy
    obtain ⟨k, rfl⟩ := hmem z hz
    refine hpunlinked i j k ?_ ?_ ?_ hlink
    · rintro rfl; exact hxy rfl
    · rintro rfl; exact hyz rfl
    · rintro rfl; exact hxz rfl

end BKLO
