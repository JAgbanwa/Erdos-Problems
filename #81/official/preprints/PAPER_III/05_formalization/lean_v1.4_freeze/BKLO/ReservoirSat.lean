/-
# Non-vacuity and truth witnesses for the fused §10 interface.

The fused interface `BKLO.VortexReservoirEngine` is an *assumed* input, so two things have to be
checked, exactly as `BKLO/InputsVortexSat.lean` checks them for the old §10 inputs.

1. **Its hypotheses are satisfiable** — `reservoirClause_hypotheses_realizable`: for every density
   schedule, ratio and threshold the interface might supply, there are arbitrarily large
   configurations `W'' ⊆ W' ⊆ W`, `F` meeting *every* hypothesis of the reservoir clause, with
   `W \ W'`, `W''` and `F ∩ cliqueEdges W''` all nonempty.  So the clause is a genuine demand and
   the interface is not vacuously true at its hypotheses.

2. **Its conclusion is attainable** — the link-cover conclusion, which is the only part of the
   interface that is not a plain "choose a random subset" statement, is *proved* here in two
   cases, neither of which routes through the engine's target:

   * `isLinkCover_of_pairing` — whenever the residual link of a vertex is paired up by
     `F`-edges avoiding `W''`, the link cover exists.  This is a construction, not an assumption.
   * `isLinkCover_single_of_dirac` — for a single vertex, the required pairing is produced by
     **Dirac's theorem** (`BKLO.PerfectMatchingDirac`) from the link being dense in itself: this is
     the `r = 2` case of the `Kᵣ`-factor step of BKLO §10, and it is where Dirac enters the
     re-architected argument.

Everything here is `sorry`-free.
-/
import BKLO.Reservoir
import BKLO.InputsVortexSat

open Finset

namespace BKLO

/-! ### A link cover from a pairing of the link -/

section Pairing

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- Two pairs of a fixed-point-free involution that meet are equal as edges. -/
theorem pair_sym2_eq_of_common {X : Finset V} {g : V → V}
    (hginv : ∀ a ∈ X, g (g a) = a) {a b v : V} (ha : a ∈ X) (hb : b ∈ X)
    (hva : v = a ∨ v = g a) (hvb : v = b ∨ v = g b) :
    s(a, g a) = s(b, g b) := by
  rw [Sym2.eq_iff]
  rcases hva with h1 | h1 <;> rcases hvb with h2 | h2
  · have hab : a = b := by rw [← h1, h2]
    exact Or.inl ⟨hab, by rw [hab]⟩
  · have hab : a = g b := by rw [← h1, h2]
    exact Or.inr ⟨hab, by rw [hab, hginv b hb]⟩
  · have hab : g a = b := by rw [← h1, h2]
    exact Or.inr ⟨by rw [← hab, hginv a ha], hab⟩
  · have hab : g a = g b := by rw [← h1, h2]
    exact Or.inl ⟨by rw [← hginv a ha, hab, hginv b hb], hab⟩

/-- **A link cover from a pairing.**  If the residual link `X` of the single vertex `u` is paired
up by a fixed-point-free involution `g` such that every pair `{a, g a}` is an `F`-edge inside
`W' \ W''`, then the triangles `{u, a, g a}` form a link cover: they cover exactly the crossing
edges `s(u, a)`, they use one edge inside `W'` per pair, they avoid `W''`, and each vertex of `W'`
is used at most once. -/
theorem isLinkCover_of_pairing {F : Finset (Sym2 V)} {W' W'' X : Finset V} {u : V} {γ : ℝ}
    (g : V → V) (hg : ∀ a ∈ X, g a ∈ X) (hginv : ∀ a ∈ X, g (g a) = a)
    (hgne : ∀ a ∈ X, g a ≠ a)
    (hXW' : X ⊆ W') (huW' : u ∉ W') (hXW'' : ∀ a ∈ X, a ∉ W'')
    (hXF : ∀ a ∈ X, s(u, a) ∈ F) (hgF : ∀ a ∈ X, s(a, g a) ∈ F)
    (hγ : (1 : ℝ) ≤ γ * (W'.card : ℝ)) :
    ∃ Q : Finset (Finset V), IsLinkCover F W' W'' {u} (fun _ => X) γ Q := by
  classical
  have huX : u ∉ X := fun h => huW' (hXW' h)
  refine ⟨X.image (fun a => ({u, a, g a} : Finset V)), ?_, ?_, ?_, ?_, ?_⟩
  · -- an edge-disjoint family of triangles inside `F`
    refine ⟨?_, ?_, ?_⟩
    · rintro t ht
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ht
      have h1 : u ≠ a := fun h => huX (h ▸ ha)
      have h2 : u ≠ g a := fun h => huX (h ▸ hg a ha)
      have h3 : a ≠ g a := fun h => hgne a ha h.symm
      rw [Finset.card_insert_of_notMem (by simp [h1, h2]),
        Finset.card_insert_of_notMem (by simp [h3]), Finset.card_singleton]
    · rintro t ht
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ht
      have h1 : u ≠ a := fun h => huX (h ▸ ha)
      have h2 : u ≠ g a := fun h => huX (h ▸ hg a ha)
      have h3 : a ≠ g a := fun h => hgne a ha h.symm
      rw [cliqueEdges_tripleV h1 h2 h3]
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      exacts [hXF a ha, hXF (g a) (hg a ha), hgF a ha]
    · rintro t ht t' ht' hne
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ht'
      have ha1 : u ≠ a := fun h => huX (h ▸ ha)
      have ha2 : u ≠ g a := fun h => huX (h ▸ hg a ha)
      have ha3 : a ≠ g a := fun h => hgne a ha h.symm
      have hb1 : u ≠ b := fun h => huX (h ▸ hb)
      have hb2 : u ≠ g b := fun h => huX (h ▸ hg b hb)
      have hb3 : b ≠ g b := fun h => hgne b hb h.symm
      -- the two pairs are disjoint
      have hdisj : b ≠ a ∧ b ≠ g a ∧ g b ≠ a ∧ g b ≠ g a := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rintro rfl; exact hne rfl
        · rintro rfl
          exact hne (by rw [hginv a ha, Finset.pair_comm])
        · rintro h
          have : b = g a := by rw [← h, hginv b hb]
          exact hne (by rw [this, hginv a ha, Finset.pair_comm])
        · rintro h
          have : b = a := by
            have := congrArg g h
            rwa [hginv b hb, hginv a ha] at this
          exact hne (by rw [this])
      rw [cliqueEdges_tripleV ha1 ha2 ha3, cliqueEdges_tripleV hb1 hb2 hb3]
      refine Finset.disjoint_left.2 ?_
      intro e he he'
      simp only [Finset.mem_insert, Finset.mem_singleton] at he he'
      obtain ⟨hd1, hd2, hd3, hd4⟩ := hdisj
      rcases he with rfl | rfl | rfl <;> rcases he' with h | h | h <;>
        simp only [Sym2.eq_iff] at h <;>
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        simp_all
  · -- it covers the prescribed crossing edges
    intro e he
    obtain ⟨u', hu', a, ha, rfl⟩ := mem_crossStars.1 he
    rw [Finset.mem_singleton] at hu'
    subst u'
    have h1 : u ≠ a := fun h => huX (h ▸ ha)
    have h2 : u ≠ g a := fun h => huX (h ▸ hg a ha)
    have h3 : a ≠ g a := fun h => hgne a ha h.symm
    refine Finset.mem_biUnion.2 ⟨{u, a, g a}, Finset.mem_image.2 ⟨a, ha, rfl⟩, ?_⟩
    rw [cliqueEdges_tripleV h1 h2 h3]
    simp
  · -- it uses only crossing edges of the system and edges inside `W'`
    intro e he
    obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.1 he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ht
    have h1 : u ≠ a := fun h => huX (h ▸ ha)
    have h2 : u ≠ g a := fun h => huX (h ▸ hg a ha)
    have h3 : a ≠ g a := fun h => hgne a ha h.symm
    rw [cliqueEdges_tripleV h1 h2 h3] at het
    simp only [Finset.mem_insert, Finset.mem_singleton] at het
    rcases het with rfl | rfl | rfl
    · exact Finset.mem_union_left _ (crossStars_mem (Finset.mem_singleton_self u) ha)
    · exact Finset.mem_union_left _ (crossStars_mem (Finset.mem_singleton_self u) (hg a ha))
    · refine Finset.mem_union_right _ (mem_cliqueEdgesV.2 ⟨?_, ?_⟩)
      · intro z hz
        rcases Sym2.mem_iff.1 hz with rfl | rfl
        exacts [hXW' ha, hXW' (hg a ha)]
      · simpa [Sym2.isDiag_iff_proj_eq] using h3
  · -- it touches no edge inside `W''`
    refine Finset.disjoint_left.2 ?_
    intro e he he''
    obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.1 he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ht
    have h1 : u ≠ a := fun h => huX (h ▸ ha)
    have h2 : u ≠ g a := fun h => huX (h ▸ hg a ha)
    have h3 : a ≠ g a := fun h => hgne a ha h.symm
    have hmem := (mem_cliqueEdgesV.1 he'').1
    rw [cliqueEdges_tripleV h1 h2 h3] at het
    simp only [Finset.mem_insert, Finset.mem_singleton] at het
    rcases het with rfl | rfl | rfl
    · exact hXW'' a ha (hmem a (by simp))
    · exact hXW'' (g a) (hg a ha) (hmem (g a) (by simp))
    · exact hXW'' a ha (hmem a (by simp))
  · -- each vertex of `W'` loses at most one edge
    intro v hv
    have hone : ((famEdges (X.image (fun a => ({u, a, g a} : Finset V))) ∩
        cliqueEdges W').filter (fun e => v ∈ e)).card ≤ 1 := by
      refine Finset.card_le_one.2 ?_
      intro e he e' he'
      -- every edge of the family inside `W'` is a pair `{a, g a}` containing `v`
      have key : ∀ d ∈ (famEdges (X.image (fun a => ({u, a, g a} : Finset V))) ∩
          cliqueEdges W').filter (fun e => v ∈ e), ∃ a ∈ X, d = s(a, g a) ∧ v ∈ ({a, g a} : Finset V) := by
        intro d hd
        obtain ⟨hd1, hd2⟩ := Finset.mem_filter.1 hd
        obtain ⟨hdfam, hdW'⟩ := Finset.mem_inter.1 hd1
        obtain ⟨t, ht, hdt⟩ := Finset.mem_biUnion.1 hdfam
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ht
        have h1 : u ≠ a := fun h => huX (h ▸ ha)
        have h2 : u ≠ g a := fun h => huX (h ▸ hg a ha)
        have h3 : a ≠ g a := fun h => hgne a ha h.symm
        rw [cliqueEdges_tripleV h1 h2 h3] at hdt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hdt
        rcases hdt with rfl | rfl | rfl
        · exact absurd (huW' ((mem_cliqueEdgesV.1 hdW').1 u (by simp))) (fun h => h)
        · exact absurd (huW' ((mem_cliqueEdgesV.1 hdW').1 u (by simp))) (fun h => h)
        · refine ⟨a, ha, rfl, ?_⟩
          rcases Sym2.mem_iff.1 hd2 with rfl | rfl <;> simp
      obtain ⟨a, ha, rfl, hva⟩ := key e he
      obtain ⟨b, hb, rfl, hvb⟩ := key e' he'
      -- `v` lies in both pairs, so the pairs coincide
      simp only [Finset.mem_insert, Finset.mem_singleton] at hva hvb
      exact pair_sym2_eq_of_common hginv ha hb hva hvb
    have h1 : ((edeg (famEdges (X.image (fun a => ({u, a, g a} : Finset V))) ∩
        cliqueEdges W') v : ℕ) : ℝ) ≤ 1 := by
      rw [edeg]
      exact_mod_cast hone
    linarith only [hγ, h1]

end Pairing

/-! ### The pairing from Dirac's theorem -/

/-- **Dirac supplies the pairing.**  If `X` has even size and every vertex of `X` has at least
`|X|/2` `F`-neighbours inside `X`, then `X` is paired up by `F`-edges.  This is the `r = 2` case of
the `Kᵣ`-factor step of BKLO §10. -/
theorem exists_pairing_of_dirac (hDirac : PerfectMatchingDirac) {V : Type} [Fintype V]
    [DecidableEq V] {F : Finset (Sym2 V)} {X : Finset V}
    (hXeven : Even X.card)
    (hdeg : ∀ a ∈ X, X.card ≤ 2 * edeg (F ∩ cliqueEdges X) a) :
    ∃ g : V → V, (∀ a ∈ X, g a ∈ X) ∧ (∀ a ∈ X, g (g a) = a) ∧ (∀ a ∈ X, g a ≠ a) ∧
      ∀ a ∈ X, s(a, g a) ∈ F := by
  classical
  set E : Finset (Sym2 V) := F ∩ cliqueEdges X with hE
  have hEX : E ⊆ cliqueEdges X := Finset.inter_subset_right
  have hcardX : Fintype.card {x // x ∈ X} = X.card := card_coe_eq X
  have hEven : Even (Fintype.card {x // x ∈ X}) := by rw [hcardX]; exact hXeven
  have hmin : Fintype.card {x // x ∈ X} ≤ 2 * (setGraph X E).minDegree := by
    rcases Finset.eq_empty_or_nonempty X with rfl | hX
    · simp
    · have hne : Nonempty {x // x ∈ X} := by
        obtain ⟨x, hx⟩ := hX
        exact ⟨⟨x, hx⟩⟩
      obtain ⟨a, ha⟩ := (setGraph X E).exists_minimal_degree_vertex
      rw [hcardX, ha, degree_setGraph hEX a]
      exact hdeg (a : V) a.2
  obtain ⟨M, hM⟩ := hDirac (setGraph X E) hEven hmin
  -- the partner of a vertex under the perfect matching
  have hpartner : ∀ a : {x // x ∈ X}, ∃! b, M.Adj a b := fun a => hM.1 (hM.2 a)
  choose p hp huniq using fun a => hpartner a
  have hpadj : ∀ a, M.Adj a (p a) := hp
  have hpinv : ∀ a, p (p a) = a := fun a => (huniq (p a) a (M.symm (hpadj a))).symm
  refine ⟨fun v => if h : v ∈ X then ((p ⟨v, h⟩ : {x // x ∈ X}) : V) else v, ?_, ?_, ?_, ?_⟩
  · intro a ha
    simp only [dif_pos ha]
    exact (p ⟨a, ha⟩).2
  · intro a ha
    simp only [dif_pos ha, dif_pos (p ⟨a, ha⟩).2]
    have h2 : (⟨((p ⟨a, ha⟩ : {x // x ∈ X}) : V), (p ⟨a, ha⟩).2⟩ : {x // x ∈ X}) = p ⟨a, ha⟩ := rfl
    rw [h2, hpinv ⟨a, ha⟩]
  · intro a ha h
    simp only [dif_pos ha] at h
    have hadj := hpadj ⟨a, ha⟩
    have h2 : (p ⟨a, ha⟩) = (⟨a, ha⟩ : {x // x ∈ X}) := Subtype.ext h
    rw [h2] at hadj
    simpa using M.adj_sub hadj
  · intro a ha
    simp only [dif_pos ha]
    have hadj := M.adj_sub (hpadj ⟨a, ha⟩)
    have h2 : s(a, ((p ⟨a, ha⟩ : {x // x ∈ X}) : V)) ∈ E := hadj.2
    exact (Finset.mem_inter.1 h2).1

/-- **A link cover for a single vertex, from Dirac's theorem.**  If the residual link `X ⊆ W'` of
`u ∉ W'` avoids `W''`, has even size, is joined to `u` by `F`-edges and is dense in itself, then
the link cover exists.  This is the `Kᵣ`-factor half of the cover-down for `F = K₃`, and it is a
*construction*: nothing about triangle decompositions of dense graphs is used. -/
theorem isLinkCover_single_of_dirac (hDirac : PerfectMatchingDirac) {V : Type} [Fintype V]
    [DecidableEq V] {F : Finset (Sym2 V)} {W' W'' X : Finset V} {u : V} {γ : ℝ}
    (hXW' : X ⊆ W') (huW' : u ∉ W') (hXW'' : ∀ a ∈ X, a ∉ W'')
    (hXF : ∀ a ∈ X, s(u, a) ∈ F) (hXeven : Even X.card)
    (hdeg : ∀ a ∈ X, X.card ≤ 2 * edeg (F ∩ cliqueEdges X) a)
    (hγ : (1 : ℝ) ≤ γ * (W'.card : ℝ)) :
    ∃ Q : Finset (Finset V), IsLinkCover F W' W'' {u} (fun _ => X) γ Q := by
  obtain ⟨g, hg, hginv, hgne, hgF⟩ := exists_pairing_of_dirac hDirac hXeven hdeg
  exact isLinkCover_of_pairing g hg hginv hgne hXW' huW' hXW'' hXF hgF hγ

/-- **The empty link system is covered by the empty family.**  A first, trivial witness that
`IsLinkCover` is satisfiable — obtained by construction, not from the engine's target. -/
theorem isLinkCover_empty {V : Type*} [DecidableEq V] (F : Finset (Sym2 V)) (W' W'' D : Finset V)
    {γ : ℝ} (hγ : 0 ≤ γ) :
    IsLinkCover F W' W'' D (fun _ => (∅ : Finset V)) γ ∅ := by
  classical
  refine ⟨⟨by simp, by simp, by simp⟩, ?_, by simp [famEdges], by simp [famEdges], ?_⟩
  · intro e he
    simp [crossStars] at he
  · intro v hv
    have : edeg (famEdges (∅ : Finset (Finset V)) ∩ cliqueEdges W') v = 0 := by
      simp [famEdges, edeg]
    rw [this]
    have : (0 : ℝ) ≤ γ * (W'.card : ℝ) := by positivity
    simpa using this


/-! ### Non-vacuity of the reservoir clause -/

/-- **The hypotheses of `ReservoirClause` are satisfiable.**  For every `0 < ε < 1/10`, every size
ratio `K ≥ 2` and every schedule `f` bounded above by `9/10 + ε` past `n₂`, there are arbitrarily
large configurations `W'' ⊆ W' ⊆ W` and triangle-divisible edge sets `F` meeting *every* hypothesis
of the reservoir clause, and with `W \ W'`, `W''` and `F ∩ cliqueEdges W''` all nonempty.  So the
clause is a genuine demand at each of its parts, and the fused interface is not vacuously true. -/
theorem reservoirClause_hypotheses_realizable {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 10)
    {f : ℕ → ℝ} {n₂ K : ℕ} (hK : 2 ≤ K) (hf : ∀ s : ℕ, n₂ ≤ s → f s ≤ 9 / 10 + ε) (n₀ : ℕ) :
    ∃ (N : ℕ) (W W' W'' : Finset (Fin N)) (F : Finset (Sym2 (Fin N))),
      n₀ ≤ W.card ∧ n₂ ≤ W.card ∧ W' ⊆ W ∧ W'' ⊆ W' ∧
      K * W'.card ≤ W.card ∧ W.card ≤ K * K * W'.card ∧ K * W''.card ≤ W'.card ∧
      F ⊆ cliqueEdges W ∧ TriDivisible F ∧
      (∀ v ∈ W, (9 / 10 + ε / 4) * (W.card : ℝ) ≤ (edeg F v : ℝ)) ∧
      (∀ v ∈ W', f W'.card * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) ∧
      (W \ W').Nonempty ∧ W''.Nonempty ∧ (F ∩ cliqueEdges W'').Nonempty := by
  classical
  have hKpos : 0 < K := by omega
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 / 10 - ε))
  set t : ℕ := max (max (n₀ + n₂ + k + 3) (4 * K * K)) ((n₂ + k) * K) with ht
  set N : ℕ := 6 * t + 3 with hN
  have hcard : (Finset.univ : Finset (Fin N)).card = N := by simp
  have htbig : n₀ + n₂ + k + 3 ≤ t := le_trans (le_max_left _ _) (le_max_left _ _)
  have htKK : 4 * K * K ≤ t := le_trans (le_max_right _ _) (le_max_left _ _)
  have htmul : (n₂ + k) * K ≤ t := le_max_right _ _
  have hKKN : K * K * 1 < N := by simp only [hN]; nlinarith only [htKK]
  obtain ⟨-, -, -, hKm, hmm⟩ := vortex_next_level_sizes hK (le_refl 1) hKKN
  obtain ⟨W', hW'sub, hW'card⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin N))) (n := N / K)
      (by rw [hcard]; exact Nat.div_le_self _ _)
  obtain ⟨W'', hW''sub, hW''card⟩ :=
    Finset.exists_subset_card_eq (s := W') (n := (N / K) / K)
      (by rw [hW'card]; exact Nat.div_le_self _ _)
  have hW''le : K * ((N / K) / K) ≤ N / K := Nat.le.intro (Nat.div_add_mod (N / K) K)
  have hW''pos : 2 ≤ (N / K) / K := by
    rw [Nat.le_div_iff_mul_le hKpos, Nat.le_div_iff_mul_le hKpos]
    simp only [hN]; nlinarith only [htKK]
  have hNK1 : 1 ≤ N / K := by
    rcases Nat.eq_zero_or_pos (N / K) with h | h
    · rw [h] at hW''pos; simp at hW''pos
    · exact h
  -- the two lower bounds on `N / K`
  have hlow : n₂ + k ≤ N / K := by
    rw [Nat.le_div_iff_mul_le hKpos]
    simp only [hN]; omega
  have hpos : (0 : ℝ) < 1 / 10 - ε := by linarith only [hε']
  have hkinv : (1 : ℝ) ≤ (1 / 10 - ε) * (k : ℝ) := by
    have h := hk.le
    rw [div_le_iff₀ hpos] at h
    linarith only [h]
  -- `x ≥ k` real numbers satisfy `(9/10 + ε) x ≤ x - 1`
  have hmain : ∀ x : ℝ, (k : ℝ) ≤ x → (9 / 10 + ε) * x ≤ x - 1 := by
    intro x hx
    nlinarith [hkinv, hpos]
  have hN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    have h1 : 1 ≤ N := by omega
    push_cast [Nat.cast_sub h1]; ring
  have hkN : (k : ℝ) ≤ (N : ℝ) := by
    have : k ≤ N := by simp only [hN]; omega
    exact_mod_cast this
  refine ⟨N, Finset.univ, W', W'', cliqueEdges (Finset.univ : Finset (Fin N)), ?_, ?_, hW'sub,
    hW''sub, ?_, ?_, ?_, Finset.Subset.refl _, triDivisible_cliqueEdges_univ (t := t) rfl, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [hcard]; simp only [hN]; omega
  · rw [hcard]; simp only [hN]; omega
  · rw [hcard, hW'card]; exact hKm
  · rw [hcard, hW'card]; exact hmm
  · rw [hW'card, hW''card]; exact hW''le
  · -- minimum degree on `W`
    intro v _
    rw [edeg_cliqueEdges_of_mem (Finset.mem_univ v), hcard, hN1]
    have h1 := hmain (N : ℝ) hkN
    have h2 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    nlinarith only [h1, h2, hε]
  · -- density inside `W'`
    intro v hv
    have hinter : cliqueEdges (Finset.univ : Finset (Fin N)) ∩ cliqueEdges W' = cliqueEdges W' :=
      Finset.inter_eq_right.2 (cliqueEdges_mono (Finset.subset_univ _))
    rw [hinter, edeg_cliqueEdges_of_mem hv, hW'card]
    have hn₂ : n₂ ≤ N / K := le_trans (Nat.le_add_right _ _) hlow
    have hfle : f (N / K) ≤ 9 / 10 + ε := hf _ hn₂
    have hk' : (k : ℝ) ≤ ((N / K : ℕ) : ℝ) := by
      have : k ≤ N / K := le_trans (Nat.le_add_left _ _) hlow
      exact_mod_cast this
    have hcast : (((N / K) - 1 : ℕ) : ℝ) = ((N / K : ℕ) : ℝ) - 1 := by
      push_cast [Nat.cast_sub hNK1]; ring
    rw [hcast]
    have h1 := hmain _ hk'
    have h2 : (0 : ℝ) ≤ ((N / K : ℕ) : ℝ) := by positivity
    nlinarith only [h1, h2, hfle]
  · -- `W \ W'` is nonempty
    rw [Finset.sdiff_nonempty]
    intro hsub
    have hcle : (Finset.univ : Finset (Fin N)).card ≤ W'.card := Finset.card_le_card hsub
    rw [hcard, hW'card] at hcle
    have : N / K ≤ N / 2 := Nat.div_le_div_left hK (by omega)
    omega
  · rw [← Finset.card_pos, hW''card]; omega
  · have hinter : cliqueEdges (Finset.univ : Finset (Fin N)) ∩ cliqueEdges W'' = cliqueEdges W'' :=
      Finset.inter_eq_right.2 (cliqueEdges_mono (Finset.subset_univ _))
    rw [hinter]
    exact cliqueEdges_nonempty (by omega)

/-- **The reservoir clause supplied by the fused interface is not vacuous.**  Whatever schedule,
thresholds, ratio and nibble parameter `VortexReservoirEngine` produces, configurations satisfying
every hypothesis of its reservoir clause exist, arbitrarily large. -/
theorem vortexReservoirEngine_reservoir_not_vacuous (hEng : VortexReservoirEngine)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 10) (n₀ : ℕ) (Nthr : ℝ → ℕ) :
    ∃ (f : ℕ → ℝ) (n₂ C K : ℕ) (η : ℝ), 2 ≤ K ∧ 0 < η ∧ n₀ ≤ n₂ ∧ n₂ ≤ C ∧
      ReservoirClause ε η f n₂ K ∧
      ∃ (N : ℕ) (W W' W'' : Finset (Fin N)) (F : Finset (Sym2 (Fin N))),
        n₀ ≤ W.card ∧ n₂ ≤ W.card ∧ W' ⊆ W ∧ W'' ⊆ W' ∧
        K * W'.card ≤ W.card ∧ W.card ≤ K * K * W'.card ∧ K * W''.card ≤ W'.card ∧
        F ⊆ cliqueEdges W ∧ TriDivisible F ∧
        (∀ v ∈ W, (9 / 10 + ε / 4) * (W.card : ℝ) ≤ (edeg F v : ℝ)) ∧
        (∀ v ∈ W', f W'.card * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) ∧
        (W \ W').Nonempty ∧ W''.Nonempty ∧ (F ∩ cliqueEdges W'').Nonempty := by
  obtain ⟨f, n₂, C, K, η, hK, -, hη, hn₀, -, hn₂C, -, hfbd, -, -, hRes⟩ := hEng ε hε n₀ Nthr
  exact ⟨f, n₂, C, K, η, hK, hη, hn₀, hn₂C, hRes,
    reservoirClause_hypotheses_realizable hε hε' hK (fun s hs => (hfbd s hs).2) n₀⟩

end BKLO
