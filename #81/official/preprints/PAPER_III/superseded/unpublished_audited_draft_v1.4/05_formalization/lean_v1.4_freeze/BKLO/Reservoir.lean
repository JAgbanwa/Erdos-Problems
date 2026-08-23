/-
# BKLO §10, re-architected: the fused vortex–reservoir interface.

The original split of §10 into `BKLO.VortexScheduleExists` (existence of the vortex) and
`BKLO.CoverDownK3` (the cover-down lemma) is broken: `BKLO.not_coverDownK3` shows that
`CoverDownK3`, stated for an *adversarial* leftover `F` and with no reservoir, is false — the
parity counterexample of `BKLO/CoverDownRefutationB.lean` and the counting counterexample of
`BKLO/CoverDownRefutationA.lean` between them kill every ratio `K`.  The divisible repair
`BKLO.CoverDownK3Div` of `BKLO/CoverDownRepaired.lean` is of the strength of the main theorem
itself, hence circular.

The root cause is that the cover-down was *assumed*, rather than *derived* from the data that
makes it true: a **reservoir** of edges from `W \ W'` into the next level `W'`, left untouched by
the nibble, which is what lets the nibble's leftover be covered by triangles with apexes in `W'`.

This file sets up the re-architecture.  It defines

* `resLink R W' u` — the reserved link of `u` inside `W'`;
* `crossStars D X` — the crossing edges `s(u, a)`, `u ∈ D`, `a ∈ X u`, prescribed by a *link
  system* `X`;
* `IsLinkCover` — what it means for a triangle family to cover a prescribed link system by
  triangles `{u, a, b}` with `a, b ∈ W'`, using only crossing edges of the system and edges inside
  `W'`, touching no edge inside `W''`, and damaging each vertex of `W'` by at most `γ|W'|`;
* `VortexReservoirEngine` — the **single fused interface** replacing the broken pair: it produces
  the density schedule, the bounded good bottom set, the descent to the next level *and*, at each
  level, a reservoir with the two properties the cover-down actually consumes (abundance of
  reserved common apexes, and coverability of the residual link system).

The cover-down step itself is **not** part of the interface: it is derived in
`BKLO/CoverDownFused.lean` from the interface, the strengthened nibble
(`BKLO.FracToApproxMaxDeg`), Dross's threshold, and the already-proved greedy
`BKLO.exists_coverDown_family`.

Everything here is `sorry`-free: these are definitions plus elementary lemmas about them.
-/
import BKLO.CoverDown
import BKLO.CoverDownObstruction
import BKLO.NibbleMaxDeg

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The reservoir vocabulary -/

/-- The **reserved link** of `u` inside `W'`: the vertices of `W'` joined to `u` by a reserved
edge. -/
def resLink (R : Finset (Sym2 V)) (W' : Finset V) (u : V) : Finset V :=
  W'.filter (fun a => s(u, a) ∈ R)

theorem mem_resLink {R : Finset (Sym2 V)} {W' : Finset V} {u a : V} :
    a ∈ resLink R W' u ↔ a ∈ W' ∧ s(u, a) ∈ R := by
  simp [resLink]

/-- The crossing edges prescribed by a **link system** `X` on the vertex set `D`. -/
def crossStars (D : Finset V) (X : V → Finset V) : Finset (Sym2 V) :=
  D.biUnion (fun u => (X u).image (fun a => s(u, a)))

theorem mem_crossStars {D : Finset V} {X : V → Finset V} {e : Sym2 V} :
    e ∈ crossStars D X ↔ ∃ u ∈ D, ∃ a ∈ X u, e = s(u, a) := by
  simp only [crossStars, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨u, hu, a, ha, rfl⟩; exact ⟨u, hu, a, ha, rfl⟩
  · rintro ⟨u, hu, a, ha, rfl⟩; exact ⟨u, hu, a, ha, rfl⟩

theorem crossStars_mem {D : Finset V} {X : V → Finset V} {u a : V} (hu : u ∈ D) (ha : a ∈ X u) :
    s(u, a) ∈ crossStars D X :=
  mem_crossStars.2 ⟨u, hu, a, ha, rfl⟩

/-- A reservoir is **crossing** for the pair `W' ⊆ W`: each of its edges joins a vertex of
`W \ W'` to a vertex of `W'`. -/
def IsCrossing (W W' : Finset V) (R : Finset (Sym2 V)) : Prop :=
  ∀ e ∈ R, ∃ u ∈ W \ W', ∃ a ∈ W', e = s(u, a)

/-- A crossing edge set contains no edge inside `W'`. -/
theorem disjoint_cliqueEdges_of_isCrossing {W W' : Finset V} {R : Finset (Sym2 V)}
    (h : IsCrossing W W' R) : Disjoint R (cliqueEdges W') := by
  classical
  refine Finset.disjoint_left.2 fun e he he' => ?_
  obtain ⟨u, hu, a, -, rfl⟩ := h e he
  obtain ⟨hmem, -⟩ := mem_cliqueEdgesV.1 he'
  exact (Finset.mem_sdiff.1 hu).2 (hmem u (by simp))

/-- **A link cover.**  `Q` is an edge-disjoint family of triangles inside `F` which covers every
crossing edge prescribed by the link system `X`, uses no edges other than those crossing edges and
edges inside `W'`, touches no edge inside `W''`, and consumes at most `γ|W'|` edges inside `W'` at
each vertex of `W'`. -/
def IsLinkCover (F : Finset (Sym2 V)) (W' W'' D : Finset V) (X : V → Finset V) (γ : ℝ)
    (Q : Finset (Finset V)) : Prop :=
  TriFamilyIn F Q ∧
  crossStars D X ⊆ famEdges Q ∧
  famEdges Q ⊆ crossStars D X ∪ cliqueEdges W' ∧
  Disjoint (famEdges Q) (cliqueEdges W'') ∧
  ∀ v ∈ W', (edeg (famEdges Q ∩ cliqueEdges W') v : ℝ) ≤ γ * (W'.card : ℝ)

/-! ### The fused interface -/

/-- **The bottom-set clause**: every large dense edge set contains a good bottom set of bounded
size (the probabilistic existence of the vortex's smallest level). -/
def VortexBottomClause (ε : ℝ) (f : ℕ → ℝ) (n₂ C : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (S : Finset V) (E : Finset (Sym2 V)),
    n₂ ≤ S.card → E ⊆ cliqueEdges S →
    (∀ v ∈ S, (9 / 10 + ε) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
    ∃ U : Finset V, U ⊆ S ∧ n₂ ≤ U.card ∧ U.card ≤ C ∧
      ∀ v ∈ U, f U.card * (U.card : ℝ) ≤ (edeg (E ∩ cliqueEdges U) v : ℝ)

/-- **The descent clause**: one level of the vortex, of a prescribed size, containing a prescribed
bottom set, on which the edge set is still dense. -/
def VortexDescentClause (f : ℕ → ℝ) (n₂ : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (W U : Finset V) (E : Finset (Sym2 V)) (m : ℕ),
    n₂ ≤ U.card → U ⊆ W → U.card ≤ m → 2 * m ≤ W.card → E ⊆ cliqueEdges W →
    (∀ v ∈ W, f W.card * (W.card : ℝ) ≤ (edeg E v : ℝ)) →
    ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ W'.card = m ∧
      ∀ v ∈ W', f m * (m : ℝ) ≤ (edeg (E ∩ cliqueEdges W') v : ℝ)

/-- **The reservoir clause.**  At three consecutive levels `W'' ⊆ W' ⊆ W` in the size window, for a
triangle-divisible edge set `F` that is dense on `W` and dense inside `W'`, there is a reservoir
`R ⊆ F` of crossing edges of maximum degree at most `(ε/8)|W|` with

* *(apex abundance)* any two vertices of `W \ W'` have at least `2η|W|` reserved common neighbours
  inside `W'` — exactly what the greedy `BKLO.exists_coverDown_family` consumes when the nibble's
  leftover has maximum degree at most `η|W|`;
* *(link covering)* every link system differing from the reserved links by at most `2η|W|` vertices
  at each `u`, with even links, admits a link cover with damage `ε/8`.

Both are statements about a *sparse* structure: the reservoir has maximum degree `(ε/8)|W|`, and a
link cover consumes at each vertex of `W'` only `(ε/8)|W'|` of the edges inside `W'`. -/
def ReservoirClause (ε η : ℝ) (f : ℕ → ℝ) (n₂ K : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
    n₂ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
    K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
    F ⊆ cliqueEdges W → TriDivisible F →
    (∀ v ∈ W, (9 / 10 + ε / 4) * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
    (∀ v ∈ W', f W'.card * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
    ∃ R : Finset (Sym2 V), R ⊆ F ∧ IsCrossing W W' R ∧
      (∀ v : V, (edeg R v : ℝ) ≤ ε / 8 * (W.card : ℝ)) ∧
      (∀ u ∈ W \ W', ∀ v ∈ W \ W',
        2 * η * (W.card : ℝ) ≤ ((apexes R W' u v).card : ℝ)) ∧
      (∀ X : V → Finset V,
        (∀ u ∈ W \ W', X u ⊆ W') →
        (∀ u ∈ W \ W', ∀ a ∈ X u, s(u, a) ∈ F) →
        (∀ u ∈ W \ W', Even (X u).card) →
        (∀ u ∈ W \ W', ((X u \ resLink R W' u).card : ℝ) ≤ 2 * η * (W.card : ℝ)) →
        (∀ u ∈ W \ W', ((resLink R W' u \ X u).card : ℝ) ≤ 2 * η * (W.card : ℝ)) →
        ∃ Q : Finset (Finset V), IsLinkCover F W' W'' (W \ W') X (ε / 8) Q)

/-- **The fused §10 interface: vortex + reservoir**, replacing the broken pair
`VortexScheduleExists` + `CoverDownK3`.  For every `ε > 0`, every threshold `n₀` and every
threshold function `N` (which will be the threshold of the nibble as a function of its leftover
parameter) there are a density schedule `f`, thresholds `n₂ ≤ C`, a size ratio `K ≥ max(2, 8/ε)`
and a nibble parameter `η > 0`, with `n₂` above both `n₀` and `N η`, such that `f` stays inside
`[9/10 + ε/2, 9/10 + ε]` and the bottom, descent and reservoir clauses hold. -/
def VortexReservoirEngine : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ (n₀ : ℕ) (N : ℝ → ℕ), ∃ (f : ℕ → ℝ) (n₂ C K : ℕ) (η : ℝ),
    2 ≤ K ∧ (8 : ℝ) / ε ≤ (K : ℝ) ∧ 0 < η ∧
    n₀ ≤ n₂ ∧ N η ≤ n₂ ∧ n₂ ≤ C ∧ 0 < n₂ ∧
    (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + ε) ∧
    VortexBottomClause ε f n₂ C ∧ VortexDescentClause f n₂ ∧ ReservoirClause ε η f n₂ K

/-! ### Elementary lemmas used by the derivation -/

/-- A triangle family inside a smaller edge set is one inside a larger one. -/
theorem TriFamilyIn.mono {E E' : Finset (Sym2 V)} {P : Finset (Finset V)} (h : TriFamilyIn E P)
    (hEE' : E ⊆ E') : TriFamilyIn E' P :=
  ⟨h.1, fun t ht => (h.2.1 t ht).trans hEE', h.2.2⟩

/-- A triangle family whose edges lie in a set disjoint from the edges already used is a triangle
family in the leftover. -/
theorem triFamilyIn_sdiff {E A : Finset (Sym2 V)} {P : Finset (Finset V)} (h : TriFamilyIn E P)
    (hA : ∀ t ∈ P, Disjoint (cliqueEdges t) A) : TriFamilyIn (E \ A) P :=
  ⟨h.1, fun t ht _e he => Finset.mem_sdiff.2 ⟨h.2.1 t ht he, fun hA' =>
    (Finset.disjoint_left.1 (hA t ht) he) hA'⟩, h.2.2⟩

/-- Every edge of a triangle family lies in one of its triangles. -/
theorem exists_triangle_of_mem_famEdges {P : Finset (Finset V)} {e : Sym2 V}
    (he : e ∈ famEdges P) : ∃ t ∈ P, e ∈ cliqueEdges t :=
  Finset.mem_biUnion.1 he

/-- The number of edges of a triangle family at a vertex is twice the number of its triangles
through that vertex. -/
theorem edeg_famEdges_le_two_mul_card_filter (P : Finset (Finset V)) (h3 : ∀ t ∈ P, t.card = 3)
    (u : V) : edeg (famEdges P) u ≤ 2 * (P.filter (fun t => u ∈ t)).card := by
  classical
  have hsub : (famEdges P).filter (fun e => u ∈ e) ⊆
      (P.filter (fun t => u ∈ t)).biUnion (fun t => (cliqueEdges t).filter (fun e => u ∈ e)) := by
    intro e he
    obtain ⟨heP, hue⟩ := Finset.mem_filter.1 he
    obtain ⟨t, ht, het⟩ := exists_triangle_of_mem_famEdges heP
    have hut : u ∈ t := by
      obtain ⟨hmem, -⟩ := mem_cliqueEdgesV.1 het
      exact hmem u hue
    exact Finset.mem_biUnion.2 ⟨t, Finset.mem_filter.2 ⟨ht, hut⟩,
      Finset.mem_filter.2 ⟨het, hue⟩⟩
  calc edeg (famEdges P) u ≤ ((P.filter (fun t => u ∈ t)).biUnion
        (fun t => (cliqueEdges t).filter (fun e => u ∈ e))).card := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ P.filter (fun t => u ∈ t), ((cliqueEdges t).filter (fun e => u ∈ e)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ P.filter (fun t => u ∈ t), 2 := by
        refine Finset.sum_le_sum fun t ht => ?_
        obtain ⟨htP, hut⟩ := Finset.mem_filter.1 ht
        have := edeg_cliqueEdges (h3 t htP) u
        rw [if_pos hut] at this
        exact le_of_eq this
    _ = 2 * (P.filter (fun t => u ∈ t)).card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]


/-- Splitting the degree along a subtraction (the `Type*`-general form of
`BKLO.edeg_le_edeg_sdiff_add_edeg`). -/
theorem edeg_le_sdiff_add_edeg (E A : Finset (Sym2 V)) (v : V) :
    edeg E v ≤ edeg (E \ A) v + edeg A v := by
  classical
  have hsub : E.filter (fun e => v ∈ e) ⊆
      (E \ A).filter (fun e => v ∈ e) ∪ A.filter (fun e => v ∈ e) := by
    intro e he
    rw [Finset.mem_filter] at he
    by_cases hA : e ∈ A
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hA, he.2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨he.1, hA⟩, he.2⟩)
  calc edeg E v ≤ ((E \ A).filter (fun e => v ∈ e) ∪ A.filter (fun e => v ∈ e)).card :=
        Finset.card_le_card hsub
    _ ≤ edeg (E \ A) v + edeg A v := Finset.card_union_le _ _


/-- Subadditivity of `edeg` along a union. -/
theorem edeg_union_le (A B : Finset (Sym2 V)) (v : V) : edeg (A ∪ B) v ≤ edeg A v + edeg B v := by
  classical
  unfold edeg
  rw [Finset.filter_union]
  exact Finset.card_union_le _ _

/-- The degree inside a clique is at most its size (the `Type*`-general form of
`BKLO.edeg_cliqueEdges_le`). -/
theorem edeg_cliqueEdges_le' (W : Finset V) (v : V) : edeg (cliqueEdges W) v ≤ W.card := by
  classical
  have hsub : (cliqueEdges W).filter (fun e => v ∈ e) ⊆ W.image (fun u => s(v, u)) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨hmem, -⟩ := mem_cliqueEdgesV.1 he.1
    have hv := he.2
    induction e using Sym2.ind with
    | _ x y =>
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact Finset.mem_image.2 ⟨y, hmem y (by simp), rfl⟩
      · exact Finset.mem_image.2 ⟨x, hmem x (by simp), by rw [Sym2.eq_swap]⟩
  calc edeg (cliqueEdges W) v ≤ (W.image (fun u => s(v, u))).card := Finset.card_le_card hsub
    _ ≤ W.card := Finset.card_image_le

end BKLO
