/-
  Part B (Phase 2) — the absorbing calculus and the hub gadget.

  The local chunk-absorbing property of `ChunkAbsorber.lean` asks, for a leftover config `S`, for
  a reserved edge set `F` (the covered edges of a private part of the reserved family) such that

  * `F` itself is triangle-decomposable (it is a union of edge-disjoint reserved triangles), and
  * `F ∪ S` is triangle-decomposable.

  This file isolates that relation as `Absorbs G F S` and develops its calculus:

  * `absorbs_of_triDecomposable` — a decomposable config is absorbed by nothing;
  * `Absorbs.step` — **the chain rule**: if `S ∪ D` is decomposable and `F` absorbs `D`, then
    `D ∪ F` absorbs `S`.  Absorbability therefore propagates backwards along any chain
    `S ⟶ D₁ ⟶ D₂ ⟶ ⋯ ⟶ ∅` of "moves", a move `X ⟶ Y` being the decomposability of `X ∪ Y`;
  * `Absorbs.union` — disjoint configs are absorbed by disjoint reserved sets;
  * `localAbsorbable_of_absorbs` — the passage back to `LocalAbsorbable`.

  It then builds the **hub gadget**, the general form of the double cone: a permutation `σ` of an
  index type describes a disjoint union of cycles `i ↦ v i` in `G`; picking a *hub* `z i` in the
  common neighbourhood of `v i` and `v (σ i)` subdivides every cycle edge and produces

  * the **subdivision triangles** `{v i, z i, v (σ i)}`, showing `C ∪ D` decomposable, and
  * the **ear triangles** `{z (σ⁻¹ i), v i, z i}`, showing `D ∪ Z` decomposable,

  where `C` is the cycle edge set, `D` the set of subdivision edges and `Z` the set of hub edges
  `z (σ⁻¹ i) z i`.  Two applications of the chain rule then give

      `Absorbs G (D ∪ Z) C`   as soon as   `Absorbs G ∅ Z`, i.e. `Z` is decomposable,

  and the reserved triangles actually used are exactly the ear triangles — one per edge of `C`.
  The hub sequence is free, so `Z` can be prescribed: `hubEdges_friendship` shows that running the
  hubs through an Eulerian circuit of a *friendship graph* (`k` triangles through one centre)
  makes `Z` a union of `k` triangles, hence decomposable.  This is the per-chunk mechanism the
  reserved family has to supply.
-/
import Ax2.PartB.BKLO.CycleMatching

namespace Ax2.BKLO

open SimpleGraph Finset Ax2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The absorbing relation -/

/-- **`F` absorbs `S`**: the reserved edge set `F` is disjoint from the config `S`, is itself
triangle-decomposable, and together with `S` is triangle-decomposable.  This is exactly what a
private part `P` of the reserved family has to achieve for `S`, with `F = coveredEdges P`. -/
def Absorbs (G : SimpleGraph V) [DecidableRel G.Adj] (F S : Finset (Sym2 V)) : Prop :=
  Disjoint F S ∧ TriDecomposable G F ∧ TriDecomposable G (F ∪ S)

omit [Fintype V] in
theorem Absorbs.disjoint {G : SimpleGraph V} [DecidableRel G.Adj] {F S : Finset (Sym2 V)}
    (h : Absorbs G F S) : Disjoint F S := h.1

omit [Fintype V] in
theorem Absorbs.reserved {G : SimpleGraph V} [DecidableRel G.Adj] {F S : Finset (Sym2 V)}
    (h : Absorbs G F S) : TriDecomposable G F := h.2.1

omit [Fintype V] in
theorem Absorbs.total {G : SimpleGraph V} [DecidableRel G.Adj] {F S : Finset (Sym2 V)}
    (h : Absorbs G F S) : TriDecomposable G (F ∪ S) := h.2.2

omit [Fintype V] in
/-- A decomposable config needs no reservation. -/
theorem absorbs_of_triDecomposable (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset (Sym2 V)} (h : TriDecomposable G S) : Absorbs G ∅ S :=
  ⟨Finset.disjoint_empty_left _, ⟨∅, by simp, by simp [EdgeDisjoint], by simp [coveredEdges]⟩,
    by simpa using h⟩

omit [Fintype V] in
/-- Absorbing is symmetric: `F` absorbs `S` iff `S` absorbs `F`, provided both are
decomposable. -/
theorem Absorbs.symm {G : SimpleGraph V} [DecidableRel G.Adj] {F S : Finset (Sym2 V)}
    (h : Absorbs G F S) (hS : TriDecomposable G S) : Absorbs G S F :=
  ⟨h.1.symm, hS, by rw [Finset.union_comm]; exact h.total⟩

omit [Fintype V] in
/-- **The chain rule of the absorbing calculus.**  A *move* `S ⟶ D` is the decomposability of
`S ∪ D` (a symmetric relation).  Along a move, absorbability propagates backwards: if `F` absorbs
`D`, then `D ∪ F` absorbs `S`.  Indeed `D ∪ F` is decomposable because `F` absorbs `D`, and
`(D ∪ F) ∪ S = (S ∪ D) ⊎ F` is decomposable because both parts are. -/
theorem Absorbs.step {G : SimpleGraph V} [DecidableRel G.Adj] {S D F : Finset (Sym2 V)}
    (hSD : TriDecomposable G (S ∪ D)) (hdSD : Disjoint S D) (hFD : Absorbs G F D)
    (hFS : Disjoint F S) : Absorbs G (D ∪ F) S := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.disjoint_union_left]
    exact ⟨hdSD.symm, hFS⟩
  · rw [Finset.union_comm]
    exact hFD.total
  · have heq : (D ∪ F) ∪ S = (S ∪ D) ∪ F := by ext e; simp only [Finset.mem_union]; tauto
    rw [heq]
    refine hSD.union hFD.reserved ?_
    rw [Finset.disjoint_union_left]
    exact ⟨hFS.symm, hFD.disjoint.symm⟩

omit [Fintype V] in
/-- Disjoint configs are absorbed by disjoint reserved sets. -/
theorem Absorbs.union {G : SimpleGraph V} [DecidableRel G.Adj] {F₁ S₁ F₂ S₂ : Finset (Sym2 V)}
    (h₁ : Absorbs G F₁ S₁) (h₂ : Absorbs G F₂ S₂)
    (hd : Disjoint (F₁ ∪ S₁) (F₂ ∪ S₂)) : Absorbs G (F₁ ∪ F₂) (S₁ ∪ S₂) := by
  rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    at hd
  obtain ⟨⟨hF₁F₂, hF₁S₂⟩, hS₁F₂, hS₁S₂⟩ := hd
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨h₁.disjoint, hF₁S₂⟩, hS₁F₂.symm, h₂.disjoint⟩
  · exact h₁.reserved.union h₂.reserved hF₁F₂
  · have heq : (F₁ ∪ F₂) ∪ (S₁ ∪ S₂) = (F₁ ∪ S₁) ∪ (F₂ ∪ S₂) := by
      ext e; simp only [Finset.mem_union]; tauto
    rw [heq]
    exact h₁.total.union h₂.total (by
      rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
      exact ⟨⟨hF₁F₂, hF₁S₂⟩, hS₁F₂, hS₁S₂⟩)

omit [Fintype V] in
/-- A reserved part whose covered edges absorb `S` locally absorbs `S`. -/
theorem localAbsorbable_of_absorbs (G : SimpleGraph V) [DecidableRel G.Adj]
    {P : Finset (Finset V)} {S : Finset (Sym2 V)} (h : Absorbs G (coveredEdges P) S) :
    LocalAbsorbable G P S := h.total

omit [Fintype V] in
/-- Conversely, an edge-disjoint reserved part which locally absorbs `S` (and is disjoint from
it) absorbs `S`. -/
theorem absorbs_of_localAbsorbable (G : SimpleGraph V) [DecidableRel G.Adj]
    {P : Finset (Finset V)} {S : Finset (Sym2 V)} (hP : ∀ t ∈ P, G.IsNClique 3 t)
    (hPd : EdgeDisjoint P) (hd : Disjoint (coveredEdges P) S) (h : LocalAbsorbable G P S) :
    Absorbs G (coveredEdges P) S :=
  ⟨hd, TriDecomposable.of_family G hP hPd, h⟩

omit [Fintype V] in
/-- **Two moves.**  A chain `C ⟶ D ⟶ Z ⟶ ∅` makes `D ∪ Z` absorb `C`: apply the chain rule
twice, starting from the fact that a decomposable `Z` is absorbed by nothing.  This is the shape
of every gadget below: exhibit one triangle family covering `C ∪ D` and one covering `D ∪ Z`,
with the residue `Z` decomposable. -/
theorem Absorbs.of_chain₂ {G : SimpleGraph V} [DecidableRel G.Adj] {C D Z : Finset (Sym2 V)}
    (hCD : TriDecomposable G (C ∪ D)) (hDZ : TriDecomposable G (D ∪ Z))
    (hZ : TriDecomposable G Z) (hcd : Disjoint C D) (hdz : Disjoint D Z)
    (hcz : Disjoint C Z) : Absorbs G (D ∪ Z) C := by
  have step1 : Absorbs G Z D := by
    have := Absorbs.step (G := G) hDZ hdz (absorbs_of_triDecomposable G hZ)
      (Finset.disjoint_empty_left _)
    rwa [Finset.union_empty] at this
  exact Absorbs.step (G := G) hCD hcd step1 hcz.symm

omit [Fintype V] in
/-- **Absorbability along an arbitrary chain of moves.**  If `S, S₁, …, S_k` are pairwise disjoint,
consecutive unions `S ∪ S₁`, `S₁ ∪ S₂`, … are decomposable and the last set `S_k` is decomposable,
then `S₁ ∪ ⋯ ∪ S_k` absorbs `S`.  The two-move case is `Absorbs.of_chain₂`. -/
theorem absorbs_foldr_of_chain (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ (l : List (Finset (Sym2 V))) (S : Finset (Sym2 V)),
      (S :: l).Pairwise Disjoint →
      List.IsChain (fun X Y => TriDecomposable G (X ∪ Y)) (S :: l) →
      TriDecomposable G (l.getLastD S) →
      Absorbs G (l.foldr (· ∪ ·) ∅) S := by
  intro l
  induction l with
  | nil =>
      intro S _ _ hlast
      simpa using absorbs_of_triDecomposable G (by simpa using hlast)
  | cons X t ih =>
      intro S hpair hchain hlast
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hSX, hchain'⟩ := hchain
      have hpc := List.pairwise_cons.mp hpair
      have hIH := ih X hpc.2 hchain' (by rwa [List.getLastD_cons] at hlast)
      have hfd : Disjoint (t.foldr (· ∪ ·) ∅) S := by
        rw [Finset.disjoint_left]
        intro e he heS
        obtain ⟨Y, hY, heY⟩ := mem_foldr_union.mp he
        exact (Finset.disjoint_left.mp (hpc.1 Y (by simp [hY])) heS) heY
      exact Absorbs.step (G := G) hSX (hpc.1 X (by simp)) hIH hfd

omit [Fintype V] in
/-- **The generic two-family gadget.**  Two edge-disjoint families of `G`-triangles, one covering
`C ∪ D` and one covering `D ∪ Z`, absorb the config `C` by the second family, provided the residue
`Z` is decomposable.  The reserved part is the second family, so the reservation costs exactly its
number of triangles. -/
theorem localAbsorbable_of_two_families (G : SimpleGraph V) [DecidableRel G.Adj]
    {A P : Finset (Finset V)} {C D Z : Finset (Sym2 V)}
    (hAcl : ∀ t ∈ A, G.IsNClique 3 t) (hAd : EdgeDisjoint A) (hAcov : coveredEdges A = C ∪ D)
    (hPcl : ∀ t ∈ P, G.IsNClique 3 t) (hPd : EdgeDisjoint P) (hPcov : coveredEdges P = D ∪ Z)
    (hZ : TriDecomposable G Z)
    (hcd : Disjoint C D) (hdz : Disjoint D Z) (hcz : Disjoint C Z) :
    LocalAbsorbable G P C := by
  refine localAbsorbable_of_absorbs G ?_
  rw [hPcov]
  refine Absorbs.of_chain₂ ?_ ?_ hZ hcd hdz hcz
  · rw [← hAcov]; exact TriDecomposable.of_family G hAcl hAd
  · rw [← hPcov]; exact TriDecomposable.of_family G hPcl hPd

/-! ### The hub gadget -/

section Hub

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The edge set of the disjoint union of cycles described by the permutation `σ` through the
injection `v`. -/
def cycEdges (v : ι → V) (σ : Equiv.Perm ι) : Finset (Sym2 V) :=
  Finset.univ.image (fun i => s(v i, v (σ i)))

/-- The **subdivision edges**: every config edge `v i — v (σ i)` is subdivided by the hub `z i`. -/
def subdivEdges (v z : ι → V) (σ : Equiv.Perm ι) : Finset (Sym2 V) :=
  Finset.univ.image (fun i => s(v i, z i)) ∪ Finset.univ.image (fun i => s(z i, v (σ i)))

/-- The **hub edges**: the edges of the closed hub walk `⋯ — z (σ⁻¹ i) — z i — ⋯`. -/
def hubEdges (z : ι → V) (σ : Equiv.Perm ι) : Finset (Sym2 V) :=
  Finset.univ.image (fun i => s(z (σ.symm i), z i))

/-- The **subdivision triangles** `{v i, z i, v (σ i)}`: they decompose `C ∪ D`. -/
def subdivTris (v z : ι → V) (σ : Equiv.Perm ι) : Finset (Finset V) :=
  Finset.univ.image (fun i => ({v i, z i, v (σ i)} : Finset V))

/-- The **ear triangles** `{z (σ⁻¹ i), v i, z i}`: they decompose `D ∪ Z`.  These are the
triangles the reserved family has to supply — one per edge of the config. -/
def earTris (v z : ι → V) (σ : Equiv.Perm ι) : Finset (Finset V) :=
  Finset.univ.image (fun i => ({z (σ.symm i), v i, z i} : Finset V))

variable {v z : ι → V} {σ : Equiv.Perm ι}

omit [Fintype V] [DecidableEq ι] in
theorem mem_cycEdges_iff {e : Sym2 V} : e ∈ cycEdges v σ ↔ ∃ i, e = s(v i, v (σ i)) := by
  simp [cycEdges, eq_comm]

omit [Fintype V] [DecidableEq ι] in
theorem mem_hubEdges_iff {e : Sym2 V} :
    e ∈ hubEdges z σ ↔ ∃ i, e = s(z (σ.symm i), z i) := by
  simp [hubEdges, eq_comm]

omit [Fintype V] [DecidableEq ι] in
theorem mem_subdivEdges_iff {e : Sym2 V} :
    e ∈ subdivEdges v z σ ↔ (∃ i, e = s(v i, z i)) ∨ ∃ i, e = s(z i, v (σ i)) := by
  simp [subdivEdges, eq_comm]

omit [Fintype V] [DecidableEq ι] in
/-- Every endpoint of a config edge is a config vertex. -/
theorem forall_mem_cycEdges {e : Sym2 V} (he : e ∈ cycEdges v σ) {x : V} (hx : x ∈ e) :
    ∃ i, x = v i := by
  obtain ⟨i, rfl⟩ := mem_cycEdges_iff.mp he
  rcases Sym2.mem_iff.mp hx with rfl | rfl
  exacts [⟨i, rfl⟩, ⟨σ i, rfl⟩]

omit [Fintype V] [DecidableEq ι] in
/-- Every endpoint of a hub edge is a hub. -/
theorem forall_mem_hubEdges {e : Sym2 V} (he : e ∈ hubEdges z σ) {x : V} (hx : x ∈ e) :
    ∃ i, x = z i := by
  obtain ⟨i, rfl⟩ := mem_hubEdges_iff.mp he
  rcases Sym2.mem_iff.mp hx with rfl | rfl
  exacts [⟨σ.symm i, rfl⟩, ⟨i, rfl⟩]

omit [Fintype V] [DecidableEq ι] in
/-- A subdivision edge has a hub endpoint. -/
theorem exists_hub_mem_subdivEdges {e : Sym2 V} (he : e ∈ subdivEdges v z σ) :
    ∃ i, z i ∈ e := by
  rcases mem_subdivEdges_iff.mp he with ⟨i, rfl⟩ | ⟨i, rfl⟩
  exacts [⟨i, by simp⟩, ⟨i, by simp⟩]

omit [Fintype V] [DecidableEq ι] in
/-- A subdivision edge has a config endpoint. -/
theorem exists_vertex_mem_subdivEdges {e : Sym2 V} (he : e ∈ subdivEdges v z σ) :
    ∃ i, v i ∈ e := by
  rcases mem_subdivEdges_iff.mp he with ⟨i, rfl⟩ | ⟨i, rfl⟩
  exacts [⟨i, by simp⟩, ⟨σ i, by simp⟩]

omit [Fintype V] [DecidableEq ι] in
/-- The config edges and the subdivision edges are disjoint. -/
theorem disjoint_cycEdges_subdivEdges (hzv : ∀ i j, z i ≠ v j) :
    Disjoint (cycEdges v σ) (subdivEdges v z σ) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨i, hi⟩ := exists_hub_mem_subdivEdges he'
  obtain ⟨j, hj⟩ := forall_mem_cycEdges he hi
  exact hzv i j hj

omit [Fintype V] [DecidableEq ι] in
/-- The hub edges are disjoint from the config and from the subdivision edges. -/
theorem disjoint_hubEdges (hzv : ∀ i j, z i ≠ v j) :
    Disjoint (hubEdges z σ) (cycEdges v σ ∪ subdivEdges v z σ) := by
  rw [Finset.disjoint_left]
  intro e he he'
  rcases Finset.mem_union.mp he' with h | h
  · obtain ⟨i, hi⟩ := mem_cycEdges_iff.mp h
    obtain ⟨j, hj⟩ := forall_mem_hubEdges he (show v i ∈ e by rw [hi]; simp)
    exact hzv j i hj.symm
  · obtain ⟨i, hi⟩ := exists_vertex_mem_subdivEdges h
    obtain ⟨j, hj⟩ := forall_mem_hubEdges he hi
    exact hzv j i hj.symm

omit [Fintype V] [DecidableEq ι] in
/-- **The subdivision triangles cover the config together with the subdivision edges.** -/
theorem coveredEdges_subdivTris (hv : Function.Injective v) (hzv : ∀ i j, z i ≠ v j)
    (hfix : ∀ i, σ i ≠ i) :
    coveredEdges (subdivTris v z σ) = cycEdges v σ ∪ subdivEdges v z σ := by
  have htri : ∀ i : ι, triEdges ({v i, z i, v (σ i)} : Finset V)
      = {s(v i, z i), s(v i, v (σ i)), s(z i, v (σ i))} := by
    intro i
    exact triEdges_triple (fun h => hzv i i h.symm) (fun h => hfix i (hv h).symm) (hzv i (σ i))
  rw [coveredEdges, subdivTris, Finset.image_biUnion]
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, htri, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_union, mem_cycEdges_iff, mem_subdivEdges_iff]
  constructor
  · rintro ⟨i, h | h | h⟩
    exacts [Or.inr (Or.inl ⟨i, h⟩), Or.inl ⟨i, h⟩, Or.inr (Or.inr ⟨i, h⟩)]
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩)
    exacts [⟨i, Or.inr (Or.inl rfl)⟩, ⟨i, Or.inl rfl⟩, ⟨i, Or.inr (Or.inr rfl)⟩]

omit [Fintype V] [DecidableEq ι] in
/-- **The ear triangles cover the subdivision edges together with the hub edges.** -/
theorem coveredEdges_earTris (hzv : ∀ i j, z i ≠ v j) (hstep : ∀ i, z i ≠ z (σ i)) :
    coveredEdges (earTris v z σ) = subdivEdges v z σ ∪ hubEdges z σ := by
  have hstep' : ∀ i : ι, z (σ.symm i) ≠ z i := by
    intro i
    have := hstep (σ.symm i)
    rwa [Equiv.apply_symm_apply] at this
  have htri : ∀ i : ι, triEdges ({z (σ.symm i), v i, z i} : Finset V)
      = {s(z (σ.symm i), v i), s(z (σ.symm i), z i), s(v i, z i)} := by
    intro i
    exact triEdges_triple (hzv _ i) (hstep' i) (fun h => hzv i i h.symm)
  rw [coveredEdges, earTris, Finset.image_biUnion]
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, htri, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_union, mem_hubEdges_iff, mem_subdivEdges_iff]
  constructor
  · rintro ⟨i, h | h | h⟩
    · refine Or.inl (Or.inr ⟨σ.symm i, ?_⟩)
      rw [Equiv.apply_symm_apply]
      exact h
    · exact Or.inr ⟨i, h⟩
    · exact Or.inl (Or.inl ⟨i, h⟩)
  · rintro ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact ⟨i, Or.inr (Or.inr rfl)⟩
    · refine ⟨σ i, Or.inl ?_⟩
      rw [Equiv.symm_apply_apply]
    · exact ⟨i, Or.inr (Or.inl rfl)⟩

omit [Fintype V] [DecidableEq ι] in
/-- **The subdivision triangles are edge-disjoint.** -/
theorem edgeDisjoint_subdivTris (hv : Function.Injective v) (hzv : ∀ i j, z i ≠ v j)
    (hstep : ∀ i, z i ≠ z (σ i)) (hsq : ∀ i, σ (σ i) ≠ i) :
    EdgeDisjoint (subdivTris v z σ) := by
  intro t₁ ht₁ t₂ ht₂ hne
  simp only [subdivTris, Finset.mem_image, Finset.mem_univ, true_and] at ht₁ ht₂
  obtain ⟨i, rfl⟩ := ht₁
  obtain ⟨j, rfl⟩ := ht₂
  have hij : i ≠ j := by rintro rfl; exact hne rfl
  refine triEdges_disjoint_of_card_inter_le_one ?_
  rw [Finset.card_le_one]
  have key : ∀ w : V, (w = v i ∨ w = z i ∨ w = v (σ i)) → (w = v j ∨ w = z j ∨ w = v (σ j)) →
      (w = z i ∧ z i = z j) ∨ (w = v i ∧ i = σ j) ∨ (w = v (σ i) ∧ σ i = j) := by
    intro w h1 h2
    rcases h1 with rfl | rfl | rfl
    · rcases h2 with h | h | h
      · exact absurd (hv h) hij
      · exact absurd h.symm (hzv j i)
      · exact Or.inr (Or.inl ⟨rfl, hv h⟩)
    · rcases h2 with h | h | h
      · exact absurd h (hzv i j)
      · exact Or.inl ⟨rfl, h⟩
      · exact absurd h (hzv i (σ j))
    · rcases h2 with h | h | h
      · exact Or.inr (Or.inr ⟨rfl, hv h⟩)
      · exact absurd h.symm (hzv j (σ i))
      · exact absurd (σ.injective (hv h)) hij
  have hnn : ¬ (i = σ j ∧ σ i = j) := by
    rintro ⟨rfl, h⟩
    exact hsq j h
  have hz1 : i = σ j → z i ≠ z j := by
    rintro rfl h
    exact hstep j h.symm
  have hz2 : σ i = j → z i ≠ z j := by
    rintro rfl h
    exact hstep i h
  intro x hx y hy
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx hy
  have hx' := key x hx.1 hx.2
  have hy' := key y hy.1 hy.2
  rcases hx' with ⟨rfl, hxz⟩ | ⟨rfl, hxi⟩ | ⟨rfl, hxi⟩ <;>
    rcases hy' with ⟨rfl, hyz⟩ | ⟨rfl, hyi⟩ | ⟨rfl, hyi⟩
  · rfl
  · exact absurd hxz (hz1 hyi)
  · exact absurd hxz (hz2 hyi)
  · exact absurd hyz (hz1 hxi)
  · rfl
  · exact absurd ⟨hxi, hyi⟩ hnn
  · exact absurd hyz (hz2 hxi)
  · exact absurd ⟨hyi, hxi⟩ hnn
  · rfl

omit [Fintype V] [DecidableEq ι] in
/-- **The ear triangles are edge-disjoint**, provided distinct indices use distinct hub pairs. -/
theorem edgeDisjoint_earTris (hv : Function.Injective v) (hzv : ∀ i j, z i ≠ v j)
    (hpair : ∀ i j, i ≠ j →
      (({z (σ.symm i), z i} : Finset V) ∩ ({z (σ.symm j), z j} : Finset V)).card ≤ 1) :
    EdgeDisjoint (earTris v z σ) := by
  intro t₁ ht₁ t₂ ht₂ hne
  simp only [earTris, Finset.mem_image, Finset.mem_univ, true_and] at ht₁ ht₂
  obtain ⟨i, rfl⟩ := ht₁
  obtain ⟨j, rfl⟩ := ht₂
  have hij : i ≠ j := by rintro rfl; exact hne rfl
  refine triEdges_disjoint_of_card_inter_le_one
    (le_trans (Finset.card_le_card ?_) (hpair i j hij))
  intro x hx
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  obtain ⟨h1, h2⟩ := hx
  have hxvi : x ≠ v i := by
    rintro rfl
    rcases h2 with h | h | h
    · exact hzv (σ.symm j) i h.symm
    · exact hij (hv h)
    · exact hzv j i h.symm
  have hxvj : x ≠ v j := by
    rintro rfl
    rcases h1 with h | h | h
    · exact hzv (σ.symm i) j h.symm
    · exact hij (hv h).symm
    · exact hzv i j h.symm
  refine ⟨?_, ?_⟩
  · rcases h1 with h | h | h
    exacts [Or.inl h, absurd h hxvi, Or.inr h]
  · rcases h2 with h | h | h
    exacts [Or.inl h, absurd h hxvj, Or.inr h]

omit [Fintype V] [DecidableEq ι] in
/-- The config has exactly one edge per index. -/
theorem card_cycEdges (hv : Function.Injective v) (hsq : ∀ i, σ (σ i) ≠ i) :
    (cycEdges v σ).card = Fintype.card ι := by
  have hinj : Function.Injective (fun i => s(v i, v (σ i)) : ι → Sym2 V) := by
    intro i j h
    simp only [Sym2.eq_iff] at h
    rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact hv h1
    · exact absurd (by rw [← hv h1]; exact hv h2) (hsq j)
  have hc : cycEdges v σ = Finset.image (fun i => s(v i, v (σ i))) Finset.univ := rfl
  rw [hc, Finset.card_image_of_injective _ hinj, Finset.card_univ]

omit [Fintype V] [DecidableEq ι] in
/-- One reserved ear triangle per edge of the config. -/
theorem card_earTris_le : (earTris v z σ).card ≤ Fintype.card ι :=
  le_trans Finset.card_image_le (le_of_eq Finset.card_univ)

omit [Fintype V] [DecidableEq ι] in
/-- **The hub gadget absorbs the config.**  Two applications of the chain rule:

* the subdivision triangles `{v i, z i, v (σ i)}` decompose `C ∪ D`, so `C ⟶ D`;
* the ear triangles `{z (σ⁻¹ i), v i, z i}` decompose `D ∪ Z`, so `D ⟶ Z`;
* the hub edges `Z` are assumed decomposable, i.e. `Z ⟶ ∅`.

Hence `D ∪ Z` absorbs the config `C`, and `D ∪ Z` is precisely the edge set covered by the ear
triangles: **the reserved family only has to contain the ear triangles**, one per config edge. -/
theorem absorbs_cycEdges_of_hubGadget (G : SimpleGraph V) [DecidableRel G.Adj]
    (hv : Function.Injective v) (hzv : ∀ i j, z i ≠ v j)
    (hstep : ∀ i, z i ≠ z (σ i)) (hfix : ∀ i, σ i ≠ i) (hsq : ∀ i, σ (σ i) ≠ i)
    (hpair : ∀ i j, i ≠ j →
      (({z (σ.symm i), z i} : Finset V) ∩ ({z (σ.symm j), z j} : Finset V)).card ≤ 1)
    (hsub : ∀ i, G.IsNClique 3 ({v i, z i, v (σ i)} : Finset V))
    (hear : ∀ i, G.IsNClique 3 ({z (σ.symm i), v i, z i} : Finset V))
    (hZ : TriDecomposable G (hubEdges z σ)) :
    Absorbs G (subdivEdges v z σ ∪ hubEdges z σ) (cycEdges v σ) := by
  have hclsub : ∀ t ∈ subdivTris v z σ, G.IsNClique 3 t := by
    intro t ht
    simp only [subdivTris, Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨i, rfl⟩ := ht
    exact hsub i
  have hclear : ∀ t ∈ earTris v z σ, G.IsNClique 3 t := by
    intro t ht
    simp only [earTris, Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨i, rfl⟩ := ht
    exact hear i
  have hCD : TriDecomposable G (cycEdges v σ ∪ subdivEdges v z σ) := by
    rw [← coveredEdges_subdivTris hv hzv hfix]
    exact TriDecomposable.of_family G hclsub (edgeDisjoint_subdivTris hv hzv hstep hsq)
  have hDZ : TriDecomposable G (subdivEdges v z σ ∪ hubEdges z σ) := by
    rw [← coveredEdges_earTris hzv hstep]
    exact TriDecomposable.of_family G hclear (edgeDisjoint_earTris hv hzv hpair)
  have hHall := disjoint_hubEdges (v := v) (z := z) (σ := σ) hzv
  have hHC : Disjoint (hubEdges z σ) (cycEdges v σ) :=
    Finset.disjoint_of_subset_right Finset.subset_union_left hHall
  have hHD : Disjoint (hubEdges z σ) (subdivEdges v z σ) :=
    Finset.disjoint_of_subset_right Finset.subset_union_right hHall
  exact Absorbs.of_chain₂ hCD hDZ hZ (disjoint_cycEdges_subdivEdges hzv) hHD.symm hHC.symm

omit [Fintype V] [DecidableEq ι] in
/-- **The reserved part supplied by the hub gadget**: the ear triangles locally absorb the
config. -/
theorem localAbsorbable_earTris (G : SimpleGraph V) [DecidableRel G.Adj]
    (hv : Function.Injective v) (hzv : ∀ i j, z i ≠ v j)
    (hstep : ∀ i, z i ≠ z (σ i)) (hfix : ∀ i, σ i ≠ i) (hsq : ∀ i, σ (σ i) ≠ i)
    (hpair : ∀ i j, i ≠ j →
      (({z (σ.symm i), z i} : Finset V) ∩ ({z (σ.symm j), z j} : Finset V)).card ≤ 1)
    (hsub : ∀ i, G.IsNClique 3 ({v i, z i, v (σ i)} : Finset V))
    (hear : ∀ i, G.IsNClique 3 ({z (σ.symm i), v i, z i} : Finset V))
    (hZ : TriDecomposable G (hubEdges z σ)) :
    LocalAbsorbable G (earTris v z σ) (cycEdges v σ) := by
  refine localAbsorbable_of_absorbs G ?_
  rw [coveredEdges_earTris hzv hstep]
  exact absorbs_cycEdges_of_hubGadget G hv hzv hstep hfix hsq hpair hsub hear hZ

end Hub

end Ax2.BKLO
