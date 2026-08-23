/-
  Part B (Phase 2) — structural toolkit for the reserved-split kernel
  (`ReservedSplitExists`, `AbsorbingCoreExists` in `FlexBankBuild.lean`).

  This file collects the *proved* infrastructure that any construction of the BKLO absorbing
  core has to be assembled from, and reduces the kernel to a form in which the reservation
  book-keeping (the residual min-degree condition) has been discharged:

  * closure properties of `LocalAbsorbable`: the empty config (`localAbsorbable_empty`),
    arbitrary indexed disjoint unions (`localAbsorbable_biUnion`), and a leftover that is
    already triangle-decomposable (`localAbsorbable_of_decomposable`);
  * `hexCfg` / `HexValid` — the subdivided-triangle (6-cycle) config of a reserved triangle,
    packaged so that families of them can be handled uniformly, plus the assembly of a whole
    family of hexagonal chunks (`localAbsorbable_hexFamily`);
  * `ChunkSplit` — a splitting of a leftover into locally absorbable chunks, with
    `localAbsorbable_of_chunkSplit` and the converse `chunkSplit_of_localAbsorbable`;
  * the reservation book-keeping: `degree_le_residual_degree_add_load` bounds the degree lost to
    a reserved family by twice its vertex load, and `residual_degree_bound_of_load` turns a
    vertex-load budget of `ε n / 2` into the required residual min degree `≥ 9n/10`;
  * `exists_maximal_bounded_triangle_family` — greedy reservation: a load-bounded edge-disjoint
    triangle family that cannot be extended;
  * `BoundedAbsorbingCoreExists` and `absorbingCoreExists_of_bounded` — the kernel with the
    residual-degree condition replaced by the local reservation budget.
-/
import Ax2.PartB.BKLO.FlexBankBuild

namespace Ax2.BKLO

open SimpleGraph Finset Ax2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Closure properties of `LocalAbsorbable` -/

omit [Fintype V] in
/-- A reserved family always absorbs the empty config (keep its own decomposition). -/
theorem localAbsorbable_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    {B : Finset (Finset V)} (hB : ∀ t ∈ B, G.IsNClique 3 t) (hBd : EdgeDisjoint B) :
    LocalAbsorbable G B ∅ :=
  ⟨B, hB, hBd, by simp⟩

/-- **Configs compose over an arbitrary index set.** If each `part k` absorbs `S k` and the spans
`coveredEdges (part k) ∪ S k` are pairwise disjoint, then the union of the reserved families
absorbs the union of the configs. Iterated `localAbsorbable_union`. -/
theorem localAbsorbable_biUnion (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [DecidableEq ι] (K : Finset ι)
    (part : ι → Finset (Finset V)) (S : ι → Finset (Sym2 V))
    (h : ∀ k ∈ K, LocalAbsorbable G (part k) (S k))
    (hd : ∀ k ∈ K, ∀ l ∈ K, k ≠ l →
      Disjoint (coveredEdges (part k) ∪ S k) (coveredEdges (part l) ∪ S l)) :
    LocalAbsorbable G (K.biUnion part) (K.biUnion S) := by
  classical
  induction K using Finset.induction with
  | empty => exact ⟨∅, by simp, by simp [EdgeDisjoint], by simp [coveredEdges]⟩
  | insert k K hk ih =>
      rw [Finset.biUnion_insert, Finset.biUnion_insert]
      refine localAbsorbable_union G (h k (by simp)) (ih ?_ ?_) ?_
      · intro l hl; exact h l (by simp [hl])
      · intro l hl m hm hlm; exact hd l (by simp [hl]) m (by simp [hm]) hlm
      · rw [coveredEdges_biUnion, Finset.disjoint_union_right]
        refine ⟨?_, ?_⟩ <;> rw [Finset.disjoint_biUnion_right] <;> intro l hl
        · exact (Finset.disjoint_union_right.mp (hd k (by simp) l (by simp [hl])
            (by rintro rfl; exact hk hl))).1
        · exact (Finset.disjoint_union_right.mp (hd k (by simp) l (by simp [hl])
            (by rintro rfl; exact hk hl))).2

omit [Fintype V] in
/-- A leftover that carries a triangle decomposition of its own, edge-disjoint from the reserved
edges, is absorbed by every reserved family (put the two packings side by side). -/
theorem localAbsorbable_of_decomposable (G : SimpleGraph V) [DecidableRel G.Adj]
    {B : Finset (Finset V)} (hB : ∀ t ∈ B, G.IsNClique 3 t) (hBd : EdgeDisjoint B)
    {L : Finset (Sym2 V)} {P : Finset (Finset V)} (hP : ∀ t ∈ P, G.IsNClique 3 t)
    (hPd : EdgeDisjoint P) (hPcov : coveredEdges P = L)
    (hdisj : Disjoint L (coveredEdges B)) :
    LocalAbsorbable G B L := by
  classical
  refine ⟨P ∪ B, ?_, ?_, ?_⟩
  · intro t ht
    rcases Finset.mem_union.mp ht with h | h
    exacts [hP t h, hB t h]
  · intro t₁ h₁ t₂ h₂ hne
    have key : ∀ u ∈ P, ∀ w ∈ B, Disjoint (triEdges u) (triEdges w) := by
      intro u hu w hw
      refine Finset.disjoint_of_subset_left ?_ (Finset.disjoint_of_subset_right ?_ hdisj)
      · rw [← hPcov]; exact Finset.subset_biUnion_of_mem triEdges hu
      · exact Finset.subset_biUnion_of_mem triEdges hw
    rcases Finset.mem_union.mp h₁ with h₁' | h₁' <;> rcases Finset.mem_union.mp h₂ with h₂' | h₂'
    · exact hPd _ h₁' _ h₂' hne
    · exact key _ h₁' _ h₂'
    · exact (key _ h₂' _ h₁').symm
    · exact hBd _ h₁' _ h₂' hne
  · have : coveredEdges (P ∪ B) = coveredEdges P ∪ coveredEdges B := by
      simp [coveredEdges, Finset.union_biUnion]
    rw [this, hPcov, Finset.union_comm]

/-! ### Decomposable edge sets and the transformer (cascade) step -/

/-- An edge set carries an edge-disjoint decomposition into `G`-triangles. -/
def TriDecomposable (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V)) : Prop :=
  ∃ P : Finset (Finset V), (∀ t ∈ P, G.IsNClique 3 t) ∧ EdgeDisjoint P ∧ coveredEdges P = S

omit [Fintype V] in
/-- `B` absorbs `S` exactly when the reserved edges together with `S` are decomposable. -/
theorem localAbsorbable_iff_triDecomposable (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset (Finset V)) (S : Finset (Sym2 V)) :
    LocalAbsorbable G B S ↔ TriDecomposable G (coveredEdges B ∪ S) := Iff.rfl

omit [Fintype V] in
/-- The reserved edges of an edge-disjoint triangle family are decomposable. -/
theorem TriDecomposable.of_family (G : SimpleGraph V) [DecidableRel G.Adj]
    {B : Finset (Finset V)} (hB : ∀ t ∈ B, G.IsNClique 3 t) (hBd : EdgeDisjoint B) :
    TriDecomposable G (coveredEdges B) := ⟨B, hB, hBd, rfl⟩

omit [Fintype V] in
/-- Decomposability is closed under disjoint unions. -/
theorem TriDecomposable.union {G : SimpleGraph V} [DecidableRel G.Adj] {S₁ S₂ : Finset (Sym2 V)}
    (h₁ : TriDecomposable G S₁) (h₂ : TriDecomposable G S₂) (hd : Disjoint S₁ S₂) :
    TriDecomposable G (S₁ ∪ S₂) := by
  classical
  obtain ⟨P₁, hc₁, hd₁, hcov₁⟩ := h₁
  obtain ⟨P₂, hc₂, hd₂, hcov₂⟩ := h₂
  have s₁ : ∀ u ∈ P₁, triEdges u ⊆ S₁ := by
    intro u hu; rw [← hcov₁]; exact Finset.subset_biUnion_of_mem triEdges hu
  have s₂ : ∀ u ∈ P₂, triEdges u ⊆ S₂ := by
    intro u hu; rw [← hcov₂]; exact Finset.subset_biUnion_of_mem triEdges hu
  refine ⟨P₁ ∪ P₂, ?_, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_union.mp hu with h | h
    exacts [hc₁ u h, hc₂ u h]
  · intro t₁ ht₁ t₂ ht₂ hne
    rcases Finset.mem_union.mp ht₁ with h₁' | h₁' <;>
      rcases Finset.mem_union.mp ht₂ with h₂' | h₂'
    · exact hd₁ _ h₁' _ h₂' hne
    · exact Finset.disjoint_of_subset_left (s₁ _ h₁')
        (Finset.disjoint_of_subset_right (s₂ _ h₂') hd)
    · exact Finset.disjoint_of_subset_left (s₂ _ h₁')
        (Finset.disjoint_of_subset_right (s₁ _ h₂') hd.symm)
    · exact hd₂ _ h₁' _ h₂' hne
  · rw [show coveredEdges (P₁ ∪ P₂) = coveredEdges P₁ ∪ coveredEdges P₂ by
      simp [coveredEdges, Finset.union_biUnion], hcov₁, hcov₂]

omit [Fintype V] in
/-- **The transformer (cascade) step of the absorbing method.** Suppose the reserved family `B`
absorbs the config `S'` and `R` is a *transformer* from `S` to `S'`, i.e. both `R ∪ S` and
`R ∪ S'` are triangle-decomposable, all three edge sets being suitably disjoint. Then the enlarged
reserved family obtained by adding `R` together with a copy of `S'` absorbs `S`.

This is the mechanism by which a reserved core is made to absorb configs it cannot absorb
directly: one only ever has to transform the leftover into a *canonical* config `S'` that the core
handles. Proof: `(coveredEdges B ∪ R ∪ S') ∪ S = (coveredEdges B ∪ S') ⊎ (R ∪ S)` and both parts
are decomposable; the new core itself is `coveredEdges B ⊎ (R ∪ S')`. -/
theorem localAbsorbable_transformer (G : SimpleGraph V) [DecidableRel G.Adj]
    {B : Finset (Finset V)} {S S' R : Finset (Sym2 V)}
    (hB : ∀ t ∈ B, G.IsNClique 3 t) (hBd : EdgeDisjoint B)
    (habs : LocalAbsorbable G B S')
    (hRS : TriDecomposable G (R ∪ S)) (hRS' : TriDecomposable G (R ∪ S'))
    (hd1 : Disjoint (coveredEdges B ∪ S') (R ∪ S))
    (hd2 : Disjoint (coveredEdges B) (R ∪ S')) :
    ∃ B' : Finset (Finset V), (∀ t ∈ B', G.IsNClique 3 t) ∧ EdgeDisjoint B' ∧
      coveredEdges B' = coveredEdges B ∪ (R ∪ S') ∧ LocalAbsorbable G B' S := by
  classical
  obtain ⟨B', hc, hd, hcov⟩ := (TriDecomposable.of_family G hB hBd).union hRS' hd2
  refine ⟨B', hc, hd, hcov, ?_⟩
  rw [localAbsorbable_iff_triDecomposable, hcov]
  have heq : coveredEdges B ∪ (R ∪ S') ∪ S = (coveredEdges B ∪ S') ∪ (R ∪ S) := by
    ext e; simp only [Finset.mem_union]; tauto
  rw [heq]
  exact ((localAbsorbable_iff_triDecomposable G B S').mp habs).union hRS hd1

/-! ### The hexagonal chunk -/

/-- The subdivided-triangle config of the reserved triangle `abc` with midpoints `x, y, z`:
the 6-cycle `a-x-b-z-c-y`. -/
def hexCfg (a b c x y z : V) : Finset (Sym2 V) :=
  {s(a, x), s(b, x), s(a, y), s(c, y), s(b, z), s(c, z)}

/-- The data making `hexCfg a b c x y z` a legitimate chunk for the reserved triangle `abc`:
six distinct vertices, and the three switched triangles `abx`, `acy`, `bcz` of `G`. -/
def HexValid (G : SimpleGraph V) [DecidableRel G.Adj] (a b c x y z : V) : Prop :=
  ([a, b, c, x, y, z] : List V).Nodup ∧
    G.IsNClique 3 ({a, b, x} : Finset V) ∧ G.IsNClique 3 ({a, c, y} : Finset V) ∧
      G.IsNClique 3 ({b, c, z} : Finset V)

omit [Fintype V] in
/-- A valid hexagonal chunk has a genuine `G`-triangle as its reserved triangle. -/
theorem HexValid.isNClique {G : SimpleGraph V} [DecidableRel G.Adj] {a b c x y z : V}
    (h : HexValid G a b c x y z) : G.IsNClique 3 ({a, b, c} : Finset V) := by
  obtain ⟨-, h1, h2, h3⟩ := h
  rw [SimpleGraph.is3Clique_triple_iff] at h1 h2 h3 ⊢
  exact ⟨h1.1, h2.1, h3.1⟩

omit [Fintype V] in
/-- **The hexagonal chunk is absorbed by its reserved triangle** (packaged form of
`localAbsorbable_subdividedTriangle`). -/
theorem HexValid.localAbsorbable {G : SimpleGraph V} [DecidableRel G.Adj] {a b c x y z : V}
    (h : HexValid G a b c x y z) :
    LocalAbsorbable G ({{a, b, c}} : Finset (Finset V)) (hexCfg a b c x y z) := by
  obtain ⟨hnd, h1, h2, h3⟩ := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, not_or] at hnd
  exact localAbsorbable_subdividedTriangle G (by tauto) (by tauto) (by tauto) (by tauto)
    (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) (by tauto)
    (by tauto) (by tauto) (by tauto) h1 h2 h3

/-- **A whole family of hexagonal chunks is absorbed by the family of its reserved triangles.**
This is the assembly step for the direct (route 2) construction: match each chunk of the leftover
to its own reserved triangle, with pairwise disjoint spans. -/
theorem localAbsorbable_hexFamily (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [DecidableEq ι] (K : Finset ι) (a b c x y z : ι → V)
    (hvalid : ∀ k ∈ K, HexValid G (a k) (b k) (c k) (x k) (y k) (z k))
    (hdisj : ∀ k ∈ K, ∀ l ∈ K, k ≠ l →
      Disjoint (coveredEdges ({{a k, b k, c k}} : Finset (Finset V)) ∪
          hexCfg (a k) (b k) (c k) (x k) (y k) (z k))
        (coveredEdges ({{a l, b l, c l}} : Finset (Finset V)) ∪
          hexCfg (a l) (b l) (c l) (x l) (y l) (z l))) :
    LocalAbsorbable G (K.biUnion (fun k => ({{a k, b k, c k}} : Finset (Finset V))))
      (K.biUnion (fun k => hexCfg (a k) (b k) (c k) (x k) (y k) (z k))) :=
  localAbsorbable_biUnion G K _ _ (fun k hk => (hvalid k hk).localAbsorbable) hdisj

/-! ### The double cone: transforming one 6-cycle into another -/

omit [Fintype V] in
/-- Two triangles meeting in at most one vertex have disjoint edge sets. -/
theorem triEdges_disjoint_of_card_inter_le_one {t u : Finset V} (h : (t ∩ u).card ≤ 1) :
    Disjoint (triEdges t) (triEdges u) := by
  refine Finset.disjoint_left.mpr ?_
  intro e he he'
  revert he he'
  induction e using Sym2.inductionOn with
  | _ p q =>
    simp only [triEdges, Finset.mem_filter, Finset.mem_sym2_iff, Sym2.mk_isDiag_iff]
    rintro ⟨hmem, hne⟩ ⟨hmem', -⟩
    have hp : p ∈ t ∩ u := Finset.mem_inter.mpr ⟨hmem p (by simp), hmem' p (by simp)⟩
    have hq : q ∈ t ∩ u := Finset.mem_inter.mpr ⟨hmem q (by simp), hmem' q (by simp)⟩
    exact hne (Finset.card_le_one.mp h p hp q hq)

/-- The twelve spokes from two apexes `w, u` to the six vertices `a, x, b, z, c, y`. -/
def doubleConeEdges (a x b z c y w u : V) : Finset (Sym2 V) :=
  {s(w, a), s(w, x), s(w, b), s(w, z), s(w, c), s(w, y),
   s(u, a), s(u, x), s(u, b), s(u, z), s(u, c), s(u, y)}

/-- The 6-cycle `a-x-b-z-c-y-a`. -/
def sixCycleEdges (a x b z c y : V) : Finset (Sym2 V) :=
  {s(a, x), s(x, b), s(b, z), s(z, c), s(c, y), s(y, a)}

omit [Fintype V] in
/-- The 6-cycle of `sixCycleEdges` is the subdivided-triangle config `hexCfg` of the alternating
triple `a, b, c` with midpoints `x, y, z`. -/
theorem sixCycleEdges_eq_hexCfg (a x b z c y : V) :
    sixCycleEdges a x b z c y = hexCfg a b c x y z := by
  ext e
  simp only [sixCycleEdges, hexCfg, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_swap]
  constructor <;> (intro h; rcases h with h|h|h|h|h|h <;> subst h <;> simp)

set_option maxHeartbeats 1000000 in
omit [Fintype V] in
/-- **The double cone is triangle-decomposable together with the 6-cycle it spans.** Take two
apexes `w, u` outside the 6-cycle `a-x-b-z-c-y` and join both to all six of its vertices. Then the
resulting 18 edges split into the six triangles `wax`, `wbz`, `wcy`, `uxb`, `uzc`, `uya`: the
apex `w` picks up the alternate edges `ax, bz, cy` of the cycle and the apex `u` the remaining
ones `xb, zc, ya`.

This is the *transformer* of the absorbing method (`localAbsorbable_transformer`): applying it
twice, once to the 6-cycle `C` and once to any other 6-cycle `C'` on the *same six vertices*, the
double cone `R` transforms `C` into `C'`. Hence a reserved family absorbing some rewiring `C'` of
`C` (for instance one whose alternating triple spans a triangle of `G`, absorbed by the
subdivided-triangle gadget `HexValid.localAbsorbable`) can be enlarged by `R ∪ C'` so as to absorb
`C` itself. A single apex would not do: the cone over a 6-cycle has odd degrees. -/
theorem triDecomposable_doubleCone (G : SimpleGraph V) [DecidableRel G.Adj]
    {a x b z c y w u : V}
    (hnd : ([a, x, b, z, c, y, w, u] : List V).Nodup)
    (h1 : G.IsNClique 3 ({w, a, x} : Finset V)) (h2 : G.IsNClique 3 ({w, b, z} : Finset V))
    (h3 : G.IsNClique 3 ({w, c, y} : Finset V)) (h4 : G.IsNClique 3 ({u, x, b} : Finset V))
    (h5 : G.IsNClique 3 ({u, z, c} : Finset V)) (h6 : G.IsNClique 3 ({u, y, a} : Finset V)) :
    TriDecomposable G (doubleConeEdges a x b z c y w u ∪ sixCycleEdges a x b z c y) := by
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, not_or,
    or_false, and_true, not_false_eq_true] at hnd'
  obtain ⟨⟨hax, hab, haz, hac, hay, haw, hau⟩, ⟨hxb, hxz, hxc, hxy, hxw, hxu⟩,
    ⟨hbz, hbc, hby, hbw, hbu⟩, ⟨hzc, hzy, hzw, hzu⟩, ⟨hcy, hcw, hcu⟩, ⟨hyw, hyu⟩, hwu⟩ := hnd'
  refine ⟨{{w, a, x}, {w, b, z}, {w, c, y}, {u, x, b}, {u, z, c}, {u, y, a}}, ?_, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl|rfl|rfl|rfl|rfl|rfl
    exacts [h1, h2, h3, h4, h5, h6]
  · intro t₁ ht₁ t₂ ht₂ hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht₁ ht₂
    rcases ht₁ with rfl|rfl|rfl|rfl|rfl|rfl <;> rcases ht₂ with rfl|rfl|rfl|rfl|rfl|rfl <;>
      first
        | exact absurd rfl hne
        | (refine triEdges_disjoint_of_card_inter_le_one ?_
           rw [Finset.card_le_one]
           intro p hp q hq
           simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hp hq
           obtain ⟨hp1, hp2⟩ := hp
           obtain ⟨hq1, hq2⟩ := hq
           rcases hp1 with rfl|rfl|rfl <;> rcases hq1 with rfl|rfl|rfl <;> simp_all [eq_comm])
  · rw [coveredEdges]
    simp only [Finset.biUnion_insert, Finset.singleton_biUnion,
      triEdges_triple (Ne.symm haw) (Ne.symm hxw) hax,
      triEdges_triple (Ne.symm hbw) (Ne.symm hzw) hbz,
      triEdges_triple (Ne.symm hcw) (Ne.symm hyw) hcy,
      triEdges_triple (Ne.symm hxu) (Ne.symm hbu) hxb,
      triEdges_triple (Ne.symm hzu) (Ne.symm hcu) hzc,
      triEdges_triple (Ne.symm hyu) (Ne.symm hau) (Ne.symm hay)]
    ext e
    simp only [doubleConeEdges, sixCycleEdges, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton]
    tauto

omit [Fintype V] in
/-- **Absorbing a 6-cycle by transforming it into an absorbable one.** If the reserved family `B`
absorbs the 6-cycle `C' = a'-x'-b'-z'-c'-y'` and `C = a-x-b-z-c-y` spans the same six vertices
(`hsame`, phrased as equality of the two double cones), then `B` enlarged by the double cone and
by `C'` absorbs `C`. Instance of `localAbsorbable_transformer` with the transformer
`triDecomposable_doubleCone` applied to both cycles. -/
theorem localAbsorbable_sixCycle_of_doubleCone (G : SimpleGraph V) [DecidableRel G.Adj]
    {a x b z c y a' x' b' z' c' y' w u : V} {B : Finset (Finset V)}
    (hB : ∀ t ∈ B, G.IsNClique 3 t) (hBd : EdgeDisjoint B)
    (habs : LocalAbsorbable G B (sixCycleEdges a' x' b' z' c' y'))
    (hnd : ([a, x, b, z, c, y, w, u] : List V).Nodup)
    (hnd' : ([a', x', b', z', c', y', w, u] : List V).Nodup)
    (hsame : doubleConeEdges a' x' b' z' c' y' w u = doubleConeEdges a x b z c y w u)
    (h1 : G.IsNClique 3 ({w, a, x} : Finset V)) (h2 : G.IsNClique 3 ({w, b, z} : Finset V))
    (h3 : G.IsNClique 3 ({w, c, y} : Finset V)) (h4 : G.IsNClique 3 ({u, x, b} : Finset V))
    (h5 : G.IsNClique 3 ({u, z, c} : Finset V)) (h6 : G.IsNClique 3 ({u, y, a} : Finset V))
    (h1' : G.IsNClique 3 ({w, a', x'} : Finset V)) (h2' : G.IsNClique 3 ({w, b', z'} : Finset V))
    (h3' : G.IsNClique 3 ({w, c', y'} : Finset V)) (h4' : G.IsNClique 3 ({u, x', b'} : Finset V))
    (h5' : G.IsNClique 3 ({u, z', c'} : Finset V)) (h6' : G.IsNClique 3 ({u, y', a'} : Finset V))
    (hd1 : Disjoint (coveredEdges B ∪ sixCycleEdges a' x' b' z' c' y')
      (doubleConeEdges a x b z c y w u ∪ sixCycleEdges a x b z c y))
    (hd2 : Disjoint (coveredEdges B)
      (doubleConeEdges a x b z c y w u ∪ sixCycleEdges a' x' b' z' c' y')) :
    ∃ B' : Finset (Finset V), (∀ t ∈ B', G.IsNClique 3 t) ∧ EdgeDisjoint B' ∧
      coveredEdges B' = coveredEdges B ∪
        (doubleConeEdges a x b z c y w u ∪ sixCycleEdges a' x' b' z' c' y') ∧
      LocalAbsorbable G B' (sixCycleEdges a x b z c y) := by
  refine localAbsorbable_transformer G hB hBd habs
    (triDecomposable_doubleCone G hnd h1 h2 h3 h4 h5 h6) ?_ hd1 hd2
  have hcone := triDecomposable_doubleCone G hnd' h1' h2' h3' h4' h5' h6'
  rwa [hsame] at hcone

/-! ### Splitting a leftover into chunks -/


/-- **A chunked absorption of the leftover `L` by the reserved family `B`**: a partition of `B`
into parts and of `L` into configs, one config per part, with pairwise disjoint spans, each part
absorbing its own config. This is the shape in which an absorbing core is actually built. -/
def ChunkSplit (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset (Finset V)) (L : Finset (Sym2 V)) : Prop :=
  ∃ (K : Finset ℕ) (part : ℕ → Finset (Finset V)) (S : ℕ → Finset (Sym2 V)),
    K.biUnion part = B ∧ K.biUnion S = L ∧
    (∀ k ∈ K, LocalAbsorbable G (part k) (S k)) ∧
    (∀ k ∈ K, ∀ l ∈ K, k ≠ l →
      Disjoint (coveredEdges (part k) ∪ S k) (coveredEdges (part l) ∪ S l))

/-- A chunked absorption is an absorption. -/
theorem localAbsorbable_of_chunkSplit (G : SimpleGraph V) [DecidableRel G.Adj]
    {B : Finset (Finset V)} {L : Finset (Sym2 V)} (h : ChunkSplit G B L) :
    LocalAbsorbable G B L := by
  obtain ⟨K, part, S, hB, hL, hloc, hdisj⟩ := h
  have := localAbsorbable_biUnion G K part S hloc hdisj
  rwa [hB, hL] at this

omit [Fintype V] in
/-- Conversely, an absorption is (trivially) a one-chunk chunked absorption: the two notions
are equivalent, so nothing is lost by building absorbing cores chunkwise. -/
theorem chunkSplit_of_localAbsorbable (G : SimpleGraph V) [DecidableRel G.Adj]
    {B : Finset (Finset V)} {L : Finset (Sym2 V)} (h : LocalAbsorbable G B L) :
    ChunkSplit G B L := by
  refine ⟨{0}, fun _ => B, fun _ => L, by simp, by simp, ?_, ?_⟩
  · intro k _; exact h
  · intro k hk l hl hkl
    simp only [Finset.mem_singleton] at hk hl
    omega

/-! ### Reservation book-keeping: vertex load and the residual degree -/

/-- Every `G`-neighbour of `v` is either still a neighbour in the residual graph, or lies in one
of the reserved triangles through `v`. -/
theorem residual_neighborFinset_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset (Finset V)) (v : V) :
    G.neighborFinset v ⊆ (residual G B).neighborFinset v ∪
      (B.filter (fun t => v ∈ t)).biUnion (fun t => t.erase v) := by
  classical
  intro u hu
  rw [SimpleGraph.mem_neighborFinset] at hu
  by_cases hcov : s(v, u) ∈ coveredEdges B
  · refine Finset.mem_union_right _ ?_
    simp only [coveredEdges, Finset.mem_biUnion, Finset.mem_filter] at hcov ⊢
    obtain ⟨t, ht, hte⟩ := hcov
    simp only [triEdges, Finset.mem_filter, Finset.mem_sym2_iff] at hte
    exact ⟨t, ⟨ht, hte.1 v (by simp)⟩, Finset.mem_erase.mpr ⟨hu.ne', hte.1 u (by simp)⟩⟩
  · refine Finset.mem_union_left _ ?_
    rw [SimpleGraph.mem_neighborFinset]
    refine ⟨hu, ?_⟩
    rintro ⟨h, -⟩
    exact hcov (by simpa using h)

/-- **The degree lost to a reserved family is at most twice the vertex load.** Each reserved
triangle through `v` destroys at most the two edges of that triangle at `v`. -/
theorem degree_le_residual_degree_add_load (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset (Finset V)) (hB : ∀ t ∈ B, t.card ≤ 3) (v : V) :
    G.degree v ≤ (residual G B).degree v + 2 * (B.filter (fun t => v ∈ t)).card := by
  classical
  have h1 := Finset.card_le_card (residual_neighborFinset_subset G B v)
  have h2 := Finset.card_union_le ((residual G B).neighborFinset v)
    ((B.filter (fun t => v ∈ t)).biUnion (fun t => t.erase v))
  have h3 : ((B.filter (fun t => v ∈ t)).biUnion (fun t => t.erase v)).card
      ≤ ∑ t ∈ B.filter (fun t => v ∈ t), (t.erase v).card := Finset.card_biUnion_le
  have h4 : ∑ t ∈ B.filter (fun t => v ∈ t), (t.erase v).card
      ≤ ∑ _t ∈ B.filter (fun t => v ∈ t), 2 := by
    refine Finset.sum_le_sum ?_
    intro t ht
    rw [Finset.mem_filter] at ht
    have hcard := hB t ht.1
    have herase : (t.erase v).card = t.card - 1 := Finset.card_erase_of_mem ht.2
    have hpos : 1 ≤ t.card := Finset.card_pos.mpr ⟨v, ht.2⟩
    omega
  simp only [Finset.sum_const, smul_eq_mul] at h4
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h2
  omega

/-- **The reservation budget.** If every vertex carries at most `ε n / 2` reserved triangles,
then a graph with `δ(G) ≥ (9/10 + ε) n` still has residual min degree `≥ 9n/10` — the condition
required by `ReservedSplitExists` / `AbsorbingCoreExists`. -/
theorem residual_degree_bound_of_load (G : SimpleGraph V) [DecidableRel G.Adj] {ε : ℝ}
    (B : Finset (Finset V)) (hB : ∀ t ∈ B, G.IsNClique 3 t)
    (hδ : (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ))
    (hload : ∀ v : V, (20 * (B.filter (fun t => v ∈ t)).card : ℝ)
      ≤ 10 * ε * (Fintype.card V : ℝ)) (v : V) :
    9 * Fintype.card V ≤ 10 * (residual G B).degree v := by
  classical
  set n : ℕ := Fintype.card V
  set ℓ : ℕ := (B.filter (fun t => v ∈ t)).card with hℓ
  have hcard : ∀ t ∈ B, t.card ≤ 3 := fun t ht => le_of_eq (hB t ht).card_eq
  have hdeg : G.degree v ≤ (residual G B).degree v + 2 * ℓ :=
    degree_le_residual_degree_add_load G B hcard v
  have hmin : (G.minDegree : ℝ) ≤ (G.degree v : ℝ) := by
    exact_mod_cast Nat.cast_le.mpr (G.minDegree_le_degree v)
  -- real inequality: 9 n + 20 ℓ ≤ 10 deg ≤ 10 res + 20 ℓ
  have key : (9 * n : ℝ) ≤ 10 * ((residual G B).degree v : ℝ) := by
    have h1 : (9 * n : ℝ) + 10 * ε * n ≤ 10 * (G.degree v : ℝ) := by
      have := hδ.trans hmin
      nlinarith [this]
    have h2 : (20 * ℓ : ℝ) ≤ 10 * ε * n := hload v
    have h3 : (G.degree v : ℝ) ≤ ((residual G B).degree v : ℝ) + 2 * ℓ := by
      exact_mod_cast Nat.cast_le.mpr hdeg
    linarith
  exact_mod_cast (by exact_mod_cast key : ((9 * n : ℕ) : ℝ) ≤ ((10 * (residual G B).degree v : ℕ) : ℝ))

/-! ### Greedy reservation -/

open scoped Classical in
/-- **Greedy reservation.** For every budget `m` there is an edge-disjoint family of `G`-triangles
with vertex load at most `m` that cannot be extended: any `G`-triangle avoiding its reserved edges
has a vertex whose load is already `m`. (Take a family of maximum size among the load-bounded
edge-disjoint ones.) -/
theorem exists_maximal_bounded_triangle_family (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) :
    ∃ B : Finset (Finset V), (∀ t ∈ B, G.IsNClique 3 t) ∧ EdgeDisjoint B ∧
      (∀ v : V, (B.filter (fun t => v ∈ t)).card ≤ m) ∧
      ∀ t : Finset V, G.IsNClique 3 t → Disjoint (triEdges t) (coveredEdges B) →
        ∃ v ∈ t, m ≤ (B.filter (fun u => v ∈ u)).card := by
  classical
  set Good : Finset (Finset V) → Prop := fun B =>
    (∀ t ∈ B, G.IsNClique 3 t) ∧ EdgeDisjoint B ∧ ∀ v : V, (B.filter (fun t => v ∈ t)).card ≤ m
    with hGood
  have hne : ((Finset.univ : Finset (Finset (Finset V))).filter Good).Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hGood]
    exact ⟨by simp, by simp [EdgeDisjoint], by simp⟩
  obtain ⟨B, hBmem, hBmax⟩ :=
    Finset.exists_max_image ((Finset.univ : Finset (Finset (Finset V))).filter Good)
      Finset.card hne
  rw [Finset.mem_filter] at hBmem
  obtain ⟨-, hcl, hd, hload⟩ := hBmem
  refine ⟨B, hcl, hd, hload, ?_⟩
  intro t ht hdisj
  by_contra hcon
  push_neg at hcon
  have htB : t ∉ B := by
    intro htB
    have hsub : triEdges t ⊆ coveredEdges B := Finset.subset_biUnion_of_mem triEdges htB
    have h3 : (triEdges t).card = 3 := triEdges_card_of_isNClique G ht
    have hself : triEdges t = ∅ := by
      simpa using Finset.disjoint_of_subset_right hsub hdisj
    rw [hself] at h3
    simp at h3
  have hgood : Good (insert t B) := by
    refine ⟨?_, ?_, ?_⟩
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      exacts [ht, hcl u hu]
    · intro t₁ h₁ t₂ h₂ hne'
      have key : ∀ u ∈ B, Disjoint (triEdges t) (triEdges u) := fun u hu =>
        Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem triEdges hu) hdisj
      rcases Finset.mem_insert.mp h₁ with rfl | h₁'
      · rcases Finset.mem_insert.mp h₂ with rfl | h₂'
        · exact absurd rfl hne'
        · exact key _ h₂'
      · rcases Finset.mem_insert.mp h₂ with rfl | h₂'
        · exact (key _ h₁').symm
        · exact hd _ h₁' _ h₂' hne'
    · intro v
      by_cases hv : v ∈ t
      · have hlt := hcon v hv
        rw [Finset.filter_insert, if_pos hv, Finset.card_insert_of_notMem (by
          simp [htB, Finset.mem_filter])]
        omega
      · rw [Finset.filter_insert, if_neg hv]
        exact hload v
  have hle := hBmax (insert t B) (by simp [Finset.mem_filter, hgood])
  rw [Finset.card_insert_of_notMem htB] at hle
  omega

/-! ### The kernel with the reservation book-keeping discharged -/

/-- **The absorbing-core kernel with a local reservation budget.** Same as
`AbsorbingCoreExists`, except that the global residual min-degree requirement is replaced by the
local condition that no vertex carries more than `ε n / 2` reserved triangles — which is what a
construction actually controls. By `absorbingCoreExists_of_bounded` this implies
`AbsorbingCoreExists ε`, hence `ReservedSplitExists ε`. -/
def BoundedAbsorbingCoreExists (ε : ℝ) : Prop :=
  ∃ (n₀ : ℕ) (β₀ : ℝ), 0 < β₀ ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ),
      n₀ ≤ Fintype.card V → 0 < β → β ≤ β₀ →
      (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
      ∃ B : Finset (Finset V), (∀ t ∈ B, G.IsNClique 3 t) ∧ EdgeDisjoint B ∧
        (∀ v : V, (20 * (B.filter (fun t => v ∈ t)).card : ℝ)
          ≤ 10 * ε * (Fintype.card V : ℝ)) ∧
        ∀ L : Finset (Sym2 V), L ⊆ G.edgeFinset → Disjoint L (coveredEdges B) →
          (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 → 3 ∣ L.card →
          (∀ v : V, Even ((L.filter (fun e => v ∈ e)).card)) → LocalAbsorbable G B L

/-- **Reduction (sorry-free): a load-bounded absorbing core is an absorbing core.** The residual
min-degree condition follows from the reservation budget by
`residual_degree_bound_of_load`. -/
theorem absorbingCoreExists_of_bounded (ε : ℝ) (h : BoundedAbsorbingCoreExists ε) :
    AbsorbingCoreExists ε := by
  obtain ⟨n₀, β₀, hβ₀, H⟩ := h
  refine ⟨n₀, β₀, hβ₀, ?_⟩
  intro V _ _ G _ β hn hβpos hβ hδ
  obtain ⟨B, hcl, hd, hload, habs⟩ := H G β hn hβpos hβ hδ
  exact ⟨B, hcl, hd, residual_degree_bound_of_load G B hcl hδ hload, habs⟩

/-- **The converse of `reservedSplitExists_of_absorbingCore`: a reserved split gives a single
absorbing core.** Take `B = ⋃_{i∈I} base i`; a splitting `L = ⋃_{i∈J} f i` is absorbed unit by
unit (`localAbsorbable_biUnion`), the unused units absorbing the empty config. Hence the
single-core kernel is *equivalent* to `ReservedSplitExists`, not a strengthening of it, so
nothing is lost by attacking the kernel in absorbing-core form. -/
theorem absorbingCoreExists_of_reservedSplit (ε : ℝ) (h : ReservedSplitExists ε) :
    AbsorbingCoreExists ε := by
  classical
  obtain ⟨n₀, β₀, hβ₀, H⟩ := h
  refine ⟨n₀, β₀, hβ₀, ?_⟩
  intro V _ _ G _ β hn hβpos hβ hδ
  obtain ⟨I, base, hcl, hdisj, hcross, hdeg, hsplit⟩ := H G β hn hβpos hβ hδ
  refine ⟨I.biUnion base, ?_, ?_, hdeg, ?_⟩
  · intro t ht
    obtain ⟨i, hi, hti⟩ := Finset.mem_biUnion.mp ht
    exact hcl i hi t hti
  · intro t₁ h₁ t₂ h₂ hne
    obtain ⟨i, hi, ht₁⟩ := Finset.mem_biUnion.mp h₁
    obtain ⟨j, hj, ht₂⟩ := Finset.mem_biUnion.mp h₂
    by_cases hij : i = j
    · subst hij; exact hdisj i hi t₁ ht₁ t₂ ht₂ hne
    · exact Finset.disjoint_of_subset_left (Finset.subset_biUnion_of_mem triEdges ht₁)
        (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem triEdges ht₂)
          (hcross i hi j hj hij))
  · intro L hLsub hLdisj hLcard hLdiv hLeven
    obtain ⟨J, f, hJI, hf, hfd, hfL⟩ := hsplit L hLsub hLdisj hLcard hLdiv hLeven
    set g : ℕ → Finset (Sym2 V) := fun i => if i ∈ J then f i else ∅ with hg
    have hgsub : ∀ i, g i ⊆ L := by
      intro i
      by_cases hi : i ∈ J
      · simp only [hg, if_pos hi, ← hfL]
        exact Finset.subset_biUnion_of_mem f hi
      · simp [hg, hi]
    have hIg : I.biUnion g = L := by
      rw [← hfL]
      apply Finset.Subset.antisymm
      · intro e he
        obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
        by_cases hiJ : i ∈ J
        · exact Finset.mem_biUnion.mpr ⟨i, hiJ, by simpa [hg, hiJ] using hei⟩
        · simp [hg, hiJ] at hei
      · intro e he
        obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
        exact Finset.mem_biUnion.mpr ⟨i, hJI hi, by simpa [hg, hi] using hei⟩
    have key := localAbsorbable_biUnion G I base g ?_ ?_
    · rwa [hIg] at key
    · intro i hi
      by_cases hiJ : i ∈ J
      · simpa [hg, hiJ] using hf i hiJ
      · simpa [hg, hiJ] using localAbsorbable_empty G (hcl i hi) (hdisj i hi)
    · intro i hi j hj hij
      have hcovij := hcross i hi j hj hij
      have hgi : Disjoint (g i) (coveredEdges (I.biUnion base)) :=
        Finset.disjoint_of_subset_left (hgsub i) hLdisj
      have hgj : Disjoint (g j) (coveredEdges (I.biUnion base)) :=
        Finset.disjoint_of_subset_left (hgsub j) hLdisj
      have hsubi : coveredEdges (base i) ⊆ coveredEdges (I.biUnion base) := by
        rw [coveredEdges_biUnion]
        exact Finset.subset_biUnion_of_mem (fun k => coveredEdges (base k)) hi
      have hsubj : coveredEdges (base j) ⊆ coveredEdges (I.biUnion base) := by
        rw [coveredEdges_biUnion]
        exact Finset.subset_biUnion_of_mem (fun k => coveredEdges (base k)) hj
      have hgij : Disjoint (g i) (g j) := by
        by_cases hiJ : i ∈ J
        · by_cases hjJ : j ∈ J
          · simpa [hg, hiJ, hjJ] using hfd i hiJ j hjJ hij
          · simp [hg, hjJ]
        · simp [hg, hiJ]
      rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
      exact ⟨⟨hcovij, (Finset.disjoint_of_subset_right hsubi hgj).symm⟩,
        ⟨Finset.disjoint_of_subset_right hsubj hgi, hgij⟩⟩

/-- **The kernel in absorbing-core form is exactly the kernel.** -/
theorem absorbingCoreExists_iff_reservedSplitExists (ε : ℝ) :
    AbsorbingCoreExists ε ↔ ReservedSplitExists ε :=
  ⟨reservedSplitExists_of_absorbingCore ε, absorbingCoreExists_of_reservedSplit ε⟩

end Ax2.BKLO
