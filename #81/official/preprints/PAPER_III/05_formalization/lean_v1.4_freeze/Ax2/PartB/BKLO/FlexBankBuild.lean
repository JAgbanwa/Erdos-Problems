/-
  Part B (Phase 2) — building flexible transformer banks, and the reduction of `FlexBankExists`
  to the smallest remaining existence statement.

  This file sits between `FlexBank.lean` (the corrected interface + `absorber_of_flexBank`) and
  `TransformerAbsorberTry.lean` (the B2/B3 target).  It contains:

  * `transformer_gadget_switch` — the concrete 6-edge switch (moved here from
    `TransformerAbsorberTry.lean`, same statement and fully qualified name), used as the local
    unit brick for flexible configs.
  * `LocalAbsorbable G B S` — "the reserved triangle family `B` can be re-decomposed so as to
    additionally cover exactly the config `S`".  This is the *tautological* config family of a
    unit, hence the most permissive `cfg` a `FlexBank` unit can have.
  * `localAbsorbable_subdividedTriangle` — the transformer gadget as a `LocalAbsorbable` fact: a
    single reserved triangle `abc` absorbs the subdivided triangle (6-cycle) `a-x-b-z-c-y` for
    ANY admissible midpoints `x, y, z`.  Together with `localAbsorbable_adj` (the adjacency form)
    this is the flexible unit the rigid interface could not provide.
  * `localAbsorbable_triangle`, `localAbsorbable_union` — the two closure properties of the
    config family (absorb a fresh triangle; absorb a disjoint union of configs).
  * `flexBankOfBases` — a `FlexBank` from any family of reserved, pairwise edge-disjoint triangle
    families, with the tautological `cfg`.
  * `exists_subdividedTriangle_config` — in the dense regime a reserved triangle always has a
    free subdivided-triangle config available, avoiding any prescribed small vertex set.
  * `localAbsorbable_card_dvd_three`, `localAbsorbable_degrees_even` — every config is itself
    triangle-divisible (the constraint that rules out bounded-size chunk families).
  * `ReservedSplitExists ε` — the remaining research kernel, and
    `flexBankExists_of_reservedSplit : ReservedSplitExists ε → FlexBankExists ε` (sorry-free);
    `AbsorbingCoreExists ε` with `reservedSplitExists_of_absorbingCore` is the classical
    single-absorber sufficient condition for it.
  * `hexConfig_absorbable_not_decomposable` — non-vacuity: the units absorb configs that carry no
    triangle at all.
-/
import Ax2.PartB.BKLO.FlexBank
import Ax2.PartB.BKLO.BankElim

namespace Ax2.BKLO

open SimpleGraph Finset Ax2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The transformer gadget -/

omit [Fintype V] in
/-- **The transformer gadget — the switch identity (design validation).** On 6 distinct vertices, the
default packing `B = {abc}` and the switched packing `Ab = {abx, acy, bcz}` satisfy
`coveredEdges (Ab) = coveredEdges (B) ∪ S` with the NONEMPTY switch-set
`S = {ax, bx, ay, cy, bz, cz}` (6 edges, `≡ 0 mod 3`). This is the concrete transformer the octahedron
(`S = ∅`) could not provide: `Ab` re-triangulates `abc`'s scaffold and picks up 6 extra edges. -/
theorem transformer_gadget_switch {a b c x y z : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hax : a ≠ x) (hbx : b ≠ x) (hcx : c ≠ x)
    (hay : a ≠ y) (hby : b ≠ y) (hcy : c ≠ y) (hxy : x ≠ y)
    (haz : a ≠ z) (hbz : b ≠ z) (hcz : c ≠ z) (hxz : x ≠ z) (hyz : y ≠ z) :
    coveredEdges ({{a, b, x}, {a, c, y}, {b, c, z}} : Finset (Finset V))
      = coveredEdges ({{a, b, c}} : Finset (Finset V))
        ∪ ({s(a, x), s(b, x), s(a, y), s(c, y), s(b, z), s(c, z)} : Finset (Sym2 V)) := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u w =>
    simp only [coveredEdges, triEdges, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_filter, Finset.mem_sym2_iff, Sym2.mk_isDiag_iff, Finset.mem_union, Sym2.eq_iff]
    aesop

/-! ### Locally absorbable configs -/

/-- The **config family of a reserved triangle family**: `B` can locally absorb `S` when the
reserved edges together with `S` carry an edge-disjoint decomposition into `G`-triangles. This is
the most permissive `cfg` a flexible-bank unit can have; every unit's `cfg` is contained in it
(`absorb_cov`). -/
def LocalAbsorbable (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset (Finset V)) (S : Finset (Sym2 V)) : Prop :=
  ∃ P : Finset (Finset V), (∀ t ∈ P, G.IsNClique 3 t) ∧ EdgeDisjoint P ∧
    coveredEdges P = coveredEdges B ∪ S

omit [Fintype V] in
/-- Two triangles sharing exactly one vertex have disjoint edge sets. -/
theorem triEdges_disjoint_of_share_one {p q r s t : V}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hpt : p ≠ t)
    (hqs : q ≠ s) (hqt : q ≠ t) (hrs : r ≠ s) (hrt : r ≠ t) :
    Disjoint (triEdges ({p, q, r} : Finset V)) (triEdges ({p, s, t} : Finset V)) := by
  refine Finset.disjoint_left.mpr ?_
  intro e he he'
  revert he he'
  induction e using Sym2.inductionOn with
  | _ u w =>
    simp only [triEdges, Finset.mem_filter, Finset.mem_sym2_iff, Finset.mem_insert,
      Finset.mem_singleton, Sym2.mk_isDiag_iff]
    aesop

omit [Fintype V] in
/-- The switched packing `{abx, acy, bcz}` of the transformer gadget is edge-disjoint: its three
triangles pairwise share exactly one vertex (`a`, `b` and `c` respectively). -/
theorem edgeDisjoint_switchPacking {a b c x y z : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hax : a ≠ x) (hbx : b ≠ x) (hcx : c ≠ x)
    (hay : a ≠ y) (hby : b ≠ y) (hcy : c ≠ y) (hxy : x ≠ y)
    (haz : a ≠ z) (hbz : b ≠ z) (hcz : c ≠ z) (hxz : x ≠ z) (hyz : y ≠ z) :
    EdgeDisjoint ({{a, b, x}, {a, c, y}, {b, c, z}} : Finset (Finset V)) := by
  have d12 : Disjoint (triEdges ({a, b, x} : Finset V)) (triEdges ({a, c, y} : Finset V)) :=
    triEdges_disjoint_of_share_one hab hax hac hay hbc hby hcx.symm hxy
  have d13 : Disjoint (triEdges ({a, b, x} : Finset V)) (triEdges ({b, c, z} : Finset V)) := by
    rw [Finset.insert_comm]
    exact triEdges_disjoint_of_share_one hab.symm hbx hbc hbz hac haz hcx.symm hxz
  have d23 : Disjoint (triEdges ({a, c, y} : Finset V)) (triEdges ({b, c, z} : Finset V)) := by
    rw [Finset.insert_comm, Finset.insert_comm b c]
    exact triEdges_disjoint_of_share_one hac.symm hcy hbc.symm hcz hab haz hby.symm hyz
  intro t₁ ht₁ t₂ ht₂ hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht₁ ht₂
  rcases ht₁ with rfl | rfl | rfl <;> rcases ht₂ with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hne
      | exact d12 | exact d13 | exact d23
      | exact d12.symm | exact d13.symm | exact d23.symm

omit [Fintype V] in
/-- **The subdivided triangle is a flexible config.** A single reserved triangle `{a,b,c}`
absorbs the 6-cycle `a-x-b-z-c-y` for any midpoints `x, y, z` making `abx`, `acy`, `bcz`
triangles of `G`. Proof: the switched packing `{abx, acy, bcz}` and `transformer_gadget_switch`. -/
theorem localAbsorbable_subdividedTriangle (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b c x y z : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hax : a ≠ x) (hbx : b ≠ x) (hcx : c ≠ x)
    (hay : a ≠ y) (hby : b ≠ y) (hcy : c ≠ y) (hxy : x ≠ y)
    (haz : a ≠ z) (hbz : b ≠ z) (hcz : c ≠ z) (hxz : x ≠ z) (hyz : y ≠ z)
    (h1 : G.IsNClique 3 ({a, b, x} : Finset V)) (h2 : G.IsNClique 3 ({a, c, y} : Finset V))
    (h3 : G.IsNClique 3 ({b, c, z} : Finset V)) :
    LocalAbsorbable G ({{a, b, c}} : Finset (Finset V))
      ({s(a, x), s(b, x), s(a, y), s(c, y), s(b, z), s(c, z)} : Finset (Sym2 V)) := by
  have hcl : ∀ t ∈ ({{a, b, x}, {a, c, y}, {b, c, z}} : Finset (Finset V)), G.IsNClique 3 t := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    exacts [h1, h2, h3]
  exact ⟨_, hcl,
    edgeDisjoint_switchPacking hab hac hbc hax hbx hcx hay hby hcy hxy haz hbz hcz hxz hyz,
    transformer_gadget_switch hab hac hbc hax hbx hcx hay hby hcy hxy haz hbz hcz hxz hyz⟩

omit [Fintype V] in
/-- **Adjacency form of the gadget.** If `x` is a common neighbour of `a, b`, `y` of `a, c` and
`z` of `b, c`, and all six vertices are distinct, then the reserved triangle `{a,b,c}` absorbs the
subdivided triangle `a-x-b-z-c-y`. -/
theorem localAbsorbable_adj (G : SimpleGraph V) [DecidableRel G.Adj] {a b c x y z : V}
    (hax : a ≠ x) (hbx : b ≠ x) (hcx : c ≠ x)
    (hay : a ≠ y) (hby : b ≠ y) (hcy : c ≠ y) (hxy : x ≠ y)
    (haz : a ≠ z) (hbz : b ≠ z) (hcz : c ≠ z) (hxz : x ≠ z) (hyz : y ≠ z)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hya : G.Adj y a) (hyc : G.Adj y c)
    (hzb : G.Adj z b) (hzc : G.Adj z c) :
    LocalAbsorbable G ({{a, b, c}} : Finset (Finset V))
      ({s(a, x), s(b, x), s(a, y), s(c, y), s(b, z), s(c, z)} : Finset (Sym2 V)) :=
  localAbsorbable_subdividedTriangle G hab.ne hac.ne hbc.ne hax hbx hcx hay hby hcy hxy
    haz hbz hcz hxz hyz
    (SimpleGraph.is3Clique_triple_iff.2 ⟨hab, hxa.symm, hxb.symm⟩)
    (SimpleGraph.is3Clique_triple_iff.2 ⟨hac, hya.symm, hyc.symm⟩)
    (SimpleGraph.is3Clique_triple_iff.2 ⟨hbc, hzb.symm, hzc.symm⟩)

/-- **Gadget availability in a dense graph.** Let `abc` be a triangle of `G` and let `F` be any
set of vertices to be avoided (e.g. the vertices already used by other chunks). If every pair of
vertices has degree sum exceeding `n + |F| + 5`, then midpoints `x, y, z ∉ F` can be chosen so
that the reserved triangle `abc` absorbs the subdivided triangle `a-x-b-z-c-y`. So the flexible
unit is not just formally flexible: in the dense regime it always has a free config available. -/
theorem exists_subdividedTriangle_config (G : SimpleGraph V) [DecidableRel G.Adj] {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) (F : Finset V)
    (hF : ∀ u w : V, Fintype.card V + (F.card + 5) < G.degree u + G.degree w) :
    ∃ x y z : V, x ∉ F ∧ y ∉ F ∧ z ∉ F ∧
      LocalAbsorbable G ({{a, b, c}} : Finset (Finset V))
        ({s(a, x), s(b, x), s(a, y), s(c, y), s(b, z), s(c, z)} : Finset (Sym2 V)) := by
  classical
  have pick : ∀ (u w : V) (E : Finset V), E.card ≤ F.card + 5 →
      ∃ p, p ∉ E ∧ G.Adj u p ∧ G.Adj w p := by
    intro u w E hE
    have h1 := card_common_neighbors_ge G u w
    have h2 := hF u w
    have h3 : ¬ ((G.neighborFinset u ∩ G.neighborFinset w) ⊆ E) := by
      intro hsub
      have := Finset.card_le_card hsub
      omega
    obtain ⟨p, hp, hpE⟩ := Finset.not_subset.mp h3
    rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at hp
    exact ⟨p, hpE, hp.1, hp.2⟩
  have cins : ∀ (p : V) (E : Finset V), (insert p E).card ≤ E.card + 1 := fun p E =>
    Finset.card_insert_le p E
  obtain ⟨x, hx, hax, hbx⟩ := pick a b (insert a (insert b (insert c F)))
    (by have := cins a (insert b (insert c F)); have := cins b (insert c F)
        have := cins c F; omega)
  obtain ⟨y, hy, hay, hcy⟩ := pick a c (insert a (insert b (insert c (insert x F))))
    (by have := cins a (insert b (insert c (insert x F)))
        have := cins b (insert c (insert x F)); have := cins c (insert x F)
        have := cins x F; omega)
  obtain ⟨z, hz, hbz, hcz⟩ := pick b c (insert a (insert b (insert c (insert x (insert y F)))))
    (by have := cins a (insert b (insert c (insert x (insert y F))))
        have := cins b (insert c (insert x (insert y F)))
        have := cins c (insert x (insert y F)); have := cins x (insert y F)
        have := cins y F; omega)
  simp only [Finset.mem_insert, not_or] at hx hy hz
  obtain ⟨hxa, hxb, hxc, hxF⟩ := hx
  obtain ⟨hya, hyb, hyc, hyx, hyF⟩ := hy
  obtain ⟨hza, hzb', hzc', hzx, hzy, hzF⟩ := hz
  refine ⟨x, y, z, hxF, hyF, hzF, ?_⟩
  exact localAbsorbable_adj G (Ne.symm hxa) (Ne.symm hxb) (Ne.symm hxc)
    (Ne.symm hya) (Ne.symm hyb) (Ne.symm hyc) (Ne.symm hyx)
    (Ne.symm hza) (Ne.symm hzb') (Ne.symm hzc') (Ne.symm hzx) (Ne.symm hzy)
    hab hac hbc hax.symm hbx.symm hay.symm hcy.symm hbz.symm hcz.symm

omit [Fintype V] in
/-- **A fresh triangle is always a config.** Any reserved family absorbs the edge set of a
`G`-triangle disjoint from its reserved edges (just add the triangle to the packing). -/
theorem localAbsorbable_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    {B : Finset (Finset V)} (hB : ∀ t ∈ B, G.IsNClique 3 t) (hBd : EdgeDisjoint B)
    {t : Finset V} (ht : G.IsNClique 3 t) (hdisj : Disjoint (triEdges t) (coveredEdges B)) :
    LocalAbsorbable G B (triEdges t) := by
  refine ⟨insert t B, ?_, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact ht
    · exact hB u hu
  · intro t₁ h₁ t₂ h₂ hne
    have key : ∀ u ∈ B, Disjoint (triEdges t) (triEdges u) := fun u hu =>
      Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem triEdges hu) hdisj
    rcases Finset.mem_insert.mp h₁ with rfl | h₁'
    · rcases Finset.mem_insert.mp h₂ with rfl | h₂'
      · exact absurd rfl hne
      · exact key _ h₂'
    · rcases Finset.mem_insert.mp h₂ with rfl | h₂'
      · exact (key _ h₁').symm
      · exact hBd _ h₁' _ h₂' hne
  · rw [coveredEdges, Finset.biUnion_insert, Finset.union_comm]
    rfl

omit [Fintype V] in
/-- **Configs compose.** Two reserved families with disjoint spans absorb the union of their
configs. -/
theorem localAbsorbable_union (G : SimpleGraph V) [DecidableRel G.Adj]
    {B₁ B₂ : Finset (Finset V)} {S₁ S₂ : Finset (Sym2 V)}
    (h₁ : LocalAbsorbable G B₁ S₁) (h₂ : LocalAbsorbable G B₂ S₂)
    (hspan : Disjoint (coveredEdges B₁ ∪ S₁) (coveredEdges B₂ ∪ S₂)) :
    LocalAbsorbable G (B₁ ∪ B₂) (S₁ ∪ S₂) := by
  obtain ⟨P₁, hc₁, hd₁, hcov₁⟩ := h₁
  obtain ⟨P₂, hc₂, hd₂, hcov₂⟩ := h₂
  have s₁ : ∀ u ∈ P₁, triEdges u ⊆ coveredEdges B₁ ∪ S₁ := by
    intro u hu
    rw [← hcov₁]
    exact Finset.subset_biUnion_of_mem triEdges hu
  have s₂ : ∀ u ∈ P₂, triEdges u ⊆ coveredEdges B₂ ∪ S₂ := by
    intro u hu
    rw [← hcov₂]
    exact Finset.subset_biUnion_of_mem triEdges hu
  refine ⟨P₁ ∪ P₂, ?_, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_union.mp hu with h | h
    exacts [hc₁ u h, hc₂ u h]
  · intro t₁ ht₁ t₂ ht₂ hne
    rcases Finset.mem_union.mp ht₁ with h₁' | h₁' <;> rcases Finset.mem_union.mp ht₂ with h₂' | h₂'
    · exact hd₁ _ h₁' _ h₂' hne
    · exact Finset.disjoint_of_subset_left (s₁ _ h₁')
        (Finset.disjoint_of_subset_right (s₂ _ h₂') hspan)
    · exact Finset.disjoint_of_subset_left (s₂ _ h₁')
        (Finset.disjoint_of_subset_right (s₁ _ h₂') hspan.symm)
    · exact hd₂ _ h₁' _ h₂' hne
  · have hcovB : coveredEdges (B₁ ∪ B₂) = coveredEdges B₁ ∪ coveredEdges B₂ := by
      simp [coveredEdges, Finset.union_biUnion]
    have hcovP : coveredEdges (P₁ ∪ P₂) = coveredEdges P₁ ∪ coveredEdges P₂ := by
      simp [coveredEdges, Finset.union_biUnion]
    rw [hcovP, hcov₁, hcov₂, hcovB]
    ext e
    simp only [Finset.mem_union]
    tauto

/-! ### Necessary conditions on configs -/

/-- **Every locally absorbable config is `3`-divisible** (specialisation of
`config_card_dvd_three`): a unit can never absorb a chunk whose size is not a multiple of `3`. -/
theorem localAbsorbable_card_dvd_three (G : SimpleGraph V) [DecidableRel G.Adj]
    {B : Finset (Finset V)} {S : Finset (Sym2 V)}
    (hB : ∀ t ∈ B, G.IsNClique 3 t) (hBd : EdgeDisjoint B)
    (h : LocalAbsorbable G B S) (hdisj : Disjoint S (coveredEdges B)) : 3 ∣ S.card := by
  obtain ⟨P, hcl, hd, hcov⟩ := h
  exact config_card_dvd_three G hB hcl hBd hd hcov hdisj

omit [Fintype V] in
/-- **Every locally absorbable config has even degrees** (specialisation of
`config_degrees_even`).  Together with `localAbsorbable_card_dvd_three`: the chunks occurring in
`ReservedSplitExists` are themselves triangle-divisible, which is why a leftover cannot in general
be split into chunks of bounded size. -/
theorem localAbsorbable_degrees_even (G : SimpleGraph V) [DecidableRel G.Adj]
    {B : Finset (Finset V)} {S : Finset (Sym2 V)}
    (hB : ∀ t ∈ B, G.IsNClique 3 t) (hBd : EdgeDisjoint B)
    (h : LocalAbsorbable G B S) (hdisj : Disjoint S (coveredEdges B)) (v : V) :
    Even ((S.filter (fun e => v ∈ e)).card) := by
  obtain ⟨P, hcl, hd, hcov⟩ := h
  exact config_degrees_even G hB hcl hBd hd hcov hdisj v

/-! ### Banks with the tautological config family -/

open scoped Classical in
/-- A `FlexBank` from any family of reserved, pairwise edge-disjoint triangle families, whose
units absorb *every* config their reserved edges can absorb. This is the most permissive bank on
a given reserved core, so `Rich` for it is the weakest possible richness hypothesis. -/
noncomputable def flexBankOfBases (G : SimpleGraph V) [DecidableRel G.Adj]
    (I : Finset ℕ) (base : ℕ → Finset (Finset V))
    (hcl : ∀ i ∈ I, ∀ t ∈ base i, G.IsNClique 3 t)
    (hdisj : ∀ i ∈ I, EdgeDisjoint (base i))
    (hcross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (coveredEdges (base i)) (coveredEdges (base j))) :
    FlexBank G where
  I := I
  base := base
  cfg := fun i S => LocalAbsorbable G (base i) S
  absorb := fun i S => if h : LocalAbsorbable G (base i) S then h.choose else ∅
  base_clique := hcl
  base_disj := hdisj
  base_cross := hcross
  absorb_clique := by
    intro i _ S hS t ht
    rw [dif_pos hS] at ht
    exact hS.choose_spec.1 t ht
  absorb_disj := by
    intro i _ S hS
    rw [dif_pos hS]
    exact hS.choose_spec.2.1
  absorb_cov := by
    intro i _ S hS
    rw [dif_pos hS]
    exact hS.choose_spec.2.2

omit [Fintype V] in
@[simp] theorem flexBankOfBases_core (G : SimpleGraph V) [DecidableRel G.Adj]
    (I : Finset ℕ) (base : ℕ → Finset (Finset V)) (hcl hdisj hcross) :
    (flexBankOfBases G I base hcl hdisj hcross).core = I.biUnion base := rfl

/-! ### The remaining kernel and the reduction -/

/-- **The remaining research kernel of B2/B3, in its smallest form.** For every `ε > 0` there are
thresholds `n₀, β₀ > 0` such that every graph with `n ≥ n₀` and `δ(G) ≥ (9/10+ε)n` carries a
family of reserved, pairwise edge-disjoint triangle families ("units") whose removal leaves min
degree `≥ 9n/10`, and such that every admissible leftover `L` splits into pairwise disjoint
configs, one per unit, each locally absorbable by its unit's reserved edges.

Compared with `FlexBankExists` this drops all the bank bookkeeping (the `FlexBank` structure, the
choice of `absorb`, and the rerouting): what is left is purely the reservation plus the
combinatorial splitting of the leftover into locally absorbable chunks. -/
def ReservedSplitExists (ε : ℝ) : Prop :=
  ∃ (n₀ : ℕ) (β₀ : ℝ), 0 < β₀ ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ),
      n₀ ≤ Fintype.card V → 0 < β → β ≤ β₀ →
      (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
      ∃ (I : Finset ℕ) (base : ℕ → Finset (Finset V)),
        (∀ i ∈ I, ∀ t ∈ base i, G.IsNClique 3 t) ∧
        (∀ i ∈ I, EdgeDisjoint (base i)) ∧
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          Disjoint (coveredEdges (base i)) (coveredEdges (base j))) ∧
        (∀ v, 9 * Fintype.card V ≤ 10 * (residual G (I.biUnion base)).degree v) ∧
        (∀ L : Finset (Sym2 V), L ⊆ G.edgeFinset →
          Disjoint L (coveredEdges (I.biUnion base)) →
          (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 → 3 ∣ L.card →
          (∀ v : V, Even ((L.filter (fun e => v ∈ e)).card)) →
          ∃ (J : Finset ℕ) (f : ℕ → Finset (Sym2 V)), J ⊆ I ∧
            (∀ i ∈ J, LocalAbsorbable G (base i) (f i)) ∧
            (∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (f i) (f j)) ∧ J.biUnion f = L)

/-- **Reduction (sorry-free): reserved units plus a splitting of every admissible leftover give a
rich flexible transformer bank.** -/
theorem flexBankExists_of_reservedSplit (ε : ℝ) (h : ReservedSplitExists ε) :
    FlexBankExists ε := by
  obtain ⟨n₀, β₀, hβ₀, H⟩ := h
  refine ⟨n₀, β₀, hβ₀, ?_⟩
  intro V _ _ G _ β hn hβpos hβ hδ
  obtain ⟨I, base, hcl, hdisj, hcross, hdeg, hsplit⟩ := H G β hn hβpos hβ hδ
  refine ⟨flexBankOfBases G I base hcl hdisj hcross, ?_, hdeg⟩
  intro L hLsub hLdisj hLcard hLdiv hLeven
  exact hsplit L hLsub hLdisj hLcard hLdiv hLeven

/-- The classical **single-absorber** form of the kernel: one reserved edge-disjoint triangle
family whose reserved edges, together with any admissible leftover, carry a triangle
decomposition. It is a (formally stronger) sufficient condition for `ReservedSplitExists`, kept
here because it is the shape in which the absorbing lemma is usually stated. -/
def AbsorbingCoreExists (ε : ℝ) : Prop :=
  ∃ (n₀ : ℕ) (β₀ : ℝ), 0 < β₀ ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ),
      n₀ ≤ Fintype.card V → 0 < β → β ≤ β₀ →
      (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
      ∃ B : Finset (Finset V), (∀ t ∈ B, G.IsNClique 3 t) ∧ EdgeDisjoint B ∧
        (∀ v, 9 * Fintype.card V ≤ 10 * (residual G B).degree v) ∧
        ∀ L : Finset (Sym2 V), L ⊆ G.edgeFinset → Disjoint L (coveredEdges B) →
          (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 → 3 ∣ L.card →
          (∀ v : V, Even ((L.filter (fun e => v ∈ e)).card)) → LocalAbsorbable G B L

/-- A single absorbing core is a (one-unit) reserved split. -/
theorem reservedSplitExists_of_absorbingCore (ε : ℝ) (h : AbsorbingCoreExists ε) :
    ReservedSplitExists ε := by
  obtain ⟨n₀, β₀, hβ₀, H⟩ := h
  refine ⟨n₀, β₀, hβ₀, ?_⟩
  intro V _ _ G _ β hn hβpos hβ hδ
  obtain ⟨B, hcl, hd, hdeg, habs⟩ := H G β hn hβpos hβ hδ
  refine ⟨{0}, fun _ => B, ?_, ?_, ?_, ?_, ?_⟩
  · intro i _ t ht; exact hcl t ht
  · intro i _; exact hd
  · intro i hi j hj hij
    simp only [Finset.mem_singleton] at hi hj
    omega
  · rw [Finset.singleton_biUnion]
    exact hdeg
  · intro L hLsub hLdisj hLcard hLdiv hLeven
    rw [Finset.singleton_biUnion] at hLdisj
    exact ⟨{0}, fun _ => L, Finset.Subset.refl _, fun i _ =>
      habs L hLsub hLdisj hLcard hLdiv hLeven,
      by intro i hi j hj hij; simp only [Finset.mem_singleton] at hi hj; omega,
      by simp [Finset.singleton_biUnion]⟩

/-! ### Non-vacuity of the flexible config family -/

/-- The 6-cycle `0-3-1-5-2-4` inside `K₆`, i.e. the switch-set of the transformer gadget with
`a,b,c = 0,1,2` and midpoints `x,y,z = 3,4,5`. -/
def hexConfig : Finset (Sym2 (Fin 6)) :=
  {s(0, 3), s(1, 3), s(0, 4), s(2, 4), s(1, 5), s(2, 5)}

/-- **The flexible units genuinely absorb configs that are not triangle-decomposable.** In `K₆`
the reserved triangle `{0,1,2}` absorbs `hexConfig`, while `hexConfig` — a 6-cycle — carries no
triangle at all, so it is not the covered-edge set of any triangle family on its own. This is the
exact contrast with the rigid interface (`rigid_bank_hrich_elim`) and with the octahedral flex
unit (whose switch-set is empty). -/
theorem hexConfig_absorbable_not_decomposable :
    LocalAbsorbable (⊤ : SimpleGraph (Fin 6)) ({{0, 1, 2}} : Finset (Finset (Fin 6))) hexConfig ∧
      ¬ ∃ P : Finset (Finset (Fin 6)),
        (∀ t ∈ P, (⊤ : SimpleGraph (Fin 6)).IsNClique 3 t) ∧ coveredEdges P = hexConfig := by
  constructor
  · have h : LocalAbsorbable (⊤ : SimpleGraph (Fin 6))
        ({{(0 : Fin 6), 1, 2}} : Finset (Finset (Fin 6)))
        ({s((0 : Fin 6), 3), s((1 : Fin 6), 3), s((0 : Fin 6), 4), s((2 : Fin 6), 4),
          s((1 : Fin 6), 5), s((2 : Fin 6), 5)} : Finset (Sym2 (Fin 6))) := by
      refine localAbsorbable_adj _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)
    simpa [hexConfig] using h
  · rintro ⟨P, hcl, hcov⟩
    have hP : P = ∅ := by
      by_contra hne
      obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hsub : triEdges t ⊆ hexConfig := by
        rw [← hcov]
        exact Finset.subset_biUnion_of_mem triEdges ht
      have h3 : t.card = 3 := (hcl t ht).card_eq
      have hno : ∀ u : Finset (Fin 6), triEdges u ⊆ hexConfig → u.card ≠ 3 := by decide
      exact hno t hsub h3
    rw [hP] at hcov
    simp only [coveredEdges, Finset.biUnion_empty] at hcov
    revert hcov
    decide

end Ax2.BKLO
