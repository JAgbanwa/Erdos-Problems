import Mathlib

/-!
# The uniform-incidence bridge for a complete split terminal

This module is self-contained: it depends on Mathlib only.  It contains no
reference to `FarRounding`, to Paper V, or to any historical aggregate result,
and it uses no `sorry`, `admit`, `axiom`, `@[implemented_by]` or
`native_decide`.

## Setting

Two *disjoint* finite vertex sets are fixed: a clique side `Core` (of size
`k = #Core`) and a host side `Hosts` (of size `h = #Hosts`).  The *complete
split graph* `splitGraph Core Hosts` joins

* every two distinct core vertices (an **inner** edge), and
* every core vertex to every host vertex (a **cross** edge),

while host vertices are pairwise non-adjacent.  Hence the graph has
`a = C(k,2)` inner edges and `b = k*h` cross edges.

## The three literal families

Three families of *literal* cliques of the split graph are defined:

* `famK3 Core Hosts` — triangles with two core vertices and one host vertex;
* `famK4 Core Hosts` — `K₄`'s with three core vertices and one host vertex;
* `famK4core Core`   — `K₄`'s entirely inside the core.

Each member of each family is proved to be an actual clique of the split graph
of the correct cardinality.

## Uniform incidence

Every edge of a given type meets the same number of members of each family
(proved by explicit finite bijections, see
`card_filter_superset_powersetCard`):

| family      | inner edge   | cross edge   |
| ----------- | ------------ | ------------ |
| `famK3`     | `h`          | `k - 1`      |
| `famK4`     | `(k-2) * h`  | `C(k-1,2)`   |
| `famK4core` | `C(k-2,2)`   | `0`          |

## Uniform weights and per-edge loads

Distributing aggregate masses `u`, `v`, `w` uniformly over the three families
(`uniformWeight`), the literal per-edge load (`totalLoad`) is

* `(u + 3v + 6w) / a` on every inner edge, and
* `(2u + 3v) / b` on every cross edge,

with `a = C(k,2)` and `b = k*h`.  These are exactly the two quantities
constrained by the scalar complete-split LP.

The degenerate cases `k < 4`, `h = 0` and empty families are treated
explicitly rather than assumed away.
-/

namespace PaperIV.SplitUniformIncidence

open Finset

variable {V : Type*} [DecidableEq V]

/-! ## Binomial identities used by the uniform-weight computation -/

private theorem two_mul_choose_two (n : ℕ) : 2 * (n + 2).choose 2 = (n + 2) * (n + 1) := by
  induction n with
  | zero => decide
  | succ m ih =>
    rw [show m + 1 + 2 = (m + 2) + 1 from rfl, Nat.choose_succ_succ (m + 2) 1]
    simp only [Nat.choose_one_right] at *
    ring_nf
    ring_nf at ih
    omega

private theorem six_mul_choose_three (n : ℕ) :
    6 * (n + 3).choose 3 = (n + 3) * (n + 2) * (n + 1) := by
  induction n with
  | zero => decide
  | succ m ih =>
    have h := two_mul_choose_two (m + 1)
    rw [show m + 1 + 3 = (m + 3) + 1 from rfl, Nat.choose_succ_succ (m + 3) 2]
    have : (m + 3).choose 2 = (m + 1 + 2).choose 2 := by ring_nf
    nlinarith [ih, h]

private theorem twentyfour_mul_choose_four (n : ℕ) :
    24 * (n + 4).choose 4 = (n + 4) * (n + 3) * (n + 2) * (n + 1) := by
  induction n with
  | zero => decide
  | succ m ih =>
    have h := six_mul_choose_three (m + 1)
    rw [show m + 1 + 4 = (m + 4) + 1 from rfl, Nat.choose_succ_succ (m + 4) 3]
    have : (m + 4).choose 3 = (m + 1 + 3).choose 3 := by ring_nf
    nlinarith [ih, h]

/-- `k(k-1) = 2·C(k,2)`, valid for every `k` (truncated subtraction included). -/
theorem mul_pred_eq_two_mul_choose_two (k : ℕ) : k * (k - 1) = 2 * k.choose 2 := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> decide
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    show (n + 2) * (n + 1) = 2 * (n + 2).choose 2
    exact (two_mul_choose_two n).symm

/-- `3·C(k,3) = (k-2)·C(k,2)`, valid for every `k`. -/
theorem three_mul_choose_three (k : ℕ) : 3 * k.choose 3 = (k - 2) * k.choose 2 := by
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k <;> decide
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
    have h2 : 2 * (n + 3).choose 2 = (n + 3) * (n + 2) := by
      have := two_mul_choose_two (n + 1); omega
    have h3 := six_mul_choose_three n
    have : 2 * (3 * (n + 3).choose 3) = 2 * ((n + 3 - 2) * (n + 3).choose 2) := by
      have : n + 3 - 2 = n + 1 := by omega
      rw [this]
      nlinarith [h2, h3]
    omega

/-- `6·C(k,4) = C(k-2,2)·C(k,2)`, valid for every `k`. -/
theorem six_mul_choose_four (k : ℕ) : 6 * k.choose 4 = (k - 2).choose 2 * k.choose 2 := by
  rcases Nat.lt_or_ge k 4 with hk | hk
  · interval_cases k <;> decide
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 4 := ⟨k - 4, by omega⟩
    have h2 : 2 * (n + 4).choose 2 = (n + 4) * (n + 3) := by
      have := two_mul_choose_two (n + 2); omega
    have h2' : 2 * (n + 2).choose 2 = (n + 2) * (n + 1) := two_mul_choose_two n
    have h4 := twentyfour_mul_choose_four n
    have key : 4 * (6 * (n + 4).choose 4) = 4 * ((n + 4 - 2).choose 2 * (n + 4).choose 2) := by
      have : n + 4 - 2 = n + 2 := by omega
      rw [this]
      nlinarith [h2, h2', h4]
    omega

/-- `k·C(k-1,2) = 3·C(k,3)`, valid for every `k`. -/
theorem mul_choose_two_pred (k : ℕ) : k * (k - 1).choose 2 = 3 * k.choose 3 := by
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k <;> decide
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
    have h2 : 2 * (n + 2).choose 2 = (n + 2) * (n + 1) := two_mul_choose_two n
    have h3 := six_mul_choose_three n
    have key : 2 * ((n + 3) * (n + 3 - 1).choose 2) = 2 * (3 * (n + 3).choose 3) := by
      have : n + 3 - 1 = n + 2 := by omega
      rw [this]
      nlinarith [h2, h3]
    omega

/-! ## The complete split graph -/

/-- The complete split graph on a core `Core` and a host side `Hosts`: the core is a
clique, every core vertex is joined to every host vertex, and hosts are pairwise
non-adjacent. -/
def splitGraph (Core Hosts : Finset V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ((x ∈ Core ∧ y ∈ Core) ∨ (x ∈ Core ∧ y ∈ Hosts) ∨ (x ∈ Hosts ∧ y ∈ Core))
  symm := by
    rintro x y ⟨hne, h⟩
    exact ⟨hne.symm, by tauto⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem splitGraph_adj_iff {Core Hosts : Finset V} {x y : V} :
    (splitGraph Core Hosts).Adj x y ↔
      x ≠ y ∧ ((x ∈ Core ∧ y ∈ Core) ∨ (x ∈ Core ∧ y ∈ Hosts) ∨ (x ∈ Hosts ∧ y ∈ Core)) :=
  Iff.rfl

/-- Two distinct core vertices are adjacent: these are the *inner* edges. -/
theorem splitGraph_adj_inner {Core Hosts : Finset V} {x y : V} (hx : x ∈ Core) (hy : y ∈ Core)
    (hxy : x ≠ y) : (splitGraph Core Hosts).Adj x y :=
  ⟨hxy, Or.inl ⟨hx, hy⟩⟩

/-- A core vertex and a host vertex are adjacent: these are the *cross* edges. -/
theorem splitGraph_adj_cross {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {x z : V}
    (hx : x ∈ Core) (hz : z ∈ Hosts) : (splitGraph Core Hosts).Adj x z := by
  refine ⟨?_, Or.inr (Or.inl ⟨hx, hz⟩)⟩
  rintro rfl
  exact (Finset.disjoint_left.mp hd hx) hz

/-- Two host vertices are never adjacent. -/
theorem splitGraph_not_adj_hosts {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {x y : V}
    (hx : x ∈ Hosts) (hy : y ∈ Hosts) : ¬ (splitGraph Core Hosts).Adj x y := by
  rintro ⟨-, ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩⟩
  · exact (Finset.disjoint_left.mp hd h) hx
  · exact (Finset.disjoint_left.mp hd h) hx
  · exact (Finset.disjoint_left.mp hd h) hy

/-! ## The inner and cross edge sets, and the scalars `a` and `b` -/

/-- The inner edges of the split graph, as the two-element subsets of the core. -/
def innerPairs (Core : Finset V) : Finset (Finset V) := Core.powersetCard 2

/-- The cross edges of the split graph, as core/host pairs. -/
def crossPairs (Core Hosts : Finset V) : Finset (V × V) := Core ×ˢ Hosts

/-- `a = C(k,2)`, the number of inner edges. -/
def splitA (Core : Finset V) : ℚ := (Core.card.choose 2 : ℚ)

/-- `b = k·h`, the number of cross edges. -/
def splitB (Core Hosts : Finset V) : ℚ := (Core.card : ℚ) * (Hosts.card : ℚ)

omit [DecidableEq V] in
@[simp] theorem card_innerPairs (Core : Finset V) :
    (innerPairs Core).card = Core.card.choose 2 :=
  Finset.card_powersetCard _ _

omit [DecidableEq V] in
@[simp] theorem card_crossPairs (Core Hosts : Finset V) :
    (crossPairs Core Hosts).card = Core.card * Hosts.card :=
  Finset.card_product _ _

omit [DecidableEq V] in
theorem splitA_eq_card (Core : Finset V) : splitA Core = ((innerPairs Core).card : ℚ) := by
  simp [splitA]

omit [DecidableEq V] in
theorem splitB_eq_card (Core Hosts : Finset V) :
    splitB Core Hosts = ((crossPairs Core Hosts).card : ℚ) := by
  simp [splitB]

/-! ## Counting subsets containing a fixed set: the basic finite bijection -/

/-- The number of `r`-subsets of `Core` containing a fixed subset `T` equals
`C(#Core - #T, r - #T)`.  Proved by the explicit bijection `s ↦ s \ T` onto the
`(r - #T)`-subsets of `Core \ T`, with inverse `s' ↦ s' ∪ T`. -/
theorem card_filter_superset_powersetCard {Core T : Finset V} (hT : T ⊆ Core) {r : ℕ}
    (hr : T.card ≤ r) :
    (((Core.powersetCard r).filter (fun s => T ⊆ s)).card)
      = (Core.card - T.card).choose (r - T.card) := by
  have hcard : (((Core \ T).powersetCard (r - T.card)).card)
      = (Core.card - T.card).choose (r - T.card) := by
    rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hT]
  rw [← hcard]
  refine Finset.card_nbij' (fun s => s \ T) (fun s => s ∪ T) ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_powersetCard] at hs ⊢
    obtain ⟨⟨hsC, hscard⟩, hTs⟩ := hs
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Finset.mem_sdiff] at hx ⊢
      exact ⟨hsC hx.1, hx.2⟩
    · rw [Finset.card_sdiff_of_subset hTs, hscard]
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hs
    obtain ⟨hsC, hscard⟩ := hs
    have hdisj : Disjoint s T := by
      rw [Finset.disjoint_right]
      intro x hxT hxs
      exact (Finset.mem_sdiff.mp (hsC hxs)).2 hxT
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, Finset.subset_union_right⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_sdiff.mp (hsC hx)).1
      · exact hT hx
    · rw [Finset.card_union_of_disjoint hdisj, hscard]
      omega
  · intro s hs
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powersetCard] at hs
    exact Finset.sdiff_union_of_subset hs.2
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hs
    have hdisj : Disjoint s T := by
      rw [Finset.disjoint_right]
      intro x hxT hxs
      exact (Finset.mem_sdiff.mp (hs.1 hxs)).2 hxT
    exact Finset.union_sdiff_cancel_right hdisj

/-! ## The three literal families -/

/-- Attaching one host vertex to each member of a family of core subsets. -/
def hostFam (S : Finset (Finset V)) (Hosts : Finset V) : Finset (Finset V) :=
  (S ×ˢ Hosts).image fun p => insert p.2 p.1

theorem mem_hostFam {S : Finset (Finset V)} {Hosts : Finset V} {t : Finset V} :
    t ∈ hostFam S Hosts ↔ ∃ s ∈ S, ∃ z ∈ Hosts, t = insert z s := by
  simp only [hostFam, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨s, z, ⟨hs, hz⟩, rfl⟩; exact ⟨s, hs, z, hz, rfl⟩
  · rintro ⟨s, hs, z, hz, rfl⟩; exact ⟨s, z, ⟨hs, hz⟩, rfl⟩

/-- Triangles with two core vertices and one host vertex. -/
def famK3 (Core Hosts : Finset V) : Finset (Finset V) :=
  hostFam (Core.powersetCard 2) Hosts

/-- `K₄`'s with three core vertices and one host vertex. -/
def famK4 (Core Hosts : Finset V) : Finset (Finset V) :=
  hostFam (Core.powersetCard 3) Hosts

/-- `K₄`'s entirely inside the core. -/
def famK4core (Core : Finset V) : Finset (Finset V) := Core.powersetCard 4

/-! ## The members of the families are literal cliques -/

theorem isClique_insert_host {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {s : Finset V}
    (hs : s ⊆ Core) {z : V} (hz : z ∈ Hosts) :
    (splitGraph Core Hosts).IsClique ↑(insert z s) := by
  intro x hx y hy hxy
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · exact absurd rfl hxy
    · exact ((splitGraph_adj_cross hd (hs hy) hz).symm)
  · rcases hy with rfl | hy
    · exact splitGraph_adj_cross hd (hs hx) hz
    · exact splitGraph_adj_inner (hs hx) (hs hy) hxy

theorem isClique_of_subset_core {Core Hosts : Finset V} {s : Finset V} (hs : s ⊆ Core) :
    (splitGraph Core Hosts).IsClique ↑s := by
  intro x hx y hy hxy
  exact splitGraph_adj_inner (hs hx) (hs hy) hxy

theorem famK3_isClique {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {t : Finset V}
    (ht : t ∈ famK3 Core Hosts) :
    (splitGraph Core Hosts).IsClique ↑t ∧ t.card = 3 := by
  obtain ⟨s, hs, z, hz, rfl⟩ := mem_hostFam.mp ht
  rw [Finset.mem_powersetCard] at hs
  have hzs : z ∉ s := fun h => (Finset.disjoint_left.mp hd (hs.1 h)) hz
  exact ⟨isClique_insert_host hd hs.1 hz, by rw [Finset.card_insert_of_notMem hzs, hs.2]⟩

theorem famK4_isClique {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {t : Finset V}
    (ht : t ∈ famK4 Core Hosts) :
    (splitGraph Core Hosts).IsClique ↑t ∧ t.card = 4 := by
  obtain ⟨s, hs, z, hz, rfl⟩ := mem_hostFam.mp ht
  rw [Finset.mem_powersetCard] at hs
  have hzs : z ∉ s := fun h => (Finset.disjoint_left.mp hd (hs.1 h)) hz
  exact ⟨isClique_insert_host hd hs.1 hz, by rw [Finset.card_insert_of_notMem hzs, hs.2]⟩

theorem famK4core_isClique {Core Hosts : Finset V} {t : Finset V} (ht : t ∈ famK4core Core) :
    (splitGraph Core Hosts).IsClique ↑t ∧ t.card = 4 := by
  rw [famK4core, Finset.mem_powersetCard] at ht
  exact ⟨isClique_of_subset_core ht.1, ht.2⟩

/-! ## Cardinalities of the families -/

theorem hostFam_injOn {Core : Finset V} {S : Finset (Finset V)} {Hosts : Finset V}
    (hS : ∀ s ∈ S, s ⊆ Core) (hd : Disjoint Core Hosts) :
    Set.InjOn (fun p : Finset V × V => insert p.2 p.1) ↑(S ×ˢ Hosts) := by
  rintro ⟨s, g⟩ hp ⟨t, z⟩ hq hEq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hq
  obtain ⟨hs, hg⟩ := hp
  obtain ⟨ht, hz⟩ := hq
  simp only at hEq
  have hgs : g ∉ s := fun h => (Finset.disjoint_left.mp hd (hS s hs h)) hg
  have hzt : z ∉ t := fun h => (Finset.disjoint_left.mp hd (hS t ht h)) hz
  have hgz : g = z := by
    have hgmem : g ∈ insert z t := by rw [← hEq]; exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hgmem with h | h
    · exact h
    · exact absurd (hS t ht h) (fun hc => (Finset.disjoint_left.mp hd hc) hg)
  subst hgz
  have : s = t := by
    have h1 : (insert g s).erase g = s := Finset.erase_insert hgs
    have h2 : (insert g t).erase g = t := Finset.erase_insert hzt
    rw [← h1, ← h2, hEq]
  simp [this]

theorem card_hostFam {Core : Finset V} {S : Finset (Finset V)} {Hosts : Finset V}
    (hS : ∀ s ∈ S, s ⊆ Core) (hd : Disjoint Core Hosts) :
    (hostFam S Hosts).card = S.card * Hosts.card := by
  rw [hostFam, Finset.card_image_of_injOn (hostFam_injOn hS hd), Finset.card_product]

theorem card_famK3 {Core Hosts : Finset V} (hd : Disjoint Core Hosts) :
    (famK3 Core Hosts).card = Core.card.choose 2 * Hosts.card := by
  rw [famK3, card_hostFam (fun s hs => (Finset.mem_powersetCard.mp hs).1) hd,
    Finset.card_powersetCard]

theorem card_famK4 {Core Hosts : Finset V} (hd : Disjoint Core Hosts) :
    (famK4 Core Hosts).card = Core.card.choose 3 * Hosts.card := by
  rw [famK4, card_hostFam (fun s hs => (Finset.mem_powersetCard.mp hs).1) hd,
    Finset.card_powersetCard]

omit [DecidableEq V] in
theorem card_famK4core (Core : Finset V) :
    (famK4core Core).card = Core.card.choose 4 :=
  Finset.card_powersetCard _ _

/-! ## Incidence -/

/-- The number of members of a family of cliques that contain both endpoints of the
edge `{x, y}`. -/
def incidence (F : Finset (Finset V)) (x y : V) : ℕ :=
  (F.filter fun s => x ∈ s ∧ y ∈ s).card

theorem incidence_comm (F : Finset (Finset V)) (x y : V) :
    incidence F x y = incidence F y x := by
  unfold incidence
  congr 1
  apply Finset.filter_congr
  intro s _
  tauto

@[simp] theorem incidence_empty (x y : V) : incidence (∅ : Finset (Finset V)) x y = 0 := by
  simp [incidence]

/-! ### Counting core subsets through one or two fixed core vertices -/

/-- The `r`-subsets of the core through two fixed distinct core vertices. -/
theorem card_filter_mem_two {Core : Finset V} {x y : V} (hx : x ∈ Core) (hy : y ∈ Core)
    (hxy : x ≠ y) {r : ℕ} (hr : 2 ≤ r) :
    ((Core.powersetCard r).filter fun s => x ∈ s ∧ y ∈ s).card
      = (Core.card - 2).choose (r - 2) := by
  have hT : ({x, y} : Finset V) ⊆ Core := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · rw [Finset.mem_singleton] at hz; exact hz ▸ hy
  have hTcard : ({x, y} : Finset V).card = 2 := Finset.card_pair hxy
  have hfilter : ((Core.powersetCard r).filter fun s => x ∈ s ∧ y ∈ s)
      = ((Core.powersetCard r).filter fun s => ({x, y} : Finset V) ⊆ s) := by
    apply Finset.filter_congr
    intro s _
    simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]
  rw [hfilter, card_filter_superset_powersetCard hT (by omega), hTcard]

/-- The `r`-subsets of the core through one fixed core vertex. -/
theorem card_filter_mem_one {Core : Finset V} {x : V} (hx : x ∈ Core) {r : ℕ} (hr : 1 ≤ r) :
    ((Core.powersetCard r).filter fun s => x ∈ s).card = (Core.card - 1).choose (r - 1) := by
  have hT : ({x} : Finset V) ⊆ Core := Finset.singleton_subset_iff.mpr hx
  have hfilter : ((Core.powersetCard r).filter fun s => x ∈ s)
      = ((Core.powersetCard r).filter fun s => ({x} : Finset V) ⊆ s) := by
    apply Finset.filter_congr
    intro s _
    simp [Finset.singleton_subset_iff]
  rw [hfilter, card_filter_superset_powersetCard hT (by simpa using hr),
    Finset.card_singleton]

/-! ### Uniform incidence of the host families -/

/-- Inner edges meet the members of a host family uniformly. -/
theorem incidence_hostFam_inner {Core : Finset V} {S : Finset (Finset V)} {Hosts : Finset V}
    (hS : ∀ s ∈ S, s ⊆ Core) (hd : Disjoint Core Hosts) {x y : V} (hx : x ∈ Core)
    (hy : y ∈ Core) :
    incidence (hostFam S Hosts) x y = (S.filter fun s => x ∈ s ∧ y ∈ s).card * Hosts.card := by
  have hset : ((S ×ˢ Hosts).filter
        fun p : Finset V × V => x ∈ insert p.2 p.1 ∧ y ∈ insert p.2 p.1)
      = (S.filter fun s => x ∈ s ∧ y ∈ s) ×ˢ Hosts := by
    ext ⟨s, z⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert]
    constructor
    · rintro ⟨⟨hs, hz⟩, hx', hy'⟩
      have hxz : x ≠ z := fun h => (Finset.disjoint_left.mp hd hx) (h ▸ hz)
      have hyz : y ≠ z := fun h => (Finset.disjoint_left.mp hd hy) (h ▸ hz)
      exact ⟨⟨hs, hx'.resolve_left hxz, hy'.resolve_left hyz⟩, hz⟩
    · rintro ⟨⟨hs, hxs, hys⟩, hz⟩
      exact ⟨⟨hs, hz⟩, Or.inr hxs, Or.inr hys⟩
  have hsub : ((S.filter fun s => x ∈ s ∧ y ∈ s) ×ˢ Hosts : Finset (Finset V × V)) ⊆ S ×ˢ Hosts :=
    Finset.product_subset_product (Finset.filter_subset _ _) (Finset.Subset.refl _)
  unfold incidence hostFam
  rw [Finset.filter_image, hset,
    Finset.card_image_of_injOn ((hostFam_injOn hS hd).mono (Finset.coe_subset.mpr hsub)),
    Finset.card_product]

/-- Cross edges meet the members of a host family uniformly. -/
theorem incidence_hostFam_cross {Core : Finset V} {S : Finset (Finset V)} {Hosts : Finset V}
    (hS : ∀ s ∈ S, s ⊆ Core) (hd : Disjoint Core Hosts) {x z : V} (hx : x ∈ Core)
    (hz : z ∈ Hosts) :
    incidence (hostFam S Hosts) x z = (S.filter fun s => x ∈ s).card := by
  have hset : ((S ×ˢ Hosts).filter
        fun p : Finset V × V => x ∈ insert p.2 p.1 ∧ z ∈ insert p.2 p.1)
      = (S.filter fun s => x ∈ s) ×ˢ ({z} : Finset V) := by
    ext ⟨s, g⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hs, hg⟩, hx', hz'⟩
      have hxg : x ≠ g := fun h => (Finset.disjoint_left.mp hd hx) (h ▸ hg)
      refine ⟨⟨hs, hx'.resolve_left hxg⟩, ?_⟩
      rcases hz' with h | h
      · exact h.symm
      · exact absurd (hS s hs h) fun hc => (Finset.disjoint_left.mp hd hc) hz
    · rintro ⟨⟨hs, hxs⟩, rfl⟩
      exact ⟨⟨hs, hz⟩, Or.inr hxs, Or.inl rfl⟩
  have hsub : ((S.filter fun s => x ∈ s) ×ˢ ({z} : Finset V) : Finset (Finset V × V))
      ⊆ S ×ˢ Hosts :=
    Finset.product_subset_product (Finset.filter_subset _ _)
      (Finset.singleton_subset_iff.mpr hz)
  unfold incidence hostFam
  rw [Finset.filter_image, hset,
    Finset.card_image_of_injOn ((hostFam_injOn hS hd).mono (Finset.coe_subset.mpr hsub)),
    Finset.card_product, Finset.card_singleton, mul_one]

/-! ### Uniform incidence of the three literal families -/

/-- Each inner edge lies in exactly `h` triangles of the two-core-one-host family. -/
theorem incidence_famK3_inner {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {x y : V}
    (hx : x ∈ Core) (hy : y ∈ Core) (hxy : x ≠ y) :
    incidence (famK3 Core Hosts) x y = Hosts.card := by
  rw [famK3, incidence_hostFam_inner (fun s hs => (Finset.mem_powersetCard.mp hs).1) hd hx hy,
    card_filter_mem_two hx hy hxy (le_refl 2)]
  simp

/-- Each cross edge lies in exactly `k - 1` triangles of the two-core-one-host family. -/
theorem incidence_famK3_cross {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {x z : V}
    (hx : x ∈ Core) (hz : z ∈ Hosts) :
    incidence (famK3 Core Hosts) x z = Core.card - 1 := by
  rw [famK3, incidence_hostFam_cross (fun s hs => (Finset.mem_powersetCard.mp hs).1) hd hx hz,
    card_filter_mem_one hx (by norm_num)]
  simp

/-- Each inner edge lies in exactly `(k - 2) * h` members of the three-core-one-host family. -/
theorem incidence_famK4_inner {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {x y : V}
    (hx : x ∈ Core) (hy : y ∈ Core) (hxy : x ≠ y) :
    incidence (famK4 Core Hosts) x y = (Core.card - 2) * Hosts.card := by
  rw [famK4, incidence_hostFam_inner (fun s hs => (Finset.mem_powersetCard.mp hs).1) hd hx hy,
    card_filter_mem_two hx hy hxy (by norm_num)]
  simp

/-- Each cross edge lies in exactly `C(k-1,2)` members of the three-core-one-host family. -/
theorem incidence_famK4_cross {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {x z : V}
    (hx : x ∈ Core) (hz : z ∈ Hosts) :
    incidence (famK4 Core Hosts) x z = (Core.card - 1).choose 2 := by
  rw [famK4, incidence_hostFam_cross (fun s hs => (Finset.mem_powersetCard.mp hs).1) hd hx hz,
    card_filter_mem_one hx (by norm_num)]

/-- Each inner edge lies in exactly `C(k-2,2)` members of the core-`K₄` family. -/
theorem incidence_famK4core_inner {Core : Finset V} {x y : V} (hx : x ∈ Core) (hy : y ∈ Core)
    (hxy : x ≠ y) :
    incidence (famK4core Core) x y = (Core.card - 2).choose 2 := by
  rw [famK4core, incidence, card_filter_mem_two hx hy hxy (by norm_num)]

/-- No member of the core-`K₄` family contains a host vertex, so cross edges have
incidence `0` there. -/
theorem incidence_famK4core_cross {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {x z : V}
    (hz : z ∈ Hosts) : incidence (famK4core Core) x z = 0 := by
  rw [incidence, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro s hs ⟨-, hzs⟩
  rw [famK4core, Finset.mem_powersetCard] at hs
  exact (Finset.disjoint_left.mp hd (hs.1 hzs)) hz

/-! ## Uniform rational weights and literal per-edge loads -/

/-- The uniform weight carried by each member of a family `F` of total mass `m`.
If the family is empty the weight is `0`. -/
def uniformWeight (F : Finset (Finset V)) (m : ℚ) : ℚ := m / (F.card : ℚ)

/-- The literal load put on the edge `{x, y}` by a uniformly weighted family. -/
def load (F : Finset (Finset V)) (m : ℚ) (x y : V) : ℚ :=
  ∑ _s ∈ F.filter fun s => x ∈ s ∧ y ∈ s, uniformWeight F m

omit [DecidableEq V] in
/-- The weights of a nonempty family add up to its aggregate mass. -/
theorem sum_uniformWeight {F : Finset (Finset V)} (hF : F.Nonempty) (m : ℚ) :
    ∑ _s ∈ F, uniformWeight F m = m := by
  have hc : (F.card : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem hF.choose_spec)
  rw [Finset.sum_const, uniformWeight, nsmul_eq_mul, mul_div_cancel₀ _ hc]

/-- The load of an edge is its incidence times the uniform weight. -/
theorem load_eq_incidence_mul (F : Finset (Finset V)) (m : ℚ) (x y : V) :
    load F m x y = (incidence F x y : ℚ) * (m / (F.card : ℚ)) := by
  rw [load, Finset.sum_const, nsmul_eq_mul, incidence, uniformWeight]

@[simp] theorem load_empty (m : ℚ) (x y : V) : load (∅ : Finset (Finset V)) m x y = 0 := by
  simp [load]

theorem load_eq_zero_of_empty {F : Finset (Finset V)} (hF : F = ∅) (m : ℚ) (x y : V) :
    load F m x y = 0 := by
  subst hF; simp

/-- The total literal load put on the edge `{x, y}` by the three uniformly weighted
families with aggregate masses `u`, `v`, `w`. -/
def totalLoad (Core Hosts : Finset V) (u v w : ℚ) (x y : V) : ℚ :=
  load (famK3 Core Hosts) u x y + load (famK4 Core Hosts) v x y + load (famK4core Core) w x y

/-! ### Auxiliary positivity facts -/

theorem two_le_card_core {Core : Finset V} {x y : V} (hx : x ∈ Core) (hy : y ∈ Core)
    (hxy : x ≠ y) : 2 ≤ Core.card := by
  have hsub : ({x, y} : Finset V) ⊆ Core := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · rw [Finset.mem_singleton] at hz; exact hz ▸ hy
  calc 2 = ({x, y} : Finset V).card := (Finset.card_pair hxy).symm
    _ ≤ Core.card := Finset.card_le_card hsub

private theorem choose_cast_ne_zero {k r : ℕ} (h : r ≤ k) : (k.choose r : ℚ) ≠ 0 := by
  exact_mod_cast (Nat.choose_pos h).ne'

/-- The elementary rational manipulation behind every per-edge load computation: an
incidence `N` against a family of size `D` and mass `m` gives load `c * m / E` as soon as
`N * E = c * D`. -/
private theorem incidence_load_eq {N m c D E : ℚ} (hD : D ≠ 0) (hE : E ≠ 0)
    (h : N * E = c * D) : N * (m / D) = c * m / E := by
  field_simp
  linear_combination m * h

/-! ### Inner (core-core) loads -/

/-- The two-core-one-host family puts load `u / a` on every inner edge. -/
theorem load_famK3_inner {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {x y : V}
    (hx : x ∈ Core) (hy : y ∈ Core) (hxy : x ≠ y) (hh : 0 < Hosts.card) (u : ℚ) :
    load (famK3 Core Hosts) u x y = u / splitA Core := by
  have hk2 : 2 ≤ Core.card := two_le_card_core hx hy hxy
  have hA : (Core.card.choose 2 : ℚ) ≠ 0 := choose_cast_ne_zero hk2
  have hH : (Hosts.card : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [load_eq_incidence_mul, incidence_famK3_inner hd hx hy hxy, card_famK3 hd, splitA,
    Nat.cast_mul]
  rw [show (Hosts.card : ℚ) * (u / ((Core.card.choose 2 : ℚ) * (Hosts.card : ℚ)))
      = 1 * u / (Core.card.choose 2 : ℚ) from
    incidence_load_eq (by simp [hA, hH]) hA (by ring), one_mul]

/-- The three-core-one-host family puts load `3v / a` on every inner edge. -/
theorem load_famK4_inner {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {x y : V}
    (hx : x ∈ Core) (hy : y ∈ Core) (hxy : x ≠ y) (hk3 : 3 ≤ Core.card) (hh : 0 < Hosts.card)
    (v : ℚ) :
    load (famK4 Core Hosts) v x y = 3 * v / splitA Core := by
  have hA : (Core.card.choose 2 : ℚ) ≠ 0 := choose_cast_ne_zero (by omega)
  have hB : (Core.card.choose 3 : ℚ) ≠ 0 := choose_cast_ne_zero hk3
  have hH : (Hosts.card : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  have hidQ : (3 : ℚ) * (Core.card.choose 3 : ℚ)
      = ((Core.card - 2 : ℕ) : ℚ) * (Core.card.choose 2 : ℚ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) (three_mul_choose_three Core.card)
  rw [load_eq_incidence_mul, incidence_famK4_inner hd hx hy hxy, card_famK4 hd, splitA,
    Nat.cast_mul, Nat.cast_mul]
  exact incidence_load_eq (by simp [hB, hH]) hA
    (by linear_combination -((Hosts.card : ℚ) * hidQ))

/-- The core-`K₄` family puts load `6w / a` on every inner edge. -/
theorem load_famK4core_inner {Core : Finset V} {x y : V} (hx : x ∈ Core) (hy : y ∈ Core)
    (hxy : x ≠ y) (hk4 : 4 ≤ Core.card) (w : ℚ) :
    load (famK4core Core) w x y = 6 * w / splitA Core := by
  have hA : (Core.card.choose 2 : ℚ) ≠ 0 := choose_cast_ne_zero (by omega)
  have hC : (Core.card.choose 4 : ℚ) ≠ 0 := choose_cast_ne_zero hk4
  have hidQ : (6 : ℚ) * (Core.card.choose 4 : ℚ)
      = (((Core.card - 2).choose 2 : ℕ) : ℚ) * (Core.card.choose 2 : ℚ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) (six_mul_choose_four Core.card)
  rw [load_eq_incidence_mul, incidence_famK4core_inner hx hy hxy, card_famK4core, splitA]
  exact incidence_load_eq hC hA (by linear_combination -hidQ)

/-- **Uniform inner load.**  With aggregate masses `u`, `v`, `w` spread uniformly over the
three literal families, every core-core edge of the complete split graph carries the load
`(u + 3v + 6w) / a`, where `a = C(k,2)`. -/
theorem totalLoad_inner {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {x y : V}
    (hx : x ∈ Core) (hy : y ∈ Core) (hxy : x ≠ y) (hk4 : 4 ≤ Core.card) (hh : 0 < Hosts.card)
    (u v w : ℚ) :
    totalLoad Core Hosts u v w x y = (u + 3 * v + 6 * w) / splitA Core := by
  rw [totalLoad, load_famK3_inner hd hx hy hxy hh, load_famK4_inner hd hx hy hxy (by omega) hh,
    load_famK4core_inner hx hy hxy hk4]
  ring

/-! ### Cross (core-host) loads -/

/-- The two-core-one-host family puts load `2u / b` on every cross edge. -/
theorem load_famK3_cross {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {x z : V}
    (hx : x ∈ Core) (hz : z ∈ Hosts) (hk2 : 2 ≤ Core.card) (u : ℚ) :
    load (famK3 Core Hosts) u x z = 2 * u / splitB Core Hosts := by
  have hA : (Core.card.choose 2 : ℚ) ≠ 0 := choose_cast_ne_zero hk2
  have hK : (Core.card : ℚ) ≠ 0 := by
    have : 0 < Core.card := by omega
    exact_mod_cast this.ne'
  have hH : (Hosts.card : ℚ) ≠ 0 := by
    have : 0 < Hosts.card := Finset.card_pos.mpr ⟨z, hz⟩
    exact_mod_cast this.ne'
  have hidQ : (Core.card : ℚ) * ((Core.card - 1 : ℕ) : ℚ) = 2 * (Core.card.choose 2 : ℚ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) (mul_pred_eq_two_mul_choose_two Core.card)
  rw [load_eq_incidence_mul, incidence_famK3_cross hd hx hz, card_famK3 hd, splitB, Nat.cast_mul]
  exact incidence_load_eq (by simp [hA, hH]) (by simp [hK, hH])
    (by linear_combination (Hosts.card : ℚ) * hidQ)

/-- The three-core-one-host family puts load `3v / b` on every cross edge. -/
theorem load_famK4_cross {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {x z : V}
    (hx : x ∈ Core) (hz : z ∈ Hosts) (hk3 : 3 ≤ Core.card) (v : ℚ) :
    load (famK4 Core Hosts) v x z = 3 * v / splitB Core Hosts := by
  have hB : (Core.card.choose 3 : ℚ) ≠ 0 := choose_cast_ne_zero hk3
  have hK : (Core.card : ℚ) ≠ 0 := by
    have : 0 < Core.card := by omega
    exact_mod_cast this.ne'
  have hH : (Hosts.card : ℚ) ≠ 0 := by
    have : 0 < Hosts.card := Finset.card_pos.mpr ⟨z, hz⟩
    exact_mod_cast this.ne'
  have hidQ : (Core.card : ℚ) * (((Core.card - 1).choose 2 : ℕ) : ℚ)
      = 3 * (Core.card.choose 3 : ℚ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) (mul_choose_two_pred Core.card)
  rw [load_eq_incidence_mul, incidence_famK4_cross hd hx hz, card_famK4 hd, splitB, Nat.cast_mul]
  exact incidence_load_eq (by simp [hB, hH]) (by simp [hK, hH])
    (by linear_combination (Hosts.card : ℚ) * hidQ)

/-- The core-`K₄` family puts no load on cross edges. -/
theorem load_famK4core_cross {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {x z : V}
    (hz : z ∈ Hosts) (w : ℚ) : load (famK4core Core) w x z = 0 := by
  rw [load_eq_incidence_mul, incidence_famK4core_cross hd hz]
  simp

/-- **Uniform cross load.**  With aggregate masses `u`, `v`, `w` spread uniformly over the
three literal families, every core-host edge of the complete split graph carries the load
`(2u + 3v) / b`, where `b = k * h`. -/
theorem totalLoad_cross {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {x z : V}
    (hx : x ∈ Core) (hz : z ∈ Hosts) (hk4 : 4 ≤ Core.card) (u v w : ℚ) :
    totalLoad Core Hosts u v w x z = (2 * u + 3 * v) / splitB Core Hosts := by
  rw [totalLoad, load_famK3_cross hd hx hz (by omega), load_famK4_cross hd hx hz (by omega),
    load_famK4core_cross hd hz]
  ring

/-! ## The degenerate cases -/

omit [DecidableEq V] in
/-- If the core has fewer than four vertices the core-`K₄` family is empty. -/
theorem famK4core_eq_empty (Core : Finset V) (hk : Core.card < 4) : famK4core Core = ∅ :=
  Finset.powersetCard_eq_empty.mpr hk

/-- If the core has fewer than three vertices the three-core-one-host family is empty. -/
theorem famK4_eq_empty_of_card_lt (Core Hosts : Finset V) (hk : Core.card < 3) :
    famK4 Core Hosts = ∅ := by
  rw [famK4, hostFam, Finset.powersetCard_eq_empty.mpr hk]
  simp

/-- If the core has fewer than two vertices the two-core-one-host family is empty. -/
theorem famK3_eq_empty_of_card_lt (Core Hosts : Finset V) (hk : Core.card < 2) :
    famK3 Core Hosts = ∅ := by
  rw [famK3, hostFam, Finset.powersetCard_eq_empty.mpr hk]
  simp

/-- With no hosts the two host families are empty. -/
theorem famK3_eq_empty_of_hosts_empty (Core : Finset V) : famK3 Core (∅ : Finset V) = ∅ := by
  simp [famK3, hostFam]

theorem famK4_eq_empty_of_hosts_empty (Core : Finset V) : famK4 Core (∅ : Finset V) = ∅ := by
  simp [famK4, hostFam]

omit [DecidableEq V] in
/-- With no hosts the split graph has no cross edges at all. -/
theorem crossPairs_eq_empty (Core : Finset V) : crossPairs Core (∅ : Finset V) = ∅ := by
  simp [crossPairs]

omit [DecidableEq V] in
/-- With no hosts the cross scalar `b` vanishes. -/
@[simp] theorem splitB_hosts_empty (Core : Finset V) : splitB Core (∅ : Finset V) = 0 := by
  simp [splitB]

/-- **`h = 0`.**  With no hosts only the core-`K₄` family survives, and the inner load is
`6w / a`. -/
theorem totalLoad_inner_hosts_empty {Core : Finset V} {x y : V} (hx : x ∈ Core) (hy : y ∈ Core)
    (hxy : x ≠ y) (hk4 : 4 ≤ Core.card) (u v w : ℚ) :
    totalLoad Core (∅ : Finset V) u v w x y = 6 * w / splitA Core := by
  rw [totalLoad, load_eq_zero_of_empty (famK3_eq_empty_of_hosts_empty Core),
    load_eq_zero_of_empty (famK4_eq_empty_of_hosts_empty Core),
    load_famK4core_inner hx hy hxy hk4]
  ring

/-- **`k = 3`.**  A three-vertex core carries no core-`K₄`, and the inner load is
`(u + 3v) / a` with `a = 3`. -/
theorem totalLoad_inner_core_three {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {x y : V}
    (hx : x ∈ Core) (hy : y ∈ Core) (hxy : x ≠ y) (hk3 : Core.card = 3) (hh : 0 < Hosts.card)
    (u v w : ℚ) :
    totalLoad Core Hosts u v w x y = (u + 3 * v) / splitA Core ∧ splitA Core = 3 := by
  constructor
  · rw [totalLoad, load_famK3_inner hd hx hy hxy hh, load_famK4_inner hd hx hy hxy (by omega) hh,
      load_eq_zero_of_empty (famK4core_eq_empty Core (by omega))]
    ring
  · rw [splitA, hk3]
    norm_num

/-- **`k < 4`.**  Below four core vertices the core-`K₄` family contributes nothing, so the
total load is carried by the two host families alone. -/
theorem totalLoad_of_card_lt_four {Core Hosts : Finset V} (hk : Core.card < 4) (u v w : ℚ)
    (x y : V) :
    totalLoad Core Hosts u v w x y = load (famK3 Core Hosts) u x y + load (famK4 Core Hosts) v x y
    := by
  rw [totalLoad, load_eq_zero_of_empty (famK4core_eq_empty Core hk)]
  ring

/-- **`k < 2`, `h = 0`.**  If either side degenerates completely, all three families are empty
and every load vanishes. -/
theorem totalLoad_eq_zero_of_degenerate {Core Hosts : Finset V} (hk : Core.card < 2)
    (hh : Hosts = ∅) (u v w : ℚ) (x y : V) : totalLoad Core Hosts u v w x y = 0 := by
  subst hh
  rw [totalLoad, load_eq_zero_of_empty (famK3_eq_empty_of_card_lt Core ∅ hk),
    load_eq_zero_of_empty (famK4_eq_empty_of_hosts_empty Core),
    load_eq_zero_of_empty (famK4core_eq_empty Core (by omega))]
  ring

/-- An empty family carries no load whatever its nominal mass. -/
theorem load_of_empty_family (m : ℚ) (x y : V) : load (∅ : Finset (Finset V)) m x y = 0 :=
  load_empty m x y

/-! ## A concrete non-vacuity check

Core `{0,1,2,3}` and hosts `{4,5}`, so `k = 4`, `h = 2`, `a = 6`, `b = 8`. -/

section Example

private def exCore : Finset ℕ := {0, 1, 2, 3}
private def exHosts : Finset ℕ := {4, 5}

theorem example_disjoint : Disjoint exCore exHosts := by decide

theorem example_card_famK3 : (famK3 exCore exHosts).card = 12 := by decide

theorem example_card_famK4 : (famK4 exCore exHosts).card = 8 := by decide

theorem example_card_famK4core : (famK4core exCore).card = 1 := by decide

theorem example_incidence_inner :
    incidence (famK3 exCore exHosts) 0 1 = 2 ∧ incidence (famK4 exCore exHosts) 0 1 = 4 ∧
      incidence (famK4core exCore) 0 1 = 1 := by decide

theorem example_incidence_cross :
    incidence (famK3 exCore exHosts) 0 4 = 3 ∧ incidence (famK4 exCore exHosts) 0 4 = 3 ∧
      incidence (famK4core exCore) 0 4 = 0 := by decide

/-- The inner per-edge load on the concrete split: `(u + 3v + 6w) / 6`. -/
theorem example_totalLoad_inner (u v w : ℚ) :
    totalLoad exCore exHosts u v w 0 1 = (u + 3 * v + 6 * w) / 6 := by
  have hA : splitA exCore = 6 := by decide
  rw [totalLoad_inner example_disjoint (by decide) (by decide) (by decide) (by decide)
    (by decide), hA]

/-- The cross per-edge load on the concrete split: `(2u + 3v) / 8`. -/
theorem example_totalLoad_cross (u v w : ℚ) :
    totalLoad exCore exHosts u v w 0 4 = (2 * u + 3 * v) / 8 := by
  have hB : splitB exCore exHosts = 8 := by
    have hk : exCore.card = 4 := by decide
    have hh : exHosts.card = 2 := by decide
    rw [splitB, hk, hh]; norm_num
  rw [totalLoad_cross example_disjoint (by decide) (by decide) (by decide), hB]

end Example

end PaperIV.SplitUniformIncidence
