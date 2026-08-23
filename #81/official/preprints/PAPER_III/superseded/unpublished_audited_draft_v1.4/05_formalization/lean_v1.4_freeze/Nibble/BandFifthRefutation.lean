/-
# Nibble — the band `1/5` nibble is FALSE for `3`-uniform hypergraphs

At the Dross density `9|V| ≤ 10 δ(G)` the edge-type triangle hypergraph
`Nibble.YusterE.triangleHypergraphSub` is nearly `|V|`-regular only with band `μ = 1/5` (its degrees
are the codegrees `|N(u) ∩ N(v)| ∈ [(4/5)|V|, |V|]`), while the library's nibble
`Nibble.NibbleTheoremMostCeil` fixes its own band `μ = μ(β)`, small when `β` is.  Bridging that gap
by "running the nibble at `μ = 1/5`" is one of the tempting routes to
`Nibble.DenseGlobalSmallLeftover`.

**This file refutes that route as a statement about general `3`-uniform hypergraphs.**  It builds,
for every `p = n + 1`, a `3`-uniform hypergraph on `4p` vertices which is

* *exactly* inside the band `1/5` around `d = 5p/2` (left degrees `3p = (1 + 1/5)d`, right degrees
  `2p = (1 − 1/5)d`), and
* has codegree at most `2 ≤ (1/5)d`,

but in which **every matching has at most `p = |V|/4` edges** — because every edge meets the left
side in exactly one vertex.  So no matching covers more than `(3/4)|V|` vertices, while the nibble
conclusion at `β = 1/5` demands `(1 − 1/5)|V|/3 = (16/15)p` edges.

* `Nibble.bandHG` — the witness: vertices `ZMod p ⊕ (ZMod p × ZMod 3)`, edges
  `{inl x, inr (t, c), inr (x + t, c + 1)}`.
* `Nibble.bandHG_isUniform`, `Nibble.bandDegree_inl`, `Nibble.bandDegree_inr`,
  `Nibble.bandHG_codegree_le_two`, `Nibble.bandHG_matching_card_le` — its parameters.
* `Nibble.NibbleBandFifth`, `Nibble.not_nibbleBandFifth` — the refuted interface.

The moral: the `1/5` band gap between the triangle hypergraph at density `9/10` and the nibble's own
band is **not** a bookkeeping artefact.  Any route from the Dross density to an approximate triangle
decomposition must use graph-specific structure (a near-perfect *fractional* triangle decomposition,
i.e. Dross' theorem), not the general near-regular nibble.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Regular
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.RCLike.Basic

open Finset Hypergraph

namespace Nibble

/-! ### The witness -/

/-- Vertex type of the band-`1/5` witness: `p = n+1` left vertices and `3p` right vertices. -/
abbrev BandVtx (n : ℕ) : Type := ZMod (n + 1) ⊕ (ZMod (n + 1) × ZMod 3)

/-- The edge attached to a parameter triple `(x, t, c)`. -/
def bandEdge (n : ℕ) (a : ZMod (n + 1) × ZMod (n + 1) × ZMod 3) : Finset (BandVtx n) :=
  {Sum.inl a.1, Sum.inr (a.2.1, a.2.2), Sum.inr (a.1 + a.2.1, a.2.2 + 1)}

theorem mem_bandEdge (n : ℕ) (a : ZMod (n + 1) × ZMod (n + 1) × ZMod 3) (v : BandVtx n) :
    v ∈ bandEdge n a ↔ v = Sum.inl a.1 ∨ v = Sum.inr (a.2.1, a.2.2) ∨
      v = Sum.inr (a.1 + a.2.1, a.2.2 + 1) := by
  simp [bandEdge]

/-- The band-`1/5` witness hypergraph. -/
def bandHG (n : ℕ) : Finset (Finset (BandVtx n)) := Finset.image (bandEdge n) Finset.univ

theorem mem_bandHG (n : ℕ) (e : Finset (BandVtx n)) :
    e ∈ bandHG n ↔ ∃ a, bandEdge n a = e := by
  simp [bandHG]

/-- Distinct parameter triples give distinct edges. -/
theorem bandEdge_injective (n : ℕ) : Function.Injective (bandEdge n) := by
  rintro ⟨x, t, c⟩ ⟨x', t', c'⟩ h
  have hx : (Sum.inl x : BandVtx n) ∈ bandEdge n (x', t', c') := by
    rw [← h]; simp [mem_bandEdge]
  rw [mem_bandEdge] at hx
  simp only [Sum.inl.injEq, reduceCtorEq, or_false] at hx
  subst hx
  have ht : (Sum.inr (t, c) : BandVtx n) ∈ bandEdge n (x, t', c') := by
    rw [← h]; simp [mem_bandEdge]
  rw [mem_bandEdge] at ht
  simp only [reduceCtorEq, Sum.inr.injEq, Prod.mk.injEq, false_or] at ht
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · exfalso
    have ht' : (Sum.inr (t', c') : BandVtx n) ∈ bandEdge n (x, t, c) := by
      rw [h]; simp [mem_bandEdge]
    rw [mem_bandEdge] at ht'
    simp only [reduceCtorEq, Sum.inr.injEq, Prod.mk.injEq, false_or] at ht'
    rcases ht' with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · have h0 : (0 : ZMod 3) = 1 := by linear_combination h2 + h4
      exact absurd h0 (by decide)
    · have h0 : (0 : ZMod 3) = 2 := by linear_combination h2 + h4
      exact absurd h0 (by decide)

/-- The witness is `3`-uniform. -/
theorem bandHG_isUniform (n : ℕ) : IsUniform (bandHG n) 3 := by
  intro e he
  rw [mem_bandHG] at he
  obtain ⟨a, rfl⟩ := he
  have h1 : (Sum.inr (a.2.1, a.2.2) : BandVtx n) ≠ Sum.inr (a.1 + a.2.1, a.2.2 + 1) := by
    intro h
    simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    have h0 : (0 : ZMod 3) = 1 := by linear_combination h.2
    exact absurd h0 (by decide)
  rw [bandEdge, Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp [h1]),
    Finset.card_singleton]

/-- The number of vertices of the witness. -/
theorem card_bandVtx (n : ℕ) : Fintype.card (BandVtx n) = 4 * (n + 1) := by
  simp [BandVtx, Fintype.card_sum, ZMod.card]
  ring

/-! ### Degrees -/

theorem bandDegree_eq (n : ℕ) (v : BandVtx n) :
    degree (bandHG n) v = (Finset.univ.filter (fun a => v ∈ bandEdge n a)).card := by
  rw [degree, bandHG, ← Finset.card_image_of_injective _ (bandEdge_injective n)]
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨a, rfl⟩, hv⟩; exact ⟨a, hv, rfl⟩
  · rintro ⟨a, hv, rfl⟩; exact ⟨⟨a, rfl⟩, hv⟩

/-- **Left degrees are `3p`** — the top of the band. -/
theorem bandDegree_inl (n : ℕ) (x : ZMod (n + 1)) :
    degree (bandHG n) (Sum.inl x) = 3 * (n + 1) := by
  rw [bandDegree_eq]
  have h : (Finset.univ.filter
      (fun a : ZMod (n+1) × ZMod (n+1) × ZMod 3 => (Sum.inl x : BandVtx n) ∈ bandEdge n a))
      = ({x} : Finset (ZMod (n+1))) ×ˢ (Finset.univ : Finset (ZMod (n+1) × ZMod 3)) := by
    ext ⟨y, t, c⟩
    simp [mem_bandEdge, eq_comm]
  rw [h, Finset.card_product, Finset.card_singleton, Finset.card_univ]
  simp [ZMod.card]
  ring

/-- **Right degrees are `2p`** — the bottom of the band. -/
theorem bandDegree_inr (n : ℕ) (u : ZMod (n + 1)) (c : ZMod 3) :
    degree (bandHG n) (Sum.inr (u, c)) = 2 * (n + 1) := by
  classical
  rw [bandDegree_eq]
  set S1 : Finset (ZMod (n+1) × ZMod (n+1) × ZMod 3) :=
    Finset.image (fun x : ZMod (n+1) => (x, u, c)) Finset.univ with hS1
  set S2 : Finset (ZMod (n+1) × ZMod (n+1) × ZMod 3) :=
    Finset.image (fun x : ZMod (n+1) => (x, u - x, c - 1)) Finset.univ with hS2
  have hfilter : (Finset.univ.filter
      (fun a : ZMod (n+1) × ZMod (n+1) × ZMod 3 => (Sum.inr (u, c) : BandVtx n) ∈ bandEdge n a))
      = S1 ∪ S2 := by
    ext ⟨y, t, d⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_bandEdge, Finset.mem_union,
      hS1, hS2, Finset.mem_image, Prod.mk.injEq, reduceCtorEq, Sum.inr.injEq, false_or]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨y, ⟨rfl, rfl, rfl⟩⟩
      · exact Or.inr ⟨y, rfl, by linear_combination h1, by linear_combination h2⟩
    · rintro (⟨z, hz1, hz2, hz3⟩ | ⟨z, hz1, hz2, hz3⟩)
      · exact Or.inl ⟨hz2, hz3⟩
      · exact Or.inr ⟨by linear_combination hz2 + hz1, by linear_combination hz3⟩
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    rintro ⟨y, t, d⟩ h1 h2
    simp only [hS1, hS2, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at h1 h2
    obtain ⟨z, -, -, hd⟩ := h1
    obtain ⟨w, -, -, hd'⟩ := h2
    rw [← hd] at hd'
    have h0 : (0 : ZMod 3) = 1 := by linear_combination hd'
    exact absurd h0 (by decide)
  have hc1 : S1.card = n + 1 := by
    rw [hS1, Finset.card_image_of_injective _ (fun a b hab => by simpa using congrArg Prod.fst hab),
      Finset.card_univ, ZMod.card]
  have hc2 : S2.card = n + 1 := by
    rw [hS2, Finset.card_image_of_injective _ (fun a b hab => by simpa using congrArg Prod.fst hab),
      Finset.card_univ, ZMod.card]
  rw [hfilter, Finset.card_union_of_disjoint hdisj, hc1, hc2]
  ring

/-! ### Codegrees -/

theorem card_le_two_of_subset_pair {α : Type*} [DecidableEq α] {s : Finset α} {a b : α}
    (h : s ⊆ {a, b}) : s.card ≤ 2 :=
  le_trans (Finset.card_le_card h)
    (le_trans (Finset.card_insert_le _ _) (by simp))

theorem bandCodegree_eq (n : ℕ) (v w : BandVtx n) :
    codegree (bandHG n) v w
      = (Finset.univ.filter (fun a => v ∈ bandEdge n a ∧ w ∈ bandEdge n a)).card := by
  rw [codegree, bandHG, ← Finset.card_image_of_injective _ (bandEdge_injective n)]
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨a, rfl⟩, hv⟩; exact ⟨a, hv, rfl⟩
  · rintro ⟨a, hv, rfl⟩; exact ⟨⟨a, rfl⟩, hv⟩

/-- **Codegrees are at most `2`** (two distinct vertices lie in at most two edges). -/
theorem bandHG_codegree_le_two (n : ℕ) (v w : BandVtx n) (hvw : v ≠ w) :
    codegree (bandHG n) v w ≤ 2 := by
  classical
  rw [bandCodegree_eq]
  set T := Finset.univ.filter
    (fun a : ZMod (n+1) × ZMod (n+1) × ZMod 3 => v ∈ bandEdge n a ∧ w ∈ bandEdge n a) with hT
  match v, w with
  | Sum.inl x, Sum.inl x' =>
      have hsub : T ⊆ (∅ : Finset (ZMod (n+1) × ZMod (n+1) × ZMod 3)) := by
        intro a ha
        rw [hT, Finset.mem_filter] at ha
        obtain ⟨-, h1, h2⟩ := ha
        rw [mem_bandEdge] at h1 h2
        simp only [Sum.inl.injEq, reduceCtorEq, or_false] at h1 h2
        exact absurd (by rw [h1, h2] : (Sum.inl x : BandVtx n) = Sum.inl x') hvw
      have h0 : T.card = 0 := Finset.card_eq_zero.mpr (Finset.subset_empty.mp hsub)
      omega
  | Sum.inl x, Sum.inr (u, c) =>
      refine card_le_two_of_subset_pair (a := (x, u, c)) (b := (x, u - x, c - 1)) ?_
      rintro ⟨a1, a2, a3⟩ ha
      rw [hT, Finset.mem_filter] at ha
      obtain ⟨-, h1, h2⟩ := ha
      rw [mem_bandEdge] at h1 h2
      simp only [Sum.inl.injEq, reduceCtorEq, or_false] at h1
      simp only [reduceCtorEq, Sum.inr.injEq, Prod.mk.injEq, false_or] at h2
      rcases h2 with ⟨g1, g2⟩ | ⟨g1, g2⟩
      · have e1 : a1 = x := by linear_combination -h1
        have e2 : a2 = u := by linear_combination -g1
        have e3 : a3 = c := by linear_combination -g2
        rw [e1, e2, e3]; simp
      · have e1 : a1 = x := by linear_combination -h1
        have e2 : a2 = u - x := by linear_combination -g1 + h1
        have e3 : a3 = c - 1 := by linear_combination -g2
        rw [e1, e2, e3]; simp
  | Sum.inr (u, c), Sum.inl x =>
      refine card_le_two_of_subset_pair (a := (x, u, c)) (b := (x, u - x, c - 1)) ?_
      rintro ⟨a1, a2, a3⟩ ha
      rw [hT, Finset.mem_filter] at ha
      obtain ⟨-, h2, h1⟩ := ha
      rw [mem_bandEdge] at h1 h2
      simp only [Sum.inl.injEq, reduceCtorEq, or_false] at h1
      simp only [reduceCtorEq, Sum.inr.injEq, Prod.mk.injEq, false_or] at h2
      rcases h2 with ⟨g1, g2⟩ | ⟨g1, g2⟩
      · have e1 : a1 = x := by linear_combination -h1
        have e2 : a2 = u := by linear_combination -g1
        have e3 : a3 = c := by linear_combination -g2
        rw [e1, e2, e3]; simp
      · have e1 : a1 = x := by linear_combination -h1
        have e2 : a2 = u - x := by linear_combination -g1 + h1
        have e3 : a3 = c - 1 := by linear_combination -g2
        rw [e1, e2, e3]; simp
  | Sum.inr (u, c), Sum.inr (u', c') =>
      refine card_le_two_of_subset_pair (a := (u' - u, u, c)) (b := (u - u', u', c')) ?_
      rintro ⟨a1, a2, a3⟩ ha
      rw [hT, Finset.mem_filter] at ha
      obtain ⟨-, h1, h2⟩ := ha
      rw [mem_bandEdge] at h1 h2
      simp only [reduceCtorEq, Sum.inr.injEq, Prod.mk.injEq, false_or] at h1 h2
      rcases h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases h2 with ⟨f1, f2⟩ | ⟨f1, f2⟩
      · exfalso
        have hu : u = u' := by linear_combination e1 - f1
        have hc : c = c' := by linear_combination e2 - f2
        exact absurd (by rw [hu, hc] : (Sum.inr (u, c) : BandVtx n) = Sum.inr (u', c')) hvw
      · have g1 : a1 = u' - u := by linear_combination -f1 + e1
        have g2 : a2 = u := by linear_combination -e1
        have g3 : a3 = c := by linear_combination -e2
        rw [g1, g2, g3]; simp
      · have g1 : a1 = u - u' := by linear_combination -e1 + f1
        have g2 : a2 = u' := by linear_combination -f1
        have g3 : a3 = c' := by linear_combination -f2
        rw [g1, g2, g3]; simp
      · exfalso
        have hu : u = u' := by linear_combination e1 - f1
        have hc : c = c' := by linear_combination e2 - f2
        exact absurd (by rw [hu, hc] : (Sum.inr (u, c) : BandVtx n) = Sum.inr (u', c')) hvw

/-! ### Every matching is small -/

/-- **Every matching has at most `p` edges**: each edge meets the left side in exactly one vertex,
and distinct edges of a matching are disjoint. -/
theorem bandHG_matching_card_le (n : ℕ) {M : Finset (Finset (BandVtx n))}
    (hM : IsMatching (bandHG n) M) : M.card ≤ n + 1 := by
  classical
  set T : Finset (Finset (BandVtx n)) :=
    Finset.image (fun x : ZMod (n+1) => ({Sum.inl x} : Finset (BandVtx n))) Finset.univ with hTdef
  have hmaps : ∀ e ∈ M, e.filter (fun v => Sum.isLeft v) ∈ T := by
    intro e he
    obtain ⟨a, rfl⟩ := (mem_bandHG n e).mp (hM.subset he)
    refine Finset.mem_image.mpr ⟨a.1, Finset.mem_univ _, ?_⟩
    ext v
    constructor
    · intro hv
      rw [Finset.mem_singleton] at hv
      subst hv
      rw [Finset.mem_filter]
      exact ⟨by simp [mem_bandEdge], rfl⟩
    · intro hv
      rw [Finset.mem_filter] at hv
      obtain ⟨hv1, hv2⟩ := hv
      rw [mem_bandEdge] at hv1
      rcases hv1 with h | h | h
      · rw [h]; simp
      · rw [h] at hv2; simp at hv2
      · rw [h] at hv2; simp at hv2
  have hinj : ∀ e ∈ M, ∀ f ∈ M, e.filter (fun v => Sum.isLeft v) = f.filter (fun v => Sum.isLeft v)
      → e = f := by
    intro e he f hf hef
    by_contra hne
    obtain ⟨a, rfl⟩ := (mem_bandHG n e).mp (hM.subset he)
    have hmem : (Sum.inl a.1 : BandVtx n) ∈ (bandEdge n a).filter (fun v => Sum.isLeft v) := by
      simp [mem_bandEdge]
    rw [hef] at hmem
    have h1 : (Sum.inl a.1 : BandVtx n) ∈ f := (Finset.mem_filter.mp hmem).1
    have h2 : (Sum.inl a.1 : BandVtx n) ∈ bandEdge n a := by simp [mem_bandEdge]
    exact Finset.disjoint_left.mp (hM.disjoint _ he _ hf hne) h2 h1
  calc M.card ≤ T.card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ (Finset.univ : Finset (ZMod (n+1))).card := Finset.card_image_le
    _ = n + 1 := by rw [Finset.card_univ, ZMod.card]

/-! ### The refuted interface -/

/-- **The band-`1/5` nibble interface.**  For `3`-uniform hypergraphs that are `(1 ± 1/5)`-nearly
`d`-regular with codegree at most `(1/5)d`, a matching covering all but a `1/5`-fraction of the
vertices.  (Any threshold `d₀` is allowed.) -/
def NibbleBandFifth : Prop :=
  ∃ d₀ : ℝ, ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ),
    0 < d → d₀ ≤ d → IsUniform H 3 → NearlyRegular H d (1/5) → CodegreeBounded H (1/5 * d) →
    ∃ M : Finset (Finset V), IsMatching H M ∧
      (1 - 1/5) * ((Fintype.card V : ℝ) / 3) ≤ (M.card : ℝ)

/-- **The band-`1/5` nibble is false.**  The witness `Nibble.bandHG` satisfies every hypothesis and
has matching number `|V|/4 < (4/5)(|V|/3)`. -/
theorem not_nibbleBandFifth : ¬ NibbleBandFifth := by
  rintro ⟨d₀, hmain⟩
  classical
  obtain ⟨n, hn⟩ : ∃ n : ℕ, max d₀ 4 ≤ ((n : ℝ) + 1) :=
    ⟨⌈max d₀ 4⌉₊, le_trans (Nat.le_ceil _) (by push_cast; linarith)⟩
  set p : ℝ := (n : ℝ) + 1 with hp
  have hp4 : (4 : ℝ) ≤ p := le_trans (le_max_right _ _) hn
  have hpd : d₀ ≤ p := le_trans (le_max_left _ _) hn
  set d : ℝ := 5 * p / 2 with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  have hd0 : d₀ ≤ d := by rw [hd]; linarith
  have hcast3 : ((3 * (n + 1) : ℕ) : ℝ) = 3 * p := by rw [hp]; push_cast; ring
  have hcast2 : ((2 * (n + 1) : ℕ) : ℝ) = 2 * p := by rw [hp]; push_cast; ring
  have hreg : NearlyRegular (bandHG n) d (1/5) := by
    intro v
    match v with
    | Sum.inl x =>
        rw [bandDegree_inl, hcast3, hd]
        constructor <;> linarith
    | Sum.inr (u, c) =>
        rw [bandDegree_inr, hcast2, hd]
        constructor <;> linarith
  have hcod : CodegreeBounded (bandHG n) (1/5 * d) := by
    intro x y hxy
    have h2 : (codegree (bandHG n) x y : ℝ) ≤ 2 := by
      exact_mod_cast bandHG_codegree_le_two n x y hxy
    have : (2 : ℝ) ≤ 1/5 * d := by rw [hd]; linarith
    linarith
  obtain ⟨M, hM, hcard⟩ := hmain (bandHG n) d hdpos hd0 (bandHG_isUniform n) hreg hcod
  have hMle : (M.card : ℝ) ≤ p := by
    have hnat := bandHG_matching_card_le n hM
    have hcast : (M.card : ℝ) ≤ ((n : ℝ) + 1) := by exact_mod_cast hnat
    rw [hp]; exact hcast
  have hcardV : (Fintype.card (BandVtx n) : ℝ) = 4 * p := by
    rw [card_bandVtx, hp]; push_cast; ring
  rw [hcardV] at hcard
  have hppos : 0 < p := by linarith
  linarith

end Nibble
