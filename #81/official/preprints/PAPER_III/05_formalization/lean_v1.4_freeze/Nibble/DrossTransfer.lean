/-
# Nibble — the `K₄` transfer network for fractional triangle decompositions

Dross's proof of the fractional triangle decomposition theorem starts from a *base* triangle
weighting and then redistributes coverage between **opposite edges of a `K₄`**: inside a `K₄` on
`{a, d} ∪ {b, c}` the signed triangle weighting

  `+½` on `abc` and `bcd`,  `-½` on `abd` and `acd`

raises the coverage of `bc` by `1`, lowers the coverage of `ad` by `1`, and leaves every other edge
of `G` untouched.  Superposing such moves along a **flow** in the network whose nodes are the edges
of `G` and whose arcs are the opposite pairs of `K₄`s converts any base weighting into an exact
fractional triangle decomposition, provided the flow's divergence matches the base weighting's
deficiency.  The weights move by at most the total capacity through each triangle, which is what
keeps them nonnegative and `O(1/|V|)`.

* `Nibble.IsOppPair` — two edges are opposite edges of a `K₄` of `G`.
* `Nibble.transferSign` — the signed effect of the arc `e₁ → e₂` on a triangle (twice the weight
  change).
* `Nibble.sum_transferSign` — **the coverage identity**: summing the effect over the triangles
  through an edge gives `+2` at `e₂`, `-2` at `e₁` and `0` elsewhere.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DrossGadget
import Nibble.FlowFeasibility

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Opposite pairs of a `K₄` -/

/-- Two edges of `G` are **opposite edges of a `K₄`**: every endpoint of the one is adjacent to
every endpoint of the other. -/
def IsOppPair (G : SimpleGraph V) [DecidableRel G.Adj] (e₁ e₂ : EdgeV G) : Prop :=
  ∀ x ∈ e₁.val, ∀ y ∈ e₂.val, G.Adj x y

theorem IsOppPair.symm {G : SimpleGraph V} [DecidableRel G.Adj] {e₁ e₂ : EdgeV G}
    (h : IsOppPair G e₁ e₂) : IsOppPair G e₂ e₁ :=
  fun x hx y hy => (h y hy x hx).symm

/-- The endpoints of opposite edges are distinct. -/
theorem IsOppPair.not_mem {G : SimpleGraph V} [DecidableRel G.Adj] {e₁ e₂ : EdgeV G}
    (h : IsOppPair G e₁ e₂) {x : V} (hx : x ∈ e₁.val) : x ∉ e₂.val := by
  intro hx2
  exact (h x hx x hx2).ne rfl

/-! ### The transfer move -/

/-- The **signed effect of the transfer arc `e₁ → e₂` on the triangle `T`**: `+1` on the two
triangles of the `K₄` through `e₂`, `-1` on the two through `e₁`, `0` elsewhere.  The actual weight
change is half of this. -/
noncomputable def transferSign (G : SimpleGraph V) [DecidableRel G.Adj] (e₁ e₂ : EdgeV G)
    (T : Finset (EdgeV G)) : ℝ :=
  (if e₂.val ⊆ triOf G T ∧ triOf G T ⊆ e₁.val ∪ e₂.val then (1 : ℝ) else 0)
    - (if e₁.val ⊆ triOf G T ∧ triOf G T ⊆ e₁.val ∪ e₂.val then (1 : ℝ) else 0)

theorem abs_transferSign_le (G : SimpleGraph V) [DecidableRel G.Adj] (e₁ e₂ : EdgeV G)
    (T : Finset (EdgeV G)) : |transferSign G e₁ e₂ T| ≤ 1 := by
  rw [transferSign, abs_le]
  constructor <;> split_ifs <;> norm_num

/-- Reversing the arc negates its effect. -/
theorem transferSign_swap (G : SimpleGraph V) [DecidableRel G.Adj] (e₁ e₂ : EdgeV G)
    (T : Finset (EdgeV G)) : transferSign G e₂ e₁ T = - transferSign G e₁ e₂ T := by
  rw [transferSign, transferSign, Finset.union_comm]
  ring

/-- The size of the effect is symmetric in the two edges. -/
theorem abs_transferSign_swap (G : SimpleGraph V) [DecidableRel G.Adj] (e₁ e₂ : EdgeV G)
    (T : Finset (EdgeV G)) : |transferSign G e₂ e₁ T| = |transferSign G e₁ e₂ T| := by
  rw [transferSign_swap, abs_neg]

omit [Fintype V] in
/-- A three-element subset of a four-element set is one of the four triples. -/
theorem card_three_subset_four (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {t : Finset V} (ht : t.card = 3)
    (hsub : t ⊆ ({a, b, c, d} : Finset V)) :
    t = {a, b, c} ∨ t = {a, b, d} ∨ t = {a, c, d} ∨ t = {b, c, d} := by
  classical
  have h4 : ({a, b, c, d} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
  have hne : t ≠ ({a, b, c, d} : Finset V) := by intro h; rw [h, h4] at ht; omega
  obtain ⟨x, hxmem, hxt⟩ := Finset.exists_of_ssubset (hsub.ssubset_of_ne hne)
  have hte : t ⊆ ({a, b, c, d} : Finset V).erase x := fun y hy =>
    Finset.mem_erase.mpr ⟨fun h => hxt (h ▸ hy), hsub hy⟩
  have hcard : (({a, b, c, d} : Finset V).erase x).card = 3 := by
    rw [Finset.card_erase_of_mem hxmem, h4]
  have heq : t = ({a, b, c, d} : Finset V).erase x :=
    Finset.eq_of_subset_of_card_le hte (by omega)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
  rcases hxmem with rfl | rfl | rfl | rfl
  · right; right; right
    rw [heq]; ext y
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  · right; right; left
    rw [heq]; ext y
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  · right; left
    rw [heq]; ext y
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  · left
    rw [heq]; ext y
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop

omit [Fintype V] in
set_option maxHeartbeats 1000000 in
/-- **The four triangles of the `K₄`.**  On triples, the signed effect of the transfer
`{a,d} → {b,c}` is `+1` on `abc` and `bcd` and `-1` on `abd` and `acd`. -/
theorem transferSign_triple_eval (a d b c : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {t : Finset V} (ht : t.card = 3) :
    ((if ({b, c} : Finset V) ⊆ t ∧ t ⊆ ({a, d} : Finset V) ∪ {b, c} then (1 : ℝ) else 0)
      - (if ({a, d} : Finset V) ⊆ t ∧ t ⊆ ({a, d} : Finset V) ∪ {b, c} then (1 : ℝ) else 0))
    = (if t = ({a, b, c} : Finset V) then (1 : ℝ) else 0)
      + (if t = ({b, c, d} : Finset V) then (1 : ℝ) else 0)
      - (if t = ({a, b, d} : Finset V) then (1 : ℝ) else 0)
      - (if t = ({a, c, d} : Finset V) then (1 : ℝ) else 0) := by
  classical
  have hba := hab.symm; have hca := hac.symm; have hda := had.symm
  have hcb := hbc.symm; have hdb := hbd.symm; have hdc := hcd.symm
  have hQ : ({a, d} : Finset V) ∪ {b, c} = ({a, b, c, d} : Finset V) := by
    ext y; simp; tauto
  rw [hQ]
  by_cases hsub : t ⊆ ({a, b, c, d} : Finset V)
  · rcases card_three_subset_four a b c d hab hac had hbc hbd hcd ht hsub with rfl|rfl|rfl|rfl <;>
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_insert,
        Finset.mem_singleton, Finset.Subset.antisymm_iff, hab, hac, had, hbc, hbd, hcd,
        hba, hca, hda, hcb, hdb, hdc, or_false, or_true, and_true,
        and_false, if_true, if_false] <;> norm_num
  · rw [if_neg (by tauto), if_neg (by tauto)]
    have h1 : ∀ s : Finset V, s ⊆ ({a, b, c, d} : Finset V) → t ≠ s := by
      intro s hs h; exact hsub (h ▸ hs)
    rw [if_neg (h1 _ (by intro y hy; simp at hy ⊢; tauto)),
      if_neg (h1 _ (by intro y hy; simp at hy ⊢; tauto)),
      if_neg (h1 _ (by intro y hy; simp at hy ⊢; tauto)),
      if_neg (h1 _ (by intro y hy; simp at hy ⊢; tauto))]
    norm_num

omit [Fintype V] in
/-- The indicator identity behind `Nibble.sum_transferSign`: for a `K₄` on `{a, d} ∪ {b, c}` and an
edge `{p, q}`, the four triangles of the `K₄` contribute `+2` exactly at `{b, c}`, `-2` exactly at
`{a, d}`, and cancel on the four remaining edges. -/
theorem transfer_indicator_eval (a d b c p q : V) (hpq : p ≠ q)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (if ({p, q} : Finset V) ⊆ ({a, b, c} : Finset V) then (1 : ℝ) else 0)
      + (if ({p, q} : Finset V) ⊆ ({b, c, d} : Finset V) then (1 : ℝ) else 0)
      - (if ({p, q} : Finset V) ⊆ ({a, b, d} : Finset V) then (1 : ℝ) else 0)
      - (if ({p, q} : Finset V) ⊆ ({a, c, d} : Finset V) then (1 : ℝ) else 0)
      = 2 * (if ({p, q} : Finset V) ⊆ ({b, c} : Finset V) then (1 : ℝ) else 0)
        - 2 * (if ({p, q} : Finset V) ⊆ ({a, d} : Finset V) then (1 : ℝ) else 0) := by
  classical
  have hqp : q ≠ p := hpq.symm
  have hba : b ≠ a := hab.symm
  have hca : c ≠ a := hac.symm
  have hda : d ≠ a := had.symm
  have hcb : c ≠ b := hbc.symm
  have hdb : d ≠ b := hbd.symm
  have hdc : d ≠ c := hcd.symm
  by_cases hp : p ∈ ({a, b, c, d} : Finset V)
  · by_cases hq : q ∈ ({a, b, c, d} : Finset V)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
      rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
        simp_all [Finset.subset_iff] <;> norm_num
    · have h1 : ¬ (({p, q} : Finset V) ⊆ ({a, b, c, d} : Finset V)) := by
        intro hsub; exact hq (hsub (by simp))
      have h2 : ∀ A : Finset V, A ⊆ ({a, b, c, d} : Finset V) → ¬ (({p, q} : Finset V) ⊆ A) :=
        fun A hA hsub => h1 (hsub.trans hA)
      rw [if_neg (h2 _ (by intro x hx; simp at hx ⊢; tauto)),
        if_neg (h2 _ (by intro x hx; simp at hx ⊢; tauto)),
        if_neg (h2 _ (by intro x hx; simp at hx ⊢; tauto)),
        if_neg (h2 _ (by intro x hx; simp at hx ⊢; tauto)),
        if_neg (h2 _ (by intro x hx; simp at hx ⊢; tauto)),
        if_neg (h2 _ (by intro x hx; simp at hx ⊢; tauto))]
      norm_num
  · have h1 : ¬ (({p, q} : Finset V) ⊆ ({a, b, c, d} : Finset V)) := by
      intro hsub; exact hp (hsub (by simp))
    have h2 : ∀ A : Finset V, A ⊆ ({a, b, c, d} : Finset V) → ¬ (({p, q} : Finset V) ⊆ A) :=
      fun A hA hsub => h1 (hsub.trans hA)
    rw [if_neg (h2 _ (by intro x hx; simp at hx ⊢; tauto)),
      if_neg (h2 _ (by intro x hx; simp at hx ⊢; tauto)),
      if_neg (h2 _ (by intro x hx; simp at hx ⊢; tauto)),
      if_neg (h2 _ (by intro x hx; simp at hx ⊢; tauto)),
      if_neg (h2 _ (by intro x hx; simp at hx ⊢; tauto)),
      if_neg (h2 _ (by intro x hx; simp at hx ⊢; tauto))]
    norm_num

/-! ### The coverage identity -/

/-- An edge of `G` is determined by any edge of `G` it contains. -/
theorem edgeV_subset_iff_eq (G : SimpleGraph V) [DecidableRel G.Adj] (e f : EdgeV G) :
    e.val ⊆ f.val ↔ e = f := by
  constructor
  · intro h
    have hc₁ : e.val.card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp e.property).card_eq
    have hc₂ : f.val.card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp f.property).card_eq
    exact Subtype.ext (Finset.eq_of_subset_of_card_le h (by omega))
  · rintro rfl; exact Finset.Subset.refl _

/-- **The coverage identity.**  For an opposite pair `e₁, e₂` of a `K₄`, the transfer arc
`e₁ → e₂` raises the coverage of `e₂` by `2`, lowers that of `e₁` by `2` and leaves every other
edge of `G` unchanged.  (Recall the actual weight change is half of `transferSign`.) -/
theorem sum_transferSign (G : SimpleGraph V) [DecidableRel G.Adj] {e₁ e₂ : EdgeV G}
    (hopp : IsOppPair G e₁ e₂) (e : EdgeV G) :
    ∑ T ∈ trianglesThrough G e, transferSign G e₁ e₂ T
      = 2 * (if e = e₂ then (1 : ℝ) else 0) - 2 * (if e = e₁ then (1 : ℝ) else 0) := by
  classical
  obtain ⟨a, d, had, hadA, hval₁⟩ := exists_pair_of_edgeV G e₁
  obtain ⟨b, c, hbc, hbcA, hval₂⟩ := exists_pair_of_edgeV G e₂
  have hma : a ∈ e₁.val := by rw [hval₁]; simp
  have hmd : d ∈ e₁.val := by rw [hval₁]; simp
  have hmb : b ∈ e₂.val := by rw [hval₂]; simp
  have hmc : c ∈ e₂.val := by rw [hval₂]; simp
  have habA : G.Adj a b := hopp a hma b hmb
  have hacA : G.Adj a c := hopp a hma c hmc
  have hbdA : G.Adj d b := hopp d hmd b hmb
  have hcdA : G.Adj d c := hopp d hmd c hmc
  have hab : a ≠ b := habA.ne
  have hac : a ≠ c := hacA.ne
  have hbd : b ≠ d := hbdA.ne.symm
  have hcd : c ≠ d := hcdA.ne.symm
  -- the four triangles of the `K₄`
  have habc : G.IsNClique 3 ({a, b, c} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨habA, hacA, hbcA⟩
  have hbcd : G.IsNClique 3 ({b, c, d} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hbcA, hbdA.symm, hcdA.symm⟩
  have habd : G.IsNClique 3 ({a, b, d} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨habA, hadA, hbdA.symm⟩
  have hacd : G.IsNClique 3 ({a, c, d} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hacA, hadA, hcdA.symm⟩
  have hF := sum_trianglesThrough_eq G e (fun t : Finset V =>
      (if e₂.val ⊆ t ∧ t ⊆ e₁.val ∪ e₂.val then (1 : ℝ) else 0)
        - (if e₁.val ⊆ t ∧ t ⊆ e₁.val ∪ e₂.val then (1 : ℝ) else 0))
  rw [show (∑ T ∈ trianglesThrough G e, transferSign G e₁ e₂ T) = _ from hF]
  have hstep : ∀ t ∈ (G.cliqueFinset 3).filter (fun t => e.val ⊆ t),
      ((if e₂.val ⊆ t ∧ t ⊆ e₁.val ∪ e₂.val then (1 : ℝ) else 0)
        - (if e₁.val ⊆ t ∧ t ⊆ e₁.val ∪ e₂.val then (1 : ℝ) else 0))
      = (if t = ({a, b, c} : Finset V) then (1 : ℝ) else 0)
        + (if t = ({b, c, d} : Finset V) then (1 : ℝ) else 0)
        - (if t = ({a, b, d} : Finset V) then (1 : ℝ) else 0)
        - (if t = ({a, c, d} : Finset V) then (1 : ℝ) else 0) := by
    intro t ht
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
    rw [hval₁, hval₂]
    exact transferSign_triple_eval a d b c hab hac had hbc hbd hcd ht.1.card_eq
  rw [Finset.sum_congr rfl hstep]
  have hsum : ∑ t ∈ (G.cliqueFinset 3).filter (fun t => e.val ⊆ t),
      ((if t = ({a, b, c} : Finset V) then (1 : ℝ) else 0)
        + (if t = ({b, c, d} : Finset V) then (1 : ℝ) else 0)
        - (if t = ({a, b, d} : Finset V) then (1 : ℝ) else 0)
        - (if t = ({a, c, d} : Finset V) then (1 : ℝ) else 0))
      = (if e.val ⊆ ({a, b, c} : Finset V) then (1 : ℝ) else 0)
        + (if e.val ⊆ ({b, c, d} : Finset V) then (1 : ℝ) else 0)
        - (if e.val ⊆ ({a, b, d} : Finset V) then (1 : ℝ) else 0)
        - (if e.val ⊆ ({a, c, d} : Finset V) then (1 : ℝ) else 0) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff]
    simp [habc, hbcd, habd, hacd]
  rw [hsum]
  obtain ⟨p, q, hpq, -, hvale⟩ := exists_pair_of_edgeV G e
  rw [hvale]
  rw [transfer_indicator_eval a d b c p q hpq hab hac had hbc hbd hcd]
  have h₂ : (({p, q} : Finset V) ⊆ ({b, c} : Finset V)) ↔ e = e₂ := by
    rw [← hvale, ← hval₂]; exact edgeV_subset_iff_eq G e e₂
  have h₁ : (({p, q} : Finset V) ⊆ ({a, d} : Finset V)) ↔ e = e₁ := by
    rw [← hvale, ← hval₁]; exact edgeV_subset_iff_eq G e e₁
  simp only [h₁, h₂]

/-! ### The bridge: a feasible flow produces an exact decomposition -/

/-- **The transferred weighting.**  Start from the constant base weight `w0` on every triangle and
superpose the transfer moves prescribed by the flow `f` (each unit of flow on the arc `e₁ → e₂`
moves one unit of coverage from `e₁` to `e₂` using `±½` on the four triangles of the `K₄`). -/
noncomputable def transferDecomp (G : SimpleGraph V) [DecidableRel G.Adj] (w0 : ℝ)
    (f : EdgeV G → EdgeV G → ℝ) (T : Finset (EdgeV G)) : ℝ :=
  w0 + (1 / 2) * ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G, f e₁ e₂ * transferSign G e₁ e₂ T

/-- **The coverage of the transferred weighting**: the base coverage plus the divergence of the
flow. -/
theorem sum_transferDecomp (G : SimpleGraph V) [DecidableRel G.Adj] (w0 : ℝ)
    {f : EdgeV G → EdgeV G → ℝ} (hsupp : ∀ e₁ e₂, f e₁ e₂ ≠ 0 → IsOppPair G e₁ e₂)
    (e : EdgeV G) :
    ∑ T ∈ trianglesThrough G e, transferDecomp G w0 f T
      = w0 * ((trianglesThrough G e).card : ℝ) + Flow.netFlow f e := by
  classical
  simp only [transferDecomp, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum]
  have hswap : ∑ T ∈ trianglesThrough G e,
      (∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G, f e₁ e₂ * transferSign G e₁ e₂ T)
      = ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G,
          f e₁ e₂ * ∑ T ∈ trianglesThrough G e, transferSign G e₁ e₂ T := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e₁ _ => ?_)
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun e₂ _ => by rw [Finset.mul_sum])
  have hterm : ∀ e₁ e₂ : EdgeV G,
      f e₁ e₂ * ∑ T ∈ trianglesThrough G e, transferSign G e₁ e₂ T
        = f e₁ e₂ * (2 * (if e = e₂ then (1 : ℝ) else 0))
          - f e₁ e₂ * (2 * (if e = e₁ then (1 : ℝ) else 0)) := by
    intro e₁ e₂
    by_cases h : f e₁ e₂ = 0
    · simp [h]
    · rw [sum_transferSign G (hsupp e₁ e₂ h) e]; ring
  rw [hswap, Finset.sum_congr rfl (fun e₁ _ => Finset.sum_congr rfl (fun e₂ _ => hterm e₁ e₂))]
  simp only [Finset.sum_sub_distrib]
  have h1 : ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G, f e₁ e₂ * (2 * (if e = e₂ then (1 : ℝ) else 0))
      = 2 * ∑ e₁ : EdgeV G, f e₁ e := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e₁ _ => ?_)
    rw [Finset.sum_eq_single e]
    · rw [if_pos rfl]; ring
    · intro e₂ _ hne; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ e) h
  have h2 : ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G, f e₁ e₂ * (2 * (if e = e₁ then (1 : ℝ) else 0))
      = 2 * ∑ e₂ : EdgeV G, f e e₂ := by
    rw [Finset.sum_eq_single e]
    · rw [Finset.mul_sum, if_pos rfl]
      exact Finset.sum_congr rfl (fun e₂ _ => by ring)
    · intro e₁ _ hne; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ e) h
  rw [h1, h2, Flow.netFlow]
  ring

/-- **The transferred weighting stays inside the capacity band.** -/
theorem abs_transferDecomp_sub_le (G : SimpleGraph V) [DecidableRel G.Adj] (w0 : ℝ)
    (f : EdgeV G → EdgeV G → ℝ) (hf0 : ∀ e₁ e₂, 0 ≤ f e₁ e₂) (T : Finset (EdgeV G)) :
    |transferDecomp G w0 f T - w0|
      ≤ (1 / 2) * ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G, f e₁ e₂ * |transferSign G e₁ e₂ T| := by
  classical
  have h : transferDecomp G w0 f T - w0
      = (1 / 2) * ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G, f e₁ e₂ * transferSign G e₁ e₂ T := by
    rw [transferDecomp]; ring
  rw [h, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc |∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G, f e₁ e₂ * transferSign G e₁ e₂ T|
      ≤ ∑ e₁ : EdgeV G, |∑ e₂ : EdgeV G, f e₁ e₂ * transferSign G e₁ e₂ T| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G, f e₁ e₂ * |transferSign G e₁ e₂ T| := by
        refine Finset.sum_le_sum (fun e₁ _ => ?_)
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun e₂ _ => ?_))
        rw [abs_mul, abs_of_nonneg (hf0 e₁ e₂)]

/-- **The bridge.**  A nonnegative flow supported on opposite pairs of `K₄`s, whose divergence is
the deficiency of the base weighting and whose total throughput at every triangle is at most the
base weight, turns the base weighting into an *exact* fractional triangle decomposition with all
weights in `[0, 2 w0]`. -/
theorem isFracTriangleDecomp_transfer (G : SimpleGraph V) [DecidableRel G.Adj] {w0 : ℝ}
    {f : EdgeV G → EdgeV G → ℝ} (hf0 : ∀ e₁ e₂, 0 ≤ f e₁ e₂)
    (hsupp : ∀ e₁ e₂, f e₁ e₂ ≠ 0 → IsOppPair G e₁ e₂)
    (hdiv : ∀ e : EdgeV G, Flow.netFlow f e = 1 - w0 * ((trianglesThrough G e).card : ℝ))
    (hbnd : ∀ T ∈ triangleHypergraphSub G,
      (1 / 2) * ∑ e₁ : EdgeV G, ∑ e₂ : EdgeV G, f e₁ e₂ * |transferSign G e₁ e₂ T| ≤ w0) :
    IsFracTriangleDecomp G (transferDecomp G w0 f) ∧
      ∀ T ∈ triangleHypergraphSub G, transferDecomp G w0 f T ≤ 2 * w0 := by
  have hband : ∀ T ∈ triangleHypergraphSub G, |transferDecomp G w0 f T - w0| ≤ w0 := fun T hT =>
    le_trans (abs_transferDecomp_sub_le G w0 f hf0 T) (hbnd T hT)
  refine ⟨⟨fun T hT => ?_, fun e => ?_⟩, fun T hT => ?_⟩
  · have := abs_le.mp (hband T hT); linarith only [this.1]
  · rw [sum_transferDecomp G w0 hsupp e, hdiv e]; ring
  · have := abs_le.mp (hband T hT); linarith only [this.2]

end Nibble
