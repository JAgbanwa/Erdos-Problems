import BoundedCliqueGap.CSPorts
import PaperIV.Vizing

/-
`BoundedCliqueGap.GVizing` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Rung G0 — integration of the shipped modules, and the matching-family form
of Vizing's theorem

The three modules `PaperIV.Vizing`, `BoundedCliqueGap.OneFactorizationContrib` and
`BoundedCliqueGap.NearOneFactorizationContrib` are integrated verbatim (only the line
endings were normalised).  This file re-exports the API that the later rungs
need, in the shape the port engine of `BoundedCliqueGap.CSPorts` consumes:

* `exists_matchingFamily` — **Vizing, matching form**.  Every finite simple
  graph `H` with `Δ(H) ≤ q` has its edge set partitioned into `q+1` matchings,
  each presented as a `Finset (Finset K)` of two-element sets.
* `exists_matchingFamily_drop` — the same, keeping only `q` of the `q+1`
  classes: the discarded class can be taken of size at most `|E(H)| / (q+1)`,
  and in particular at most `|K| / 2`.
-/

namespace BoundedCliqueGap

open Finset SimpleGraph

/-! ## `Sym2` bookkeeping -/

variable {K : Type*} [DecidableEq K]

lemma sym2_toFinset_mk (a b : K) : (s(a, b) : Sym2 K).toFinset = {a, b} := by
  ext x
  simp [Sym2.mem_toFinset]

lemma sym2_toFinset_injective {z z' : Sym2 K} (hz : ¬ z.IsDiag)
    (h : z.toFinset = z'.toFinset) : z = z' := by
  induction z with
  | _ a b =>
    induction z' with
    | _ c d =>
      rw [sym2_toFinset_mk, sym2_toFinset_mk] at h
      have hab : a ≠ b := by simpa using hz
      rcases pair_eq_pair hab h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap

/-! ## Vizing in matching form -/

/-- **Rung G0 / Vizing, matching form.**  If `Δ(H) ≤ q`, the edges of `H` split
into `q+1` matchings `M i`, presented as finsets of two-element vertex sets:
distinct classes are disjoint, each class is a matching, and the class sizes
add up to `|E(H)|`. -/
theorem exists_matchingFamily [Fintype K]
    (H : SimpleGraph K) [DecidableRel H.Adj] (q : ℕ) (hq : H.maxDegree ≤ q) :
    ∃ M : Fin (q + 1) → Finset (Finset K),
      (∀ i, ∀ e ∈ M i, e.card = 2) ∧
      (∀ i, ∀ e ∈ M i, ∀ a ∈ e, ∀ b ∈ e, a ≠ b → H.Adj a b) ∧
      (∀ i, ∀ e ∈ M i, ∀ e' ∈ M i, e ≠ e' → Disjoint e e') ∧
      (∀ i j : Fin (q + 1), ∀ e, e ∈ M i → e ∈ M j → i = j) ∧
      ∑ i, (M i).card = H.edgeFinset.card := by
  classical
  obtain ⟨c, hc⟩ := Vizing.PEC.exists_total (G := H) (C := Fin (q + 1))
    (by simpa using Nat.lt_succ_of_le hq)
  -- the colour of an edge is realised by `col` on any representation
  have hcol : ∀ u v : K, H.Adj u v → c.col u v = some (c.edgeColor s(u, v)) := by
    intro u v huv
    obtain ⟨γ, hγ⟩ : ∃ γ, c.col u v = some γ := Option.ne_none_iff_exists'.1 (hc u v huv)
    simp [Vizing.PEC.edgeColor_mk, hγ]
  set M : Fin (q + 1) → Finset (Finset K) :=
    fun i => (H.edgeFinset.filter (fun e => c.edgeColor e = i)).image Sym2.toFinset with hM
  have hmemM : ∀ (i : Fin (q + 1)) (e : Finset K), e ∈ M i ↔
      ∃ z ∈ H.edgeFinset, c.edgeColor z = i ∧ z.toFinset = e := by
    intro i e
    simp only [hM, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨z, ⟨hz, hzc⟩, rfl⟩; exact ⟨z, hz, hzc, rfl⟩
    · rintro ⟨z, hz, hzc, rfl⟩; exact ⟨z, ⟨hz, hzc⟩, rfl⟩
  have hinj : ∀ (i : Fin (q + 1)) (z : Sym2 K), z ∈ H.edgeFinset →
      ∀ z' ∈ H.edgeFinset, z.toFinset = z'.toFinset → z = z' := by
    intro i z hz z' _ h
    exact sym2_toFinset_injective
      (SimpleGraph.not_isDiag_of_mem_edgeSet _ (by simpa using hz)) h
  refine ⟨M, ?_, ?_, ?_, ?_, ?_⟩
  · -- cardinality two
    intro i e he
    obtain ⟨z, hz, -, rfl⟩ := (hmemM i e).1 he
    rw [Sym2.card_toFinset, if_neg (SimpleGraph.not_isDiag_of_mem_edgeSet _ (by simpa using hz))]
  · -- the two ends are adjacent
    intro i e he a ha b hb hab
    obtain ⟨z, hz, -, rfl⟩ := (hmemM i e).1 he
    induction z with
    | _ u v =>
      rw [sym2_toFinset_mk] at ha hb
      have huv : H.Adj u v := by simpa using hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact huv
      · exact huv.symm
      · exact absurd rfl hab
  · -- each class is a matching
    intro i e he e' he' hne
    obtain ⟨z, hz, hzc, rfl⟩ := (hmemM i e).1 he
    obtain ⟨z', hz', hzc', rfl⟩ := (hmemM i e').1 he'
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Sym2.mem_toFinset] at hx hx'
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 hx
    obtain ⟨v, rfl⟩ := Sym2.mem_iff_exists.1 hx'
    have hxu : H.Adj x u := by simpa using hz
    have hxv : H.Adj x v := by simpa using hz'
    have h1 : c.col x u = some (c.edgeColor s(x, u)) := hcol x u hxu
    have h2 : c.col x v = some (c.edgeColor s(x, v)) := hcol x v hxv
    rw [hzc] at h1
    rw [hzc'] at h2
    have : u = v := c.col_proper h1 h2
    exact hne (by rw [this])
  · -- distinct classes are disjoint
    intro i j e hei hej
    obtain ⟨z, hz, hzc, hze⟩ := (hmemM i e).1 hei
    obtain ⟨z', hz', hzc', hze'⟩ := (hmemM j e).1 hej
    have : z = z' := hinj i z hz z' hz' (by rw [hze, hze'])
    rw [← hzc, ← hzc', this]
  · -- the classes exhaust the edge set
    have hcard : ∀ i : Fin (q + 1),
        (M i).card = (H.edgeFinset.filter (fun e => c.edgeColor e = i)).card := by
      intro i
      refine Finset.card_image_of_injOn ?_
      intro z hz z' hz' h
      have hz2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hz)).1
      have hz2' := (Finset.mem_filter.1 (Finset.mem_coe.1 hz')).1
      exact hinj i z hz2 z' hz2' h
    rw [Finset.sum_congr rfl (fun i _ => hcard i)]
    exact (Finset.card_eq_sum_card_fiberwise
      (f := fun e => c.edgeColor e) (s := H.edgeFinset) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))).symm

/-- A matching in a finite vertex set has at most `|K| / 2` edges. -/
lemma card_le_half_of_matching [Fintype K] (M : Finset (Finset K))
    (hcard2 : ∀ e ∈ M, e.card = 2)
    (hmatch : ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → Disjoint e e') :
    2 * M.card ≤ Fintype.card K := by
  classical
  have hbi : (M.biUnion fun e : Finset K => e).card = ∑ e ∈ M, (e : Finset K).card :=
    Finset.card_biUnion (fun e he e' he' hne => hmatch e he e' he' hne)
  have hsum : ∑ e ∈ M, (e : Finset K).card = 2 * M.card := by
    rw [Finset.sum_congr rfl (fun e he => hcard2 e he), Finset.sum_const, smul_eq_mul,
      Nat.mul_comm]
  have hle : (M.biUnion fun e : Finset K => e).card ≤ Fintype.card K :=
    Finset.card_le_univ _
  omega

/-! ## Axiom audit -/

end BoundedCliqueGap
