import PaperIV.FarRounding

/-!
# E01 bridge analysis: batches of literal `K₃`/`K₄` items

This module attacks the bridge requested in `docs/E01_TASK_BRIEF.md`, which asks to
decompose the literal fractional support of the mixed `{K₃, K₄}` LP into *terminal
batches* consumable by the P4-498 kernel, and to assemble the batch outputs into a
single `FarRounding.Packing`.

It contains three things, all `Mathlib`-only and `sorry`-free, and it makes **no
claim that E01 is closed**:

* **§1 (point 4 has a price).** `two_mul_card_le_card_edgeFinset`: the injectivity
  hypothesis `hinj` of the kernel forces every batch to consume two *distinct real
  edges* per object, so a batch never exceeds half the edges of `G`.  This is the
  exact budget any decomposition must respect.

* **§2 (points 6 and 7 are provable, and are the easy half).**
  `exists_packing_of_batches`: a family of batches whose **full** edge supports are
  pairwise disjoint — inside each batch and across batches — assembles into a
  literal `FarRounding.Packing G` whose `gain` is exactly the sum of the batch
  gains.  No rounding is involved.

* **§3 (the residual obligation, with a literal witness).**
  `bases_not_controlled`: two literal items of a small graph, each carrying two
  distinct non-degenerate terminal edges, with all four terminal edges pairwise
  distinct — so the kernel hypothesis `hinj` holds for that two-object batch — and
  yet the two items **share an edge**.  Since `termGraph`, `FracPoint` and
  `CoversTerminals` are functions of the terminal data only, no consequence of the
  kernel can certify edge-disjointness of the selected items.  Point 6 of the brief
  must therefore be delivered by the decomposition, not derived from points 1–5.

Read together, §2 and §3 give a dichotomy that constrains any solution of E01:

> either the decomposition already delivers pairwise disjoint **full** edge supports
> — in which case the selected family is a packing outright (§2) and the kernel is
> needed only for the *counting*, not for feasibility — or two selected items share
> a non-terminal edge, and the kernel's conclusion cannot exclude it (§3).

The quantitative gap this leaves is recorded in `E01_BRIDGE_STATUS.md`.
-/

namespace PaperIV.FarRoundingBatchBridge

open Finset
open PaperIV.FarRounding

/-! ## 0. Elementary facts about literal edge supports -/

section Support

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- An item always has at least one edge, so its edge support is nonempty. -/
theorem pairs_nonempty {K : Finset V} (h : IsItem G K) : (pairs K).Nonempty := by
  rw [← Finset.card_pos, card_pairs_of_isItem h]
  omega

/-- The number of edges of an item that are *not* among its two terminal edges:
one for a `K₃`, four for a `K₄`.  These are exactly the edges the terminal data of
the P4-498 kernel never mentions. -/
theorem card_pairs_sdiff_two {K : Finset V} (h : IsItem G K)
    {e₀ e₁ : Sym2 V} (h₀ : e₀ ∈ pairs K) (h₁ : e₁ ∈ pairs K) (hne : e₀ ≠ e₁) :
    (pairs K \ {e₀, e₁}).card = gainOf K - 1 := by
  classical
  have hsub : ({e₀, e₁} : Finset (Sym2 V)) ⊆ pairs K := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he'
    · exact h₀
    · rw [Finset.mem_singleton] at he'; exact he' ▸ h₁
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair hne, card_pairs_of_isItem h]
  omega

end Support

/-! ## 1. The price of terminal injectivity (point 4 of the brief) -/

section Budget

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {ι : Type*} [DecidableEq ι]

/-- **Budget of a terminal batch.**  If the occurrence map `(P, i) ↦ emap P i` is
injective on a batch and lands in the real edges of `G`, then the batch has at most
half as many objects as `G` has edges.  Any decomposition of the fractional support
into terminal batches must respect this bound batch by batch. -/
theorem two_mul_card_le_card_edgeFinset
    (emap : ι → Fin 2 → Sym2 V) (Pall : Finset ι)
    (hmaps : ∀ P ∈ Pall, ∀ i : Fin 2, emap P i ∈ G.edgeFinset)
    (hinj : Set.InjOn (fun p : ι × Fin 2 => emap p.1 p.2) {p | p.1 ∈ Pall}) :
    2 * Pall.card ≤ G.edgeFinset.card := by
  classical
  have hmem : ∀ p ∈ Pall ×ˢ (univ : Finset (Fin 2)),
      (fun p : ι × Fin 2 => emap p.1 p.2) p ∈ G.edgeFinset := by
    intro p hp
    exact hmaps p.1 (Finset.mem_product.1 hp).1 p.2
  have hinj' : Set.InjOn (fun p : ι × Fin 2 => emap p.1 p.2)
      ↑(Pall ×ˢ (univ : Finset (Fin 2))) := by
    intro p hp q hq h
    have hp' : p.1 ∈ Pall := (Finset.mem_product.1 (Finset.mem_coe.1 hp)).1
    have hq' : q.1 ∈ Pall := (Finset.mem_product.1 (Finset.mem_coe.1 hq)).1
    exact hinj hp' hq' h
  have hle := Finset.card_le_card_of_injOn _ hmem hinj'
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hle
  omega

end Budget

/-! ## 2. Assembly of batches with disjoint edge supports (points 6 and 7) -/

section Assembly

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {β : Type*} [DecidableEq β]

/-- **Assembly.**  A finite family of batches of literal items whose edge supports
are pairwise disjoint — within each batch and between distinct batches — is a
literal `FarRounding.Packing`, and its gain is exactly the sum of the batch gains.

This is the provable half of points 6 and 7 of the brief.  Note what it requires:
disjointness of the *full* supports `pairs K`, not merely of the two terminal edges
the P4-498 kernel sees. -/
theorem exists_packing_of_batches
    (Bs : Finset β) (batch : β → Finset (Finset V))
    (hitem : ∀ b ∈ Bs, ∀ K ∈ batch b, IsItem G K)
    (hin : ∀ b ∈ Bs, ∀ K ∈ batch b, ∀ L ∈ batch b, K ≠ L →
      Disjoint (pairs K) (pairs L))
    (hcross : ∀ b ∈ Bs, ∀ b' ∈ Bs, b ≠ b' → ∀ K ∈ batch b, ∀ L ∈ batch b',
      Disjoint (pairs K) (pairs L)) :
    ∃ P : Packing G,
      P.pieces = Bs.biUnion batch ∧
        P.gain = ∑ b ∈ Bs, ∑ K ∈ batch b, gainOf K := by
  classical
  -- distinct batches are disjoint as families, because a shared item would have an
  -- edge support disjoint from itself
  have hdisjB : (↑Bs : Set β).PairwiseDisjoint batch := by
    intro b hb b' hb' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro K hK hK'
    have hself := hcross b (by simpa using hb) b' (by simpa using hb') hne K hK K hK'
    rw [disjoint_self] at hself
    exact absurd hself (Finset.nonempty_iff_ne_empty.1
      (pairs_nonempty (hitem b (by simpa using hb) K hK)))
  refine ⟨⟨Bs.biUnion batch, ?_, ?_⟩, rfl, ?_⟩
  · intro K hK
    obtain ⟨b, hb, hKb⟩ := Finset.mem_biUnion.1 hK
    exact hitem b hb K hKb
  · intro K hK L hL hKL
    obtain ⟨b, hb, hKb⟩ := Finset.mem_biUnion.1 hK
    obtain ⟨b', hb', hLb'⟩ := Finset.mem_biUnion.1 hL
    by_cases hbb : b = b'
    · subst hbb
      exact hin b hb K hKb L hLb' hKL
    · exact hcross b hb b' hb' hbb K hKb L hLb'
  · show ∑ K ∈ Bs.biUnion batch, gainOf K = _
    exact Finset.sum_biUnion hdisjB

end Assembly

/-! ## 3. The residual obligation: terminal data does not control the other edges -/

section Obstruction

/-! The witness lives in `K₄`, which is chordal, so it is a legitimate instance of
the far-regime setting.  Only `IsItem` and `pairs` are used, so no decidability
instance for the graph is required. -/

/-- Two triangles of `K₄` glued along the edge `{0, 1}`. -/
def triA : Finset (Fin 4) := {0, 1, 2}

def triB : Finset (Fin 4) := {0, 1, 3}

theorem isItem_triA : IsItem (⊤ : SimpleGraph (Fin 4)) triA := by
  refine ⟨fun a _ b _ hab => hab, Or.inl ?_⟩
  decide

theorem isItem_triB : IsItem (⊤ : SimpleGraph (Fin 4)) triB := by
  refine ⟨fun a _ b _ hab => hab, Or.inl ?_⟩
  decide

theorem triA_ne_triB : triA ≠ triB := by decide

/-- The shared edge, a non-terminal edge of both items. -/
theorem shared_edge_mem : s(0, 1) ∈ pairs triA ∧ s(0, 1) ∈ pairs triB := by
  constructor <;> rw [mk_mem_pairs] <;> exact ⟨by decide, by decide, by decide⟩

/-- **The residual obligation of the E01 bridge, as a literal witness.**

Two literal items of `K₄`, each equipped with two distinct non-degenerate terminal
edges of its own support, with the four terminal edges pairwise distinct — so the
two-object batch satisfies the kernel hypotheses `hinj` and `hloop` — and yet the
two items are **not** edge-disjoint.

Since `termGraph`, `FracPoint` and `CoversTerminals` are functions of the terminal
map only, no consequence of the P4-498 kernel can rule this configuration out.  The
edge-disjointness required by point 6 of the brief must be delivered by the
decomposition, not derived from points 1--5. -/
theorem bases_not_controlled :
    ∃ (K L : Finset (Fin 4)) (e₀ e₁ f₀ f₁ : Sym2 (Fin 4)),
      IsItem (⊤ : SimpleGraph (Fin 4)) K ∧ IsItem (⊤ : SimpleGraph (Fin 4)) L ∧
      K ≠ L ∧
      e₀ ∈ pairs K ∧ e₁ ∈ pairs K ∧ f₀ ∈ pairs L ∧ f₁ ∈ pairs L ∧
      (¬ e₀.IsDiag ∧ ¬ e₁.IsDiag ∧ ¬ f₀.IsDiag ∧ ¬ f₁.IsDiag) ∧
      (e₀ ≠ e₁ ∧ e₀ ≠ f₀ ∧ e₀ ≠ f₁ ∧ e₁ ≠ f₀ ∧ e₁ ≠ f₁ ∧ f₀ ≠ f₁) ∧
      ¬ Disjoint (pairs K) (pairs L) := by
  refine ⟨triA, triB, s(0, 2), s(1, 2), s(0, 3), s(1, 3),
    isItem_triA, isItem_triB, triA_ne_triB, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mk_mem_pairs]; exact ⟨by decide, by decide, by decide⟩
  · rw [mk_mem_pairs]; exact ⟨by decide, by decide, by decide⟩
  · rw [mk_mem_pairs]; exact ⟨by decide, by decide, by decide⟩
  · rw [mk_mem_pairs]; exact ⟨by decide, by decide, by decide⟩
  · refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Sym2.isDiag_iff_proj_eq] <;> decide
  · exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · rw [Finset.not_disjoint_iff]
    exact ⟨s(0, 1), shared_edge_mem.1, shared_edge_mem.2⟩

end Obstruction

end PaperIV.FarRoundingBatchBridge
