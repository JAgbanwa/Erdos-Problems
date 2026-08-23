/-
# The nibble in its maximum-degree form, in edge-set language.

`BKLO/SetGraph.lean` transports Dross's threshold and the Haxell–Rödl nibble
(`BKLO.approxTriDecomp_of_inputs`) into the edge-set vocabulary of the engine, with a bound on the
*total number* of leftover edges.  §10 needs more: the leftover has to be covered by triangles
whose apexes lie in the next vortex level, and the greedy that does this
(`BKLO.exists_coverDown_family`) consumes, at an edge `uv` of the leftover, one reserved apex per
leftover edge at `u` and at `v`.  What it therefore needs is a bound on the *maximum degree* of the
leftover.

This file records that form of the nibble in edge-set language, from the strengthened classical
input `BKLO.FracToApproxMaxDeg` (Pippenger–Spencer / Haxell–Rödl) together with Dross's threshold.
It also checks that the strengthened input really is a strengthening: it implies the old
`BKLO.FracToApprox` (`BKLO.fracToApprox_of_maxDeg`).

Everything here is `sorry`-free.
-/
import BKLO.SetGraph

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### The strengthened input implies the old one -/

/-- An edge set is contained in the union, over all vertices, of its stars. -/
theorem card_le_sum_edeg {V : Type} [Fintype V] [DecidableEq V] (L : Finset (Sym2 V)) :
    L.card ≤ ∑ v : V, (L.filter (fun e => v ∈ e)).card := by
  classical
  have hsub : L ⊆ (Finset.univ : Finset V).biUnion (fun v => L.filter (fun e => v ∈ e)) := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      exact Finset.mem_biUnion.2 ⟨x, Finset.mem_univ x, Finset.mem_filter.2 ⟨he, by simp⟩⟩
  calc L.card ≤ ((Finset.univ : Finset V).biUnion (fun v => L.filter (fun e => v ∈ e))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ v : V, (L.filter (fun e => v ∈ e)).card := Finset.card_biUnion_le

/-- The maximum-degree form of the nibble implies the total-count form. -/
theorem isApproxTriangleDecomp_of_maxDeg {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {parts : Finset (Finset V)} {η : ℝ}
    (h : IsApproxTriangleDecompMaxDeg G parts η) : IsApproxTriangleDecomp G parts η := by
  classical
  obtain ⟨hcl, hdisj, hdeg⟩ := h
  refine ⟨hcl, hdisj, ?_⟩
  set L : Finset (Sym2 V) := G.edgeFinset \ parts.biUnion cliqueEdges with hL
  have h1 : (L.card : ℝ) ≤ ∑ _v : V, η * (Fintype.card V : ℝ) := by
    refine le_trans ?_ (Finset.sum_le_sum (fun v _ => hdeg v))
    exact_mod_cast card_le_sum_edeg L
  calc (L.card : ℝ) ≤ ∑ _v : V, η * (Fintype.card V : ℝ) := h1
    _ = η * (Fintype.card V : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- **The strengthened nibble input implies the original one.** -/
theorem fracToApprox_of_maxDeg (h : FracToApproxMaxDeg) : FracToApprox := by
  intro η hη
  obtain ⟨n₀, hn₀⟩ := h η hη
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hcard hfrac
  obtain ⟨parts, hparts⟩ := hn₀ G hcard hfrac
  exact ⟨parts, isApproxTriangleDecomp_of_maxDeg G hparts⟩

/-! ### Transport of the degree bound -/

variable {S : Finset V} {E : Finset (Sym2 V)}

theorem edeg_eq_zero_of_notMem (hE : E ⊆ cliqueEdges S) {v : V} (hv : v ∉ S) : edeg E v = 0 := by
  classical
  rw [edeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hve
  obtain ⟨hmem, -⟩ := mem_cliqueEdgesV.1 (hE he)
  exact hv (hmem v hve)

theorem edeg_sdiff_famEdges_image_val (hE : E ⊆ cliqueEdges S)
    (parts : Finset (Finset {x // x ∈ S})) (a : {x // x ∈ S}) :
    edeg (E \ famEdges (parts.image (fun t => t.image Subtype.val))) (a : V)
      = (((setGraph S E).edgeFinset \ parts.biUnion cliqueEdges).filter
          (fun e => a ∈ e)).card := by
  classical
  have h1 : E \ famEdges (parts.image (fun t => t.image Subtype.val))
      = ((setGraph S E).edgeFinset \ parts.biUnion cliqueEdges).image (sym2val S) := by
    rw [Finset.image_sdiff _ _ (sym2val_injective S), image_edgeFinset_setGraph hE,
      famEdges_image_val]
  have h2 : (((setGraph S E).edgeFinset \ parts.biUnion cliqueEdges).image
        (sym2val S)).filter (fun e => (a : V) ∈ e)
      = (((setGraph S E).edgeFinset \ parts.biUnion cliqueEdges).filter
          (fun e => a ∈ e)).image (sym2val S) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨f, hf, rfl⟩, hae⟩
      exact ⟨f, ⟨hf, (mem_sym2val S a f).1 hae⟩, rfl⟩
    · rintro ⟨f, ⟨hf, haf⟩, rfl⟩
      exact ⟨⟨f, hf, rfl⟩, (mem_sym2val S a f).2 haf⟩
  rw [edeg, h1, h2, Finset.card_image_of_injective _ (sym2val_injective S)]

/-! ### The nibble with bounded leftover degree, in edge-set language -/

/-- **The nibble, maximum-degree form, in edge-set language.**  Dross's threshold and the
strengthened nibble give, for every `η > 0` and every large enough vertex set `S`, an
edge-disjoint family of triangles inside any edge set `E` spanned by `S` of minimum degree at
least `(9/10)|S|`, whose leftover has maximum degree at most `η|S|`. -/
theorem nibbleMaxDeg_of_inputs (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg)
    {η : ℝ} (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ {V : Type} [DecidableEq V] (S : Finset V) (E : Finset (Sym2 V)),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → (∀ v ∈ S, (9 / 10 : ℝ) * S.card ≤ edeg E v) →
      ∃ P : Finset (Finset V), TriFamilyIn E P ∧
        ∀ v : V, (edeg (E \ famEdges P) v : ℝ) ≤ η * (S.card : ℝ) := by
  classical
  obtain ⟨n₀, hn₀⟩ := hNib η hη
  refine ⟨n₀, ?_⟩
  intro V _ S E hcard hE hdeg
  obtain ⟨parts, hcl, hdisj, hlef⟩ :=
    hn₀ (setGraph S E) (by rw [card_coe_eq]; exact hcard)
      (fracTriangleDecomposable_setGraph hDross hE hdeg)
  refine ⟨parts.image (fun t => t.image Subtype.val), triFamilyIn_image_val hE hcl hdisj, ?_⟩
  intro v
  by_cases hv : v ∈ S
  · have h := hlef ⟨v, hv⟩
    rw [card_coe_eq] at h
    rw [edeg_sdiff_famEdges_image_val hE parts ⟨v, hv⟩]
    exact h
  · have hsub : E \ famEdges (parts.image (fun t => t.image Subtype.val)) ⊆ cliqueEdges S :=
      (Finset.sdiff_subset).trans hE
    rw [edeg_eq_zero_of_notMem hsub hv]
    have : (0:ℝ) ≤ η * (S.card : ℝ) := by positivity
    simpa using this

end BKLO
