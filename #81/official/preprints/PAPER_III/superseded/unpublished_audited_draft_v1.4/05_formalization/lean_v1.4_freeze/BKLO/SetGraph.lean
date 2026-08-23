/-
# From edge sets on a vertex subset to graphs on a type, and back.

The engine works with edge sets `E : Finset (Sym2 V)` spanned by a vertex set `S : Finset V`
(this is what makes the vortex recursion of `BKLO/Vortex.lean` a plain induction on `|S|`), while
the external inputs of §4 — Dross's fractional threshold and the Haxell–Rödl nibble — are stated
for `SimpleGraph`s on a type.  This file provides the translation: the graph `setGraph S E` on the
subtype `↥S`, the identification of its edges, degrees and triangle decompositions with those of
`E`, and the two consequences needed by §10:

* `fracTriangleDecomposable_setGraph` — Dross applies to `setGraph S E` as soon as `E` has minimum
  degree at least `(9/10)|S|` on `S`;
* `approxTriDecomp_of_inputs` — the two inputs give, for every `η > 0` and every large `S`, an
  edge-disjoint family of triangles inside `E` missing at most `η|S|²` edges of `E`.

Everything here is `sorry`-free.
-/
import BKLO.Inputs
import BKLO.Vortex

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### The graph induced by an edge set on a vertex subset -/

/-- The graph on the subtype `↥S` whose edges are the edges of `E` inside `S`. -/
def setGraph (S : Finset V) (E : Finset (Sym2 V)) : SimpleGraph {x // x ∈ S} where
  Adj a b := a ≠ b ∧ s((a : V), (b : V)) ∈ E
  symm := fun a b h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (S : Finset V) (E : Finset (Sym2 V)) : DecidableRel (setGraph S E).Adj := by
  intro a b
  unfold setGraph
  infer_instance

/-- The embedding of `Sym2 ↥S` into `Sym2 V`. -/
def sym2val (S : Finset V) : Sym2 {x // x ∈ S} → Sym2 V := Sym2.map Subtype.val

omit [DecidableEq V] in
theorem sym2val_injective (S : Finset V) : Function.Injective (sym2val S) :=
  Sym2.map.injective Subtype.val_injective

omit [DecidableEq V] in
@[simp] theorem sym2val_mk (S : Finset V) (a b : {x // x ∈ S}) :
    sym2val S s(a, b) = s((a : V), (b : V)) := rfl

omit [DecidableEq V] in
theorem mem_sym2val (S : Finset V) (a : {x // x ∈ S}) (e : Sym2 {x // x ∈ S}) :
    (a : V) ∈ sym2val S e ↔ a ∈ e := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [sym2val_mk, Sym2.mem_iff]
    constructor
    · rintro (h | h)
      exacts [Or.inl (Subtype.ext h.symm).symm, Or.inr (Subtype.ext h.symm).symm]
    · rintro (rfl | rfl)
      exacts [Or.inl rfl, Or.inr rfl]

variable {S : Finset V} {E : Finset (Sym2 V)}

theorem mem_edgeFinset_setGraph {e : Sym2 {x // x ∈ S}} :
    e ∈ (setGraph S E).edgeFinset ↔ sym2val S e ∈ E ∧ ¬ e.IsDiag := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, sym2val_mk,
      Sym2.isDiag_iff_proj_eq]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- The edges of `setGraph S E`, pushed into `Sym2 V`, are exactly `E`. -/
theorem image_edgeFinset_setGraph (hE : E ⊆ cliqueEdges S) :
    (setGraph S E).edgeFinset.image (sym2val S) = E := by
  ext e
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact (mem_edgeFinset_setGraph.1 hf).1
  · intro he
    obtain ⟨hmem, hnd⟩ := mem_cliqueEdgesV.1 (hE he)
    induction e using Sym2.ind with
    | _ x y =>
      have hx : x ∈ S := hmem x (by simp)
      have hy : y ∈ S := hmem y (by simp)
      refine ⟨s((⟨x, hx⟩ : {x // x ∈ S}), ⟨y, hy⟩), ?_, rfl⟩
      refine mem_edgeFinset_setGraph.2 ⟨he, ?_⟩
      simp only [Sym2.isDiag_iff_proj_eq]
      intro h
      exact hnd (by simpa [Sym2.isDiag_iff_proj_eq] using congrArg Subtype.val h)

theorem card_edgeFinset_setGraph (hE : E ⊆ cliqueEdges S) :
    (setGraph S E).edgeFinset.card = E.card := by
  have h := Finset.card_image_of_injective (setGraph S E).edgeFinset (sym2val_injective S)
  rw [image_edgeFinset_setGraph hE] at h
  exact h.symm

theorem degree_setGraph (hE : E ⊆ cliqueEdges S) (a : {x // x ∈ S}) :
    (setGraph S E).degree a = edeg E (a : V) := by
  classical
  have h1 : (setGraph S E).degree a
      = ((setGraph S E).edgeFinset.filter (fun e => a ∈ e)).card := by
    rw [← (setGraph S E).card_incidenceFinset_eq_degree a,
      (setGraph S E).incidenceFinset_eq_filter a]
  have h2 : ((setGraph S E).edgeFinset.filter (fun e => a ∈ e)).image (sym2val S)
      = E.filter (fun e => (a : V) ∈ e) := by
    ext e
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨f, ⟨hf, haf⟩, rfl⟩
      exact ⟨(mem_edgeFinset_setGraph.1 hf).1, (mem_sym2val S a f).2 haf⟩
    · rintro ⟨he, hae⟩
      have hmem : e ∈ (setGraph S E).edgeFinset.image (sym2val S) := by
        rw [image_edgeFinset_setGraph hE]; exact he
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hmem
      exact ⟨f, ⟨hf, (mem_sym2val S a f).1 hae⟩, rfl⟩
  rw [h1, edeg, ← h2, Finset.card_image_of_injective _ (sym2val_injective S)]

omit [DecidableEq V] in
theorem card_coe_eq (S : Finset V) : Fintype.card {x // x ∈ S} = S.card :=
  Fintype.card_coe S

/-! ### Triangles -/

theorem cliqueEdges_image_val (t : Finset {x // x ∈ S}) :
    cliqueEdges (t.image Subtype.val) = (cliqueEdges t).image (sym2val S) := by
  classical
  ext e
  simp only [Finset.mem_image]
  constructor
  · intro he
    obtain ⟨hmem, hnd⟩ := mem_cliqueEdgesV.1 he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (hmem _ (by simp : x ∈ s(x, y)))
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (hmem _ (by simp : y ∈ s((a : V), y)))
      refine ⟨s(a, b), mem_cliqueEdgesV.2 ⟨?_, ?_⟩, rfl⟩
      · intro z hz
        rcases Sym2.mem_iff.1 hz with rfl | rfl
        exacts [ha, hb]
      · simp only [Sym2.isDiag_iff_proj_eq]
        intro h
        exact hnd (by simpa [Sym2.isDiag_iff_proj_eq] using congrArg Subtype.val h)
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨hmem, hnd⟩ := mem_cliqueEdgesV.1 hf
    induction f using Sym2.ind with
    | _ a b =>
      refine mem_cliqueEdgesV.2 ⟨?_, ?_⟩
      · intro z hz
        simp only [sym2val_mk, Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        exacts [Finset.mem_image_of_mem _ (hmem a (by simp)),
          Finset.mem_image_of_mem _ (hmem b (by simp))]
      · simp only [sym2val_mk, Sym2.isDiag_iff_proj_eq] at *
        intro h
        exact hnd (Subtype.ext h)

/-- The edges of a clique of `setGraph S E` are edges of the graph. -/
theorem cliqueEdges_subset_edgeFinset {t : Finset {x // x ∈ S}}
    (ht : (setGraph S E).IsClique (t : Set {x // x ∈ S})) :
    cliqueEdges t ⊆ (setGraph S E).edgeFinset := by
  intro e he
  obtain ⟨hmem, hnd⟩ := mem_cliqueEdgesV.1 he
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := by
      intro h; exact hnd (by simp [Sym2.isDiag_iff_proj_eq, h])
    exact SimpleGraph.mem_edgeFinset.2
      (ht (hmem a (by simp)) (hmem b (by simp)) hab)

theorem famEdges_image_val (parts : Finset (Finset {x // x ∈ S})) :
    famEdges (parts.image (fun t => t.image Subtype.val))
      = (parts.biUnion cliqueEdges).image (sym2val S) := by
  classical
  ext e
  simp only [famEdges, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨u, ⟨t, ht, rfl⟩, he⟩
    rw [cliqueEdges_image_val] at he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 he
    exact ⟨f, ⟨t, ht, hf⟩, rfl⟩
  · rintro ⟨f, ⟨t, ht, hf⟩, rfl⟩
    refine ⟨t.image Subtype.val, ⟨t, ht, rfl⟩, ?_⟩
    rw [cliqueEdges_image_val]
    exact Finset.mem_image_of_mem _ hf

/-- A family of edge-disjoint triangles of `setGraph S E` pushes forward to one inside `E`. -/
theorem triFamilyIn_image_val (hE : E ⊆ cliqueEdges S) {parts : Finset (Finset {x // x ∈ S})}
    (hcl : ∀ t ∈ parts, (setGraph S E).IsNClique 3 t)
    (hdisj : ∀ t ∈ parts, ∀ t' ∈ parts, t ≠ t' → Disjoint (cliqueEdges t) (cliqueEdges t')) :
    TriFamilyIn E (parts.image (fun t => t.image Subtype.val)) := by
  classical
  have himg : (setGraph S E).edgeFinset.image (sym2val S) = E := image_edgeFinset_setGraph hE
  refine ⟨?_, ?_, ?_⟩
  · rintro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    exact (hcl t ht).2
  · rintro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
    rw [cliqueEdges_image_val, ← himg]
    exact Finset.image_subset_image (cliqueEdges_subset_edgeFinset (hcl t ht).1)
  · rintro u hu u' hu' hne
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hu'
    have htt' : t ≠ t' := by
      intro h; exact hne (by rw [h])
    rw [cliqueEdges_image_val, cliqueEdges_image_val]
    exact Finset.disjoint_image (sym2val_injective S) |>.2 (hdisj t ht t' ht' htt')

theorem card_sdiff_famEdges_image_val (hE : E ⊆ cliqueEdges S)
    (parts : Finset (Finset {x // x ∈ S})) :
    (E \ famEdges (parts.image (fun t => t.image Subtype.val))).card
      = ((setGraph S E).edgeFinset \ parts.biUnion cliqueEdges).card := by
  classical
  have h1 : E \ famEdges (parts.image (fun t => t.image Subtype.val))
      = ((setGraph S E).edgeFinset \ parts.biUnion cliqueEdges).image (sym2val S) := by
    rw [Finset.image_sdiff _ _ (sym2val_injective S), image_edgeFinset_setGraph hE,
      famEdges_image_val]
  rw [h1, Finset.card_image_of_injective _ (sym2val_injective S)]

/-! ### The two external inputs, in edge-set language -/

/-- **Dross, in edge-set language.**  An edge set of minimum degree at least `(9/10)|S|` on `S`
induces a fractionally triangle decomposable graph on `S`. -/
theorem fracTriangleDecomposable_setGraph (hDross : FracTriangleThreshold)
    (hE : E ⊆ cliqueEdges S) (hdeg : ∀ v ∈ S, (9 / 10 : ℝ) * S.card ≤ edeg E v) :
    FracTriangleDecomposable (setGraph S E) := by
  classical
  refine hDross (setGraph S E) ?_
  rcases Finset.eq_empty_or_nonempty S with rfl | hS
  · simp
  · have hne : Nonempty {x // x ∈ S} := by
      obtain ⟨x, hx⟩ := hS
      exact ⟨⟨x, hx⟩⟩
    obtain ⟨a, ha⟩ := (setGraph S E).exists_minimal_degree_vertex
    have hd : (9 / 10 : ℝ) * S.card ≤ ((setGraph S E).degree a : ℝ) := by
      rw [degree_setGraph hE a]
      exact_mod_cast hdeg (a : V) a.2
    have : (9 : ℝ) * S.card ≤ 10 * ((setGraph S E).degree a : ℝ) := by linarith
    rw [card_coe_eq, ha]
    exact_mod_cast this

/-- **The nibble, in edge-set language.**  Dross's threshold and Haxell–Rödl give, for every
`η > 0` and every large enough vertex set `S`, an edge-disjoint family of triangles inside any
edge set `E` spanned by `S` of minimum degree at least `(9/10)|S|`, missing at most `η|S|²` edges
of `E`. -/
theorem approxTriDecomp_of_inputs (hDross : FracTriangleThreshold) (hHR : FracToApprox)
    {η : ℝ} (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ {V : Type} [DecidableEq V] (S : Finset V) (E : Finset (Sym2 V)),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → (∀ v ∈ S, (9 / 10 : ℝ) * S.card ≤ edeg E v) →
      ∃ P : Finset (Finset V), TriFamilyIn E P ∧
        ((E \ famEdges P).card : ℝ) ≤ η * (S.card : ℝ) ^ 2 := by
  classical
  obtain ⟨n₀, hn₀⟩ := hHR η hη
  refine ⟨n₀, ?_⟩
  intro V _ S E hcard hE hdeg
  obtain ⟨parts, hcl, hdisj, hcov⟩ :=
    hn₀ (setGraph S E) (by rw [card_coe_eq]; exact hcard)
      (fracTriangleDecomposable_setGraph hDross hE hdeg)
  refine ⟨parts.image (fun t => t.image Subtype.val), triFamilyIn_image_val hE hcl hdisj, ?_⟩
  rw [card_sdiff_famEdges_image_val hE parts]
  rw [card_coe_eq] at hcov
  exact hcov

/-! ### The nibble inside a vortex step -/

theorem edeg_cliqueEdges_le (W : Finset V) (v : V) : edeg (cliqueEdges W) v ≤ W.card := by
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

theorem edeg_le_edeg_sdiff_add_edeg (E F : Finset (Sym2 V)) (v : V) :
    edeg E v ≤ edeg (E \ F) v + edeg F v := by
  classical
  have hsub : E.filter (fun e => v ∈ e) ⊆ (E \ F).filter (fun e => v ∈ e) ∪ F.filter (fun e => v ∈ e) := by
    intro e he
    rw [Finset.mem_filter] at he
    by_cases hF : e ∈ F
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hF, he.2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨he.1, hF⟩, he.2⟩)
  calc edeg E v ≤ ((E \ F).filter (fun e => v ∈ e) ∪ F.filter (fun e => v ∈ e)).card :=
        Finset.card_le_card hsub
    _ ≤ edeg (E \ F) v + edeg F v := Finset.card_union_le _ _

/-- **The nibble inside a vortex step.**  Fix `ε, η > 0`.  For a large vertex set `S`, an edge set
`E` spanned by `S` of minimum degree at least `(9/10 + ε)|S|`, and any *reserved* edge set `R` of
maximum degree at most `ε|S|` on `S`, the two external inputs cover all but at most `η|S|²` of the
unreserved edges `E \ R` by edge-disjoint triangles that use no reserved edge at all.

This is the first half of the cover-down step of §10: with `R` the edges inside the next vortex
set `W` together with the reservoir of edges from `S \ W` to `W`, the nibble leaves both
completely untouched, so they are still available for covering the leftover down into `W` and for
carrying the next level of the vortex. -/
theorem nibbleReserving_of_inputs (hDross : FracTriangleThreshold) (hHR : FracToApprox)
    {ε η : ℝ} (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ {V : Type} [DecidableEq V] (S : Finset V) (E R : Finset (Sym2 V)),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → (∀ v ∈ S, (9 / 10 + ε) * S.card ≤ edeg E v) →
      (∀ v ∈ S, (edeg R v : ℝ) ≤ ε * S.card) →
      ∃ P : Finset (Finset V), TriFamilyIn (E \ R) P ∧
        (((E \ R) \ famEdges P).card : ℝ) ≤ η * (S.card : ℝ) ^ 2 := by
  classical
  obtain ⟨n₀, hn₀⟩ := approxTriDecomp_of_inputs hDross hHR hη
  refine ⟨n₀, ?_⟩
  intro V _ S E R hcard hE hdeg hR
  refine hn₀ S (E \ R) hcard ((Finset.sdiff_subset).trans hE) ?_
  intro v hv
  have h1 := hdeg v hv
  have h2 : (edeg E v : ℝ) ≤ (edeg (E \ R) v : ℝ) + (edeg R v : ℝ) := by
    exact_mod_cast edeg_le_edeg_sdiff_add_edeg E R v
  have h3 := hR v hv
  linarith

/-- The special case of `nibbleReserving_of_inputs` in which the reserved edges are exactly the
edges inside the next vortex set `W`. -/
theorem nibbleAvoiding_of_inputs (hDross : FracTriangleThreshold) (hHR : FracToApprox)
    {ε η : ℝ} (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ {V : Type} [DecidableEq V] (S W : Finset V) (E : Finset (Sym2 V)),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → (∀ v ∈ S, (9 / 10 + ε) * S.card ≤ edeg E v) →
      (W.card : ℝ) ≤ ε * S.card →
      ∃ P : Finset (Finset V), TriFamilyIn (E \ cliqueEdges W) P ∧
        (((E \ cliqueEdges W) \ famEdges P).card : ℝ) ≤ η * (S.card : ℝ) ^ 2 := by
  classical
  obtain ⟨n₀, hn₀⟩ := nibbleReserving_of_inputs hDross hHR (ε := ε) hη
  refine ⟨n₀, ?_⟩
  intro V _ S W E hcard hE hdeg hW
  refine hn₀ S E (cliqueEdges W) hcard hE hdeg (fun v _ => ?_)
  have h3 : (edeg (cliqueEdges W) v : ℝ) ≤ (W.card : ℝ) := by
    exact_mod_cast edeg_cliqueEdges_le W v
  linarith

end BKLO
