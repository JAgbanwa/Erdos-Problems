/-
# Transporting the §10 edge-set vocabulary between a vertex *type* and a vertex *set*

Several §10 statements come in two flavours: one on a `Fintype` vertex type `V` (with
`Finset.univ` as the vertex set) and one on a vertex *set* `S : Finset V`.  This file provides the
dictionary between the two, along the inclusion `↥S ↪ V` of `BKLO/SetGraph.lean`:

* `BKLO.subEdges S E` — the edge set `E` pulled back to the subtype `↥S`;
* `BKLO.pushEdges S X` — an edge set on `↥S` pushed forward to `V`;
* `BKLO.subPart`, `BKLO.subParts` — the same for parts and partitions;
* the transport of degrees (`BKLO.edeg_pushEdges`), of `crossParts`, `edgesIn`, `TriDecomp`,
  `TriFamilyIn`, `IsEquitablePartition` and `IsKDeltaPartition`;
* `BKLO.approxTriDecompMinDeg_set` — the approximate-decomposition threshold `δ_F^η`
  (`BKLO.ApproxTriDecompMinDeg`, stated on a `Fintype`) in its vertex-set form.

Everything here is `sorry`-free.
-/
import BKLO.SetGraph
import BKLO.Section10TransformStepProof

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V] {S : Finset V}

/-! ### Edge sets -/

/-- The image in `Sym2 V` of an edge set on the subtype `↥S`. -/
def pushEdges (S : Finset V) (X : Finset (Sym2 {x // x ∈ S})) : Finset (Sym2 V) :=
  X.image (sym2val S)

/-- The restriction to the subtype `↥S` of an edge set on `V`. -/
noncomputable def subEdges (S : Finset V) (E : Finset (Sym2 V)) : Finset (Sym2 {x // x ∈ S}) :=
  E.preimage (sym2val S) ((sym2val_injective S).injOn)

omit [DecidableEq V] in
@[simp] theorem mem_subEdges {E : Finset (Sym2 V)} {e : Sym2 {x // x ∈ S}} :
    e ∈ subEdges S E ↔ sym2val S e ∈ E := Finset.mem_preimage

@[simp] theorem mem_pushEdges {X : Finset (Sym2 {x // x ∈ S})} {e : Sym2 V} :
    e ∈ pushEdges S X ↔ ∃ f ∈ X, sym2val S f = e := Finset.mem_image

omit [DecidableEq V] in
theorem mem_sym2val_iff (S : Finset V) (f : Sym2 {x // x ∈ S}) (u : V) :
    u ∈ sym2val S f ↔ ∃ a ∈ f, (a : V) = u := by
  induction f using Sym2.ind with
  | _ a b =>
    simp only [sym2val_mk, Sym2.mem_iff]
    constructor
    · rintro (rfl | rfl)
      exacts [⟨a, by simp, rfl⟩, ⟨b, by simp, rfl⟩]
    · rintro ⟨c, hc, rfl⟩
      rcases hc with rfl | rfl
      exacts [Or.inl rfl, Or.inr rfl]

omit [DecidableEq V] in
theorem isDiag_sym2val (e : Sym2 {x // x ∈ S}) : (sym2val S e).IsDiag ↔ e.IsDiag := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [sym2val_mk, Sym2.isDiag_iff_proj_eq]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem pushEdges_subEdges {E : Finset (Sym2 V)} (hE : E ⊆ cliqueEdges S) :
    pushEdges S (subEdges S E) = E := by
  ext e
  simp only [mem_pushEdges, mem_subEdges]
  constructor
  · rintro ⟨f, hf, rfl⟩; exact hf
  · intro he
    obtain ⟨hmem, hnd⟩ := mem_cliqueEdgesV.1 (hE he)
    induction e using Sym2.ind with
    | _ x y =>
      have hx : x ∈ S := hmem x (by simp)
      have hy : y ∈ S := hmem y (by simp)
      exact ⟨s((⟨x, hx⟩ : {x // x ∈ S}), ⟨y, hy⟩), he, rfl⟩

theorem subEdges_pushEdges (X : Finset (Sym2 {x // x ∈ S})) : subEdges S (pushEdges S X) = X := by
  ext e
  simp only [mem_subEdges, mem_pushEdges]
  exact ⟨fun ⟨f, hf, hfe⟩ => (sym2val_injective S hfe) ▸ hf, fun he => ⟨e, he, rfl⟩⟩

theorem pushEdges_mono {X Y : Finset (Sym2 {x // x ∈ S})} (h : X ⊆ Y) :
    pushEdges S X ⊆ pushEdges S Y := Finset.image_subset_image h

theorem pushEdges_sdiff (X Y : Finset (Sym2 {x // x ∈ S})) :
    pushEdges S (X \ Y) = pushEdges S X \ pushEdges S Y :=
  Finset.image_sdiff _ _ (sym2val_injective S)

theorem card_pushEdges (X : Finset (Sym2 {x // x ∈ S})) : (pushEdges S X).card = X.card :=
  Finset.card_image_of_injective _ (sym2val_injective S)

theorem loopless_pushEdges {X : Finset (Sym2 {x // x ∈ S})} (h : ∀ e ∈ X, ¬ e.IsDiag) :
    ∀ e ∈ pushEdges S X, ¬ e.IsDiag := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := mem_pushEdges.1 he
  rw [isDiag_sym2val]
  exact h f hf

omit [DecidableEq V] in
theorem loopless_subEdges {E : Finset (Sym2 V)} (h : ∀ e ∈ E, ¬ e.IsDiag) :
    ∀ e ∈ subEdges S E, ¬ e.IsDiag := by
  intro e he
  rw [← isDiag_sym2val]
  exact h _ (mem_subEdges.1 he)

theorem edeg_pushEdges (X : Finset (Sym2 {x // x ∈ S})) (a : {x // x ∈ S}) :
    edeg (pushEdges S X) (a : V) = edeg X a := by
  classical
  have h : (pushEdges S X).filter (fun e => (a : V) ∈ e)
      = (X.filter (fun e => a ∈ e)).image (sym2val S) := by
    ext e
    simp only [Finset.mem_filter, mem_pushEdges, Finset.mem_image]
    constructor
    · rintro ⟨⟨f, hf, rfl⟩, hae⟩
      exact ⟨f, ⟨hf, (mem_sym2val S a f).1 hae⟩, rfl⟩
    · rintro ⟨f, ⟨hf, haf⟩, rfl⟩
      exact ⟨⟨f, hf, rfl⟩, (mem_sym2val S a f).2 haf⟩
  rw [edeg, h, Finset.card_image_of_injective _ (sym2val_injective S), edeg]

theorem edeg_pushEdges_eq_zero (X : Finset (Sym2 {x // x ∈ S})) {v : V} (hv : v ∉ S) :
    edeg (pushEdges S X) v = 0 := by
  classical
  rw [edeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hve
  obtain ⟨f, -, rfl⟩ := mem_pushEdges.1 he
  obtain ⟨a, -, rfl⟩ := (mem_sym2val_iff S f _).1 hve
  exact hv a.2

/-! ### Triangles -/

theorem famEdges_push (T : Finset (Finset {x // x ∈ S})) :
    famEdges (T.image (fun t => t.image Subtype.val)) = pushEdges S (famEdges T) := by
  rw [famEdges_image_val T]
  rfl

theorem TriDecomp.push {X : Finset (Sym2 {x // x ∈ S})} (h : TriDecomp X) :
    TriDecomp (pushEdges S X) := by
  classical
  obtain ⟨T, h3, hdisj, hcov⟩ := h
  refine ⟨T.image (fun t => t.image Subtype.val), ?_, ?_, ?_⟩
  · rintro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    exact h3 t ht
  · rintro u hu u' hu' hne
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hu'
    have htt' : t ≠ t' := fun h => hne (by rw [h])
    rw [cliqueEdges_image_val, cliqueEdges_image_val]
    exact (Finset.disjoint_image (sym2val_injective S)).2 (hdisj t ht t' ht' htt')
  · rw [famEdges_push, hcov]

theorem TriFamilyIn.push {X : Finset (Sym2 {x // x ∈ S})} {T : Finset (Finset {x // x ∈ S})}
    (h : TriFamilyIn X T) :
    TriFamilyIn (pushEdges S X) (T.image (fun t => t.image Subtype.val)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rintro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    exact h.1 t ht
  · rintro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
    rw [cliqueEdges_image_val]
    exact pushEdges_mono (h.2.1 t ht)
  · rintro u hu u' hu' hne
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hu'
    have htt' : t ≠ t' := fun h => hne (by rw [h])
    rw [cliqueEdges_image_val, cliqueEdges_image_val]
    exact (Finset.disjoint_image (sym2val_injective S)).2 (h.2.2 t ht t' ht' htt')

/-! ### Parts and partitions -/

/-- A part `W ⊆ S`, viewed inside the subtype `↥S`. -/
def subPart (S : Finset V) (W : Finset V) : Finset {x // x ∈ S} := W.subtype (· ∈ S)

/-- A partition of `S`, viewed inside the subtype `↥S`. -/
def subParts (S : Finset V) (P : Finset (Finset V)) : Finset (Finset {x // x ∈ S}) :=
  P.image (subPart S)

@[simp] theorem mem_subPart {W : Finset V} {a : {x // x ∈ S}} :
    a ∈ subPart S W ↔ (a : V) ∈ W := Finset.mem_subtype

theorem image_val_subPart {W : Finset V} (hW : W ⊆ S) : (subPart S W).image Subtype.val = W := by
  ext x
  simp only [Finset.mem_image, mem_subPart]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ha
  · intro hx; exact ⟨⟨x, hW hx⟩, hx, rfl⟩

theorem card_subPart {W : Finset V} (hW : W ⊆ S) : (subPart S W).card = W.card := by
  conv_rhs => rw [← image_val_subPart hW]
  rw [Finset.card_image_of_injective _ Subtype.val_injective]

theorem subPart_injOn {P : Finset (Finset V)} (hP : ∀ W ∈ P, W ⊆ S) :
    Set.InjOn (subPart S) P := by
  intro W hW W' hW' h
  rw [← image_val_subPart (hP W hW), ← image_val_subPart (hP W' hW'), h]

theorem mem_subParts {P : Finset (Finset V)} {W : Finset V} (hW : W ∈ P) :
    subPart S W ∈ subParts S P := Finset.mem_image_of_mem _ hW

/-! ### The transported edge vocabulary -/

theorem edgesIn_pushEdges (X : Finset (Sym2 {x // x ∈ S})) (W : Finset V) :
    edgesIn (pushEdges S X) W = pushEdges S (edgesIn X (subPart S W)) := by
  ext e
  constructor
  · intro he
    obtain ⟨heP, hall⟩ := mem_edgesIn.1 he
    obtain ⟨f, hf, rfl⟩ := mem_pushEdges.1 heP
    refine mem_pushEdges.2 ⟨f, mem_edgesIn.2 ⟨hf, fun a ha => ?_⟩, rfl⟩
    exact mem_subPart.2 (hall (a : V) ((mem_sym2val_iff S f _).2 ⟨a, ha, rfl⟩))
  · intro he
    obtain ⟨f, hf, rfl⟩ := mem_pushEdges.1 he
    obtain ⟨hfX, hall⟩ := mem_edgesIn.1 hf
    refine mem_edgesIn.2 ⟨mem_pushEdges.2 ⟨f, hfX, rfl⟩, fun u hu => ?_⟩
    obtain ⟨a, ha, rfl⟩ := (mem_sym2val_iff S f u).1 hu
    exact mem_subPart.1 (hall a ha)

theorem crossParts_pushEdges (X : Finset (Sym2 {x // x ∈ S})) (P : Finset (Finset V)) :
    crossParts (pushEdges S X) P = pushEdges S (crossParts X (subParts S P)) := by
  have key : ∀ f : Sym2 {x // x ∈ S},
      (∃ W ∈ P, ∀ u ∈ sym2val S f, u ∈ W) ↔ ∃ W' ∈ subParts S P, ∀ a ∈ f, a ∈ W' := by
    intro f
    constructor
    · rintro ⟨W, hW, hall⟩
      exact ⟨subPart S W, mem_subParts hW,
        fun a ha => mem_subPart.2 (hall (a : V) ((mem_sym2val_iff S f _).2 ⟨a, ha, rfl⟩))⟩
    · rintro ⟨W', hW', hall⟩
      obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hW'
      refine ⟨W, hW, fun u hu => ?_⟩
      obtain ⟨a, ha, rfl⟩ := (mem_sym2val_iff S f u).1 hu
      exact mem_subPart.1 (hall a ha)
  ext e
  constructor
  · intro he
    obtain ⟨heP, hno⟩ := mem_crossParts.1 he
    obtain ⟨f, hf, rfl⟩ := mem_pushEdges.1 heP
    exact mem_pushEdges.2 ⟨f, mem_crossParts.2 ⟨hf, fun hc => hno ((key f).2 hc)⟩, rfl⟩
  · intro he
    obtain ⟨f, hf, rfl⟩ := mem_pushEdges.1 he
    obtain ⟨hfX, hno⟩ := mem_crossParts.1 hf
    exact mem_crossParts.2 ⟨mem_pushEdges.2 ⟨f, hfX, rfl⟩, fun hc => hno ((key f).1 hc)⟩

theorem nbhdIn_subEdges (E : Finset (Sym2 V)) (a : {x // x ∈ S}) {W : Finset V} (hW : W ⊆ S) :
    (nbhdIn (subEdges S E) a (subPart S W)).image Subtype.val = nbhdIn E (a : V) W := by
  ext y
  simp only [Finset.mem_image, mem_nbhdIn, mem_subPart]
  constructor
  · rintro ⟨b, ⟨hb, hab⟩, rfl⟩
    exact ⟨hb, by simpa [sym2val] using mem_subEdges.1 hab⟩
  · rintro ⟨hy, hay⟩
    exact ⟨⟨y, hW hy⟩, ⟨hy, mem_subEdges.2 (by simpa [sym2val] using hay)⟩, rfl⟩

theorem degTo_subEdges (E : Finset (Sym2 V)) (a : {x // x ∈ S}) {W : Finset V} (hW : W ⊆ S) :
    degTo (subEdges S E) a (subPart S W) = degTo E (a : V) W := by
  rw [degTo, degTo, ← nbhdIn_subEdges E a hW,
    Finset.card_image_of_injective _ Subtype.val_injective]

theorem isEquitablePartition_subParts {k : ℕ} {P : Finset (Finset V)}
    (h : IsEquitablePartition k P S) :
    IsEquitablePartition k (subParts S P) (Finset.univ : Finset {x // x ∈ S}) := by
  classical
  have hP : ∀ W ∈ P, W ⊆ S := fun W hW => h.subset_of_mem hW
  have hcard : (Finset.univ : Finset {x // x ∈ S}).card = S.card := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [subParts, Finset.card_image_of_injOn (subPart_injOn hP)]
    exact h.card_parts
  · rintro U hU U' hU' hne
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hU
    obtain ⟨W', hW', rfl⟩ := Finset.mem_image.1 hU'
    have hWW' : W ≠ W' := fun hc => hne (by rw [hc])
    refine Finset.disjoint_left.2 fun a ha ha' => ?_
    exact (Finset.disjoint_left.1 (h.pairwise_disjoint W hW W' hW' hWW'))
      (mem_subPart.1 ha) (mem_subPart.1 ha')
  · ext a
    simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true, id, subParts, Finset.mem_image]
    have ha : (a : V) ∈ P.biUnion id := by rw [h.cover]; exact a.2
    obtain ⟨W, hW, haW⟩ := Finset.mem_biUnion.1 ha
    exact ⟨subPart S W, ⟨W, hW, rfl⟩, mem_subPart.2 haW⟩
  · rintro U hU
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hU
    rw [card_subPart (hP W hW), hcard]
    exact h.size_lower W hW
  · rintro U hU
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hU
    rw [card_subPart (hP W hW), hcard]
    exact h.size_upper W hW

theorem isKDeltaPartition_subParts {k : ℕ} {d : ℝ} {P : Finset (Finset V)} {E : Finset (Sym2 V)}
    (h : IsKDeltaPartition k d P E S) :
    IsKDeltaPartition k d (subParts S P) (subEdges S E) (Finset.univ : Finset {x // x ∈ S}) := by
  refine ⟨isEquitablePartition_subParts h.1, ?_⟩
  rintro a - U hU
  obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hU
  have hWS : W ⊆ S := h.1.subset_of_mem hW
  rw [card_subPart hWS, degTo_subEdges E a hWS]
  exact h.2 (a : V) a.2 W hW

/-! ### The approximate-decomposition threshold on a vertex set -/

/-- **`BKLO.ApproxTriDecompMinDeg` on a vertex set.**  If the approximate-decomposition threshold
`δ_F^η` holds for `δ` (on a vertex type), then for every `η > 0` every large enough vertex set `S`
carrying an edge set `E ⊆ cliqueEdges S` of minimum degree at least `δ|S|` has an edge-disjoint
triangle family inside `E` leaving at most `η|S|²` edges of `E` uncovered. -/
theorem approxTriDecompMinDeg_set {δ : ℝ} (happ : ApproxTriDecompMinDeg δ) {η : ℝ} (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → (∀ v ∈ S, δ * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ T : Finset (Finset V), TriFamilyIn E T ∧
        ((E \ famEdges T).card : ℝ) ≤ η * (S.card : ℝ) ^ 2 := by
  classical
  obtain ⟨n₀, hn₀⟩ := happ η hη
  refine ⟨n₀, ?_⟩
  intro V _ E S hcard hE hdeg
  have hpush : pushEdges S (subEdges S E) = E := pushEdges_subEdges hE
  have hcardV : Fintype.card {x // x ∈ S} = S.card := card_coe_eq S
  have hloop : ∀ e ∈ subEdges S E, ¬ e.IsDiag :=
    loopless_subEdges (fun e he => (mem_cliqueEdgesV.1 (hE he)).2)
  have hdeg' : ∀ a : {x // x ∈ S},
      δ * (Fintype.card {x // x ∈ S} : ℝ) ≤ (edeg (subEdges S E) a : ℝ) := by
    intro a
    rw [hcardV, ← edeg_pushEdges (subEdges S E) a, hpush]
    exact hdeg (a : V) a.2
  obtain ⟨T', hT', hcardT'⟩ :=
    hn₀ (V := {x // x ∈ S}) (subEdges S E) (by rw [hcardV]; exact hcard) hloop hdeg'
  refine ⟨T'.image (fun t => t.image Subtype.val), ?_, ?_⟩
  · have h := hT'.push (S := S)
    rwa [hpush] at h
  · have hsdiff : E \ famEdges (T'.image (fun t => t.image Subtype.val))
        = pushEdges S (subEdges S E \ famEdges T') := by
      rw [pushEdges_sdiff, hpush, famEdges_push]
    rw [hsdiff, card_pushEdges]
    rw [hcardV] at hcardT'
    exact hcardT'

end BKLO
