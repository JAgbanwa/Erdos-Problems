/-
# Core edge-set utilities for the absorber construction (BKLO §8.1).

The absorber construction of `BKLO.AbsorberExists` works in the edge-set model of
`BKLO.Transformer`, over the **infinite** vertex set `ℕ`: this is what makes *fresh vertices*
available, which the F-expansion construction of BKLO §8.1 genuinely needs (a triangle-divisible
graph need not have an absorber on its own vertex set).

This file collects the elementary tools:

* `supp` — the vertices used by an edge set, and the two "height" predicates `Below` / `Touches`
  that drive all edge-disjointness bookkeeping (fresh vertices are *large* naturals);
* `triDecomp_tri` — a single triangle is triangle-decomposable, the atom of every construction;
* `TriDecomp.map` — triangle-decomposability transports along an injective relabelling of the
  vertices (used to place the explicit finite gadgets on arbitrary fresh vertices);
* `Covers`, `isTransformer_of_covers`, `isAbsorber_of_covers` — the two composition patterns:
  *two consecutive covers form a transformer*, and *a cover plus an absorber of the covering set
  is an absorber*.
-/
import BKLO.Transformer
import BKLO.Absorber

open Finset

namespace BKLO

/-! ### Support of an edge set -/

/-- The set of vertices incident to some edge of `E`. -/
def supp (E : Finset (Sym2 ℕ)) : Finset ℕ := E.biUnion Sym2.toFinset

@[simp] theorem mem_supp {E : Finset (Sym2 ℕ)} {v : ℕ} :
    v ∈ supp E ↔ ∃ e ∈ E, v ∈ e := by
  simp [supp]

@[simp] theorem supp_empty : supp (∅ : Finset (Sym2 ℕ)) = ∅ := by simp [supp]

theorem supp_union (A B : Finset (Sym2 ℕ)) : supp (A ∪ B) = supp A ∪ supp B := by
  ext v; simp only [mem_supp, Finset.mem_union]; aesop

theorem supp_mono {A B : Finset (Sym2 ℕ)} (h : A ⊆ B) : supp A ⊆ supp B := by
  intro v hv
  simp only [mem_supp] at hv ⊢
  obtain ⟨e, he, hv⟩ := hv
  exact ⟨e, h he, hv⟩

/-- All vertices of `E` are `< b`. -/
def Below (b : ℕ) (E : Finset (Sym2 ℕ)) : Prop := ∀ v ∈ supp E, v < b

/-- Every edge of `A` has an endpoint `≥ b`. -/
def Touches (b : ℕ) (A : Finset (Sym2 ℕ)) : Prop := ∀ e ∈ A, ∃ v ∈ e, b ≤ v

theorem Below.mono {b : ℕ} {A B : Finset (Sym2 ℕ)} (h : A ⊆ B) (hB : Below b B) : Below b A :=
  fun _ hv => hB _ (supp_mono h hv)

theorem Below.mono_le {b c : ℕ} {A : Finset (Sym2 ℕ)} (hbc : b ≤ c) (h : Below b A) :
    Below c A := fun v hv => lt_of_lt_of_le (h v hv) hbc

theorem Touches.mono {b : ℕ} {A B : Finset (Sym2 ℕ)} (h : A ⊆ B) (hB : Touches b B) :
    Touches b A := fun e he => hB e (h he)

theorem Touches.mono_le {b c : ℕ} {A : Finset (Sym2 ℕ)} (hcb : c ≤ b) (h : Touches b A) :
    Touches c A := fun e he => by
  obtain ⟨v, hv, hle⟩ := h e he
  exact ⟨v, hv, le_trans hcb hle⟩

theorem Below.union {b : ℕ} {A B : Finset (Sym2 ℕ)} (hA : Below b A) (hB : Below b B) :
    Below b (A ∪ B) := by
  intro v hv
  rw [supp_union, Finset.mem_union] at hv
  rcases hv with h | h
  · exact hA v h
  · exact hB v h

theorem Touches.union {b : ℕ} {A B : Finset (Sym2 ℕ)} (hA : Touches b A) (hB : Touches b B) :
    Touches b (A ∪ B) := by
  intro e he
  rcases Finset.mem_union.1 he with h | h
  · exact hA e h
  · exact hB e h

theorem Touches.empty (b : ℕ) : Touches b (∅ : Finset (Sym2 ℕ)) := by simp [Touches]

theorem Below.empty (b : ℕ) : Below b (∅ : Finset (Sym2 ℕ)) := by simp [Below]

/-- The basic disjointness engine: an edge set whose every edge reaches above `b` is disjoint
from an edge set living entirely below `b`. -/
theorem disjoint_of_touches_below {b : ℕ} {A B : Finset (Sym2 ℕ)}
    (hA : Touches b A) (hB : Below b B) : Disjoint A B := by
  rw [Finset.disjoint_left]
  intro e heA heB
  obtain ⟨v, hv, hle⟩ := hA e heA
  exact absurd (hB v (mem_supp.2 ⟨e, heB, hv⟩)) (by omega)

theorem below_of_supp_subset {b : ℕ} {E : Finset (Sym2 ℕ)} (h : ∀ v ∈ supp E, v < b) :
    Below b E := h

/-! ### A triangle -/

theorem mem_cliqueEdges {t : Finset ℕ} {e : Sym2 ℕ} :
    e ∈ cliqueEdges t ↔ (∀ x ∈ e, x ∈ t) ∧ ¬ e.IsDiag := by
  simp [cliqueEdges, Finset.mem_sym2_iff]

theorem cliqueEdges_triple {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cliqueEdges ({a, b, c} : Finset ℕ) = ({s(a,b), s(b,c), s(a,c)} : Finset (Sym2 ℕ)) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [mem_cliqueEdges, Sym2.mem_iff, Sym2.isDiag_iff_proj_eq, Finset.mem_insert,
      Finset.mem_singleton, Sym2.eq_iff]
    constructor
    · rintro ⟨h, hne⟩
      rcases h x (Or.inl rfl) with rfl | rfl | rfl <;> rcases h y (Or.inr rfl) with rfl | rfl | rfl <;>
        simp_all
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        refine ⟨?_, ?_⟩ <;> simp_all <;> tauto

/-- **The atom.** The three edges of a triangle form a triangle-decomposable edge set. -/
theorem triDecomp_tri {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    TriDecomp ({s(a,b), s(b,c), s(a,c)} : Finset (Sym2 ℕ)) := by
  refine ⟨{({a, b, c} : Finset ℕ)}, ?_, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_singleton] at ht
    subst ht
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc])]
    simp
  · simp
  · simp [famEdges, cliqueEdges_triple hab hbc hac]

/-! ### Relabelling vertices -/

theorem cliqueEdges_image {f : ℕ → ℕ} (hf : Function.Injective f) (t : Finset ℕ) :
    cliqueEdges (t.image f) = (cliqueEdges t).image (Sym2.map f) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [mem_cliqueEdges, Sym2.mem_iff, Sym2.isDiag_iff_proj_eq, Finset.mem_image]
    constructor
    · rintro ⟨h, hne⟩
      obtain ⟨a, ha, rfl⟩ := h x (Or.inl rfl)
      obtain ⟨b, hb, rfl⟩ := h y (Or.inr rfl)
      refine ⟨s(a, b), ⟨?_, ?_⟩, by simp⟩
      · rintro z hz
        simp only [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl <;> assumption
      · simpa using fun h => hne (by rw [h])
    · rintro ⟨e, ⟨he, hne⟩, heq⟩
      induction e using Sym2.ind with
      | _ a b =>
        simp only [Sym2.map_pair_eq, Sym2.eq_iff] at heq
        simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at he
        simp only [Sym2.isDiag_iff_proj_eq] at hne
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨by rintro z (rfl | rfl); exacts [⟨a, he.1, rfl⟩, ⟨b, he.2, rfl⟩],
            fun h => hne (hf h)⟩
        · exact ⟨by rintro z (rfl | rfl); exacts [⟨b, he.2, rfl⟩, ⟨a, he.1, rfl⟩],
            fun h => hne (hf h).symm⟩

/-- **Transport.** Triangle-decomposability is preserved by an injective relabelling of the
vertices. -/
theorem TriDecomp.map {f : ℕ → ℕ} (hf : Function.Injective f) {E : Finset (Sym2 ℕ)}
    (h : TriDecomp E) : TriDecomp (E.image (Sym2.map f)) := by
  obtain ⟨P, hc, hd, he⟩ := h
  refine ⟨P.image (fun t => t.image f), ?_, ?_, ?_⟩
  · rintro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    rw [Finset.card_image_of_injective _ hf, hc s hs]
  · rintro t ht t' ht' hne
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 ht'
    have hss' : s ≠ s' := by rintro rfl; exact hne rfl
    rw [cliqueEdges_image hf, cliqueEdges_image hf]
    exact (Finset.disjoint_image (Sym2.map.injective hf)).2 (hd s hs s' hs' hss')
  · rw [← he]
    simp only [famEdges]
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨t, ⟨s, hs, rfl⟩, hmem⟩
      rw [cliqueEdges_image hf] at hmem
      obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 hmem
      exact ⟨e', ⟨s, hs, he'⟩, rfl⟩
    · rintro ⟨e', ⟨s, hs, he'⟩, rfl⟩
      exact ⟨s.image f, ⟨s, hs, rfl⟩, by
        rw [cliqueEdges_image hf]; exact Finset.mem_image_of_mem _ he'⟩

/-! ### Covers, transformers and absorbers -/

/-- `T` **covers** `C`: `T` is edge-disjoint from `C` and `T ∪ C` is triangle-decomposable.
(In BKLO's language `T` is "half a transformer".) -/
def Covers (T C : Finset (Sym2 ℕ)) : Prop := Disjoint T C ∧ TriDecomp (T ∪ C)

/-- **Two consecutive covers make a transformer.**  If `B` covers `A` and `C` covers `B`, then
`B` is an `(A, C)`-transformer.  This is the engine that lets a chain of reductions be composed:
a single cover flips the residue of the edge count mod 3, two covers preserve it. -/
theorem isTransformer_of_covers {A B C : Finset (Sym2 ℕ)}
    (h1 : Covers B A) (h2 : Covers C B) : IsTransformer B A C :=
  ⟨h1.1, h2.1.symm, h1.2, by rw [Finset.union_comm]; exact h2.2⟩

/-- **A cover plus an absorber of the covering set is an absorber.** -/
theorem isAbsorber_of_covers {T C A' : Finset (Sym2 ℕ)}
    (hcov : Covers T C) (hA' : IsAbsorber A' T) (hdisj : Disjoint A' C) :
    IsAbsorber (T ∪ A') C := by
  obtain ⟨hTC, hdec⟩ := hcov
  obtain ⟨hA'T, hA'dec, hA'Tdec⟩ := hA'
  refine ⟨Finset.disjoint_union_left.mpr ⟨hTC, hdisj⟩, ?_, ?_⟩
  · rw [Finset.union_comm]; exact hA'Tdec
  · have hd : Disjoint (T ∪ C) A' :=
      Finset.disjoint_union_left.mpr ⟨hA'T.symm, hdisj.symm⟩
    have := TriDecomp.union hd hdec hA'dec
    convert this using 1
    ext x; simp only [Finset.mem_union]; tauto

/-- Union of two covers on edge-disjoint parts. -/
theorem Covers.union {T₁ C₁ T₂ C₂ : Finset (Sym2 ℕ)} (h1 : Covers T₁ C₁) (h2 : Covers T₂ C₂)
    (d1 : Disjoint (T₁ ∪ C₁) (T₂ ∪ C₂)) : Covers (T₁ ∪ T₂) (C₁ ∪ C₂) := by
  obtain ⟨hd1, hdec1⟩ := h1
  obtain ⟨hd2, hdec2⟩ := h2
  have hT₁C₂ : Disjoint T₁ C₂ :=
    ((Finset.disjoint_union_left.1 d1).1.mono_right Finset.subset_union_right)
  have hT₂C₁ : Disjoint T₂ C₁ :=
    (((Finset.disjoint_union_right.1 ((Finset.disjoint_union_left.1 d1).2)).1).symm)
  refine ⟨Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨hd1, hT₁C₂⟩,
       Finset.disjoint_union_right.mpr ⟨hT₂C₁, hd2⟩⟩, ?_⟩
  have := TriDecomp.union d1 hdec1 hdec2
  convert this using 1
  ext x; simp only [Finset.mem_union]; tauto

/-- Union of two transformers on edge-disjoint parts. -/
theorem isTransformer_union {T₁ H₁ H₁' T₂ H₂ H₂' : Finset (Sym2 ℕ)}
    (h1 : IsTransformer T₁ H₁ H₁') (h2 : IsTransformer T₂ H₂ H₂')
    (d1 : Disjoint (T₁ ∪ H₁ ∪ H₁') (T₂ ∪ H₂ ∪ H₂')) :
    IsTransformer (T₁ ∪ T₂) (H₁ ∪ H₂) (H₁' ∪ H₂') := by
  obtain ⟨d11, d12, dec11, dec12⟩ := h1
  obtain ⟨d21, d22, dec21, dec22⟩ := h2
  have hsub : ∀ {X Y : Finset (Sym2 ℕ)}, X ⊆ T₁ ∪ H₁ ∪ H₁' → Y ⊆ T₂ ∪ H₂ ∪ H₂' → Disjoint X Y :=
    fun hX hY => Finset.disjoint_of_subset_left hX (Finset.disjoint_of_subset_right hY d1)
  have s1 : T₁ ⊆ T₁ ∪ H₁ ∪ H₁' := by intro x hx; simp only [Finset.mem_union]; tauto
  have s2 : H₁ ⊆ T₁ ∪ H₁ ∪ H₁' := by intro x hx; simp only [Finset.mem_union]; tauto
  have s3 : H₁' ⊆ T₁ ∪ H₁ ∪ H₁' := by intro x hx; simp only [Finset.mem_union]; tauto
  have s4 : T₂ ⊆ T₂ ∪ H₂ ∪ H₂' := by intro x hx; simp only [Finset.mem_union]; tauto
  have s5 : H₂ ⊆ T₂ ∪ H₂ ∪ H₂' := by intro x hx; simp only [Finset.mem_union]; tauto
  have s6 : H₂' ⊆ T₂ ∪ H₂ ∪ H₂' := by intro x hx; simp only [Finset.mem_union]; tauto
  have s7 : T₁ ∪ H₁ ⊆ T₁ ∪ H₁ ∪ H₁' := by intro x hx; simp only [Finset.mem_union] at hx ⊢; tauto
  have s8 : T₁ ∪ H₁' ⊆ T₁ ∪ H₁ ∪ H₁' := by intro x hx; simp only [Finset.mem_union] at hx ⊢; tauto
  have s9 : T₂ ∪ H₂ ⊆ T₂ ∪ H₂ ∪ H₂' := by intro x hx; simp only [Finset.mem_union] at hx ⊢; tauto
  have s10 : T₂ ∪ H₂' ⊆ T₂ ∪ H₂ ∪ H₂' := by
    intro x hx; simp only [Finset.mem_union] at hx ⊢; tauto
  have hT₁H₂ : Disjoint T₁ H₂ := hsub s1 s5
  have hT₂H₁ : Disjoint T₂ H₁ := (hsub s2 s4).symm
  have hT₁H₂' : Disjoint T₁ H₂' := hsub s1 s6
  have hT₂H₁' : Disjoint T₂ H₁' := (hsub s3 s4).symm
  refine ⟨Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨d11, hT₁H₂⟩,
       Finset.disjoint_union_right.mpr ⟨hT₂H₁, d21⟩⟩,
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨d12, hT₁H₂'⟩,
       Finset.disjoint_union_right.mpr ⟨hT₂H₁', d22⟩⟩, ?_, ?_⟩
  · have hd : Disjoint (T₁ ∪ H₁) (T₂ ∪ H₂) := hsub s7 s9
    have := TriDecomp.union hd dec11 dec21
    convert this using 1
    ext x; simp only [Finset.mem_union]; tauto
  · have hd : Disjoint (T₁ ∪ H₁') (T₂ ∪ H₂') := hsub s8 s10
    have := TriDecomp.union hd dec12 dec22
    convert this using 1
    ext x; simp only [Finset.mem_union]; tauto

end BKLO
