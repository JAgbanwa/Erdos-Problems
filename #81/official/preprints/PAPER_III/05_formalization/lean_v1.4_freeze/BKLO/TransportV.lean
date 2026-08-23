/-
# Transporting the edge-set calculus to an arbitrary vertex type.

The absorber construction of §8.1 lives on `ℕ` (fresh vertices are needed).  The engine has to move
its output into the host graph `G` on a finite vertex type `V`, along an injective placement
`f : ℕ → V` of the finitely many vertices involved.  This file provides that transport, together
with the elementary divisibility calculus used by the assembly:

* `TriDecomp.mapOn`, `IsAbsorber.mapOn` — transport along a map injective on the support;
* `TriDecomp.biUnion` — a pairwise edge-disjoint union of decomposable sets is decomposable;
* `TriDecomp.triDivisible` — a decomposable edge set is triangle-divisible;
* `TriDivisible.sdiff` — divisibility passes to the difference of divisible sets;
* `triangleDecomposable_of_triDecomp` — a decomposition of `E(G)` as an abstract edge set is a
  triangle decomposition of `G`.
-/
import BKLO.Embedding
import BKLO.Absorber
import BKLO.Transport
import Mathlib.Tactic.Ring

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- Support of an edge set over an arbitrary vertex type. -/
def esupp (E : Finset (Sym2 V)) : Finset V := E.biUnion Sym2.toFinset

theorem mem_esupp {E : Finset (Sym2 V)} {v : V} : v ∈ esupp E ↔ ∃ e ∈ E, v ∈ e := by
  simp [esupp]

theorem mem_cliqueEdgesV {t : Finset V} {e : Sym2 V} :
    e ∈ cliqueEdges t ↔ (∀ x ∈ e, x ∈ t) ∧ ¬ e.IsDiag := by
  simp [cliqueEdges, Finset.mem_sym2_iff]

theorem cliqueEdges_mono {s t : Finset V} (h : s ⊆ t) : cliqueEdges s ⊆ cliqueEdges t := by
  intro e he
  rw [mem_cliqueEdgesV] at he ⊢
  exact ⟨fun x hx => h (he.1 x hx), he.2⟩

/-- The three edges of a `3`-set. -/
theorem cliqueEdges_card_three {t : Finset V} (h : t.card = 3) : (cliqueEdges t).card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 h
  have h3 : cliqueEdges ({a, b, c} : Finset V) = ({s(a,b), s(b,c), s(a,c)} : Finset (Sym2 V)) := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [mem_cliqueEdgesV, Sym2.mem_iff, Sym2.isDiag_iff_proj_eq, Finset.mem_insert,
        Finset.mem_singleton, Sym2.eq_iff]
      constructor
      · rintro ⟨h, hne⟩
        rcases h x (Or.inl rfl) with rfl | rfl | rfl <;>
          rcases h y (Or.inr rfl) with rfl | rfl | rfl <;> simp_all
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
          refine ⟨?_, ?_⟩ <;> simp_all <;> tauto
  rw [h3]
  rw [Finset.card_insert_of_notMem (by simp; tauto),
    Finset.card_insert_of_notMem (by simp; tauto)]
  simp

/-! ### Transport along an injective placement -/

omit [DecidableEq V] in
theorem sym2_map_inj_of_injOn {f : ℕ → V} {S : Finset ℕ}
    (hf : ∀ u ∈ S, ∀ v ∈ S, f u = f v → u = v)
    {e e' : Sym2 ℕ} (he : ∀ v ∈ e, v ∈ S) (he' : ∀ v ∈ e', v ∈ S)
    (h : Sym2.map f e = Sym2.map f e') : e = e' := by
  induction e using Sym2.ind with
  | _ x y =>
    induction e' using Sym2.ind with
    | _ a b =>
      have hx : x ∈ S := he x (by simp)
      have hy : y ∈ S := he y (by simp)
      have ha : a ∈ S := he' a (by simp)
      have hb : b ∈ S := he' b (by simp)
      simp only [Sym2.map_pair_eq, Sym2.eq_iff] at h ⊢
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hf x hx a ha h1, hf y hy b hb h2⟩
      · exact Or.inr ⟨hf x hx b hb h1, hf y hy a ha h2⟩

theorem cliqueEdges_image_injOn {f : ℕ → V} {t : Finset ℕ}
    (hf : ∀ u ∈ t, ∀ v ∈ t, f u = f v → u = v) :
    cliqueEdges (t.image f) = (cliqueEdges t).image (Sym2.map f) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [mem_cliqueEdgesV, Sym2.mem_iff, Sym2.isDiag_iff_proj_eq,
      Finset.mem_image]
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
            fun h => hne (hf a he.1 b he.2 h)⟩
        · exact ⟨by rintro z (rfl | rfl); exacts [⟨b, he.2, rfl⟩, ⟨a, he.1, rfl⟩],
            fun h => hne (hf a he.1 b he.2 h.symm)⟩

theorem triangle_subset_supp {E : Finset (Sym2 ℕ)} {t : Finset ℕ} (h3 : t.card = 3)
    (hsub : cliqueEdges t ⊆ E) : ∀ v ∈ t, v ∈ supp E := by
  intro v hv
  obtain ⟨u, hu, hne⟩ : ∃ u ∈ t, u ≠ v := by
    by_contra hcon
    push_neg at hcon
    have hsing : t ⊆ {v} := fun x hx => Finset.mem_singleton.2 (hcon x hx)
    have := Finset.card_le_card hsing
    simp [h3] at this
  refine mem_supp.2 ⟨s(u, v), hsub (mem_cliqueEdges.2 ⟨?_, ?_⟩), by simp⟩
  · rintro z hz
    simp only [Sym2.mem_iff] at hz
    rcases hz with rfl | rfl <;> assumption
  · simpa [Sym2.isDiag_iff_proj_eq] using hne

/-- **Transport.** Triangle-decomposability moves along a placement injective on the support. -/
theorem TriDecomp.mapOn {f : ℕ → V} {E : Finset (Sym2 ℕ)}
    (hf : ∀ u ∈ supp E, ∀ v ∈ supp E, f u = f v → u = v) (h : TriDecomp E) :
    TriDecomp (E.image (Sym2.map f)) := by
  classical
  obtain ⟨P, hc, hd, he⟩ := h
  have hsub : ∀ t ∈ P, cliqueEdges t ⊆ E := by
    intro t ht; rw [← he]; exact Finset.subset_biUnion_of_mem cliqueEdges ht
  have htsupp : ∀ t ∈ P, ∀ v ∈ t, v ∈ supp E := fun t ht => triangle_subset_supp (hc t ht) (hsub t ht)
  have hfinj : ∀ t ∈ P, ∀ u ∈ t, ∀ v ∈ t, f u = f v → u = v := fun t ht u hu v hv =>
    hf u (htsupp t ht u hu) v (htsupp t ht v hv)
  refine ⟨P.image (fun t => t.image f), ?_, ?_, ?_⟩
  · rintro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    rw [Finset.card_image_of_injOn (fun u hu v hv => hfinj s hs u hu v hv), hc s hs]
  · rintro t ht t' ht' hne
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 ht'
    have hss' : s ≠ s' := by rintro rfl; exact hne rfl
    rw [cliqueEdges_image_injOn (fun u hu v hv => hfinj s hs u hu v hv),
      cliqueEdges_image_injOn (fun u hu v hv => hfinj s' hs' u hu v hv)]
    rw [Finset.disjoint_left]
    rintro e hein hein'
    obtain ⟨e₁, he₁, rfl⟩ := Finset.mem_image.1 hein
    obtain ⟨e₂, he₂, heq⟩ := Finset.mem_image.1 hein'
    have h1 : ∀ v ∈ e₁, v ∈ supp E := fun v hv =>
      mem_supp.2 ⟨e₁, hsub s hs he₁, hv⟩
    have h2 : ∀ v ∈ e₂, v ∈ supp E := fun v hv =>
      mem_supp.2 ⟨e₂, hsub s' hs' he₂, hv⟩
    have : e₂ = e₁ := sym2_map_inj_of_injOn hf h2 h1 heq
    subst this
    exact (Finset.disjoint_left.1 (hd s hs s' hs' hss') he₁) he₂
  · rw [← he]
    simp only [famEdges]
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨t, ⟨s, hs, rfl⟩, hmem⟩
      rw [cliqueEdges_image_injOn (fun u hu v hv => hfinj s hs u hu v hv)] at hmem
      obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 hmem
      exact ⟨e', ⟨s, hs, he'⟩, rfl⟩
    · rintro ⟨e', ⟨s, hs, he'⟩, rfl⟩
      exact ⟨s.image f, ⟨s, hs, rfl⟩, by
        rw [cliqueEdges_image_injOn (fun u hu v hv => hfinj s hs u hu v hv)]
        exact Finset.mem_image_of_mem _ he'⟩

/-- **Transport of absorbers.** -/
theorem IsAbsorber.mapOn {f : ℕ → V} {A H : Finset (Sym2 ℕ)}
    (hf : ∀ u ∈ supp (A ∪ H), ∀ v ∈ supp (A ∪ H), f u = f v → u = v)
    (h : IsAbsorber A H) : IsAbsorber (A.image (Sym2.map f)) (H.image (Sym2.map f)) := by
  classical
  obtain ⟨hd, hA, hAH⟩ := h
  have hsuppA : supp A ⊆ supp (A ∪ H) := supp_mono Finset.subset_union_left
  have hsuppH : supp H ⊆ supp (A ∪ H) := supp_mono Finset.subset_union_right
  refine ⟨?_, TriDecomp.mapOn (fun u hu v hv => hf u (hsuppA hu) v (hsuppA hv)) hA, ?_⟩
  · rw [Finset.disjoint_left]
    rintro e heA heH
    obtain ⟨e₁, he₁, rfl⟩ := Finset.mem_image.1 heA
    obtain ⟨e₂, he₂, heq⟩ := Finset.mem_image.1 heH
    have h1 : ∀ v ∈ e₁, v ∈ supp (A ∪ H) := fun v hv =>
      mem_supp.2 ⟨e₁, Finset.mem_union_left _ he₁, hv⟩
    have h2 : ∀ v ∈ e₂, v ∈ supp (A ∪ H) := fun v hv =>
      mem_supp.2 ⟨e₂, Finset.mem_union_right _ he₂, hv⟩
    have : e₂ = e₁ := sym2_map_inj_of_injOn hf h2 h1 heq
    subst this
    exact (Finset.disjoint_left.1 hd he₁) he₂
  · have := TriDecomp.mapOn hf hAH
    rwa [Finset.image_union] at this

/-! ### Unions -/

theorem TriDecomp.biUnion {ι : Type*} [DecidableEq ι] {s : Finset ι} {E : ι → Finset (Sym2 V)}
    (hdec : ∀ i ∈ s, TriDecomp (E i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (E i) (E j)) :
    TriDecomp (s.biUnion E) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using triDecomp_empty
  | insert a s ha ih =>
    rw [Finset.biUnion_insert]
    have hdec' : ∀ i ∈ s, TriDecomp (E i) := fun i hi => hdec i (Finset.mem_insert_of_mem hi)
    have hdisj' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (E i) (E j) :=
      fun i hi j hj => hdisj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    refine TriDecomp.union ?_ (hdec a (Finset.mem_insert_self a s)) (ih hdec' hdisj')
    rw [Finset.disjoint_biUnion_right]
    intro i hi
    exact hdisj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
      (fun h => ha (h ▸ hi))

/-! ### Divisibility -/

/-- The number of edges of `E` at `v`. -/
def edeg (E : Finset (Sym2 V)) (v : V) : ℕ := (E.filter (fun e => v ∈ e)).card

theorem triDivisible_iff {E : Finset (Sym2 V)} :
    TriDivisible E ↔ (∀ v : V, Even (edeg E v)) ∧ 3 ∣ E.card := Iff.rfl

theorem edeg_cliqueEdges {t : Finset V} (h3 : t.card = 3) (v : V) :
    edeg (cliqueEdges t) v = if v ∈ t then 2 else 0 := by
  classical
  by_cases hv : v ∈ t
  · rw [if_pos hv]
    have hcard : (t.erase v).card = 2 := by rw [Finset.card_erase_of_mem hv, h3]
    have hfil : (cliqueEdges t).filter (fun e => v ∈ e) = (t.erase v).image (fun u => s(v, u)) := by
      ext e
      induction e using Sym2.ind with
      | _ p q =>
        simp only [Finset.mem_filter, mem_cliqueEdgesV, Sym2.mem_iff, Sym2.isDiag_iff_proj_eq,
          Finset.mem_image, Finset.mem_erase, Sym2.eq_iff]
        constructor
        · rintro ⟨⟨hmem, hne⟩, hvpq⟩
          rcases hvpq with rfl | rfl
          · exact ⟨q, ⟨fun h => hne h.symm, hmem q (Or.inr rfl)⟩, Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨p, ⟨fun h => hne h, hmem p (Or.inl rfl)⟩, Or.inr ⟨rfl, rfl⟩⟩
        · rintro ⟨u, ⟨hu1, hu2⟩, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
          · refine ⟨⟨?_, ?_⟩, Or.inl rfl⟩
            · rintro z (rfl | rfl)
              exacts [hv, hu2]
            · exact fun h => hu1 h.symm
          · refine ⟨⟨?_, ?_⟩, Or.inr rfl⟩
            · rintro z (rfl | rfl)
              exacts [hu2, hv]
            · exact fun h => hu1 h
    have hinj : Set.InjOn (fun u => s(v, u)) (t.erase v) := by
      intro a _ b _ hab
      simp only [Sym2.eq_iff] at hab
      rcases hab with ⟨_, h⟩ | ⟨h1, h2⟩
      · exact h
      · exact h2.trans h1
    rw [edeg, hfil, Finset.card_image_of_injOn hinj, hcard]
  · rw [if_neg hv, edeg]
    have : (cliqueEdges t).filter (fun e => v ∈ e) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun e he hve => hv ?_
      exact (mem_cliqueEdgesV.1 he).1 v hve
    rw [this, Finset.card_empty]

/-- A triangle-decomposable edge set is triangle-divisible. -/
theorem TriDecomp.triDivisible {E : Finset (Sym2 V)} (h : TriDecomp E) : TriDivisible E := by
  classical
  obtain ⟨P, hc, hd, he⟩ := h
  subst he
  constructor
  · intro v
    have : edeg (famEdges P) v = ∑ t ∈ P, edeg (cliqueEdges t) v := by
      unfold edeg famEdges
      rw [Finset.filter_biUnion]
      refine Finset.card_biUnion ?_
      intro x hx y hy hxy
      exact Finset.disjoint_filter_filter (hd x hx y hy hxy)
    have hsum : ∑ t ∈ P, edeg (cliqueEdges t) v = 2 * (P.filter (fun t => v ∈ t)).card := by
      rw [Finset.sum_congr rfl (fun t ht => edeg_cliqueEdges (hc t ht) v)]
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
      simp [Nat.mul_comm]
    show Even (edeg (famEdges P) v)
    rw [this, hsum]
    exact ⟨(P.filter (fun t => v ∈ t)).card, by ring⟩
  · unfold famEdges
    rw [Finset.card_biUnion (fun x hx y hy hxy => hd x hx y hy hxy)]
    have : ∑ t ∈ P, (cliqueEdges t).card = ∑ t ∈ P, 3 :=
      Finset.sum_congr rfl (fun t ht => cliqueEdges_card_three (hc t ht))
    rw [this]
    simp [Finset.sum_const]

/-- Divisibility passes to the difference. -/
theorem TriDivisible.sdiff {E A : Finset (Sym2 V)} (hAE : A ⊆ E) (hE : TriDivisible E)
    (hA : TriDivisible A) : TriDivisible (E \ A) := by
  classical
  refine ⟨fun v => ?_, ?_⟩
  · have hsub : A.filter (fun e => v ∈ e) ⊆ E.filter (fun e => v ∈ e) :=
      Finset.filter_subset_filter _ hAE
    have hcard : ((E \ A).filter (fun e => v ∈ e)).card
        = (E.filter (fun e => v ∈ e)).card - (A.filter (fun e => v ∈ e)).card := by
      have hsplit : (E \ A).filter (fun e => v ∈ e)
          = E.filter (fun e => v ∈ e) \ A.filter (fun e => v ∈ e) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
      rw [hsplit]
      exact Finset.card_sdiff_of_subset hsub
    have h1 := hE.1 v
    have h2 := hA.1 v
    have h3 := Finset.card_le_card hsub
    rw [hcard]
    rcases h1 with ⟨k, hk⟩
    rcases h2 with ⟨m, hm⟩
    exact ⟨k - m, by omega⟩
  · have hcd : (E \ A).card = E.card - A.card := Finset.card_sdiff_of_subset hAE
    rw [hcd]
    obtain ⟨k, hk⟩ := hE.2
    obtain ⟨m, hm⟩ := hA.2
    have hle : A.card ≤ E.card := Finset.card_le_card hAE
    exact ⟨k - m, by omega⟩

/-- Divisibility transports back along an injective placement. -/
theorem triDivisible_of_image {f : ℕ → V} {H : Finset (Sym2 ℕ)}
    (hinj : ∀ u ∈ supp H, ∀ v ∈ supp H, f u = f v → u = v)
    (h : TriDivisible (H.image (Sym2.map f))) : TriDivisible H := by
  classical
  have hmapinj : ∀ e ∈ H, ∀ e' ∈ H, Sym2.map f e = Sym2.map f e' → e = e' := by
    intro e he e' he' heq
    exact sym2_map_inj_of_injOn hinj (fun v hv => mem_supp.2 ⟨e, he, hv⟩)
      (fun v hv => mem_supp.2 ⟨e', he', hv⟩) heq
  refine ⟨fun v => ?_, ?_⟩
  · by_cases hv : v ∈ supp H
    · have hcongr : H.filter (fun e => f v ∈ Sym2.map f e) = H.filter (fun e => v ∈ e) := by
        refine Finset.filter_congr fun e he => ?_
        constructor
        · intro hfve
          obtain ⟨u, hu, hfu⟩ := Sym2.mem_map.1 hfve
          have : u = v := hinj u (mem_supp.2 ⟨e, he, hu⟩) v hv hfu
          exact this ▸ hu
        · intro hve
          exact Sym2.mem_map.2 ⟨v, hve, rfl⟩
      have hbij : ((H.image (Sym2.map f)).filter (fun e => f v ∈ e)).card
          = (H.filter (fun e => v ∈ e)).card := by
        rw [Finset.filter_image, hcongr]
        refine Finset.card_image_of_injOn ?_
        intro e he e' he' heq
        exact hmapinj e (Finset.mem_filter.1 he).1 e' (Finset.mem_filter.1 he').1 heq
      rw [← hbij]
      exact h.1 (f v)
    · have : H.filter (fun e => v ∈ e) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun e he hve => hv (mem_supp.2 ⟨e, he, hve⟩)
      simp [this]
  · have : (H.image (Sym2.map f)).card = H.card := Finset.card_image_of_injOn hmapinj
    rw [← this]
    exact h.2

variable [Fintype V]

/-- Divisibility of a graph, in the edge-set language. -/
theorem triDivisible_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : 3 ∣ G.edgeFinset.card) (heven : ∀ v, Even (G.degree v)) :
    TriDivisible G.edgeFinset := by
  refine ⟨fun v => ?_, h3⟩
  have : G.edgeFinset.filter (fun e => v ∈ e) = G.incidenceFinset v :=
    (G.incidenceFinset_eq_filter v).symm
  rw [this, G.card_incidenceFinset_eq_degree v]
  exact heven v

/-- A decomposition of the edge set of `G` into abstract triangles is a triangle decomposition
of `G`. -/
theorem triangleDecomposable_of_triDecomp (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : TriDecomp G.edgeFinset) : TriangleDecomposable G := by
  classical
  obtain ⟨P, hc, hd, he⟩ := h
  have hsub : ∀ t ∈ P, cliqueEdges t ⊆ G.edgeFinset := by
    intro t ht; rw [← he]; exact Finset.subset_biUnion_of_mem cliqueEdges ht
  refine ⟨P, fun t ht => ?_, fun e hee => ?_⟩
  · refine ⟨?_, hc t ht⟩
    intro x hx y hy hxy
    have hmem : s(x, y) ∈ cliqueEdges t := by
      refine mem_cliqueEdgesV.2 ⟨?_, ?_⟩
      · rintro z hz
        simp only [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl <;> assumption
      · simpa [Sym2.isDiag_iff_proj_eq] using hxy
    have hEd := hsub t ht hmem
    rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hEd
  · rw [← he] at hee
    obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.1 hee
    refine ⟨t, ⟨ht, het⟩, ?_⟩
    rintro t' ⟨ht', het'⟩
    by_contra hne
    exact (Finset.disjoint_left.1 (hd t' ht' t ht hne)) het' het

end BKLO
