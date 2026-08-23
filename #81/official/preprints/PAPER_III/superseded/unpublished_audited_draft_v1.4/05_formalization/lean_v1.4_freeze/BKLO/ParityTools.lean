/-
# Parity tools for §9 (`r = 2`, `F = K₃`)

Elementary counting facts about the edge-set model (`Finset (Sym2 V)`) that the parity arguments
of BKLO §9 need:

* `degTo_union_edges` / `degTo_union_sets` — additivity of `d_E(x, W)` in the edge set and in the
  target set;
* `edeg_eq_degTo_of_supp` — for a graph supported inside `S`, the degree of `x` equals `d_E(x, S)`;
* `sum_degTo_self_even` — the handshake lemma: `∑_{u ∈ A} d_E(u, A)` is even;
* `even_edeg_of_sdiff` — if `E' ⊆ E` and both `E` and `E \ E'` have even degrees, so has `E'`.

Everything here is `sorry`-free.
-/
import BKLO.Section1012Defs

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- Neighbourhoods add over a disjoint union of edge sets. -/
theorem nbhdIn_union_edges (X Y : Finset (Sym2 V)) (u : V) (W : Finset V) :
    nbhdIn (X ∪ Y) u W = nbhdIn X u W ∪ nbhdIn Y u W := by
  ext y
  simp only [mem_nbhdIn, Finset.mem_union]
  tauto

/-- Degrees add over a disjoint union of edge sets. -/
theorem degTo_union_edges {X Y : Finset (Sym2 V)} (h : Disjoint X Y) (u : V) (W : Finset V) :
    degTo (X ∪ Y) u W = degTo X u W + degTo Y u W := by
  classical
  have hd : Disjoint (nbhdIn X u W) (nbhdIn Y u W) := by
    refine Finset.disjoint_left.2 fun y hy hy' => ?_
    exact (Finset.disjoint_left.1 h (mem_nbhdIn.1 hy).2) (mem_nbhdIn.1 hy').2
  rw [degTo, nbhdIn_union_edges, Finset.card_union_of_disjoint hd]
  rfl

/-- Degrees add over a disjoint union of target sets. -/
theorem degTo_union_sets (E : Finset (Sym2 V)) (u : V) {A B : Finset V} (h : Disjoint A B) :
    degTo E u (A ∪ B) = degTo E u A + degTo E u B := by
  classical
  have hd : Disjoint (nbhdIn E u A) (nbhdIn E u B) :=
    Finset.disjoint_of_subset_left (nbhdIn_subset E u A)
      (Finset.disjoint_of_subset_right (nbhdIn_subset E u B) h)
  have hu : nbhdIn E u (A ∪ B) = nbhdIn E u A ∪ nbhdIn E u B := by
    ext y; simp only [mem_nbhdIn, Finset.mem_union]; tauto
  rw [degTo, hu, Finset.card_union_of_disjoint hd]
  rfl

/-- For a graph all of whose edges have both ends in `S`, the degree of `u` is `d_E(u, S)`. -/
theorem edeg_eq_degTo_of_supp {E : Finset (Sym2 V)} {S : Finset V}
    (hsupp : ∀ e ∈ E, ∀ v ∈ e, v ∈ S) (u : V) : edeg E u = degTo E u S := by
  classical
  have himg : (nbhdIn E u S).image (fun y => s(u, y)) = E.filter (fun e => u ∈ e) := by
    ext e
    constructor
    · intro he
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 he
      exact Finset.mem_filter.2 ⟨(mem_nbhdIn.1 hy).2, by simp⟩
    · intro he
      obtain ⟨heE, hue⟩ := Finset.mem_filter.1 he
      induction e using Sym2.ind with
      | _ p q =>
        simp only [Sym2.mem_iff] at hue
        rcases hue with rfl | rfl
        · exact Finset.mem_image.2 ⟨q, mem_nbhdIn.2 ⟨hsupp _ heE q (by simp), heE⟩, rfl⟩
        · refine Finset.mem_image.2 ⟨p, mem_nbhdIn.2 ⟨hsupp _ heE p (by simp), ?_⟩, ?_⟩
          · rwa [Sym2.eq_swap]
          · rw [Sym2.eq_swap]
  have hinj : Set.InjOn (fun y => s(u, y)) (nbhdIn E u S) := by
    intro a _ b _ hab
    simp only [Sym2.eq_iff] at hab
    rcases hab with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1
  rw [edeg, ← himg, Finset.card_image_of_injOn hinj]
  rfl

/-- **Handshake.**  For a loopless graph, `∑_{u ∈ A} d_E(u, A)` is even. -/
theorem sum_degTo_self_even {E : Finset (Sym2 V)} (hloop : ∀ e ∈ E, ¬ e.IsDiag) (A : Finset V) :
    Even (∑ u ∈ A, degTo E u A) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    have hstep : ∀ u : V, degTo E u (insert a A)
        = degTo E u A + (if s(u, a) ∈ E then 1 else 0) := by
      intro u
      by_cases h : s(u, a) ∈ E
      · have hset : nbhdIn E u (insert a A) = insert a (nbhdIn E u A) := by
          ext y
          simp only [mem_nbhdIn, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hy, hE⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hy, hE⟩
          · rintro (rfl | ⟨hy, hE⟩)
            · exact ⟨Or.inl rfl, h⟩
            · exact ⟨Or.inr hy, hE⟩
        have hna : a ∉ nbhdIn E u A := fun hc => ha (mem_nbhdIn.1 hc).1
        rw [degTo, hset, Finset.card_insert_of_notMem hna, if_pos h]
        rfl
      · have hset : nbhdIn E u (insert a A) = nbhdIn E u A := by
          ext y
          simp only [mem_nbhdIn, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hy, hE⟩
            · exact absurd hE h
            · exact ⟨hy, hE⟩
          · rintro ⟨hy, hE⟩
            exact ⟨Or.inr hy, hE⟩
        rw [degTo, hset, if_neg h]
        rfl
    have hdiag : s(a, a) ∉ E := fun hc => hloop _ hc (by simp)
    have hsum : ∑ u ∈ insert a A, degTo E u (insert a A)
        = 2 * degTo E a A + ∑ u ∈ A, degTo E u A := by
      rw [Finset.sum_insert ha]
      have h1 : degTo E a (insert a A) = degTo E a A := by
        rw [hstep a, if_neg hdiag, Nat.add_zero]
      have h2 : ∑ u ∈ A, degTo E u (insert a A)
          = (∑ u ∈ A, degTo E u A) + ∑ u ∈ A, (if s(u, a) ∈ E then 1 else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun u _ => hstep u
      have h3 : ∑ u ∈ A, (if s(u, a) ∈ E then 1 else 0) = degTo E a A := by
        rw [degTo, nbhdIn, Finset.card_filter]
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases h : s(u, a) ∈ E
        · rw [if_pos h, if_pos (by rwa [Sym2.eq_swap])]
        · rw [if_neg h, if_neg (by rw [Sym2.eq_swap]; exact h)]
      rw [h1, h2, h3]
      ring
    rw [hsum]
    exact (even_two_mul _).add ih

/-- If `E' ⊆ E` then degrees split: `d_E(v) = d_{E'}(v) + d_{E \ E'}(v)`. -/
theorem edeg_add_edeg_sdiff {E E' : Finset (Sym2 V)} (h : E' ⊆ E) (v : V) :
    edeg E v = edeg E' v + edeg (E \ E') v := by
  classical
  have hsplit : E.filter (fun e => v ∈ e)
      = E'.filter (fun e => v ∈ e) ∪ (E \ E').filter (fun e => v ∈ e) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨heE, hve⟩
      by_cases h' : e ∈ E' <;> tauto
    · rintro (⟨heE, hve⟩ | ⟨⟨heE, _⟩, hve⟩)
      · exact ⟨h heE, hve⟩
      · exact ⟨heE, hve⟩
  have hdisj : Disjoint (E'.filter (fun e => v ∈ e)) ((E \ E').filter (fun e => v ∈ e)) := by
    refine Finset.disjoint_left.2 fun e he he' => ?_
    exact (Finset.mem_sdiff.1 (Finset.mem_filter.1 he').1).2 (Finset.mem_filter.1 he).1
  rw [edeg, hsplit, Finset.card_union_of_disjoint hdisj]
  rfl

/-- If `E' ⊆ E` and both `E` and `E \ E'` have even degrees, so has `E'`. -/
theorem even_edeg_of_sdiff {E E' : Finset (Sym2 V)} (h : E' ⊆ E)
    (hE : EvenDegrees E) (hd : EvenDegrees (E \ E')) : EvenDegrees E' := by
  intro v
  have := edeg_add_edeg_sdiff h v
  have h1 := hE v
  have h2 := hd v
  rw [Nat.even_iff] at h1 h2 ⊢
  omega

end BKLO
