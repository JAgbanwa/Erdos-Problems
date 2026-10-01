import E34.Sec6Main
import E34.SampleBound

/-!
# E34 — from structured samples to uniform `m`-subsets

* `card_omega_eq`: samples `ω = (pS, wU)` are sequences of length `2q + ℓM` in disguise.
* `choose_le_badSets_of_seq`: if at most half of the sequences of length `m ≤ n` induce a chordal
  graph, then at least half of the `m`-subsets induce a non-chordal graph (transfer lemma).
* `thm1_of_lemma11`: Theorem 1 of arXiv:1902.06135 (subset form) from Lemma 11 and three
  explicit parameter conditions.
-/

namespace E34

open Finset

open scoped Classical

variable {n : ℕ}

/-- Index type of a structured sample. -/
abbrev SIdx (q ℓ M : ℕ) := (Fin q × Bool) ⊕ (Fin ℓ × Fin M)

/-- The structured sample as a map on `SIdx`. -/
def omegaEquiv (n q ℓ M : ℕ) : Omega n q ℓ M ≃ (SIdx q ℓ M → Fin n) where
  toFun ω := fun i => match i with
    | Sum.inl p => sPt ω.1 p
    | Sum.inr p => ω.2 p.1 p.2
  invFun v := (fun i => (v (Sum.inl (i, false)), v (Sum.inl (i, true))),
    fun j k => v (Sum.inr (j, k)))
  left_inv ω := by
    obtain ⟨pS, wU⟩ := ω
    simp only [sPt, Bool.false_eq_true, if_false, if_true]
  right_inv v := by
    funext i
    rcases i with ⟨i, b⟩ | ⟨j, k⟩
    · cases b <;> simp [sPt]
    · rfl

theorem image_omegaEquiv {q ℓ M : ℕ} (ω : Omega n q ℓ M) :
    univ.image (omegaEquiv n q ℓ M ω) = sSet ω.1 ∪ uSet ω.2 := by
  ext v
  simp only [mem_image, mem_univ, true_and, mem_union, sSet, uSet, mem_biUnion, mem_img]
  constructor
  · rintro ⟨i, rfl⟩
    rcases i with p | ⟨j, k⟩
    · exact Or.inl ⟨p, rfl⟩
    · exact Or.inr ⟨j, k, rfl⟩
  · rintro (⟨p, rfl⟩ | ⟨j, k, rfl⟩)
    · exact ⟨Sum.inl p, rfl⟩
    · exact ⟨Sum.inr (j, k), rfl⟩

theorem card_sidx (q ℓ M : ℕ) : Fintype.card (SIdx q ℓ M) = 2 * q + M * ℓ := by
  simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]; ring

/-- Sequences over an index type with `m` elements. -/
theorem card_seq_index {ι : Type*} [Fintype ι] {m : ℕ} (hm : Fintype.card ι = m)
    (P : Finset (Fin n) → Prop) :
    (univ.filter (fun w : Fin m → Fin n => P (img w))).card =
      (univ.filter (fun v : ι → Fin n => P (univ.image v))).card := by
  subst hm
  set e := Fintype.equivFin ι
  refine card_bij (fun w _ => w ∘ e) ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    have : univ.image (w ∘ e) = img w := by
      ext x; simp only [mem_image, mem_univ, true_and, Function.comp, mem_img]
      exact ⟨fun ⟨i, h⟩ => ⟨e i, h⟩, fun ⟨j, h⟩ => ⟨e.symm j, by simp [h]⟩⟩
    rw [this]; exact hw
  · intro w _ w' _ h
    funext j
    have := congrFun h (e.symm j)
    simpa using this
  · intro v hv
    refine ⟨v ∘ e.symm, ?_, by funext i; simp⟩
    simp only [mem_filter, mem_univ, true_and] at hv ⊢
    have : img (v ∘ e.symm) = univ.image v := by
      ext x; simp only [mem_image, mem_univ, true_and, Function.comp, mem_img]
      exact ⟨fun ⟨j, h⟩ => ⟨e.symm j, h⟩, fun ⟨i, h⟩ => ⟨e i, by simp [h]⟩⟩
    rw [this]; exact hv

/-- Structured samples versus sequences of length `2q + Mℓ`. -/
theorem card_omega_eq (q ℓ M : ℕ) (P : Finset (Fin n) → Prop) :
    (univ.filter (fun w : Fin (2 * q + M * ℓ) → Fin n => P (img w))).card =
      (univ.filter (fun ω : Omega n q ℓ M => P (sSet ω.1 ∪ uSet ω.2))).card := by
  rw [card_seq_index (card_sidx q ℓ M)]
  symm
  refine card_equiv (omegaEquiv n q ℓ M) ?_
  intro ω
  simp only [mem_filter, mem_univ, true_and, image_omegaEquiv]

/-- Transfer from sequences to `m`-subsets for non-chordality. -/
theorem choose_le_badSets_of_seq (G : SimpleGraph (Fin n)) {m : ℕ} (hmn : m ≤ n)
    (h : 2 * (univ.filter (fun w : Fin m → Fin n =>
      AlonShapira.IsChordal (G.induce ((img w : Finset (Fin n)) : Set (Fin n))))).card ≤ n ^ m) :
    n.choose m ≤ 2 * (badSets G m).card := by
  obtain ⟨B, hBdef⟩ : ∃ B : Finset (Fin n) → Prop,
      B = fun U : Finset (Fin n) => ¬ AlonShapira.IsChordal (G.induce ((U : Finset (Fin n)) :
        Set (Fin n))) := ⟨_, rfl⟩
  have hB : ∀ A A', A ⊆ A' → B A → B A' := by
    subst hBdef
    intro A A' hAA' hA hA'
    exact hA (isChordal_induce_mono G hAA' hA')
  have ht := transfer B hB hmn
  have hlev : levelSets B m = badSets G m := by
    subst hBdef; unfold levelSets badSets; congr
  rw [hlev] at ht
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin m → Fin n)))
    (fun w => B (img w))
  rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hsplit
  have hC : (univ.filter (fun w : Fin m → Fin n => ¬ B (img w))).card =
      (univ.filter (fun w : Fin m → Fin n =>
        AlonShapira.IsChordal (G.induce ((img w : Finset (Fin n)) : Set (Fin n))))).card := by
    subst hBdef; congr 1; ext w; simp
  rw [hC] at hsplit
  have hpos : 0 < n ^ m := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; have : m = 0 := by omega
      subst this; simp
    · positivity
  have h2B : n ^ m ≤ 2 * (univ.filter (fun w : Fin m → Fin n => B (img w))).card := by omega
  have key : n ^ m * n.choose m ≤ n ^ m * (2 * (badSets G m).card) := by
    calc n ^ m * n.choose m ≤ 2 * (univ.filter (fun w : Fin m → Fin n => B (img w))).card *
          n.choose m := Nat.mul_le_mul_right _ h2B
      _ = 2 * ((univ.filter (fun w : Fin m → Fin n => B (img w))).card * n.choose m) := by ring
      _ ≤ 2 * (n ^ m * (badSets G m).card) := Nat.mul_le_mul_left _ ht
      _ = n ^ m * (2 * (badSets G m).card) := by ring
  exact Nat.le_of_mul_le_mul_left key hpos

/-- **Theorem 1 of arXiv:1902.06135 from Lemma 11** (subset form, explicit parameters). -/
theorem thm1_of_lemma11 (m11 : ℝ → ℕ → ℕ) (hL : Lemma11With m11) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (q ℓ M : ℕ) (hM : ∀ K0 ≤ kMax q, m11 (ε ^ 2 / 256 / 2) K0 ≤ M)
    (hcodes : 4 * nCodes q ≤ 2 ^ ℓ)
    (hq : 4 * ((ℓ * M : ℕ) : ℝ) * (1 - ε ^ 2 / 256) ^ q ≤ 1)
    (hmn : 2 * q + M * ℓ ≤ n) (hn : 1 ≤ n) (G : SimpleGraph (Fin n))
    (hfar : ∀ F : SimpleGraph (Fin n), AlonShapira.IsChordal F →
      ε * (n : ℝ) ^ 2 ≤ (AlonShapira.editDist G F : ℝ)) :
    n.choose (2 * q + M * ℓ) ≤ 2 * (badSets G (2 * q + M * ℓ)).card := by
  refine choose_le_badSets_of_seq G hmn ?_
  have e := card_omega_eq (n := n) q ℓ M (fun U => AlonShapira.IsChordal (G.induce (U : Set (Fin n))))
  have h2 := sec6_count m11 hL ε hε0 hε1 q ℓ M hM hcodes hq hn G hfar
  rw [pow_add]
  convert h2 using 2

end E34
