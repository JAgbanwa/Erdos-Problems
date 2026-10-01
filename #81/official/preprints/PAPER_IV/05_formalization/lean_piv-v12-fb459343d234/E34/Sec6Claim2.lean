import E34.Pinned
import E34.Gavril
import E34.Sec6Claim1

/-!
# E34 — §6 of arXiv:1902.06135, Claim 2 (with Lemma 10)

The set `S` is sampled as `q` ordered pairs `pS : Fin q → Fin n × Fin n`; its points are indexed
by `Pos q = Fin q × Bool`.  A *label* of a vertex `u` is a pair of positions `(i, j)` whose points
`a, b` are distinct, non-adjacent and both adjacent to `u` (so `u ∈ Y_S`); `lab G pS u` picks one
(or `none` if `u ∉ Y_S`).

**Claim 2 (combinatorial form).**  If `G[S ∪ U]` is chordal and `U ∩ Y ⊆ Y_S`, then there are a
rooted tree `Γ` with at most `(4q²+1)²` vertices and pins `y : labels → Γ` such that the padded
graph `H[U]` is `(y ∘ lab)`-pinned on `Γ`.

Proof: Gavril's representation of `G[S ∪ U]`; for every non-edge `ab` of `S` the gate point
`y_ab` (Lemma 10, `RTree.gate_exists`) lies in every `T_u` with `u` adjacent to `a` and `b`;
compress the gate points (`RTree.compress`); vertices of `X` get the whole tree.
-/

namespace E34

open Finset

open scoped Classical

variable {n : ℕ}

/-- Positions of the `S`-sample. -/
abbrev Pos (q : ℕ) := Fin q × Bool

/-- The point of the `S`-sample at a position. -/
def sPt {q : ℕ} (pS : Fin q → Fin n × Fin n) (i : Pos q) : Fin n :=
  if i.2 then (pS i.1).2 else (pS i.1).1

/-- The vertex set of the `S`-sample. -/
def sSet {q : ℕ} (pS : Fin q → Fin n × Fin n) : Finset (Fin n) := univ.image (sPt pS)

theorem sPt_mem {q : ℕ} (pS : Fin q → Fin n × Fin n) (i : Pos q) : sPt pS i ∈ sSet pS :=
  mem_image_of_mem _ (mem_univ _)

/-- `l` witnesses that the neighbourhood of `u` in `S` is not a clique. -/
def Valid (G : SimpleGraph (Fin n)) {q : ℕ} (pS : Fin q → Fin n × Fin n) (u : Fin n)
    (l : Pos q × Pos q) : Prop :=
  G.Adj u (sPt pS l.1) ∧ G.Adj u (sPt pS l.2) ∧ sPt pS l.1 ≠ sPt pS l.2 ∧
    ¬ G.Adj (sPt pS l.1) (sPt pS l.2)

/-- `u ∈ Y_S`. -/
def InYS (G : SimpleGraph (Fin n)) {q : ℕ} (pS : Fin q → Fin n × Fin n) (u : Fin n) : Prop :=
  ∃ l, Valid G pS u l

/-- The label of `u`. -/
noncomputable def lab (G : SimpleGraph (Fin n)) {q : ℕ} (pS : Fin q → Fin n × Fin n)
    (u : Fin n) : Option (Pos q × Pos q) :=
  if h : InYS G pS u then some h.choose else none

theorem lab_spec {G : SimpleGraph (Fin n)} {q : ℕ} {pS : Fin q → Fin n × Fin n} {u : Fin n}
    (h : InYS G pS u) : ∃ l, lab G pS u = some l ∧ Valid G pS u l :=
  ⟨h.choose, by simp only [lab, h, dif_pos], h.choose_spec⟩

/-- **Claim 2** of §6 (combinatorial form). -/
theorem sec6_claim2 (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) {q : ℕ}
    (pS : Fin q → Fin n × Fin n) (U : Finset (Fin n))
    (hch : AlonShapira.IsChordal (G.induce ((sSet pS ∪ U : Finset (Fin n)) : Set (Fin n))))
    (hY : ∀ u ∈ U, u ∉ X → InYS G pS u) :
    ∃ K0, K0 ≤ (4 * q ^ 2 + 1) ^ 2 ∧ ∃ Γ : RTree K0, ∃ y : Option (Pos q × Pos q) → Fin K0,
      PinnedOn Γ (fun u => y (lab G pS u)) (padGraph G X) U := by
  set W := sSet pS ∪ U
  obtain ⟨T, Tu, hsub, hadj⟩ := gavril G W hch
  -- gate points
  let GateProp : Pos q × Pos q → Fin (n + 1) → Prop := fun l y =>
    ∀ C, T.IsSub C → (C ∩ Tu (sPt pS l.1)).Nonempty → (C ∩ Tu (sPt pS l.2)).Nonempty → y ∈ C
  let z : Option (Pos q × Pos q) → Fin (n + 1) := fun o =>
    match o with
    | none => T.root
    | some l => if h : ∃ y, GateProp l y then h.choose else T.root
  have hz : ∀ l, sPt pS l.1 ≠ sPt pS l.2 → ¬ G.Adj (sPt pS l.1) (sPt pS l.2) →
      GateProp l (z (some l)) := by
    intro l hne hna
    have ha : sPt pS l.1 ∈ W := mem_union_left _ (sPt_mem pS _)
    have hb : sPt pS l.2 ∈ W := mem_union_left _ (sPt_mem pS _)
    have hdisj : Disjoint (Tu (sPt pS l.1)) (Tu (sPt pS l.2)) := by
      rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
      exact fun h => hna ((hadj _ ha _ hb hne).2 h)
    obtain ⟨y, -, hy⟩ := T.gate_exists (hsub _ ha) (hsub _ hb) hdisj
    have hex : ∃ y, GateProp l y := ⟨y, hy⟩
    simp only [z, hex, dif_pos]
    exact hex.choose_spec
  have hcardL : Fintype.card (Option (Pos q × Pos q)) = 4 * q ^ 2 + 1 := by
    simp [Fintype.card_option, Fintype.card_prod, Fintype.card_bool]; ring
  obtain ⟨K0, hK0, Γ, y, ι, hιy, hpath⟩ := T.compress z
  rw [hcardL] at hK0
  refine ⟨K0, hK0, Γ, y, n + 1, T, ι, fun u => if u ∈ X then univ else Tu u, hpath, ?_, ?_⟩
  · intro u hu
    by_cases huX : u ∈ X
    · simp only [huX, if_true]
      exact ⟨T.isSub_univ, mem_univ _⟩
    · simp only [huX, if_false]
      have huW : u ∈ W := mem_union_right _ hu
      refine ⟨hsub u huW, ?_⟩
      obtain ⟨l, hl, hv⟩ := lab_spec (hY u hu huX)
      rw [hl, hιy]
      obtain ⟨h1, h2, h3, h4⟩ := hv
      have ha : sPt pS l.1 ∈ W := mem_union_left _ (sPt_mem pS _)
      have hb : sPt pS l.2 ∈ W := mem_union_left _ (sPt_mem pS _)
      refine hz l h3 h4 (Tu u) (hsub u huW) ?_ ?_
      · exact (hadj u huW _ ha (G.ne_of_adj h1)).1 h1
      · exact (hadj u huW _ hb (G.ne_of_adj h2)).1 h2
  · intro u hu v hv huv
    have hne : ∀ w ∈ U, (if w ∈ X then (univ : Finset (Fin (n + 1))) else Tu w).Nonempty := by
      intro w hw
      split_ifs
      · exact univ_nonempty_iff.2 ⟨T.root⟩
      · obtain ⟨t, ht⟩ := hsub w (mem_union_right _ hw); exact ⟨t, ht.1⟩
    by_cases huX : u ∈ X
    · simp only [huX, if_true, univ_inter]
      exact iff_of_true ⟨huv, Or.inl huX⟩ (by simpa [huX] using hne v hv)
    by_cases hvX : v ∈ X
    · simp only [hvX, if_true, inter_univ]
      exact iff_of_true ⟨huv, Or.inr (Or.inl hvX)⟩ (by simpa [huX] using hne u hu)
    simp only [huX, hvX, if_false]
    have : (padGraph G X).Adj u v ↔ G.Adj u v := by
      simp only [padGraph, huX, hvX, false_or]
      exact ⟨fun h => h.2, fun h => ⟨huv, h⟩⟩
    rw [this]
    exact hadj u (mem_union_right _ hu) v (mem_union_right _ hv) huv

end E34
