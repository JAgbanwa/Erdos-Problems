/-
# Veblen's theorem: an even graph is an edge-disjoint union of cycles.

The absorber construction needs the classical structure theorem behind BKLO §8.1: a finite loopless
edge set all of whose vertex degrees are even splits into edge-disjoint cycles.  The proof is the
standard one — a longest path in a graph of minimum degree `≥ 2` closes up into a cycle, and
removing that cycle preserves evenness — organised as a strong induction on the number of edges.
-/
import BKLO.Cycles

open Finset

namespace BKLO

/-! ### Degrees -/

theorem deg_pos_of_mem_supp {E : Finset (Sym2 ℕ)} {v : ℕ} (h : v ∈ supp E) : 0 < deg E v := by
  classical
  obtain ⟨e, he, hv⟩ := mem_supp.1 h
  rw [deg, Finset.card_pos]
  exact ⟨e, Finset.mem_filter.2 ⟨he, hv⟩⟩

theorem mem_supp_of_deg_pos {E : Finset (Sym2 ℕ)} {v : ℕ} (h : 0 < deg E v) : v ∈ supp E := by
  classical
  rw [deg, Finset.card_pos] at h
  obtain ⟨e, he⟩ := h
  rw [Finset.mem_filter] at he
  exact mem_supp.2 ⟨e, he.1, he.2⟩

theorem deg_mono {C E : Finset (Sym2 ℕ)} (h : C ⊆ E) (v : ℕ) : deg C v ≤ deg E v := by
  classical
  unfold deg
  refine Finset.card_le_card ?_
  intro e he
  simp only [Finset.mem_filter] at he ⊢
  exact ⟨h he.1, he.2⟩

theorem deg_sdiff {C E : Finset (Sym2 ℕ)} (h : C ⊆ E) (v : ℕ) :
    deg (E \ C) v = deg E v - deg C v := by
  classical
  have h1 : (E \ C).filter (fun e : Sym2 ℕ => v ∈ e)
      = E.filter (fun e : Sym2 ℕ => v ∈ e) \ C.filter (fun e : Sym2 ℕ => v ∈ e) := by
    ext e; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  have hs : C.filter (fun e : Sym2 ℕ => v ∈ e) ⊆ E.filter (fun e : Sym2 ℕ => v ∈ e) := by
    intro e he
    simp only [Finset.mem_filter] at he ⊢
    exact ⟨h he.1, he.2⟩
  rw [deg, deg, deg, h1, Finset.card_sdiff_of_subset hs]

/-- A vertex of even degree at least `2` in a loopless edge set has two distinct neighbours. -/
theorem exists_two_nbrs {E : Finset (Sym2 ℕ)} {v : ℕ} (h : 2 ≤ deg E v) :
    ∃ a b, a ≠ b ∧ s(v, a) ∈ E ∧ s(v, b) ∈ E := by
  classical
  rw [deg] at h
  obtain ⟨e1, he1, e2, he2, hne⟩ := Finset.one_lt_card.1 (lt_of_lt_of_le Nat.one_lt_two h)
  rw [Finset.mem_filter] at he1 he2
  obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.1 he1.2
  obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he2.2
  exact ⟨a, b, by rintro rfl; exact hne (ha.trans hb.symm), ha ▸ he1.1, hb ▸ he2.1⟩

/-! ### A cycle inside an even graph -/

/-- **A nonempty even loopless edge set contains a cycle.**  Take a path of maximum length: its
first vertex has a neighbour other than its successor, which by maximality must already lie on the
path, closing a cycle. -/
theorem exists_cycle_subset {E : Finset (Sym2 ℕ)} (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (heven : ∀ v, Even (deg E v)) (hne : E.Nonempty) :
    ∃ l : List ℕ, l.Nodup ∧ 3 ≤ l.length ∧ cycEdges l ⊆ E := by
  classical
  set N := (supp E).card with hN
  set P : ℕ → Prop := fun n => ∃ l : List ℕ, l.Nodup ∧ (∀ v ∈ l, v ∈ supp E) ∧
      pathEdges l ⊆ E ∧ l.length = n with hPdef
  -- a one-vertex path exists
  obtain ⟨e0, he0⟩ := hne
  obtain ⟨x0, y0⟩ := e0
  have hx0 : x0 ∈ supp E := mem_supp.2 ⟨s(x0, y0), he0, by simp⟩
  have hP1 : P 1 := ⟨[x0], by simp, by simpa using hx0, by simp, rfl⟩
  -- paths are short
  have hPle : ∀ n, P n → n ≤ N := by
    rintro n ⟨l, hl, hsub, -, rfl⟩
    rw [hN, ← List.toFinset_card_of_nodup hl]
    exact Finset.card_le_card (fun v hv => hsub v (List.mem_toFinset.1 hv))
  have hN1 : 1 ≤ N := hPle 1 hP1
  set k := Nat.findGreatest P N with hk
  have hPk : P k := Nat.findGreatest_spec hN1 hP1
  have hmax : ∀ m, k < m → ¬ P m := by
    intro m hm hPm
    rcases le_or_gt m N with h | h
    · exact Nat.findGreatest_is_greatest hm h hPm
    · exact absurd (hPle m hPm) (by omega)
  obtain ⟨l, hlnd, hlsub, hlE, hlk⟩ := hPk
  have hk1 : 1 ≤ k := Nat.le_findGreatest hN1 hP1
  obtain ⟨a, t, rfl⟩ : ∃ a t, l = a :: t := by
    cases l with
    | nil => simp at hlk; omega
    | cons a t => exact ⟨a, t, rfl⟩
  -- two neighbours of the first vertex
  have ha : a ∈ supp E := hlsub a (by simp)
  have hdeg2 : 2 ≤ deg E a := by
    have h1 := deg_pos_of_mem_supp ha
    have h2 := heven a
    rw [Nat.even_iff] at h2
    omega
  obtain ⟨x, y, hxy, hxE, hyE⟩ := exists_two_nbrs hdeg2
  obtain ⟨c, hcE, hchead⟩ : ∃ c, s(a, c) ∈ E ∧ t.head? ≠ some c := by
    by_cases hx : t.head? = some x
    · exact ⟨y, hyE, by rw [hx]; simpa using hxy⟩
    · exact ⟨x, hxE, hx⟩
  have hca : c ≠ a := by
    rintro rfl
    exact hloop _ hcE (by simp)
  have hcsupp : c ∈ supp E := mem_supp.2 ⟨s(a, c), hcE, by simp⟩
  by_cases hcl : c ∈ a :: t
  · -- the path closes into a cycle
    have hct : c ∈ t := by
      rcases List.mem_cons.1 hcl with h | h
      · exact absurd h hca
      · exact h
    obtain ⟨t1, t2, ht⟩ := List.append_of_mem hct
    have ht1 : t1 ≠ [] := by
      rintro rfl
      rw [List.nil_append] at ht
      exact hchead (by rw [ht]; rfl)
    have hsublist : List.Sublist (a :: (t1 ++ [c])) (a :: t) := by
      rw [ht]
      refine List.Sublist.cons₂ _ ?_
      exact List.Sublist.append_left (List.Sublist.cons₂ _ (List.nil_sublist t2)) t1
    refine ⟨a :: (t1 ++ [c]), hsublist.nodup hlnd, ?_, ?_⟩
    · simp only [List.length_cons, List.length_append]
      have : 1 ≤ t1.length := List.length_pos_of_ne_nil ht1
      omega
    · have hlast : (a :: (t1 ++ [c])).getLast? = some c := by
        rw [show a :: (t1 ++ [c]) = (a :: t1) ++ [c] from rfl]
        exact List.getLast?_concat
      rw [cycEdges_eq_insert hlast]
      intro e he
      rcases Finset.mem_insert.1 he with rfl | he
      · rw [Sym2.eq_swap]; exact hcE
      · refine hlE ?_
        have hpre : pathEdges (a :: (t1 ++ [c])) ⊆ pathEdges ((a :: (t1 ++ [c])) ++ t2) :=
          pathEdges_subset_append _ _
        have heq : (a :: (t1 ++ [c])) ++ t2 = a :: t := by
          rw [ht]; simp
        rw [heq] at hpre
        exact hpre he
  · -- the path extends, contradicting maximality
    exfalso
    refine hmax (k + 1) (by omega) ⟨c :: a :: t, ?_, ?_, ?_, ?_⟩
    · exact List.nodup_cons.2 ⟨hcl, hlnd⟩
    · intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact hcsupp
      · exact hlsub v hv
    · rw [pathEdges_cons₂]
      intro e he
      rcases Finset.mem_insert.1 he with rfl | he
      · rw [Sym2.eq_swap]; exact hcE
      · exact hlE he
    · simp only [List.length_cons] at hlk ⊢
      omega

/-! ### Veblen's theorem -/

theorem cycEdges_subset_fam : ∀ {l : List ℕ} {L : List (List ℕ)}, l ∈ L →
    cycEdges l ⊆ cycFamEdges L
  | l, [], h => by simp at h
  | l, l' :: L, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Finset.subset_union_left
    · exact (cycEdges_subset_fam h).trans Finset.subset_union_right

theorem veblen_aux : ∀ (n : ℕ) (E : Finset (Sym2 ℕ)), E.card ≤ n → (∀ e ∈ E, ¬ e.IsDiag) →
    (∀ v, Even (deg E v)) → ∃ L : List (List ℕ), EdgeDisjFam L ∧ cycFamEdges L = E := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro E hcard hloop heven
    rcases Finset.eq_empty_or_nonempty E with rfl | hne
    · exact ⟨[], ⟨by simp, by simp, List.Pairwise.nil⟩, rfl⟩
    obtain ⟨l, hlnd, hl3, hlE⟩ := exists_cycle_subset hloop heven hne
    set C : Finset (Sym2 ℕ) := cycEdges l with hC
    have hCcard : C.card = l.length := card_cycEdges hlnd hl3
    have hCpos : 0 < C.card := by omega
    have hsub : E \ C ⊂ E := by
      refine Finset.sdiff_ssubset hlE ?_
      exact Finset.card_pos.1 hCpos
    have hlt : (E \ C).card < E.card := Finset.card_lt_card hsub
    have hEpos : 0 < E.card := Finset.card_pos.2 hne
    have hloop' : ∀ e ∈ E \ C, ¬ e.IsDiag := fun e he => hloop e (Finset.mem_sdiff.1 he).1
    have heven' : ∀ v, Even (deg (E \ C) v) := by
      intro v
      have h1 := heven v
      have h2 := even_deg_cycEdges hlnd hl3 v
      rw [← hC] at h2
      have h3 := deg_mono hlE v
      rw [Nat.even_iff] at h1 h2 ⊢
      rw [deg_sdiff hlE v]
      omega
    obtain ⟨L', hL'fam, hL'eq⟩ :=
      IH (E.card - 1) (by omega) (E \ C) (by omega) hloop' heven'
    have hdisj : Disjoint C (E \ C) := Finset.disjoint_sdiff
    refine ⟨l :: L', ⟨?_, ?_, ?_⟩, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hlnd
      · exact hL'fam.nodup x hx
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hl3
      · exact hL'fam.three x hx
    · refine List.Pairwise.cons ?_ hL'fam.pdisj
      intro l' hl'
      refine Finset.disjoint_of_subset_right ?_ hdisj
      rw [← hL'eq]
      exact cycEdges_subset_fam hl'
    · rw [cycFamEdges_cons, hL'eq, ← hC]
      rw [Finset.union_sdiff_self_eq_union]
      exact Finset.union_eq_right.2 hlE

/-- **Veblen's theorem.**  A loopless edge set with all degrees even is the edge-disjoint union of a
family of cycles. -/
theorem veblen (E : Finset (Sym2 ℕ)) (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (heven : ∀ v, Even (deg E v)) :
    ∃ L : List (List ℕ), EdgeDisjFam L ∧ cycFamEdges L = E :=
  veblen_aux E.card E le_rfl hloop heven

end BKLO
