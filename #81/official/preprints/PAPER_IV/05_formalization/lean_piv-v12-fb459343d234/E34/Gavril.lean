import E34.Trees
import E34.ChordalTools

/-!
# E34 — Gavril's theorem (chordal ⇒ subtree representation), constructive form

For `W ⊆ Fin n` with `G[W]` chordal we build a rooted tree on `Fin (n+1)` (root `Fin.last n`)
and subtrees `T_u` (`u ∈ W`) whose intersection pattern on `W` is `G[W]`.

Construction: a perfect elimination order `σ` of `G[W]` (Dirac); the parent of `v` is its
later neighbour of smallest `σ` (or the root), and `T_u = {u} ∪ {v : v ~ u, σ v < σ u}`.
-/

namespace E34

open Finset

open scoped Classical

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- A perfect elimination order of a chordal induced subgraph. -/
theorem exists_peo (W : Finset (Fin n)) (hW : AlonShapira.IsChordal (G.induce (W : Set (Fin n)))) :
    ∃ σ : Fin n → ℕ, Set.InjOn σ W ∧ (∀ v ∈ W, σ v < W.card) ∧
      ∀ v ∈ W, ∀ a ∈ W, ∀ b ∈ W, G.Adj v a → G.Adj v b → σ v < σ a → σ v < σ b → a ≠ b →
        G.Adj a b := by
  induction W using Finset.strongInduction with
  | H W ih =>
    rcases W.eq_empty_or_nonempty with hE | hne
    · subst hE
      exact ⟨fun _ => 0, by simp, by simp, by simp⟩
    obtain ⟨v, hv, hsimp⟩ := exists_simplicial_in G W hW hne
    obtain ⟨σ', hinj, hbd, hpeo⟩ := ih (W.erase v) (erase_ssubset hv)
      (isChordal_induce_mono G (erase_subset v W) hW)
    have hcard : (W.erase v).card + 1 = W.card := card_erase_add_one hv
    refine ⟨fun x => if x = v then 0 else σ' x + 1, ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only at hxy
      by_cases hxv : x = v <;> by_cases hyv : y = v
      · rw [hxv, hyv]
      · simp [hxv, hyv] at hxy
      · simp [hxv, hyv] at hxy
      · simp only [hxv, hyv, if_false, add_left_inj] at hxy
        exact hinj (mem_erase.2 ⟨hxv, hx⟩) (mem_erase.2 ⟨hyv, hy⟩) hxy
    · intro x hx
      by_cases hxv : x = v
      · simp only [hxv, if_true]; exact card_pos.2 hne
      · simp only [hxv, if_false]
        have := hbd x (mem_erase.2 ⟨hxv, hx⟩); omega
    · intro x hx a ha b hb hxa hxb hla hlb hab
      by_cases hxv : x = v
      · subst hxv; exact hsimp a ha b hb hxa hxb hab
      · simp only [hxv, if_false] at hla hlb
        have hav : a ≠ v := by rintro rfl; simp at hla
        have hbv : b ≠ v := by rintro rfl; simp at hlb
        simp only [hav, hbv, if_false, add_lt_add_iff_right] at hla hlb
        exact hpeo x (mem_erase.2 ⟨hxv, hx⟩) a (mem_erase.2 ⟨hav, ha⟩) b
          (mem_erase.2 ⟨hbv, hb⟩) hxa hxb hla hlb hab

/-- **Gavril's theorem** (constructive, on `Fin (n+1)`). -/
theorem gavril (W : Finset (Fin n)) (hW : AlonShapira.IsChordal (G.induce (W : Set (Fin n)))) :
    ∃ T : RTree (n + 1), ∃ Tu : Fin n → Finset (Fin (n + 1)),
      (∀ u ∈ W, T.IsSub (Tu u)) ∧
      ∀ u ∈ W, ∀ v ∈ W, u ≠ v → (G.Adj u v ↔ (Tu u ∩ Tu v).Nonempty) := by
  obtain ⟨σ, hinj, hbd, hpeo⟩ := exists_peo G W hW
  have hWn : W.card ≤ n := by simpa using card_le_univ W
  -- later neighbours and the parent
  let later : Fin n → Finset (Fin n) := fun v => W.filter (fun a => G.Adj v a ∧ σ v < σ a)
  have hmin : ∀ v, (later v).Nonempty → ∃ p ∈ later v, ∀ a ∈ later v, σ p ≤ σ a :=
    fun v hne => exists_min_image _ σ hne
  let pm : Fin n → Fin n := fun v => if h : (later v).Nonempty then (hmin v h).choose else v
  have hpm : ∀ v, (later v).Nonempty → pm v ∈ later v ∧ ∀ a ∈ later v, σ (pm v) ≤ σ a := by
    intro v hne
    simp only [pm, hne, dif_pos]
    exact (hmin v hne).choose_spec
  let par : Fin (n + 1) → Fin (n + 1) := fun x =>
    if hx : x = Fin.last n then Fin.last n
    else if x.castPred hx ∈ W ∧ (later (x.castPred hx)).Nonempty then (pm (x.castPred hx)).castSucc
    else Fin.last n
  let hh : Fin (n + 1) → ℕ := fun x =>
    if hx : x = Fin.last n then 0
    else if x.castPred hx ∈ W then n + 1 - σ (x.castPred hx) else 1
  have hpar_cs : ∀ v : Fin n, v ∈ W → (later v).Nonempty → par v.castSucc = (pm v).castSucc := by
    intro v hv hne
    simp only [par, Fin.castSucc_ne_last, dif_neg, not_false_eq_true, Fin.castPred_castSucc]
    rw [if_pos ⟨hv, hne⟩]
  have hh_cs : ∀ v : Fin n, v ∈ W → hh v.castSucc = n + 1 - σ v := by
    intro v hv
    simp only [hh, Fin.castSucc_ne_last, dif_neg, not_false_eq_true, Fin.castPred_castSucc]
    rw [if_pos hv]
  have hpar_lt : ∀ x, x ≠ Fin.last n → hh (par x) < hh x := by
    intro x hx
    obtain ⟨v, rfl⟩ : ∃ v : Fin n, x = v.castSucc :=
      ⟨x.castPred hx, (Fin.castSucc_castPred x hx).symm⟩
    by_cases hc : v ∈ W ∧ (later v).Nonempty
    · rw [hpar_cs v hc.1 hc.2]
      obtain ⟨hmem, -⟩ := hpm v hc.2
      simp only [later, mem_filter] at hmem
      rw [hh_cs _ hmem.1, hh_cs _ hc.1]
      have := hbd _ hmem.1
      omega
    · have e1 : par v.castSucc = Fin.last n := by
        simp only [par, Fin.castSucc_ne_last, dif_neg, not_false_eq_true, Fin.castPred_castSucc]
        rw [if_neg hc]
      rw [e1]
      simp only [hh, Fin.castSucc_ne_last, dif_neg, not_false_eq_true, Fin.castPred_castSucc,
        dif_pos]
      split_ifs with h1
      · have := hbd _ h1; omega
      · omega
  let T : RTree (n + 1) :=
    { par := par
      root := Fin.last n
      h := hh
      par_root := by simp [par]
      h_par := hpar_lt }
  let Tu : Fin n → Finset (Fin (n + 1)) := fun u =>
    (W.filter (fun v => v = u ∨ (G.Adj v u ∧ σ v < σ u))).image Fin.castSucc
  have hmemTu : ∀ u v, v.castSucc ∈ Tu u ↔ v ∈ W ∧ (v = u ∨ (G.Adj v u ∧ σ v < σ u)) := by
    intro u v
    simp only [Tu, mem_image, mem_filter]
    constructor
    · rintro ⟨w, hw, hwv⟩
      rw [Fin.castSucc_inj] at hwv
      subst hwv; exact hw
    · intro h; exact ⟨v, h, rfl⟩
  refine ⟨T, Tu, ?_, ?_⟩
  · intro u hu
    refine ⟨u.castSucc, T.isSubAt_of_closed _ _ ((hmemTu u u).2 ⟨hu, Or.inl rfl⟩) ?_⟩
    intro x hx hxt
    obtain ⟨v, hvf, rfl⟩ := mem_image.1 hx
    rw [mem_filter] at hvf
    obtain ⟨hvW, hvu⟩ := hvf
    have hvu' : v ≠ u := fun h => hxt (by rw [h])
    obtain ⟨hadj, hlt⟩ := hvu.resolve_left hvu'
    have hne : (later v).Nonempty := ⟨u, mem_filter.2 ⟨hu, hadj, hlt⟩⟩
    obtain ⟨hpmem, hpmin⟩ := hpm v hne
    simp only [later, mem_filter] at hpmem
    have hple : σ (pm v) ≤ σ u := hpmin u (mem_filter.2 ⟨hu, hadj, hlt⟩)
    refine ⟨?_, ?_⟩
    · show par v.castSucc ∈ Tu u
      rw [hpar_cs v hvW hne, hmemTu]
      refine ⟨hpmem.1, ?_⟩
      by_cases hpu : pm v = u
      · exact Or.inl hpu
      · right
        have hlt' : σ (pm v) < σ u := lt_of_le_of_ne hple (fun h => hpu (hinj hpmem.1 hu h))
        exact ⟨hpeo v hvW _ hpmem.1 u hu hpmem.2.1 hadj hpmem.2.2 hlt hpu, hlt'⟩
    · show hh u.castSucc < hh v.castSucc
      rw [hh_cs u hu, hh_cs v hvW]
      have := hbd u hu
      omega
  · intro u hu w hw huw
    constructor
    · intro hadj
      rcases lt_or_gt_of_ne (fun h : σ u = σ w => huw (hinj hu hw h)) with hlt | hlt
      · exact ⟨u.castSucc, mem_inter.2 ⟨(hmemTu u u).2 ⟨hu, Or.inl rfl⟩,
          (hmemTu w u).2 ⟨hu, Or.inr ⟨hadj, hlt⟩⟩⟩⟩
      · exact ⟨w.castSucc, mem_inter.2 ⟨(hmemTu u w).2 ⟨hw, Or.inr ⟨hadj.symm, hlt⟩⟩,
          (hmemTu w w).2 ⟨hw, Or.inl rfl⟩⟩⟩
    · rintro ⟨x, hx⟩
      rw [mem_inter] at hx
      obtain ⟨v, -, rfl⟩ := mem_image.1 hx.1
      obtain ⟨hvW, h1⟩ := (hmemTu u v).1 hx.1
      obtain ⟨-, h2⟩ := (hmemTu w v).1 hx.2
      rcases h1 with rfl | ⟨a1, l1⟩ <;> rcases h2 with rfl | ⟨a2, l2⟩
      · exact absurd rfl huw
      · exact a2
      · exact a1.symm
      · exact hpeo v hvW u hu w hw a1 a2 l1 l2 huw

end E34
