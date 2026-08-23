import Mathlib
namespace Ax2.PathBalance
open Finset
variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The set of consecutive directed pairs (edges) of a list. -/
def pairs (l : List N) : Finset (N × N) := (l.zip l.tail).toFinset

/-- Master characterization of edge membership via `getElem?` indices. -/
private theorem mem_pairs_iff' (l : List N) {u v : N} :
    (u, v) ∈ pairs l ↔ ∃ i : ℕ, l[i]? = some u ∧ l[i + 1]? = some v := by
  unfold pairs
  rw [List.mem_toFinset, List.mem_iff_getElem?]
  constructor
  · rintro ⟨i, hi⟩
    rw [List.getElem?_zip_eq_some] at hi
    obtain ⟨h1, h2⟩ := hi
    exact ⟨i, h1, by rw [List.getElem?_tail] at h2; exact h2⟩
  · rintro ⟨i, h1, h2⟩
    refine ⟨i, ?_⟩
    rw [List.getElem?_zip_eq_some]
    exact ⟨h1, by rw [List.getElem?_tail]; exact h2⟩

/-- (2) Membership in `pairs` means the two nodes are consecutive. -/
theorem mem_pairs_iff (l : List N) {u v : N} :
    (u, v) ∈ pairs l ↔ (u, v) ∈ l.zip l.tail := by
  unfold pairs
  rw [List.mem_toFinset]

/-- (1) In a duplicate-free list, no directed edge and its reverse both occur (no 2-cycle). -/
theorem pairs_antisymm (l : List N) (hnd : l.Nodup) {u v : N}
    (h : (u, v) ∈ pairs l) : (v, u) ∉ pairs l := by
  rw [mem_pairs_iff'] at h
  rw [mem_pairs_iff']
  rintro ⟨j, hj1, hj2⟩
  obtain ⟨i, hi1, hi2⟩ := h
  rw [List.getElem?_eq_some_iff] at hi1 hi2 hj1 hj2
  obtain ⟨hib, hie⟩ := hi1
  obtain ⟨hib2, hie2⟩ := hi2
  obtain ⟨hjb, hje⟩ := hj1
  obtain ⟨hjb2, hje2⟩ := hj2
  -- l[i] = u, l[i+1] = v, l[j] = v, l[j+1] = u
  -- from l[i+1] = v = l[j] : i+1 = j ; from l[j+1] = u = l[i] : j+1 = i
  have e1 : i + 1 = j := hnd.getElem_inj_iff.mp (by rw [hie2, hje])
  have e2 : j + 1 = i := hnd.getElem_inj_iff.mp (by rw [hje2, hie])
  omega

/-- (4) An edge of `pairs l` relates its endpoints under any relation the list is a chain for. -/
theorem pairs_rel {R : N → N → Prop} (l : List N) (hc : l.IsChain R)
    {u v : N} (h : (u, v) ∈ pairs l) : R u v := by
  rw [mem_pairs_iff'] at h
  obtain ⟨i, h1, h2⟩ := h
  rw [List.getElem?_eq_some_iff] at h1 h2
  obtain ⟨hib, hie⟩ := h1
  obtain ⟨hib2, hie2⟩ := h2
  have := List.isChain_iff_getElem.mp hc i hib2
  rw [hie, hie2] at this
  exact this

/-- Out-neighbour predicate: `u` sits at a non-final position. -/
private def POut (l : List N) (u : N) : Prop := ∃ i : ℕ, i + 1 < l.length ∧ l[i]? = some u
/-- In-neighbour predicate: `u` sits at a non-initial position. -/
private def PIn (l : List N) (u : N) : Prop := ∃ i : ℕ, i + 1 < l.length ∧ l[i + 1]? = some u

instance (l : List N) (u : N) : Decidable (POut l u) :=
  decidable_of_iff (∃ i ∈ Finset.range l.length, i + 1 < l.length ∧ l[i]? = some u) (by
    unfold POut; simp only [Finset.mem_range]
    exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h1, h2⟩ => ⟨i, by omega, h1, h2⟩⟩)
instance (l : List N) (u : N) : Decidable (PIn l u) :=
  decidable_of_iff (∃ i ∈ Finset.range l.length, i + 1 < l.length ∧ l[i + 1]? = some u) (by
    unfold PIn; simp only [Finset.mem_range]
    exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h1, h2⟩ => ⟨i, by omega, h1, h2⟩⟩)

private theorem out_card (l : List N) (hnd : l.Nodup) (u : N) :
    (univ.filter (fun v => (u, v) ∈ pairs l)).card = if POut l u then 1 else 0 := by
  by_cases hP : POut l u
  · rw [if_pos hP]
    obtain ⟨i, hilt, hiu⟩ := hP
    have hi1 : i + 1 < l.length := hilt
    -- successor value
    set v0 := l[i + 1] with hv0
    rw [Finset.card_eq_one]
    refine ⟨v0, ?_⟩
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [mem_pairs_iff']
      exact ⟨i, hiu, by rw [List.getElem?_eq_some_iff]; exact ⟨hi1, rfl⟩⟩
    · intro v hv
      rw [Finset.mem_filter, mem_pairs_iff'] at hv
      obtain ⟨_, j, hj1, hj2⟩ := hv
      rw [List.getElem?_eq_some_iff] at hiu hj1
      obtain ⟨hib, hie⟩ := hiu
      obtain ⟨hjb, hje⟩ := hj1
      have : j = i := hnd.getElem_inj_iff.mp (by rw [hje, hie])
      subst this
      rw [List.getElem?_eq_some_iff] at hj2
      obtain ⟨_, hjv⟩ := hj2
      rw [hv0, ← hjv]
  · rw [if_neg hP]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _
    rw [mem_pairs_iff']
    rintro ⟨i, hiu, hiv⟩
    apply hP
    rw [List.getElem?_eq_some_iff] at hiv
    obtain ⟨hib, _⟩ := hiv
    exact ⟨i, hib, hiu⟩

private theorem in_card (l : List N) (hnd : l.Nodup) (u : N) :
    (univ.filter (fun v => (v, u) ∈ pairs l)).card = if PIn l u then 1 else 0 := by
  by_cases hP : PIn l u
  · rw [if_pos hP]
    obtain ⟨i, hilt, hiu⟩ := hP
    have hi0 : i < l.length := by omega
    set v0 := l[i] with hv0
    rw [Finset.card_eq_one]
    refine ⟨v0, ?_⟩
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [mem_pairs_iff']
      exact ⟨i, by rw [List.getElem?_eq_some_iff]; exact ⟨hi0, rfl⟩, hiu⟩
    · intro v hv
      rw [Finset.mem_filter, mem_pairs_iff'] at hv
      obtain ⟨_, j, hj1, hj2⟩ := hv
      rw [List.getElem?_eq_some_iff] at hiu hj2
      obtain ⟨hib, hie⟩ := hiu
      obtain ⟨hjb, hje⟩ := hj2
      have : j + 1 = i + 1 := hnd.getElem_inj_iff.mp (by rw [hje, hie])
      have hji : j = i := by omega
      subst hji
      rw [List.getElem?_eq_some_iff] at hj1
      obtain ⟨_, hjv⟩ := hj1
      rw [hv0, ← hjv]
  · rw [if_neg hP]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _
    rw [mem_pairs_iff']
    rintro ⟨i, hiv, hiu⟩
    apply hP
    obtain ⟨hi1, _⟩ := List.getElem?_eq_some_iff.mp hiu
    exact ⟨i, hi1, hiu⟩

/-- `POut` is equivalent to: `u` occurs and is not the last element. -/
private theorem pout_iff (l : List N) (hnd : l.Nodup) (u : N) :
    POut l u ↔ (u ∈ l ∧ l.getLast? ≠ some u) := by
  constructor
  · rintro ⟨i, hilt, hiu⟩
    have hmem : u ∈ l := List.mem_iff_getElem?.mpr ⟨i, hiu⟩
    refine ⟨hmem, ?_⟩
    intro hlast
    rw [List.getLast?_eq_getElem?] at hlast
    rw [List.getElem?_eq_some_iff] at hiu hlast
    obtain ⟨hib, hie⟩ := hiu
    obtain ⟨hlb, hle⟩ := hlast
    have : i = l.length - 1 := hnd.getElem_inj_iff.mp (by rw [hie, hle])
    omega
  · rintro ⟨hmem, hlast⟩
    rw [List.mem_iff_getElem?] at hmem
    obtain ⟨i, hiu⟩ := hmem
    rw [List.getElem?_eq_some_iff] at hiu
    obtain ⟨hib, hie⟩ := hiu
    refine ⟨i, ?_, by rw [List.getElem?_eq_some_iff]; exact ⟨hib, hie⟩⟩
    -- i ≠ length-1 since otherwise it's the last element
    by_contra hcon
    push_neg at hcon
    have hi : i = l.length - 1 := by omega
    apply hlast
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_some_iff]
    subst hi
    exact ⟨by omega, hie⟩

/-- `PIn` is equivalent to: `u` occurs and is not the first element. -/
private theorem pin_iff (l : List N) (hnd : l.Nodup) (u : N) :
    PIn l u ↔ (u ∈ l ∧ l.head? ≠ some u) := by
  constructor
  · rintro ⟨i, hilt, hiu⟩
    have hmem : u ∈ l := List.mem_iff_getElem?.mpr ⟨i + 1, hiu⟩
    refine ⟨hmem, ?_⟩
    intro hhead
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getElem?_eq_some_iff] at hiu hhead
    obtain ⟨hib, hie⟩ := hiu
    obtain ⟨hhb, hhe⟩ := hhead
    have : i + 1 = 0 := hnd.getElem_inj_iff.mp (by rw [hie, hhe])
    omega
  · rintro ⟨hmem, hhead⟩
    rw [List.mem_iff_getElem?] at hmem
    obtain ⟨j, hju⟩ := hmem
    rw [List.getElem?_eq_some_iff] at hju
    obtain ⟨hjb, hje⟩ := hju
    -- j ≠ 0
    have hj0 : j ≠ 0 := by
      intro h0
      apply hhead
      rw [List.head?_eq_getElem?, List.getElem?_eq_some_iff]
      subst h0
      exact ⟨by omega, hje⟩
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact ⟨i, by omega, by rw [List.getElem?_eq_some_iff]; exact ⟨hjb, hje⟩⟩

/-- (3) Degree balance. -/
theorem degree_balance (l : List N) (hnd : l.Nodup) (u : N) :
    (∑ v, (if (u, v) ∈ pairs l then (1 : ℝ) else 0))
      - (∑ v, if (v, u) ∈ pairs l then (1 : ℝ) else 0)
    = (if l.head? = some u then (1 : ℝ) else 0) - (if l.getLast? = some u then (1 : ℝ) else 0) := by
  rw [Finset.sum_boole, Finset.sum_boole]
  rw [out_card l hnd u, in_card l hnd u]
  simp only [pout_iff l hnd u, pin_iff l hnd u]
  -- Now everything is in terms of membership and head?/getLast?
  by_cases hmem : u ∈ l
  · -- u ∈ l
    have hne : l ≠ [] := by rintro rfl; simp at hmem
    by_cases hhead : l.head? = some u <;> by_cases hlast : l.getLast? = some u <;>
      simp [hmem, hhead, hlast]
  · -- u ∉ l : head? and getLast? cannot be some u
    have h1 : l.head? ≠ some u := by
      intro h; exact hmem (List.mem_of_mem_head? h)
    have h2 : l.getLast? ≠ some u := by
      intro h; exact hmem (List.mem_of_mem_getLast? h)
    simp [hmem, h1, h2]

end Ax2.PathBalance
