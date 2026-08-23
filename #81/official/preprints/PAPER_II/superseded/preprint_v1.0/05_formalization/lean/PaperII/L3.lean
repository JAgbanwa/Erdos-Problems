import PaperII.CloneCopy

/-!
# Paper II — No clone class splits (ledger L3 = Lemma 4.2)

Copying the entire open-neighborhood clone class `{v | N(v)=A}` (source `W₁`, `A=N(W₁)`) onto a
distinct, nonadjacent clone class with neighborhood `B=N(W₂)` strictly decreases the number of clone
classes `m(G)`. The source class's neighborhood `A` disappears (all its vertices move, structurally,
since `classCopy` moves the whole class), and `W₁∪W₂` becomes one class — net drop of at least one.
-/

open scoped BigOperators
open Finset

namespace PaperII

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Unfolding of adjacency in `classCopy`: the symmetric closure of `classCopyRel` collapses to a
single symmetric disjunction. -/
lemma classCopy_adj_iff (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (a b : V) :
    (classCopy G A B).Adj a b ↔
      a ≠ b ∧ ((G.neighborFinset a ≠ A ∧ G.neighborFinset b ≠ A ∧ G.Adj a b)
        ∨ (G.neighborFinset a = A ∧ b ∈ B) ∨ (G.neighborFinset b = A ∧ a ∈ B)) := by
  unfold classCopy classCopyRel
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨hne, ?_⟩
    rcases h with h | h
    · rcases h with h | h | h
      · exact Or.inl ⟨h.1, h.2.1, h.2.2⟩
      · exact Or.inr (Or.inl ⟨h.1, h.2⟩)
      · exact Or.inr (Or.inr ⟨h.1, h.2⟩)
    · rcases h with h | h | h
      · exact Or.inl ⟨h.2.1, h.1, (G.adj_comm b a).mp h.2.2⟩
      · exact Or.inr (Or.inr ⟨h.1, h.2⟩)
      · exact Or.inr (Or.inl ⟨h.1, h.2⟩)
  · rintro ⟨hne, h⟩
    refine ⟨hne, ?_⟩
    rcases h with h | h | h
    · exact Or.inl (Or.inl ⟨h.1, h.2.1, h.2.2⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨h.1, h.2⟩))
    · exact Or.inl (Or.inr (Or.inr ⟨h.1, h.2⟩))

/-- The new open neighborhood of every vertex under `classCopy`, expressed purely in terms of its
old neighborhood `X = N_G(v)`, the moved class `S = {u | N_G(u)=A}`, and a fixed witness `w` of the
target class (`N_G(w)=B`). -/
lemma classCopy_neighborFinset_eq (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hnonadj : ∀ v, G.neighborFinset v = A → v ∉ B) (w : V) (hwB : G.neighborFinset w = B) (v : V) :
    (classCopy G A B).neighborFinset v =
      (if G.neighborFinset v = A then B
        else ((G.neighborFinset v \ (univ.filter (fun u => G.neighborFinset u = A)))
              ∪ (if w ∈ G.neighborFinset v then (univ.filter (fun u => G.neighborFinset u = A))
                  else ∅))) := by
  ext b
  rw [SimpleGraph.mem_neighborFinset, classCopy_adj_iff]
  -- v ∈ B ↔ w ∈ N_G(v)
  have hvB_iff : v ∈ B ↔ w ∈ G.neighborFinset v := by
    rw [SimpleGraph.mem_neighborFinset, G.adj_comm, ← SimpleGraph.mem_neighborFinset, hwB]
  by_cases hvA : G.neighborFinset v = A
  · rw [if_pos hvA]
    constructor
    · rintro ⟨hne, h⟩
      rcases h with h | h | h
      · exact absurd hvA h.1
      · exact h.2
      · exact absurd (hnonadj v hvA) (not_not.mpr h.2)
    · intro hbB
      have hvb : v ≠ b := by
        intro he; subst he; exact hnonadj v hvA hbB
      exact ⟨hvb, Or.inr (Or.inl ⟨hvA, hbB⟩)⟩
  · rw [if_neg hvA]
    constructor
    · rintro ⟨hne, h⟩
      rcases h with h | h | h
      · -- T1: N_G(b) ≠ A ∧ Adj v b
        rw [Finset.mem_union]
        left
        rw [Finset.mem_sdiff, Finset.mem_filter]
        refine ⟨(G.mem_neighborFinset v b).mpr h.2.2, ?_⟩
        rintro ⟨-, hbA⟩; exact h.2.1 hbA
      · exact absurd h.1 hvA
      · -- T3: N_G(b) = A ∧ v ∈ B
        rw [Finset.mem_union]
        right
        have hw : w ∈ G.neighborFinset v := hvB_iff.mp h.2
        rw [if_pos hw, Finset.mem_filter]
        exact ⟨Finset.mem_univ b, h.1⟩
    · intro h
      rw [Finset.mem_union] at h
      rcases h with h | h
      · rw [Finset.mem_sdiff, Finset.mem_filter] at h
        have hadj := (G.mem_neighborFinset v b).mp h.1
        have hbA : G.neighborFinset b ≠ A := fun hbA => h.2 ⟨Finset.mem_univ b, hbA⟩
        exact ⟨G.ne_of_adj hadj, Or.inl ⟨hvA, hbA, hadj⟩⟩
      · by_cases hw : w ∈ G.neighborFinset v
        · rw [if_pos hw, Finset.mem_filter] at h
          have hvBmem : v ∈ B := hvB_iff.mpr hw
          have hvb : v ≠ b := by
            intro he; subst he; exact hvA h.2
          exact ⟨hvb, Or.inr (Or.inr ⟨h.2, hvBmem⟩)⟩
        · rw [if_neg hw] at h
          simp at h

/-- Ledger L3 (Lemma 4.2): the clone-class count strictly decreases under `classCopy`. -/
theorem cloneClassCount_classCopy_lt (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hA : (univ.filter (fun v => G.neighborFinset v = A)).Nonempty)
    (hB : (univ.filter (fun v => G.neighborFinset v = B)).Nonempty)
    (hAB : A ≠ B)
    (hnonadj : ∀ v, G.neighborFinset v = A → v ∉ B) :
    cloneClassCount (classCopy G A B) < cloneClassCount G := by
  classical
  -- fixed witness of the target class
  obtain ⟨w, hw⟩ := hB
  rw [Finset.mem_filter] at hw
  obtain ⟨-, hwB⟩ := hw
  set S : Finset V := univ.filter (fun u => G.neighborFinset u = A) with hSdef
  -- the value function on neighborhoods
  set h : Finset V → Finset V :=
    fun X => if X = A then B else ((X \ S) ∪ (if w ∈ X then S else ∅)) with hhdef
  set f : V → Finset V := fun v => G.neighborFinset v with hfdef
  -- new neighborhood factors through old neighborhood via `h`
  have key : ∀ v, (classCopy G A B).neighborFinset v = h (f v) := by
    intro v
    rw [classCopy_neighborFinset_eq G A B hnonadj w hwB v]
  -- rewrite both counts as cardinalities of images
  have himg : (univ.image (fun v => (classCopy G A B).neighborFinset v))
      = (univ.image f).image h := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro v _
    exact key v
  have hcount : cloneClassCount (classCopy G A B) = ((univ.image f).image h).card := by
    unfold cloneClassCount
    rw [himg]
  rw [hcount]
  have hGcount : cloneClassCount G = (univ.image f).card := rfl
  rw [hGcount]
  -- membership facts
  have hAmem : A ∈ univ.image f := by
    obtain ⟨a, ha⟩ := hA
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_image]
    exact ⟨a, Finset.mem_univ a, ha.2⟩
  have hBmem : B ∈ univ.image f := by
    rw [Finset.mem_image]
    exact ⟨w, Finset.mem_univ w, hwB⟩
  -- h A = B
  have hhA : h A = B := by simp only [hhdef, if_pos rfl]
  -- h B = B
  have hwnotB : w ∉ B := by
    intro hwmem
    have : G.Adj w w := by
      have := (G.mem_neighborFinset w w).mp (by rw [hwB]; exact hwmem)
      exact this
    exact (G.irrefl this)
  have hBdisj : Disjoint B S := by
    rw [Finset.disjoint_left]
    intro x hxB hxS
    rw [hSdef, Finset.mem_filter] at hxS
    exact hnonadj x hxS.2 hxB
  have hBS : B \ S = B := by
    rw [Finset.sdiff_eq_self_iff_disjoint]; exact hBdisj
  have hhB : h B = B := by
    simp only [hhdef, if_neg (Ne.symm hAB)]
    have hwnotBset : w ∉ B := hwnotB
    rw [if_neg hwnotBset, Finset.union_empty, hBS]
  -- h is not injective on the image, so the card strictly drops
  have hle : ((univ.image f).image h).card ≤ (univ.image f).card := Finset.card_image_le
  have hne : ((univ.image f).image h).card ≠ (univ.image f).card := by
    intro he