import PaperII.L2Family
import PaperII.L1
import PaperII.IsoInvariance
import PaperII.ConvexSeq

/-!
# Paper II — L2 discrete-convexity consequence (ledger Lemma 4.1)

`H_k` interpolation family (built around the frozen `classCopy`), `f k = Φτ(H_k)`, the midpoint
convexity `fseq_midpoint` DERIVED FROM L1 (+ the single-D7 step `moveGraph_insert_eq_replaceVertex`),
and the consequence `phiTau_le_max_classCopy` via `convexSeq_le_max_endpoints`.
-/

open scoped BigOperators Classical
open Finset

namespace PaperII

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- First `m` vertices of `S` via an arbitrary enumeration. -/
noncomputable def takeSet (S : Finset V) (m : ℕ) : Finset V := (S.toList.take m).toFinset

/-- The L2 interpolation family over `[0, |S_A|+|S_B|]`. -/
noncomputable def Hk (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (k : ℕ) :
    SimpleGraph V :=
  if k ≤ (sourceClass G A).card
  then moveGraph G A B (takeSet (sourceClass G A) ((sourceClass G A).card - k))
  else moveGraph G B A (takeSet (sourceClass G B) (k - (sourceClass G A).card))

/-- `f k = Φτ(H_k)`, defined via the `moveGraph` branches so each `phiTau` uses the frozen
`moveGraph` `DecidableRel` instance (no instance diamond). -/
noncomputable def fseq (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (k : ℕ) : ℝ :=
  if k ≤ (sourceClass G A).card
  then phiTau (moveGraph G A B (takeSet (sourceClass G A) ((sourceClass G A).card - k)))
  else phiTau (moveGraph G B A (takeSet (sourceClass G B) (k - (sourceClass G A).card)))

/-! ## Basic facts about `takeSet` -/

omit [Fintype V] in
theorem takeSet_zero (S : Finset V) : takeSet S 0 = ∅ := by simp [takeSet]

omit [Fintype V] in
theorem takeSet_of_card_le (S : Finset V) {m : ℕ} (h : S.card ≤ m) : takeSet S m = S := by
  unfold takeSet
  rw [List.take_of_length_le (by rw [Finset.length_toList]; exact h)]
  simp

omit [Fintype V] in
theorem takeSet_card (S : Finset V) : takeSet S S.card = S := takeSet_of_card_le S (le_refl _)

omit [Fintype V] in
theorem takeSet_subset (S : Finset V) (m : ℕ) : takeSet S m ⊆ S := by
  unfold takeSet
  intro x hx
  simp only [List.mem_toFinset] at hx
  simpa using List.take_subset m S.toList hx

omit [Fintype V] in
theorem takeSet_succ (S : Finset V) {m : ℕ} (h : m < S.card) :
    ∃ w, w ∈ S ∧ w ∉ takeSet S m ∧ takeSet S (m + 1) = insert w (takeSet S m) := by
  have hlen : m < S.toList.length := by rw [Finset.length_toList]; exact h
  have hsplit : S.toList.take (m + 1) = S.toList.take m ++ [S.toList[m]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hlen]; rfl
  have hnodup : (S.toList.take (m + 1)).Nodup := S.nodup_toList.sublist (List.take_sublist _ _)
  rw [hsplit, List.nodup_append] at hnodup
  have hnotmem : S.toList[m] ∉ S.toList.take m := fun hc =>
    hnodup.2.2 (S.toList[m]) hc (S.toList[m]) (by simp) rfl
  refine ⟨S.toList[m], ?_, ?_, ?_⟩
  · rw [← Finset.mem_toList]; exact List.getElem_mem hlen
  · unfold takeSet; simpa using hnotmem
  · unfold takeSet; rw [hsplit, List.toFinset_append]
    ext y; simp only [Finset.mem_union, List.toFinset_cons, List.toFinset_nil,
      Finset.mem_insert]; tauto

/-! ## Adjacency helpers for `moveGraph` -/

theorem mem_sourceClass (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (v : V) :
    v ∈ sourceClass G A ↔ G.neighborFinset v = A := by simp [sourceClass]

theorem sourceClass_not_mem_target {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset V} {v : V}
    (hv : v ∈ sourceClass G A) : v ∉ A := by
  rw [mem_sourceClass] at hv; rw [← hv]; simp [SimpleGraph.mem_neighborFinset]

omit [DecidableEq V] in
theorem adj_iff_mem_nbhd (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    G.Adj x y ↔ y ∈ G.neighborFinset x := by simp [SimpleGraph.mem_neighborFinset]

omit [DecidableEq V] in
theorem moveRel_symm (G : SimpleGraph V) [DecidableRel G.Adj] (A B M : Finset V) (a b : V) :
    moveRel G A B M a b ↔ moveRel G A B M b a := by
  unfold moveRel; constructor <;> (rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)) <;>
    first
      | exact Or.inl ⟨h2, h1, h3.symm⟩
      | exact Or.inr (Or.inr ⟨h1, h2, h3⟩)
      | exact Or.inr (Or.inl ⟨h1, h2, h3⟩)

omit [DecidableEq V] in
theorem moveGraph_adj (G : SimpleGraph V) [DecidableRel G.Adj] (A B M : Finset V) (a b : V) :
    (moveGraph G A B M).Adj a b ↔ a ≠ b ∧ moveRel G A B M a b := by
  unfold moveGraph; rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, (moveRel_symm G A B M b a).1 h⟩
  · rintro ⟨hne, h⟩; exact ⟨hne, Or.inl h⟩

/-- An unmoved vertex of the `A`-class keeps neighborhood `A`. -/
theorem moveGraph_adj_unmoved (G : SimpleGraph V) [DecidableRel G.Adj] {A B M : Finset V}
    (hMA : M ⊆ sourceClass G A) (hd : Disjoint (sourceClass G A) B)
    {p : V} (hp : p ∈ sourceClass G A) (hpM : p ∉ M) (x : V) :
    (moveGraph G A B M).Adj p x ↔ x ∈ A := by
  have hpA : G.neighborFinset p = A := (mem_sourceClass G A p).1 hp
  have hpB : p ∉ B := fun hc => (Finset.disjoint_left.1 hd) hp hc
  rw [moveGraph_adj]
  constructor
  · rintro ⟨_, hmr⟩
    rcases hmr with ⟨_, _, h3⟩ | ⟨_, h2, _⟩ | ⟨_, _, h3⟩
    · rw [adj_iff_mem_nbhd, hpA] at h3; exact h3
    · exact absurd h2 hpM
    · exact absurd h3 hpB
  · intro hxA
    have hxp : x ≠ p := fun hc => sourceClass_not_mem_target hp (hc ▸ hxA)
    have hxM : x ∉ M := fun hxM => sourceClass_not_mem_target (hMA hxM) hxA
    exact ⟨(Ne.symm hxp), Or.inl ⟨fun _ => hpM, fun _ => hxM,
      by rw [adj_iff_mem_nbhd, hpA]; exact hxA⟩⟩

/-- A moved vertex of the `A`-class acquires neighborhood `B`. -/
theorem moveGraph_adj_moved (G : SimpleGraph V) [DecidableRel G.Adj] {A B M : Finset V}
    (hMA : M ⊆ sourceClass G A) (hd : Disjoint (sourceClass G A) B)
    {p : V} (hpM : p ∈ M) (x : V) :
    (moveGraph G A B M).Adj p x ↔ x ∈ B := by
  have hpA : G.neighborFinset p = A := (mem_sourceClass G A p).1 (hMA hpM)
  have hpB : p ∉ B := fun hc => (Finset.disjoint_left.1 hd) (hMA hpM) hc
  rw [moveGraph_adj]
  constructor
  · rintro ⟨_, hmr⟩
    rcases hmr with ⟨h1, _, _⟩ | ⟨_, _, h3⟩ | ⟨_, _, h3⟩
    · exact absurd hpM (h1 hpA)
    · exact h3
    · exact absurd h3 hpB
  · intro hxB
    have hxp : x ≠ p := fun hc => hpB (hc ▸ hxB)
    exact ⟨(Ne.symm hxp), Or.inr (Or.inl ⟨hpA, hpM, hxB⟩)⟩

/-- A vertex of the `B`-class keeps neighborhood `B` under an `A → B` move. -/
theorem moveGraph_adj_sourceB (G : SimpleGraph V) [DecidableRel G.Adj] {A B M : Finset V}
    (hMA : M ⊆ sourceClass G A) (hd : Disjoint (sourceClass G A) B)
    {vB : V} (hvB : vB ∈ sourceClass G B) (x : V) :
    (moveGraph G A B M).Adj vB x ↔ x ∈ B := by
  have hvBB : G.neighborFinset vB = B := (mem_sourceClass G B vB).1 hvB
  have hvBnotB : vB ∉ B := by rw [← hvBB]; simp [SimpleGraph.mem_neighborFinset]
  have hBnotM : ∀ y, y ∈ B → y ∉ M := fun y hy hyM => (Finset.disjoint_left.1 hd) (hMA hyM) hy
  rw [moveGraph_adj]
  constructor
  · rintro ⟨_, hmr⟩
    rcases hmr with ⟨_, _, h3⟩ | ⟨_, _, h3⟩ | ⟨_, _, h3⟩
    · rw [adj_iff_mem_nbhd, hvBB] at h3; exact h3
    · exact h3
    · exact absurd h3 hvBnotB
  · intro hxB
    refine ⟨fun hc => hvBnotB (hc ▸ hxB), ?_⟩
    by_cases hvBM : vB ∈ M
    · exact Or.inr (Or.inl ⟨(mem_sourceClass G A vB).1 (hMA hvBM), hvBM, hxB⟩)
    · exact Or.inl ⟨fun _ => hvBM, fun _ => hBnotM x hxB,
        by rw [adj_iff_mem_nbhd, hvBB]; exact hxB⟩

omit [Fintype V] in
/-- `replaceVertex` only depends on the source vertex through its neighborhood. -/
theorem replaceVertex_congr_source (G : SimpleGraph V) (s s' t : V)
    (h : ∀ x, G.Adj s x ↔ G.Adj s' x) : G.replaceVertex s t = G.replaceVertex s' t := by
  ext a b
  by_cases hat : a = t <;> by_cases hbt : b = t
  · subst hat; rw [hbt]; simp [SimpleGraph.replaceVertex]
  · subst hat
    rw [G.adj_replaceVertex_iff_of_ne_right s hbt, G.adj_replaceVertex_iff_of_ne_right s' hbt]
    exact h b
  · rw [hbt, SimpleGraph.adj_comm, SimpleGraph.adj_comm (G.replaceVertex s' t) a t,
        G.adj_replaceVertex_iff_of_ne_right s hat, G.adj_replaceVertex_iff_of_ne_right s' hat]
    exact h a
  · rw [G.adj_replaceVertex_iff_of_ne s hat hbt, G.adj_replaceVertex_iff_of_ne s' hat hbt]

/-- `phiTau` depends only on the graph, not on the chosen `DecidableRel` instance. -/
theorem phiTau_congr {G G' : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (h : G = G') : phiTau G = phiTau G' := by
  subst h; congr 1

/-! ## Endpoint identifications -/

/-- Empty move is the identity. -/
theorem moveGraph_empty (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    moveGraph G A B ∅ = G := by
  unfold moveGraph
  ext a b
  rw [SimpleGraph.fromRel_adj]
  unfold moveRel
  simp only [Finset.notMem_empty, false_and, and_false, or_false, not_false_iff, implies_true,
    true_and]
  refine ⟨fun h => ?_, fun h => ⟨h.ne, ?_⟩⟩
  · rcases h.2 with hadj | hadj
    · exact hadj
    · exact hadj.symm
  · exact Or.inl h

/-- Statement 1 — single-D7 step (representative pinned to the target class). -/
theorem moveGraph_insert_eq_replaceVertex (G : SimpleGraph V) [DecidableRel G.Adj] {A B : Finset V}
    {M : Finset V} (hM : M ⊆ sourceClass G A) {w : V} (hw : w ∈ sourceClass G A) (hwM : w ∉ M)
    {vB : V} (hvB : vB ∈ sourceClass G B) (hnonadj : Disjoint (sourceClass G A) B) :
    moveGraph G A B (insert w M) = (moveGraph G A B M).replaceVertex vB w := by
  have hRHS : (moveGraph G A B M).replaceVertex vB w = copyVertex (moveGraph G A B M) w vB := rfl
  rw [hRHS]
  set H := moveGraph G A B M with hH
  have hwA : G.neighborFinset w = A := (mem_sourceClass G A w).1 hw
  have hwnotB : w ∉ B := fun hc => (Finset.disjoint_left.1 hnonadj) hw hc
  have hvBB : G.neighborFinset vB = B := (mem_sourceClass G B vB).1 hvB
  have hvBnotB : vB ∉ B := by rw [← hvBB]; simp [SimpleGraph.mem_neighborFinset]
  have hLHS_core : ∀ x, x ≠ w → ((moveGraph G A B (insert w M)).Adj w x ↔ x ∈ B) := by
    intro x _
    rw [moveGraph_adj]
    constructor
    · rintro ⟨_, hmr⟩
      rcases hmr with ⟨h1, _, _⟩ | ⟨_, _, h3⟩ | ⟨_, _, h3⟩
      · exact absurd (h1 hwA) (by simp)
      · exact h3
      · exact absurd h3 hwnotB
    · intro hxB
      exact ⟨fun hc => hwnotB (hc ▸ hxB), Or.inr (Or.inl ⟨hwA, Finset.mem_insert_self w M, hxB⟩)⟩
  have hRHS_core : ∀ x, x ≠ w → ((copyVertex H w vB).Adj w x ↔ x ∈ B) := by
    intro x hx
    rw [copyVertex_adj_v H w vB x hx, hH]
    exact moveGraph_adj_sourceB G hM hnonadj hvB x
  ext a b
  by_cases haw : a = w <;> by_cases hbw : b = w
  · subst haw; subst hbw; simp
  · subst haw; rw [hLHS_core b hbw, hRHS_core b hbw]
  · subst hbw
    rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm (copyVertex H b vB) a b,
        hLHS_core a haw, hRHS_core a haw]
  · rw [copyVertex_adj_of_ne H w vB a b haw hbw, hH, moveGraph_adj, moveGraph_adj]
    refine and_congr_right (fun _ => ?_)
    unfold moveRel
    simp only [Finset.mem_insert, haw, hbw, false_or]

/-- The mirror of `moveGraph_insert_eq_replaceVertex`: un-moving a vertex is a single D7 step. -/
theorem moveGraph_erase_eq_replaceVertex (G : SimpleGraph V) [DecidableRel G.Adj] {A B : Finset V}
    {M : Finset V} (hM : M ⊆ sourceClass G A) {m : V} (hm : m ∈ M)
    {vA : V} (hvA : vA ∈ sourceClass G A) (hvAM : vA ∉ M) (hd : Disjoint (sourceClass G A) B) :
    moveGraph G A B (M.erase m) = (moveGraph G A B M).replaceVertex vA m := by
  have hRHS : (moveGraph G A B M).replaceVertex vA m = copyVertex (moveGraph G A B M) m vA := rfl
  rw [hRHS]
  set H := moveGraph G A B M with hH
  have hmA : m ∈ sourceClass G A := hM hm
  have heraseSub : M.erase m ⊆ sourceClass G A := (Finset.erase_subset m M).trans hM
  have hm_erase : m ∉ M.erase m := Finset.notMem_erase m M
  have hLHS_core : ∀ x, x ≠ m → ((moveGraph G A B (M.erase m)).Adj m x ↔ x ∈ A) :=
    fun x _ => moveGraph_adj_unmoved G heraseSub hd hmA hm_erase x
  have hRHS_core : ∀ x, x ≠ m → ((copyVertex H m vA).Adj m x ↔ x ∈ A) := by
    intro x hx
    rw [copyVertex_adj_v H m vA x hx, hH]
    exact moveGraph_adj_unmoved G hM hd hvA hvAM x
  ext a b
  by_cases ham : a = m <;> by_cases hbm : b = m
  · subst ham; rw [hbm]; simp
  · subst ham; rw [hLHS_core b hbm, hRHS_core b hbm]
  · rw [hbm, SimpleGraph.adj_comm, SimpleGraph.adj_comm (copyVertex H m vA) a m,
        hLHS_core a ham, hRHS_core a ham]
  · rw [copyVertex_adj_of_ne H m vA a b ham hbm, hH, moveGraph_adj, moveGraph_adj]
    refine and_congr_right (fun _ => ?_)
    unfold moveRel
    simp only [Finset.mem_erase, ham, hbm, ne_eq, not_false_iff, true_and]

/-! ## `fseq` branch evaluations -/

/-- `fseq` on the `A → B` branch (`k ≤ |S_A|`). -/
theorem fseq_eq_g (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) {k : ℕ}
    (hk : k ≤ (sourceClass G A).card) :
    fseq G A B k = phiTau (moveGraph G A B (takeSet (sourceClass G A) ((sourceClass G A).card - k))) := by
  unfold fseq; rw [if_pos hk]

/-- `fseq` on the `B → A` branch (`|S_A| ≤ k`); at the seam both branches agree with `Φτ(G)`. -/
theorem fseq_eq_h (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) {k : ℕ}
    (hk : (sourceClass G A).card ≤ k) :
    fseq G A B k = phiTau (moveGraph G B A (takeSet (sourceClass G B) (k - (sourceClass G A).card))) := by
  unfold fseq
  by_cases hk' : k ≤ (sourceClass G A).card
  · rw [if_pos hk']
    have hka : k = (sourceClass G A).card := le_antisymm hk' hk
    subst hka
    simp only [Nat.sub_self, takeSet_zero]
    exact phiTau_congr (by rw [moveGraph_empty, moveGraph_empty])
  · rw [if_neg hk']

/-- Endpoint `k = |S_A|`: `H_a = G`. -/
theorem fseq_a (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    fseq G A B (sourceClass G A).card = phiTau G := by
  rw [fseq_eq_g G A B (le_refl _)]
  exact phiTau_congr (by rw [Nat.sub_self, takeSet_zero, moveGraph_empty])

/-- Endpoint `k = 0`: `H_0 = classCopy G A B`. -/
theorem fseq_zero (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    fseq G A B 0 = phiTau (classCopy G A B) := by
  rw [fseq_eq_g G A B (Nat.zero_le _)]
  exact phiTau_congr (by rw [Nat.sub_zero, takeSet_card, moveGraph_sourceClass])

/-- Endpoint `k = |S_A|+|S_B|`: `H_{a+b} = classCopy G B A`. -/
theorem fseq_top (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    fseq G A B ((sourceClass G A).card + (sourceClass G B).card) = phiTau (classCopy G B A) := by
  rw [fseq_eq_h G A B (Nat.le_add_right _ _)]
  exact phiTau_congr (by rw [Nat.add_sub_cancel_left, takeSet_card, moveGraph_sourceClass])

/-! ## Convexity -/

/-- Interior convexity of the one-sided family, derived from L1 (`phiTau_copyVertex_add`) and the
single-D7 steps (`moveGraph_insert_eq_replaceVertex`, `moveGraph_erase_eq_replaceVertex`). -/
theorem interior_convex (G : SimpleGraph V) [DecidableRel G.Adj] {A B : Finset V}
    {vB : V} (hvB : vB ∈ sourceClass G B) (hd : Disjoint (sourceClass G A) B)
    {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓ2 : ℓ + 1 ≤ (sourceClass G A).card) :
    2 * phiTau (moveGraph G A B (takeSet (sourceClass G A) ℓ))
      ≤ phiTau (moveGraph G A B (takeSet (sourceClass G A) (ℓ - 1)))
        + phiTau (moveGraph G A B (takeSet (sourceClass G A) (ℓ + 1))) := by
  obtain ⟨w, hwS, hw_notin, htake_succ⟩ :=
    takeSet_succ (sourceClass G A) (by omega : ℓ < (sourceClass G A).card)
  obtain ⟨m, hmS, hm_notin, htake_ℓ⟩ :=
    takeSet_succ (sourceClass G A) (by omega : ℓ - 1 < (sourceClass G A).card)
  rw [Nat.sub_add_cancel hℓ1] at htake_ℓ
  have hbaseSub : takeSet (sourceClass G A) ℓ ⊆ sourceClass G A := takeSet_subset _ ℓ
  have hm_moved : m ∈ takeSet (sourceClass G A) ℓ := by rw [htake_ℓ]; exact Finset.mem_insert_self m _
  have hmw : m ≠ w := fun hc => hw_notin (hc ▸ hm_moved)
  set K := moveGraph G A B (takeSet (sourceClass G A) ℓ) with hK
  have hnotadj : ¬ K.Adj m w := by
    rw [hK, moveGraph_adj_moved G hbaseSub hd hm_moved w]
    exact fun hwB => (Finset.disjoint_left.1 hd) hwS hwB
  have hE1 : copyVertex K w m = moveGraph G A B (takeSet (sourceClass G A) (ℓ + 1)) := by
    have hcongr : K.replaceVertex m w = K.replaceVertex vB w := by
      apply replaceVertex_congr_source
      intro x
      rw [hK, moveGraph_adj_moved G hbaseSub hd hm_moved x]
      exact (moveGraph_adj_sourceB G hbaseSub hd hvB x).symm
    show K.replaceVertex m w = _
    rw [hcongr, htake_succ, hK]
    exact (moveGraph_insert_eq_replaceVertex G hbaseSub hwS hw_notin hvB hd).symm
  have hE2 : copyVertex K m w = moveGraph G A B (takeSet (sourceClass G A) (ℓ - 1)) := by
    have herase : (takeSet (sourceClass G A) ℓ).erase m = takeSet (sourceClass G A) (ℓ - 1) := by
      rw [htake_ℓ, Finset.erase_insert hm_notin]
    show K.replaceVertex w m = _
    rw [← herase, hK]
    exact (moveGraph_erase_eq_replaceVertex G hbaseSub hm_moved hwS hw_notin hd).symm
  have hL1 := phiTau_copyVertex_add K hnotadj hmw
  rw [phiTau_congr hE1, phiTau_congr hE2] at hL1
  linarith [hL1]

/-- Convexity lemma — midpoint inequality DERIVED FROM L1 (+ Statement 1). -/
theorem fseq_midpoint (G : SimpleGraph V) [DecidableRel G.Adj] {A B : Finset V}
    (hA : (sourceClass G A).Nonempty) (hB : (sourceClass G B).Nonempty) (hAB : A ≠ B)
    (hAd : Disjoint (sourceClass G A) B) (hBd : Disjoint (sourceClass G B) A)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ (sourceClass G A).card + (sourceClass G B).card) :
    2 * fseq G A B k ≤ fseq G A B (k - 1) + fseq G A B (k + 1) := by
  obtain ⟨vA, hvA⟩ := hA
  obtain ⟨vB, hvB⟩ := hB
  rcases lt_trichotomy k (sourceClass G A).card with hlt | heq | hgt
  · -- `k < |S_A|`: interior of the `A → B` side.
    rw [fseq_eq_g G A B (le_of_lt hlt), fseq_eq_g G A B (by omega : k - 1 ≤ (sourceClass G A).card),
      fseq_eq_g G A B (by omega : k + 1 ≤ (sourceClass G A).card)]
    have c1 : phiTau (moveGraph G A B (takeSet (sourceClass G A) ((sourceClass G A).card - (k - 1))))
        = phiTau (moveGraph G A B (takeSet (sourceClass G A) (((sourceClass G A).card - k) + 1))) :=
      phiTau_congr (congrArg (fun n => moveGraph G A B (takeSet (sourceClass G A) n))
        (by omega : (sourceClass G A).card - (k - 1) = ((sourceClass G A).card - k) + 1))
    have c2 : phiTau (moveGraph G A B (takeSet (sourceClass G A) ((sourceClass G A).card - (k + 1))))
        = phiTau (moveGraph G A B (takeSet (sourceClass G A) (((sourceClass G A).card - k) - 1))) :=
      phiTau_congr (congrArg (fun n => moveGraph G A B (takeSet (sourceClass G A) n))
        (by omega : (sourceClass G A).card - (k + 1) = ((sourceClass G A).card - k) - 1))
    rw [c1, c2]
    have hconv := interior_convex G hvB hAd (ℓ := (sourceClass G A).card - k) (by omega) (by omega)
    linarith [hconv]
  · -- `k = |S_A|`: the seam, a direct application of L1 to `G`.
    have ha_pos : 0 < (sourceClass G A).card := Finset.card_pos.mpr ⟨vA, hvA⟩
    have hb_pos : 0 < (sourceClass G B).card := Finset.card_pos.mpr ⟨vB, hvB⟩
    obtain ⟨w1, hw1S, _, hAtake⟩ := takeSet_succ (sourceClass G A) ha_pos
    obtain ⟨vB1, hvB1S, _, hBtake⟩ := takeSet_succ (sourceClass G B) hb_pos
    simp only [Nat.zero_add, takeSet_zero] at hAtake hBtake
    have hG1 : moveGraph G A B (takeSet (sourceClass G A) 1) = copyVertex G w1 vB1 := by
      rw [hAtake, moveGraph_insert_eq_replaceVertex G (Finset.empty_subset _) hw1S
        (Finset.notMem_empty _) hvB1S hAd, moveGraph_empty]
      rfl
    have hG2 : moveGraph G B A (takeSet (sourceClass G B) 1) = copyVertex G vB1 w1 := by
      rw [hBtake, moveGraph_insert_eq_replaceVertex G (A := B) (B := A) (Finset.empty_subset _)
        hvB1S (Finset.notMem_empty _) hw1S hBd, moveGraph_empty]
      rfl
    have hfk : fseq G A B k = phiTau G := by rw [heq]; exact fseq_a G A B
    have hgk1 : fseq G A B (k - 1) = phiTau (copyVertex G w1 vB1) := by
      have hidx : (sourceClass G A).card - (k - 1) = 1 := by omega
      rw [fseq_eq_g G A B (by omega : k - 1 ≤ (sourceClass G A).card), hidx]
      exact phiTau_congr hG1
    have hgk1' : fseq G A B (k + 1) = phiTau (copyVertex G vB1 w1) := by
      have hidx : (k + 1) - (sourceClass G A).card = 1 := by omega
      rw [fseq_eq_h G A B (by omega : (sourceClass G A).card ≤ k + 1), hidx]
      exact phiTau_congr hG2
    rw [hfk, hgk1, hgk1']
    have huv : ¬ G.Adj vB1 w1 := by
      intro hadj
      have hmem : w1 ∈ G.neighborFinset vB1 := (adj_iff_mem_nbhd G vB1 w1).1 hadj
      rw [(mem_sourceClass G B vB1).1 hvB1S] at hmem
      exact (Finset.disjoint_left.1 hAd) hw1S hmem
    have hne : vB1 ≠ w1 := by
      intro hc
      have h1 : G.neighborFinset w1 = A := (mem_sourceClass G A w1).1 hw1S
      have h2 : G.neighborFinset vB1 = B := (mem_sourceClass G B vB1).1 hvB1S
      rw [hc] at h2
      exact hAB (h1.symm.trans h2)
    exact phiTau_copyVertex_add G huv hne
  · -- `k > |S_A|`: interior of the `B → A` side.
    rw [fseq_eq_h G A B (le_of_lt hgt),
      fseq_eq_h G A B (by omega : (sourceClass G A).card ≤ k - 1),
      fseq_eq_h G A B (by omega : (sourceClass G A).card ≤ k + 1)]
    have c1 : phiTau (moveGraph G B A (takeSet (sourceClass G B) ((k - 1) - (sourceClass G A).card)))
        = phiTau (moveGraph G B A (takeSet (sourceClass G B) ((k - (sourceClass G A).card) - 1))) :=
      phiTau_congr (congrArg (fun n => moveGraph G B A (takeSet (sourceClass G B) n))
        (by omega : (k - 1) - (sourceClass G A).card = (k - (sourceClass G A).card) - 1))
    have c2 : phiTau (moveGraph G B A (takeSet (sourceClass G B) ((k + 1) - (sourceClass G A).card)))
        = phiTau (moveGraph G B A (takeSet (sourceClass G B) ((k - (sourceClass G A).card) + 1))) :=
      phiTau_congr (congrArg (fun n => moveGraph G B A (takeSet (sourceClass G B) n))
        (by omega : (k + 1) - (sourceClass G A).card = (k - (sourceClass G A).card) + 1))
    rw [c1, c2]
    have hconv := interior_convex G (A := B) (B := A) hvA hBd
      (ℓ := k - (sourceClass G A).card) (by omega) (by omega)
    linarith [hconv]

/-- L2 consequence (ledger Lemma 4.1): `Φτ(G) ≤ max` of the two full clone-class copies. -/
theorem phiTau_le_max_classCopy (G : SimpleGraph V) [DecidableRel G.Adj] {A B : Finset V}
    (hA : (sourceClass G A).Nonempty) (hB : (sourceClass G B).Nonempty) (hAB : A ≠ B)
    (hAd : Disjoint (sourceClass G A) B) (hBd : Disjoint (sourceClass G B) A) :
    phiTau G ≤ max (phiTau (classCopy G A B)) (phiTau (classCopy G B A)) := by
  have hconv : ∀ j, j + 2 ≤ (sourceClass G A).card + (sourceClass G B).card →
      2 * fseq G A B (j + 1) ≤ fseq G A B j + fseq G A B (j + 2) := by
    intro j hj