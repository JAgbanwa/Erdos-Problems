/-
# BKLO §11, cells route: connectors defeat the cell-wise divisibility obstruction

A reserved structure `A` pins, *before* the remainder is known, the residue mod `3` of everything
it can absorb (`BKLO.card_mod_three_eq_of_absorbs`).  So an absorber assembled as a disjoint union
of **per-cell** pieces can only absorb remainders that are triangle-divisible cell by cell, while
§10 delivers only *global* divisibility (`BKLO.not_absorbs_all_even_of_cell` makes this precise).

This file removes that obstruction, in the way BKLO's absorbing structures do: the reservation is
not a disjoint union of per-cell pieces, it also contains, on the boundary between two consecutive
cells, two bounded **connectors** — even-degree edge sets with `|c| ≡ 1 (mod 3)` lying inside the
cores of *both* neighbouring cells.  A connector may be absorbed on either side, so assigning the
two connectors of a boundary shifts the residue absorbed by a cell by `0`, `1` or `2`.  Sweeping
along the chain of cells, the residues can then be matched cell by cell, and the sweep closes at
the last cell precisely because the *global* residue vanishes.

The main results are

* `BKLO.chainSet` — the reservation-plus-remainder of a chain of cells with its connectors;
* `BKLO.triDecomp_chainSet` — a chain of cells absorbs every remainder confined to the cells that
  is even at every vertex, under only the **global** divisibility `3 ∣ |A ∪ H|`.

Everything here is `sorry`-free.
-/
import BKLO.BoundedLeftover

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-- An edge-disjoint union of two even-degree edge sets is even-degree. -/
theorem evenDegrees_union_of_disjoint {A B : Finset (Sym2 V)} (h : Disjoint A B)
    (hA : EvenDegrees A) (hB : EvenDegrees B) : EvenDegrees (A ∪ B) := by
  intro v
  rw [edeg_union_of_disjoint h]
  exact (hA v).add (hB v)

/-- **A core absorbing structure absorbs in exactly the form the chain needs.**  For a set `Z`
inside the core that is even at every vertex, the divisibility that matters is the *joint* one,
`3 ∣ |R ∪ Z|`: since `R` is itself triangle-decomposable, this is equivalent to `3 ∣ |Z|`, so `Z`
is triangle-divisible and `R` contains an absorber for it. -/
theorem CoreAbsorbers.absorbs_even {U : Finset V} {R Z : Finset (Sym2 V)}
    (h : CoreAbsorbers U R) (hZU : Z ⊆ cliqueEdges U) (hZev : EvenDegrees Z)
    (hdisj : Disjoint R Z) (hdvd : 3 ∣ (R ∪ Z).card) : TriDecomp (R ∪ Z) := by
  classical
  have hRcard : 3 ∣ R.card := (h.triDecomp.triDivisible).2
  have hcards : (R ∪ Z).card = R.card + Z.card := Finset.card_union_of_disjoint hdisj
  have hZcard : 3 ∣ Z.card := by omega
  obtain ⟨Ab, hAbR, habs, hrest⟩ := h.absorb Z hZU ⟨hZev, hZcard⟩
  have hsplit : R ∪ Z = (Ab ∪ Z) ∪ (R \ Ab) := by
    have hAbZ : Ab ∪ (R \ Ab) = R := Finset.union_sdiff_of_subset hAbR
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (heR | heZ)
      · by_cases heA : e ∈ Ab
        · exact Or.inl (Or.inl heA)
        · exact Or.inr ⟨heR, heA⟩
      · exact Or.inl (Or.inr heZ)
    · rintro ((heA | heZ) | ⟨heR, -⟩)
      · exact Or.inl (hAbR heA)
      · exact Or.inr heZ
      · exact Or.inl heR
  have hdisj2 : Disjoint (Ab ∪ Z) (R \ Ab) := by
    refine Finset.disjoint_left.2 fun e he he' => ?_
    rw [Finset.mem_sdiff] at he'
    rcases Finset.mem_union.1 he with h1 | h1
    · exact he'.2 h1
    · exact (Finset.disjoint_left.1 hdisj) he'.1 h1
  rw [hsplit]
  exact TriDecomp.union hdisj2 habs.2.2 hrest

/-! ### A remainder confined to disjoint cells splits into even per-cell remainders -/

/-- A remainder confined to the cells is the union of its per-cell parts. -/
theorem eq_biUnion_inter_cliqueEdges {H E : Finset (Sym2 V)} {Pl : Finset (Finset V)}
    (hH : H ⊆ insideParts E Pl) (hloop : ∀ e ∈ H, ¬ e.IsDiag) :
    H = Pl.biUnion (fun P => H ∩ cliqueEdges P) := by
  classical
  refine Finset.Subset.antisymm (fun e he => ?_) (fun e he => ?_)
  · obtain ⟨-, W, hW, hWe⟩ := mem_insideParts.1 (hH he)
    exact Finset.mem_biUnion.2 ⟨W, hW,
      Finset.mem_inter.2 ⟨he, mem_cliqueEdgesV.2 ⟨hWe, hloop e he⟩⟩⟩
  · obtain ⟨W, -, hWe⟩ := Finset.mem_biUnion.1 he
    exact (Finset.mem_inter.1 hWe).1

/-- **The per-cell remainders inherit the parity of the remainder.**  If the cells are pairwise
disjoint and every edge of `H` lies inside a cell, then all the edges of `H` at a vertex of a cell
`P` lie inside `P`, so `H ∩ K_P` has the same degrees as `H` there, and no edges elsewhere.

This is the parity half of what a cells absorber must absorb; the divisibility half is what the
connectors of `BKLO.ChainData` supply. -/
theorem evenDegrees_inter_cliqueEdges {H E : Finset (Sym2 V)} {Pl : Finset (Finset V)}
    {P : Finset V} (hH : H ⊆ insideParts E Pl) (hloop : ∀ e ∈ H, ¬ e.IsDiag)
    (hHev : EvenDegrees H) (hP : P ∈ Pl)
    (hdisj : ∀ W ∈ Pl, ∀ W' ∈ Pl, W ≠ W' → Disjoint W W') :
    EvenDegrees (H ∩ cliqueEdges P) := by
  classical
  intro v
  by_cases hv : v ∈ P
  · have hfilter : (H ∩ cliqueEdges P).filter (fun e => v ∈ e) = H.filter (fun e => v ∈ e) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_inter]
      constructor
      · rintro ⟨⟨he, -⟩, hve⟩; exact ⟨he, hve⟩
      · rintro ⟨he, hve⟩
        obtain ⟨-, W, hW, hWe⟩ := mem_insideParts.1 (hH he)
        have hWP : W = P := by
          by_contra hne
          exact (Finset.disjoint_left.1 (hdisj W hW P hP hne)) (hWe v hve) hv
        subst hWP
        exact ⟨⟨he, mem_cliqueEdgesV.2 ⟨hWe, hloop e he⟩⟩, hve⟩
    have hev := hHev v
    unfold edeg at hev ⊢
    rw [hfilter]
    exact hev
  · have hzero : edeg (H ∩ cliqueEdges P) v = 0 := by
      unfold edeg
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he hve
      exact hv ((mem_cliqueEdgesV.1 (Finset.mem_inter.1 he).2).1 v hve)
    rw [hzero]
    exact ⟨0, rfl⟩

/-- All the material carried by cell `i`: its reserved absorber `A i`, the remainder `Y i` left
inside it, and the two connectors `c₁ i`, `c₂ i` reserved on the boundary to cell `i+1`. -/
def cellPiece (A Y c₁ c₂ : ℕ → Finset (Sym2 V)) (i : ℕ) : Finset (Sym2 V) :=
  A i ∪ Y i ∪ c₁ i ∪ c₂ i

/-- **The chain of `n` cells starting at cell `s`**, with its connectors: cell `s` contributes its
absorber and its remainder, and, unless it is the last cell of the chain, the two connectors of the
boundary to cell `s+1`. -/
def chainSet (A Y c₁ c₂ : ℕ → Finset (Sym2 V)) : ℕ → ℕ → Finset (Sym2 V)
  | _, 0 => ∅
  | s, (n + 1) =>
      (A s ∪ Y s) ∪ (if n = 0 then (∅ : Finset (Sym2 V)) else c₁ s ∪ c₂ s) ∪
        chainSet A Y c₁ c₂ (s + 1) n

theorem chainSet_one (A Y c₁ c₂ : ℕ → Finset (Sym2 V)) (s : ℕ) :
    chainSet A Y c₁ c₂ s 1 = A s ∪ Y s := by
  simp [chainSet]

theorem chainSet_succ_succ (A Y c₁ c₂ : ℕ → Finset (Sym2 V)) (s n : ℕ) :
    chainSet A Y c₁ c₂ s (n + 2) =
      (A s ∪ Y s) ∪ (c₁ s ∪ c₂ s) ∪ chainSet A Y c₁ c₂ (s + 1) (n + 1) := by
  simp [chainSet]

/-- Every edge of a chain starting at cell `s` belongs to the material of some cell `i ≥ s`. -/
theorem chainSet_subset_cellPiece (A Y c₁ c₂ : ℕ → Finset (Sym2 V)) :
    ∀ (n s : ℕ), ∀ e ∈ chainSet A Y c₁ c₂ s n,
      ∃ i, s ≤ i ∧ i < s + n ∧ e ∈ cellPiece A Y c₁ c₂ i := by
  intro n
  induction n with
  | zero => intro s e he; simp [chainSet] at he
  | succ n ih =>
    intro s e he
    rw [chainSet] at he
    rcases Finset.mem_union.1 he with h | h
    · refine ⟨s, le_rfl, by omega, ?_⟩
      rcases Finset.mem_union.1 h with h' | h'
      · unfold cellPiece
        exact Finset.mem_union_left _ (Finset.mem_union_left _ h')
      · by_cases hn : n = 0
        · simp [hn] at h'
        · rw [if_neg hn] at h'
          unfold cellPiece
          rcases Finset.mem_union.1 h' with h'' | h''
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ h'')
          · exact Finset.mem_union_right _ h''
    · obtain ⟨i, hi, hi2, hie⟩ := ih (s + 1) e h
      exact ⟨i, by omega, by omega, hie⟩

/-- The absorber of a cell of the chain is part of the chain. -/
theorem subset_chainSet_absorber (A Y c₁ c₂ : ℕ → Finset (Sym2 V)) :
    ∀ (n s i : ℕ), s ≤ i → i < s + n → A i ⊆ chainSet A Y c₁ c₂ s n := by
  intro n
  induction n with
  | zero => intro s i hsi hi; exact absurd hi (by omega)
  | succ n ih =>
    intro s i hsi hi
    rcases Nat.eq_or_lt_of_le hsi with rfl | hlt
    · intro e he
      rw [chainSet]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ he))
    · intro e he
      rw [chainSet]
      exact Finset.mem_union_right _ (ih (s + 1) i (by omega) (by omega) he)

/-- The connectors of a boundary of the chain are part of the chain. -/
theorem subset_chainSet_conn (A Y c₁ c₂ : ℕ → Finset (Sym2 V)) :
    ∀ (n s i : ℕ), s ≤ i → i + 1 < s + n → c₁ i ∪ c₂ i ⊆ chainSet A Y c₁ c₂ s n := by
  intro n
  induction n with
  | zero => intro s i hsi hi; exact absurd hi (by omega)
  | succ n ih =>
    intro s i hsi hi
    rcases Nat.eq_or_lt_of_le hsi with rfl | hlt
    · have hn : n ≠ 0 := by omega
      intro e he
      simp only [chainSet, if_neg hn]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ he)
    · intro e he
      rw [chainSet]
      exact Finset.mem_union_right _ (ih (s + 1) i (by omega) (by omega) he)

/-- A set disjoint from the material of every cell `i ≥ s` is disjoint from the chain at `s`. -/
theorem disjoint_chainSet {A Y c₁ c₂ : ℕ → Finset (Sym2 V)} {W : Finset (Sym2 V)} {s n : ℕ}
    (h : ∀ i, s ≤ i → i < s + n → Disjoint W (cellPiece A Y c₁ c₂ i)) :
    Disjoint W (chainSet A Y c₁ c₂ s n) := by
  refine Finset.disjoint_left.2 fun e heW hec => ?_
  obtain ⟨i, hi, hi2, hie⟩ := chainSet_subset_cellPiece A Y c₁ c₂ n s e hec
  exact (Finset.disjoint_left.1 (h i hi hi2)) heW hie

/-- **Splitting the chain into the reservation and the remainders.**  The chain with remainders
`Y` is the chain with empty remainders — the reserved structure — together with the union of the
remainders of its cells. -/
theorem chainSet_split (A Y c₁ c₂ : ℕ → Finset (Sym2 V)) :
    ∀ (n s : ℕ), chainSet A Y c₁ c₂ s n
      = chainSet A (fun _ => ∅) c₁ c₂ s n ∪ (Finset.Ico s (s + n)).biUnion Y := by
  intro n
  induction n with
  | zero => intro s; simp [chainSet]
  | succ n ih =>
    intro s
    have hIco : (Finset.Ico s (s + (n + 1))).biUnion Y
        = Y s ∪ (Finset.Ico (s + 1) (s + 1 + n)).biUnion Y := by
      ext e
      simp only [Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_union]
      constructor
      · rintro ⟨i, hi, hie⟩
        rcases Nat.eq_or_lt_of_le hi.1 with rfl | hlt
        · exact Or.inl hie
        · exact Or.inr ⟨i, ⟨by omega, by omega⟩, hie⟩
      · rintro (hs | ⟨i, hi, hie⟩)
        · exact ⟨s, ⟨le_rfl, by omega⟩, hs⟩
        · exact ⟨i, ⟨by omega, by omega⟩, hie⟩
    rw [chainSet, chainSet, ih (s + 1), hIco]
    ext e
    simp only [Finset.mem_union, Finset.notMem_empty, or_false]
    itauto

section Chain

variable (A Y c₁ c₂ K : ℕ → Finset (Sym2 V)) (N : ℕ)

/-- **The hypotheses of the chain absorption theorem**, for a chain of `N` cells.  Cell `i` carries
a reserved absorber `A i` for its core `K i`, a remainder `Y i` inside the core, and, unless it is
the last cell, two connectors `c₁ i`, `c₂ i` inside the cores of both cell `i` and cell `i+1`, each
with `|c| ≡ 1 (mod 3)`.  Only the indices `i < N` are constrained; outside the chain all four
families are meant to be empty. -/
structure ChainData : Prop where
  /-- `A i` absorbs every even-degree edge set inside the core `K i` of the right residue. -/
  absorb : ∀ i < N, ∀ Z : Finset (Sym2 V), Z ⊆ K i → EvenDegrees Z → Disjoint (A i) Z →
    3 ∣ (A i ∪ Z).card → TriDecomp (A i ∪ Z)
  /-- the remainder of cell `i` lies inside its core -/
  remainder_subset : ∀ i < N, Y i ⊆ K i
  /-- the remainder of cell `i` is even at every vertex -/
  remainder_even : ∀ i < N, EvenDegrees (Y i)
  /-- the first connector of the boundary `i` lies in the core of cell `i` -/
  conn₁_left : ∀ i, i + 1 < N → c₁ i ⊆ K i
  /-- the first connector of the boundary `i` lies in the core of cell `i+1` -/
  conn₁_right : ∀ i, i + 1 < N → c₁ i ⊆ K (i + 1)
  /-- the second connector of the boundary `i` lies in the core of cell `i` -/
  conn₂_left : ∀ i, i + 1 < N → c₂ i ⊆ K i
  /-- the second connector of the boundary `i` lies in the core of cell `i+1` -/
  conn₂_right : ∀ i, i + 1 < N → c₂ i ⊆ K (i + 1)
  /-- the connectors are even at every vertex -/
  conn₁_even : ∀ i, i + 1 < N → EvenDegrees (c₁ i)
  /-- the connectors are even at every vertex -/
  conn₂_even : ∀ i, i + 1 < N → EvenDegrees (c₂ i)
  /-- a connector has `1` edge mod `3`: assigning it shifts the absorbed residue by one -/
  conn₁_card : ∀ i, i + 1 < N → (c₁ i).card % 3 = 1
  /-- a connector has `1` edge mod `3`: assigning it shifts the absorbed residue by one -/
  conn₂_card : ∀ i, i + 1 < N → (c₂ i).card % 3 = 1
  /-- distinct cells carry disjoint material -/
  pieces_disjoint : ∀ i < N, ∀ j < N, i ≠ j →
    Disjoint (cellPiece A Y c₁ c₂ i) (cellPiece A Y c₁ c₂ j)
  /-- the absorber and the remainder of a cell are edge-disjoint -/
  absorber_remainder_disjoint : ∀ i < N, Disjoint (A i) (Y i)
  /-- the connectors are edge-disjoint from the absorber and the remainder -/
  conn_disjoint : ∀ i, i + 1 < N → Disjoint (A i ∪ Y i) (c₁ i ∪ c₂ i)
  /-- the two connectors of a boundary are edge-disjoint -/
  conn₁₂_disjoint : ∀ i, i + 1 < N → Disjoint (c₁ i) (c₂ i)

variable {A Y c₁ c₂ K N}

/-- Splitting the two connectors of a boundary: the left part can be chosen to have any prescribed
number of edges mod `3`. -/
theorem exists_conn_split (h : ChainData A Y c₁ c₂ K N) {s : ℕ} (hs : s + 1 < N) (b : ℕ) :
    ∃ Lt Rt : Finset (Sym2 V), Lt ∪ Rt = c₁ s ∪ c₂ s ∧ Disjoint Lt Rt ∧
      Lt ⊆ c₁ s ∪ c₂ s ∧ Rt ⊆ c₁ s ∪ c₂ s ∧ EvenDegrees Lt ∧ EvenDegrees Rt ∧
      3 ∣ b + Lt.card := by
  have hc12 := h.conn₁₂_disjoint s hs
  have hcard : (c₁ s ∪ c₂ s).card = (c₁ s).card + (c₂ s).card :=
    Finset.card_union_of_disjoint hc12
  have h1 := h.conn₁_card s hs
  have h2 := h.conn₂_card s hs
  have hb3 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases hb3 with hb | hb | hb
  · exact ⟨∅, c₁ s ∪ c₂ s, by simp, by simp, by simp, Finset.Subset.rfl, by simp [EvenDegrees],
      evenDegrees_union_of_disjoint hc12 (h.conn₁_even s hs) (h.conn₂_even s hs),
      by simp only [Finset.card_empty]; omega⟩
  · refine ⟨c₁ s ∪ c₂ s, ∅, by simp, by simp, Finset.Subset.rfl, by simp,
      evenDegrees_union_of_disjoint hc12 (h.conn₁_even s hs) (h.conn₂_even s hs), by simp [EvenDegrees],
      by omega⟩
  · exact ⟨c₁ s, c₂ s, rfl, hc12, Finset.subset_union_left, Finset.subset_union_right,
      h.conn₁_even s hs, h.conn₂_even s hs, by omega⟩

/-- **Chain absorption.**  A chain of cells, each with its own bounded absorber and with two
connectors on each boundary, absorbs the remainder left in *all* the cells under the single
*global* divisibility hypothesis.

The statement is the inductive one: `X` is the material handed over by the previous boundary. -/
theorem triDecomp_chainSet_aux (h : ChainData A Y c₁ c₂ K N) :
    ∀ (n s : ℕ) (X : Finset (Sym2 V)), 0 < n → s + n ≤ N → X ⊆ K s → EvenDegrees X →
      (∀ i, s ≤ i → i < N → Disjoint X (cellPiece A Y c₁ c₂ i)) →
      3 ∣ (X ∪ chainSet A Y c₁ c₂ s n).card →
      TriDecomp (X ∪ chainSet A Y c₁ c₂ s n) := by
  intro n
  induction n with
  | zero => intro s X hn; exact absurd hn (by simp)
  | succ n ih =>
    intro s X _ hsN hXK hXev hXdisj hdvd
    have hsltN : s < N := by omega
    -- the material of cell `s` that `X` must avoid
    have hXA : Disjoint X (A s) :=
      (hXdisj s le_rfl hsltN).mono_right
        ((Finset.subset_union_left.trans Finset.subset_union_left).trans Finset.subset_union_left)
    have hXY : Disjoint X (Y s) :=
      (hXdisj s le_rfl hsltN).mono_right
        ((Finset.subset_union_right.trans Finset.subset_union_left).trans Finset.subset_union_left)
    have hXc : Disjoint X (c₁ s ∪ c₂ s) := by
      refine Finset.disjoint_union_right.2 ⟨?_, ?_⟩
      · exact (hXdisj s le_rfl hsltN).mono_right (Finset.subset_union_right.trans Finset.subset_union_left)
      · exact (hXdisj s le_rfl hsltN).mono_right Finset.subset_union_right
    cases n with
    | zero =>
      -- the last cell of the chain: the global divisibility is exactly what it needs
      rw [chainSet_one] at hdvd ⊢
      have hset : X ∪ (A s ∪ Y s) = A s ∪ (X ∪ Y s) := by
        ext e; simp only [Finset.mem_union]; itauto
      rw [hset] at hdvd ⊢
      refine h.absorb s hsltN (X ∪ Y s) (Finset.union_subset hXK (h.remainder_subset s hsltN))
        (evenDegrees_union_of_disjoint hXY hXev (h.remainder_even s hsltN))
        (Finset.disjoint_union_right.2 ⟨hXA.symm, h.absorber_remainder_disjoint s hsltN⟩) hdvd
    | succ k =>
      rw [chainSet_succ_succ] at hdvd ⊢
      -- the residue that cell `s` must absorb, before the connectors are assigned
      set b : ℕ := (A s ∪ (X ∪ Y s)).card with hb
      have hsucc : s + 1 < N := by omega
      obtain ⟨Lt, Rt, hLR, hLRdisj, hLsub, hRsub, hLev, hRev, hdvdL⟩ :=
        exists_conn_split h hsucc b
      -- cell `s` absorbs its remainder, the carry, and the connectors assigned to it
      have hZK : X ∪ Y s ∪ Lt ⊆ K s :=
        Finset.union_subset (Finset.union_subset hXK (h.remainder_subset s hsltN))
          (hLsub.trans (Finset.union_subset (h.conn₁_left s hsucc) (h.conn₂_left s hsucc)))
      have hXYL : Disjoint (X ∪ Y s) Lt := by
        refine Finset.disjoint_union_left.2 ⟨hXc.mono_right hLsub, ?_⟩
        exact ((h.conn_disjoint s hsucc).mono_left Finset.subset_union_right).mono_right hLsub
      have hZev : EvenDegrees (X ∪ Y s ∪ Lt) :=
        evenDegrees_union_of_disjoint hXYL
          (evenDegrees_union_of_disjoint hXY hXev (h.remainder_even s hsltN)) hLev
      have hAZ : Disjoint (A s) (X ∪ Y s ∪ Lt) := by
        refine Finset.disjoint_union_right.2 ⟨Finset.disjoint_union_right.2
          ⟨hXA.symm, h.absorber_remainder_disjoint s hsltN⟩, ?_⟩
        exact (((h.conn_disjoint s hsucc).mono_left Finset.subset_union_left)).mono_right hLsub
      have hcardZ : (A s ∪ (X ∪ Y s ∪ Lt)).card = b + Lt.card := by
        have h1 : A s ∪ (X ∪ Y s ∪ Lt) = (A s ∪ (X ∪ Y s)) ∪ Lt := by
          ext e; simp only [Finset.mem_union]; itauto
        have h2 : Disjoint (A s ∪ (X ∪ Y s)) Lt := by
          refine Finset.disjoint_union_left.2 ⟨?_, hXYL⟩
          exact (((h.conn_disjoint s hsucc).mono_left Finset.subset_union_left)).mono_right hLsub
        rw [h1, Finset.card_union_of_disjoint h2, hb]
      have hdecL : TriDecomp (A s ∪ (X ∪ Y s ∪ Lt)) :=
        h.absorb s hsltN _ hZK hZev hAZ (by rw [hcardZ]; exact hdvdL)
      -- the rest of the chain, with the connectors assigned to the right
      have hc₁cell : c₁ s ⊆ cellPiece A Y c₁ c₂ s :=
        Finset.subset_union_right.trans Finset.subset_union_left
      have hc₂cell : c₂ s ⊆ cellPiece A Y c₁ c₂ s := Finset.subset_union_right
      have hRcell : Rt ⊆ cellPiece A Y c₁ c₂ s :=
        hRsub.trans (Finset.union_subset hc₁cell hc₂cell)
      have hRdisj : ∀ i, s + 1 ≤ i → i < N → Disjoint Rt (cellPiece A Y c₁ c₂ i) := by
        intro i hi hiN
        exact (h.pieces_disjoint s hsltN i hiN (by omega)).mono_left hRcell
      have hRK : Rt ⊆ K (s + 1) :=
        hRsub.trans (Finset.union_subset (h.conn₁_right s hsucc) (h.conn₂_right s hsucc))
      -- the two halves are edge-disjoint
      have hchainDisj : ∀ (W : Finset (Sym2 V)), W ⊆ cellPiece A Y c₁ c₂ s →
          Disjoint W (chainSet A Y c₁ c₂ (s + 1) (k + 1)) := by
        intro W hW
        exact disjoint_chainSet
          (fun i hi hi2 => (h.pieces_disjoint s hsltN i (by omega) (by omega)).mono_left hW)
      have hAcell : A s ⊆ cellPiece A Y c₁ c₂ s :=
        (Finset.subset_union_left.trans Finset.subset_union_left).trans Finset.subset_union_left
      have hYcell : Y s ⊆ cellPiece A Y c₁ c₂ s :=
        (Finset.subset_union_right.trans Finset.subset_union_left).trans Finset.subset_union_left
      have hLcell : Lt ⊆ cellPiece A Y c₁ c₂ s :=
        hLsub.trans (Finset.union_subset hc₁cell hc₂cell)
      have hsplitDisj : Disjoint (A s ∪ (X ∪ Y s ∪ Lt))
          (Rt ∪ chainSet A Y c₁ c₂ (s + 1) (k + 1)) := by
        refine Finset.disjoint_union_right.2 ⟨?_, ?_⟩
        · refine Finset.disjoint_union_left.2 ⟨?_, ?_⟩
          · exact ((h.conn_disjoint s hsucc).mono_left Finset.subset_union_left).mono_right hRsub
          · refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2
              ⟨hXc.mono_right hRsub, ?_⟩, hLRdisj⟩
            exact ((h.conn_disjoint s hsucc).mono_left Finset.subset_union_right).mono_right hRsub
        · refine Finset.disjoint_union_left.2 ⟨hchainDisj _ hAcell, ?_⟩
          refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2
            ⟨disjoint_chainSet (fun i hi hi2 => hXdisj i (by omega) (by omega)),
              hchainDisj _ hYcell⟩,
            hchainDisj _ hLcell⟩
      -- rewrite the whole chain as the two halves
      have hsplit : X ∪ ((A s ∪ Y s) ∪ (c₁ s ∪ c₂ s) ∪ chainSet A Y c₁ c₂ (s + 1) (k + 1)) =
          (A s ∪ (X ∪ Y s ∪ Lt)) ∪ (Rt ∪ chainSet A Y c₁ c₂ (s + 1) (k + 1)) := by
        rw [← hLR]
        ext e; simp only [Finset.mem_union]; itauto
      rw [hsplit] at hdvd ⊢
      -- the remaining divisibility is the global one minus what cell `s` absorbed
      have hdvdR : 3 ∣ (Rt ∪ chainSet A Y c₁ c₂ (s + 1) (k + 1)).card := by
        have hcards := Finset.card_union_of_disjoint hsplitDisj
        have h3 : 3 ∣ (A s ∪ (X ∪ Y s ∪ Lt)).card := by rw [hcardZ]; exact hdvdL
        omega
      exact TriDecomp.union hsplitDisj hdecL
        (ih (s + 1) Rt (by omega) (by omega) hRK hRev hRdisj hdvdR)

/-- **A chain of cells absorbs any globally divisible remainder.**

`chainSet A Y c₁ c₂ 0 n` is the union of the reserved absorbers `A i`, the connectors `c₁ i`,
`c₂ i` and the remainders `Y i` of the `n` cells.  Under the hypotheses `BKLO.ChainData` — each
`A i` absorbs the divisible even sets inside its core, the connectors sit in the cores of both
their cells and have `1` edge mod `3` — the whole thing is triangle-decomposable as soon as its
number of edges is divisible by `3`.

No *cell-wise* divisibility is required: this is exactly what the connectors buy, and by
`BKLO.not_absorbs_all_even_of_cell` it cannot be achieved by a reservation that is a disjoint union
of per-cell pieces. -/
theorem triDecomp_chainSet (h : ChainData A Y c₁ c₂ K N) (hN : 0 < N)
    (hdvd : 3 ∣ (chainSet A Y c₁ c₂ 0 N).card) : TriDecomp (chainSet A Y c₁ c₂ 0 N) := by
  have := triDecomp_chainSet_aux h N 0 ∅ hN (by omega) (by simp) (by simp [EvenDegrees])
    (fun i _ _ => by simp) (by simpa using hdvd)
  simpa using this

/-- **The reserved chain absorbs the remainders of all its cells.**

`chainSet A (fun _ => ∅) c₁ c₂ 0 N` is the *reservation*: the per-cell absorbers `A i` together
with the connectors.  It absorbs the union of the per-cell remainders `Y i` as soon as the total is
divisible by `3` — no cell-wise divisibility is needed. -/
theorem triDecomp_chainReservation (h : ChainData A Y c₁ c₂ K N) (hN : 0 < N)
    (hdvd : 3 ∣ (chainSet A (fun _ => ∅) c₁ c₂ 0 N ∪ (Finset.range N).biUnion Y).card) :
    TriDecomp (chainSet A (fun _ => ∅) c₁ c₂ 0 N ∪ (Finset.range N).biUnion Y) := by
  have hsplit := chainSet_split A Y c₁ c₂ N 0
  rw [zero_add, ← Finset.range_eq_Ico] at hsplit
  rw [← hsplit] at hdvd ⊢
  exact triDecomp_chainSet h hN hdvd

end Chain

end BKLO
