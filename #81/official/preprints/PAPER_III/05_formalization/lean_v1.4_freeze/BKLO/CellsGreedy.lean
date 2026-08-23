/-
# The cells reservation: one bounded absorber per bottom cell, two connectors per boundary

Running `BKLO.cells_chain_step` along the bottom cells of the vortex reserves, edge-disjointly
inside the host,

* for each cell `i` a bounded core absorbing structure `Aa i` for the core
  `coreOf cell Tv i = cell i ∪ Tv (i-1)`, where `Tv (i-1)` are the eight vertices of the previous
  cell carrying the connectors of the boundary `i-1`, and
* for each boundary `i` two connectors `c₁ i`, `c₂ i`: `4`-cycles inside `Tv i ⊆ cell i`, hence
  inside the cores of *both* cell `i` and cell `i+1`.

The invariant carried along the induction is the **per-cell** degree bound: a vertex lies in at
most two of the cores, and each step adds at most `20` edges at a vertex into any single cell, so
the whole reservation sends at most `60` edges from any vertex into any cell.  This is the bound
that `BKLO.spreadAlong_of_percell` turns into `BKLO.SpreadAlong`.

* `BKLO.coreOf` — the core of a cell;
* `BKLO.exists_cellsChain_percell` — the reservation, with the per-cell degree bound.

Everything here is `sorry`-free.
-/
import BKLO.CellsStep

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-- The core of cell `i`: the cell together with the eight vertices of the previous cell that
carry the connectors of the boundary between them. -/
def coreOf (cell Tv : ℕ → Finset V) (i : ℕ) : Finset V :=
  if i = 0 then cell 0 else cell i ∪ Tv (i - 1)

theorem cell_subset_coreOf (cell Tv : ℕ → Finset V) (i : ℕ) : cell i ⊆ coreOf cell Tv i := by
  unfold coreOf
  by_cases h : i = 0
  · subst h; simp
  · rw [if_neg h]; exact Finset.subset_union_left

theorem coreOf_subset_union (cell Tv : ℕ → Finset V) (i : ℕ) :
    coreOf cell Tv i ⊆ cell i ∪ Tv (i - 1) := by
  unfold coreOf
  by_cases h : i = 0
  · subst h; simp
  · rw [if_neg h]

theorem coreOf_update_of_le {cell Tv : ℕ → Finset V} {t i : ℕ} (h : i ≤ t) (X : Finset V) :
    coreOf cell (Function.update Tv t X) i = coreOf cell Tv i := by
  unfold coreOf
  by_cases h0 : i = 0
  · simp [h0]
  · rw [if_neg h0, if_neg h0, Function.update_of_ne (by omega : i - 1 ≠ t)]

theorem biUnion_range_succ (f : ℕ → Finset (Sym2 V)) (t : ℕ) :
    (Finset.range (t + 1)).biUnion f = (Finset.range t).biUnion f ∪ f t := by
  rw [Finset.range_add_one, Finset.biUnion_insert]
  exact Finset.union_comm _ _

/-! ### The reservation -/

set_option maxHeartbeats 1000000 in
/-- **The cells reservation, spread at the scale of a single cell.**

For every bound `mmax` on the size of the bottom cells there is a threshold `n₀` such that, in
every host `E` on at least `n₀` vertices with minimum degree `(9/10)|S|` whose cells `cell 0, …,
cell (N-1)` are pairwise disjoint, of size between `m-1` and `m` with `3000 ≤ m ≤ mmax`, and dense
inside themselves, one can reserve

* a bounded core absorbing structure for every core `coreOf cell Tv i`, and
* two `4`-cycles on eight vertices `Tv i` of every cell `i` with `i + 1 < N`,

all pairwise edge-disjoint and inside `E`, in such a way that every vertex sends at most `60`
reserved edges into any single cell. -/
theorem exists_cellsChain_percell (mmax : ℕ) :
    ∃ n₀ : ℕ, ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V)
      (cell : ℕ → Finset V) (N m : ℕ),
      n₀ ≤ S.card → E ⊆ cliqueEdges S →
      (∀ q ∈ S, 9 * S.card ≤ 10 * edeg E q) →
      3000 ≤ m → m ≤ mmax → 0 < N →
      (∀ i, i < N → cell i ⊆ S) →
      (∀ i, i < N → m - 1 ≤ (cell i).card ∧ (cell i).card ≤ m) →
      (∀ i, i < N → ∀ j, j < N → i ≠ j → Disjoint (cell i) (cell j)) →
      (∀ i, i < N → ∀ v ∈ cell i, 9 * (cell i).card ≤ 10 * degTo E v (cell i)) →
      ∃ (Tv : ℕ → Finset V) (Aa c₁ c₂ : ℕ → Finset (Sym2 V)),
        (∀ i, i < N → Tv i ⊆ cell i) ∧
        (∀ i, i < N → CoreAbsorbers (coreOf cell Tv i) (Aa i)) ∧
        (∀ i, i + 1 < N → c₁ i ⊆ cliqueEdges (Tv i) ∧ c₂ i ⊆ cliqueEdges (Tv i)) ∧
        (∀ i, i + 1 < N → EvenDegrees (c₁ i) ∧ EvenDegrees (c₂ i) ∧
          (c₁ i).card = 4 ∧ (c₂ i).card = 4 ∧ Disjoint (c₁ i) (c₂ i)) ∧
        (∀ i, N ≤ i + 1 → c₁ i = ∅ ∧ c₂ i = ∅) ∧
        (∀ i, i < N → ∀ j, j < N → i ≠ j →
          Disjoint (Aa i ∪ c₁ i ∪ c₂ i) (Aa j ∪ c₁ j ∪ c₂ j)) ∧
        (∀ i, i < N → Disjoint (Aa i) (c₁ i ∪ c₂ i)) ∧
        (∀ i, i < N → Aa i ∪ c₁ i ∪ c₂ i ⊆ E) ∧
        (∀ x : V, ∀ j, j < N →
          degTo ((Finset.range N).biUnion (fun i => Aa i ∪ c₁ i ∪ c₂ i)) x (cell j) ≤ 60) := by
  classical
  choose Mf Ktf hMK using coreAbsConf_holds
  set M : ℕ := (Finset.range (mmax + 9)).sup Mf with hMdef
  set Kt : ℕ := (Finset.range (mmax + 9)).sup Ktf with hKtdef
  set Mstep : ℕ := M + 8 with hMstep
  set D₀ : ℕ := 200 * Mstep with hD₀
  set Δ : ℕ := D₀ + 3 * Mstep with hΔ
  refine ⟨20 * ((Kt + 1) * (9 * (Δ + 8) + (mmax + 8) + mmax + 2 * (mmax * (Δ + 8)) + 1) + 1)
    + 320, ?_⟩
  intro V _ E S cell N m hn hES hmindeg hm hmmax hN hcellS hcellcard hcelldisj hinternal
  -- the placement statement for every core size that occurs
  have hbase : ∀ C : ℕ, C ≤ mmax + 8 → CoreAbsConf V C M Kt := by
    intro C hC
    refine (hMK C V).mono ?_ ?_
    · exact Finset.le_sup (f := Mf) (Finset.mem_range.2 (by omega))
    · exact Finset.le_sup (f := Ktf) (Finset.mem_range.2 (by omega))
  -- basic size facts
  have hcellcard' : ∀ i, i < N → (cell i).card ≤ m := fun i hi => (hcellcard i hi).2
  have hNS : N ≤ S.card := by
    have hdisj : ∀ i ∈ Finset.range N, ∀ j ∈ Finset.range N, i ≠ j →
        Disjoint (cell i) (cell j) := by
      intro i hi j hj hij
      exact hcelldisj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hij
    have h1 : ((Finset.range N).biUnion cell).card = ∑ i ∈ Finset.range N, (cell i).card :=
      Finset.card_biUnion hdisj
    have h2 : (Finset.range N).biUnion cell ⊆ S := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.1 hx
      exact hcellS i (Finset.mem_range.1 hi) hxi
    have h3 : ∑ i ∈ Finset.range N, 1 ≤ ∑ i ∈ Finset.range N, (cell i).card := by
      refine Finset.sum_le_sum fun i hi => ?_
      have := (hcellcard i (Finset.mem_range.1 hi)).1
      omega
    have h4 : ((Finset.range N).biUnion cell).card ≤ S.card := Finset.card_le_card h2
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at h3
    omega
  have hMstep1 : 1 ≤ Mstep := by omega
  -- the count of cores containing a fixed vertex is at most two
  have hcnt2 : ∀ (Tvf : ℕ → Finset V) (t : ℕ), t ≤ N → (∀ i, i < t → Tvf i ⊆ cell i) →
      ∀ x : V, ((Finset.range t).filter (fun s => x ∈ coreOf cell Tvf s)).card ≤ 2 := by
    intro Tvf t ht hTvf x
    have hmemcore : ∀ s, s < t → x ∈ coreOf cell Tvf s →
        (x ∈ cell s ∨ (1 ≤ s ∧ x ∈ cell (s - 1))) := by
      intro s hs hx
      unfold coreOf at hx
      by_cases h0 : s = 0
      · subst h0; exact Or.inl (by simpa using hx)
      · rw [if_neg h0] at hx
        rcases Finset.mem_union.1 hx with h | h
        · exact Or.inl h
        · exact Or.inr ⟨by omega, hTvf (s - 1) (by omega) h⟩
    by_cases hx : ∃ i, i < N ∧ x ∈ cell i
    · obtain ⟨i, hi, hxi⟩ := hx
      have hsub : (Finset.range t).filter (fun s => x ∈ coreOf cell Tvf s) ⊆ {i, i + 1} := by
        intro s hs
        rw [Finset.mem_filter, Finset.mem_range] at hs
        rcases hmemcore s hs.1 hs.2 with h | ⟨hs1, h⟩
        · have : s = i := by
            by_contra hne
            exact (Finset.disjoint_left.1 (hcelldisj s (by omega) i hi hne)) h hxi
          simp [this]
        · have : s - 1 = i := by
            by_contra hne
            exact (Finset.disjoint_left.1 (hcelldisj (s - 1) (by omega) i hi hne)) h hxi
          have : s = i + 1 := by omega
          simp [this]
      refine le_trans (Finset.card_le_card hsub) ?_
      exact le_trans (Finset.card_insert_le _ _) (by simp)
    · push_neg at hx
      have hempty : (Finset.range t).filter (fun s => x ∈ coreOf cell Tvf s) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro s hs hxs
        rw [Finset.mem_range] at hs
        rcases hmemcore s hs hxs with h | ⟨hs1, h⟩
        · exact hx s (by omega) h
        · exact hx (s - 1) (by omega) h
      simp [hempty]
  -- ### the induction over the cells
  have key : ∀ t, t ≤ N → ∃ (Tv : ℕ → Finset V) (Aa c₁ c₂ : ℕ → Finset (Sym2 V)),
      (∀ i, t ≤ i → Tv i = ∅) ∧
      (∀ i, t ≤ i → Aa i = ∅ ∧ c₁ i = ∅ ∧ c₂ i = ∅) ∧
      (∀ i, i < t → Tv i ⊆ cell i) ∧
      (∀ i, i < t → (Tv i).card ≤ 8) ∧
      (∀ i, i < t → CoreAbsorbers (coreOf cell Tv i) (Aa i)) ∧
      (∀ i, i < t → i + 1 < N → c₁ i ⊆ cliqueEdges (Tv i) ∧ c₂ i ⊆ cliqueEdges (Tv i) ∧
        EvenDegrees (c₁ i) ∧ EvenDegrees (c₂ i) ∧ (c₁ i).card = 4 ∧ (c₂ i).card = 4 ∧
        Disjoint (c₁ i) (c₂ i)) ∧
      (∀ i, N ≤ i + 1 → c₁ i = ∅ ∧ c₂ i = ∅) ∧
      (∀ i, i < t → ∀ j, j < t → i ≠ j →
        Disjoint (Aa i ∪ c₁ i ∪ c₂ i) (Aa j ∪ c₁ j ∪ c₂ j)) ∧
      (∀ i, i < t → Disjoint (Aa i) (c₁ i ∪ c₂ i)) ∧
      (∀ i, i < t → Aa i ∪ c₁ i ∪ c₂ i ⊆ E) ∧
      ((Finset.range t).biUnion (fun i => Aa i ∪ c₁ i ∪ c₂ i)).card ≤ t * Mstep ∧
      (∀ x : V, edeg ((Finset.range t).biUnion (fun i => Aa i ∪ c₁ i ∪ c₂ i)) x
        ≤ D₀ + Mstep * (1 + ((Finset.range t).filter (fun s => x ∈ coreOf cell Tv s)).card)) ∧
      (∀ x : V, ∀ j, j < N →
        degTo ((Finset.range t).biUnion (fun i => Aa i ∪ c₁ i ∪ c₂ i)) x (cell j)
          ≤ 20 * (1 + ((Finset.range t).filter (fun s => x ∈ coreOf cell Tv s)).card)) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨fun _ => ∅, fun _ => ∅, fun _ => ∅, fun _ => ∅, fun _ _ => rfl,
        fun _ _ => ⟨rfl, rfl, rfl⟩, fun i hi => absurd hi (by omega),
        fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega),
        fun i hi => absurd hi (by omega), fun _ _ => ⟨rfl, rfl⟩,
        fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega),
        fun i hi => absurd hi (by omega), by simp, fun x => ?_, fun x j hj => ?_⟩
      · simp only [Finset.range_zero, Finset.biUnion_empty]
        have : edeg (∅ : Finset (Sym2 V)) x = 0 := by simp [edeg]
        omega
      · simp only [Finset.range_zero, Finset.biUnion_empty]
        have : degTo (∅ : Finset (Sym2 V)) x (cell j) = 0 := by
          simp [degTo, nbhdIn]
        omega
    | succ t ih =>
      intro htN
      obtain ⟨Tv, Aa, c₁, c₂, hTvempty, hempty, hTvcell, hTvcard, habs, hconn, hcempty,
        hpairdisj, hAac, hpieceE, hcard, hedeg, hdegcell⟩ := ih (by omega)
      have htlt : t < N := by omega
      set Acc : Finset (Sym2 V) := (Finset.range t).biUnion (fun i => Aa i ∪ c₁ i ∪ c₂ i)
        with hAccdef
      set U : Finset V := coreOf cell Tv t with hUdef
      -- the count of cores containing a vertex, so far
      have hcntle : ∀ x : V, ((Finset.range t).filter (fun s => x ∈ coreOf cell Tv s)).card ≤ 2 :=
        hcnt2 Tv t (by omega) hTvcell
      -- the hypotheses of the step
      have hAccE : Acc ⊆ E := by
        intro e he
        obtain ⟨i, hi, hie⟩ := Finset.mem_biUnion.1 he
        exact hpieceE i (Finset.mem_range.1 hi) hie
      have hAccdeg : ∀ x : V, edeg Acc x ≤ Δ := by
        intro x
        have h1 := hedeg x
        have h2 := hcntle x
        have h3 : Mstep * (1 + ((Finset.range t).filter
            (fun s => x ∈ coreOf cell Tv s)).card) ≤ Mstep * 3 :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      have hAcccell : ∀ x : V, ∀ j, j < N → degTo Acc x (cell j) ≤ 60 := by
        intro x j hj
        have h1 := hdegcell x j hj
        have h2 := hcntle x
        have h3 : 20 * (1 + ((Finset.range t).filter
            (fun s => x ∈ coreOf cell Tv s)).card) ≤ 20 * 3 :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      have hTvprev : Tv (t - 1) ⊆ S ∧ (Tv (t - 1)).card ≤ 8 := by
        by_cases h0 : t = 0
        · subst h0
          rw [hTvempty 0 le_rfl]
          simp
        · exact ⟨(hTvcell (t - 1) (by omega)).trans (hcellS (t - 1) (by omega)),
            hTvcard (t - 1) (by omega)⟩
      have hUsub : U ⊆ cell t ∪ Tv (t - 1) := coreOf_subset_union cell Tv t
      have hUS : U ⊆ S :=
        hUsub.trans (Finset.union_subset (hcellS t htlt) hTvprev.1)
      have hUcard : U.card ≤ mmax + 8 := by
        have h1 : U.card ≤ (cell t ∪ Tv (t - 1)).card := Finset.card_le_card hUsub
        have h2 : (cell t ∪ Tv (t - 1)).card ≤ (cell t).card + (Tv (t - 1)).card :=
          Finset.card_union_le _ _
        have h3 := hcellcard' t htlt
        have h4 := hTvprev.2
        omega
      have hAcccard : 40 * (Acc.card + 8) ≤ (D₀ + 1) * S.card := by
        have h1 : Acc.card ≤ t * Mstep := hcard
        have h2 : t * Mstep ≤ S.card * Mstep := Nat.mul_le_mul_right _ (by omega)
        have h3 : (D₀ + 1) * S.card = 200 * (Mstep * S.card) + S.card := by
          rw [hD₀]; ring
        have h4 : S.card * Mstep = Mstep * S.card := Nat.mul_comm _ _
        omega
      have hconst : 20 * ((Kt + 1) * (9 * (Δ + 8) + U.card + m + 2 * (m * (Δ + 8)) + 1) + 1)
          ≤ S.card := by
        have h1 : 9 * (Δ + 8) + U.card + m + 2 * (m * (Δ + 8)) + 1
            ≤ 9 * (Δ + 8) + (mmax + 8) + mmax + 2 * (mmax * (Δ + 8)) + 1 := by
          have h2 : m * (Δ + 8) ≤ mmax * (Δ + 8) := Nat.mul_le_mul_right _ hmmax
          omega
        have h3 : (Kt + 1) * (9 * (Δ + 8) + U.card + m + 2 * (m * (Δ + 8)) + 1)
            ≤ (Kt + 1) * (9 * (Δ + 8) + (mmax + 8) + mmax + 2 * (mmax * (Δ + 8)) + 1) :=
          Nat.mul_le_mul_left _ h1
        omega
      -- the step
      obtain ⟨Tvt, c1, c2, R, Fr, hTvtP, hTvtcard, hc1cl, hc2cl, hc1ev, hc2ev, hc1card, hc2card,
        hc12, hRabs, hRc, hpieceEA, hpiececard, hzero, hFrdeg, hdegpiece, hfresh⟩ :=
        cells_chain_step (E := E) (A := Acc) (S := S) (cell := cell) (U := U) (N := N) (m := m)
          (M := M) (Kt := Kt) (D₀ := D₀) (Δ := Δ) (t := t)
          (hbase U.card hUcard) hES hAccE hmindeg htlt hcellS hcellcard'
          (hcellcard t htlt).1 hcelldisj (hinternal t htlt) hm hAccdeg hAcccell hUS
          (cell_subset_coreOf cell Tv t) hAcccard hconst
      -- the updated data
      set c1' : Finset (Sym2 V) := if t + 1 < N then c1 else ∅ with hc1'def
      set c2' : Finset (Sym2 V) := if t + 1 < N then c2 else ∅ with hc2'def
      have hc1sub : c1' ⊆ c1 := by rw [hc1'def]; split <;> simp
      have hc2sub : c2' ⊆ c2 := by rw [hc2'def]; split <;> simp
      have hPsub : R ∪ c1' ∪ c2' ⊆ R ∪ c1 ∪ c2 :=
        Finset.union_subset_union (Finset.union_subset_union_right hc1sub) hc2sub
      have hPEA : R ∪ c1' ∪ c2' ⊆ E \ Acc := hPsub.trans hpieceEA
      have hPE : R ∪ c1' ∪ c2' ⊆ E := fun e he => (Finset.mem_sdiff.1 (hPEA he)).1
      have hPcard : (R ∪ c1' ∪ c2').card ≤ Mstep :=
        le_trans (Finset.card_le_card hPsub) hpiececard
      have hPzero : ∀ x : V, x ∉ U ∪ Fr → edeg (R ∪ c1' ∪ c2') x = 0 := by
        intro x hx
        have h := hzero x hx
        have := edeg_mono hPsub x
        omega
      have hPdeg : ∀ x : V, ∀ j, j < N → degTo (R ∪ c1' ∪ c2') x (cell j) ≤ 20 := by
        intro x j hj
        exact le_trans (degTo_mono_left hPsub x (cell j)) (hdegpiece x j hj)
      have hPfresh : ∀ x ∈ Fr, ∀ j, j < N → 0 < degTo (R ∪ c1' ∪ c2') x (cell j) →
          degTo Acc x (cell j) = 0 := by
        intro x hx j hj hpos
        exact hfresh x hx j hj (lt_of_lt_of_le hpos (degTo_mono_left hPsub x (cell j)))
      have holdsub : ∀ j, j < t → Aa j ∪ c₁ j ∪ c₂ j ⊆ Acc := by
        intro j hj
        rw [hAccdef]
        exact Finset.subset_biUnion_of_mem (fun i => Aa i ∪ c₁ i ∪ c₂ i) (Finset.mem_range.2 hj)
      have hnewdisj : ∀ j, j < t → Disjoint (R ∪ c1' ∪ c2') (Aa j ∪ c₁ j ∪ c₂ j) := by
        intro j hj
        refine Finset.disjoint_left.2 fun e he he' => ?_
        exact (Finset.mem_sdiff.1 (hPEA he)).2 (holdsub j hj he')
      -- the new accumulated reservation
      have hAccnew : (Finset.range (t + 1)).biUnion (fun i => (Function.update Aa t R) i ∪
          (Function.update c₁ t c1') i ∪ (Function.update c₂ t c2') i)
          = Acc ∪ (R ∪ c1' ∪ c2') := by
        rw [biUnion_range_succ]
        congr 1
        · refine Finset.biUnion_congr rfl fun i hi => ?_
          have hne : i ≠ t := by
            have := Finset.mem_range.1 hi
            omega
          rw [Function.update_of_ne hne, Function.update_of_ne hne, Function.update_of_ne hne]
        · rw [Function.update_self, Function.update_self, Function.update_self]
      -- how the count of cores changes
      have hcntsplit : ∀ x : V,
          ((Finset.range (t + 1)).filter
              (fun s => x ∈ coreOf cell (Function.update Tv t Tvt) s)).card
            = ((Finset.range t).filter (fun s => x ∈ coreOf cell Tv s)).card
              + (if x ∈ U then 1 else 0) := by
        intro x
        have hsame : (Finset.range t).filter
            (fun s => x ∈ coreOf cell (Function.update Tv t Tvt) s)
            = (Finset.range t).filter (fun s => x ∈ coreOf cell Tv s) := by
          refine Finset.filter_congr fun s hs => ?_
          have hst : s ≤ t := by
            have := Finset.mem_range.1 hs
            omega
          rw [coreOf_update_of_le hst]
        rw [Finset.range_add_one, Finset.filter_insert]
        by_cases hxU : x ∈ coreOf cell (Function.update Tv t Tvt) t
        · have hxU' : x ∈ U := by rwa [coreOf_update_of_le le_rfl] at hxU
          rw [if_pos hxU, Finset.card_insert_of_notMem (by simp), hsame, if_pos hxU']
        · have hxU' : x ∉ U := by rwa [coreOf_update_of_le le_rfl] at hxU
          rw [if_neg hxU, hsame, if_neg hxU']
          omega
      refine ⟨Function.update Tv t Tvt, Function.update Aa t R,
        Function.update c₁ t c1', Function.update c₂ t c2', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_⟩
      · intro i hi
        rw [Function.update_of_ne (by omega : i ≠ t)]
        exact hTvempty i (by omega)
      · intro i hi
        rw [Function.update_of_ne (by omega : i ≠ t), Function.update_of_ne (by omega : i ≠ t),
          Function.update_of_ne (by omega : i ≠ t)]
        exact hempty i (by omega)
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
        · rw [Function.update_of_ne (by omega : i ≠ t)]
          exact hTvcell i h
        · rw [Function.update_self]
          exact hTvtP
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
        · rw [Function.update_of_ne (by omega : i ≠ t)]
          exact hTvcard i h
        · rw [Function.update_self]
          omega
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
        · rw [coreOf_update_of_le (by omega : i ≤ t), Function.update_of_ne (by omega : i ≠ t)]
          exact habs i h
        · rw [coreOf_update_of_le (le_refl i), Function.update_self]
          exact hRabs
      · intro i hi hiN
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
        · rw [Function.update_of_ne (by omega : i ≠ t), Function.update_of_ne (by omega : i ≠ t),
            Function.update_of_ne (by omega : i ≠ t)]
          exact hconn i h hiN
        · rw [Function.update_self, Function.update_self, Function.update_self, hc1'def, hc2'def,
            if_pos hiN, if_pos hiN]
          exact ⟨hc1cl, hc2cl, hc1ev, hc2ev, hc1card, hc2card, hc12⟩
      · intro i hi
        by_cases hit : i = t
        · subst hit
          rw [Function.update_self, Function.update_self, hc1'def, hc2'def,
            if_neg (by omega), if_neg (by omega)]
          exact ⟨rfl, rfl⟩
        · rw [Function.update_of_ne hit, Function.update_of_ne hit]
          exact hcempty i hi
      · intro i hi j hj hij
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
          · rw [Function.update_of_ne (by omega : i ≠ t), Function.update_of_ne (by omega : i ≠ t),
              Function.update_of_ne (by omega : i ≠ t), Function.update_of_ne (by omega : j ≠ t),
              Function.update_of_ne (by omega : j ≠ t), Function.update_of_ne (by omega : j ≠ t)]
            exact hpairdisj i hi' j hj' hij
          · rw [Function.update_of_ne (by omega : i ≠ j), Function.update_of_ne (by omega : i ≠ j),
              Function.update_of_ne (by omega : i ≠ j), Function.update_self,
              Function.update_self, Function.update_self]
            exact (hnewdisj i hi').symm
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
          · rw [Function.update_of_ne (by omega : j ≠ i), Function.update_of_ne (by omega : j ≠ i),
              Function.update_of_ne (by omega : j ≠ i), Function.update_self,
              Function.update_self, Function.update_self]
            exact hnewdisj j hj'
          · exact absurd rfl hij
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
        · rw [Function.update_of_ne (by omega : i ≠ t), Function.update_of_ne (by omega : i ≠ t),
            Function.update_of_ne (by omega : i ≠ t)]
          exact hAac i h
        · rw [Function.update_self, Function.update_self, Function.update_self]
          exact Finset.disjoint_of_subset_right (Finset.union_subset_union hc1sub hc2sub) hRc
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
        · rw [Function.update_of_ne (by omega : i ≠ t), Function.update_of_ne (by omega : i ≠ t),
            Function.update_of_ne (by omega : i ≠ t)]
          exact hpieceE i h
        · rw [Function.update_self, Function.update_self, Function.update_self]
          exact hPE
      · rw [hAccnew]
        have h1 : (Acc ∪ (R ∪ c1' ∪ c2')).card ≤ Acc.card + (R ∪ c1' ∪ c2').card :=
          Finset.card_union_le _ _
        have h2 : (t + 1) * Mstep = t * Mstep + Mstep := by ring
        omega
      · intro x
        rw [hAccnew, hcntsplit x]
        have h1 : edeg (Acc ∪ (R ∪ c1' ∪ c2')) x ≤ edeg Acc x + edeg (R ∪ c1' ∪ c2') x :=
          edeg_union_le _ _ x
        have h2 : edeg (R ∪ c1' ∪ c2') x ≤ Mstep := by
          refine le_trans ?_ hPcard
          unfold edeg
          exact Finset.card_filter_le _ _
        have h3 := hedeg x
        by_cases hxU : x ∈ U
        · rw [if_pos hxU]
          have h4 : Mstep * (1 + (((Finset.range t).filter
              (fun s => x ∈ coreOf cell Tv s)).card + 1))
              = Mstep * (1 + ((Finset.range t).filter
                (fun s => x ∈ coreOf cell Tv s)).card) + Mstep := by ring
          omega
        · rw [if_neg hxU]
          simp only [Nat.add_zero]
          by_cases hxFr : x ∈ Fr
          · have h5 : edeg Acc x ≤ D₀ := hFrdeg x hxFr
            have h6 : Mstep ≤ Mstep * (1 + ((Finset.range t).filter
                (fun s => x ∈ coreOf cell Tv s)).card) :=
              Nat.le_mul_of_pos_right _ (by omega)
            omega
          · have h7 : edeg (R ∪ c1' ∪ c2') x = 0 := by
              refine hPzero x ?_
              intro hmem
              rcases Finset.mem_union.1 hmem with h | h
              · exact hxU h
              · exact hxFr h
            omega
      · intro x j hj
        rw [hAccnew, hcntsplit x]
        have h1 : degTo (Acc ∪ (R ∪ c1' ∪ c2')) x (cell j)
            ≤ degTo Acc x (cell j) + degTo (R ∪ c1' ∪ c2') x (cell j) := by
          unfold degTo
          rw [nbhdIn_union_edges]
          exact Finset.card_union_le _ _
        have h2 := hdegcell x j hj
        have h3 := hPdeg x j hj
        by_cases hxU : x ∈ U
        · rw [if_pos hxU]
          have h4 : 20 * (1 + (((Finset.range t).filter
              (fun s => x ∈ coreOf cell Tv s)).card + 1))
              = 20 * (1 + ((Finset.range t).filter
                (fun s => x ∈ coreOf cell Tv s)).card) + 20 := by ring
          omega
        · rw [if_neg hxU]
          simp only [Nat.add_zero]
          by_cases hxFr : x ∈ Fr
          · by_cases hpos : 0 < degTo (R ∪ c1' ∪ c2') x (cell j)
            · have h5 : degTo Acc x (cell j) = 0 := hPfresh x hxFr j hj hpos
              have h6 : (20 : ℕ) ≤ 20 * (1 + ((Finset.range t).filter
                  (fun s => x ∈ coreOf cell Tv s)).card) :=
                Nat.le_mul_of_pos_right _ (by omega)
              omega
            · omega
          · have h7 : degTo (R ∪ c1' ∪ c2') x (cell j) = 0 := by
              have h8 : edeg (R ∪ c1' ∪ c2') x = 0 := by
                refine hPzero x ?_
                intro hmem
                rcases Finset.mem_union.1 hmem with h | h
                · exact hxU h
                · exact hxFr h
              have := degTo_le_edeg (R ∪ c1' ∪ c2') x (cell j)
              omega
            omega
  -- ### the conclusion
  obtain ⟨Tv, Aa, c₁, c₂, -, -, hTvcell, -, habs, hconn, hcempty, hpairdisj, hAac, hpieceE, -, -,
    hdegcell⟩ := key N le_rfl
  refine ⟨Tv, Aa, c₁, c₂, hTvcell, habs, ?_, ?_, hcempty, hpairdisj, hAac, hpieceE, ?_⟩
  · intro i hi
    obtain ⟨h1, h2, -⟩ := hconn i (by omega) hi
    exact ⟨h1, h2⟩
  · intro i hi
    obtain ⟨-, -, h3, h4, h5, h6, h7⟩ := hconn i (by omega) hi
    exact ⟨h3, h4, h5, h6, h7⟩
  · intro x j hj
    have h1 := hdegcell x j hj
    have h2 := hcnt2 Tv N le_rfl hTvcell x
    have h3 : 20 * (1 + ((Finset.range N).filter (fun s => x ∈ coreOf cell Tv s)).card)
        ≤ 20 * 3 := Nat.mul_le_mul_left _ (by omega)
    omega

end BKLO
