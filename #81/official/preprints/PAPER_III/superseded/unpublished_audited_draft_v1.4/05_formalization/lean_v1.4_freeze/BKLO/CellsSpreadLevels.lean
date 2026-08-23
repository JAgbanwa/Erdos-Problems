/-
# From a per-cell degree bound to spread along the whole partition sequence

`BKLO.SpreadAlong` asks for `d_H(x, W) ≤ η|W|` for every part `W` of *every* level of the vortex.
This file shows that it is enough to control the degrees into the **bottom cells**: every part of
every level is partitioned by the bottom cells it contains, so a bound `d_H(x, R) ≤ η|R|` for the
bottom cells `R` sums to `d_H(x, W) ≤ η|W|` for every part `W`.

* `BKLO.PartSeq.bottom_cover` — the bottom cells contained in `S` cover `S`;
* `BKLO.spreadAlong_of_percell` — a per-bottom-cell bound gives `BKLO.SpreadAlong`;
* `BKLO.evenDegrees_biUnion` — an edge-disjoint union of even-degree sets is even.

Everything here is `sorry`-free.
-/
import BKLO.Section11CellsSeq
import BKLO.Section11CellsChain

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### Elementary facts about unions of edge sets -/

/-- The degree into a set is subadditive along a union of edge sets. -/
theorem degTo_biUnion_le {ι : Type*} [DecidableEq ι] (Q : Finset ι) (f : ι → Finset (Sym2 V))
    (x : V) (W : Finset V) : degTo (Q.biUnion f) x W ≤ ∑ i ∈ Q, degTo (f i) x W := by
  classical
  have hsub : nbhdIn (Q.biUnion f) x W ⊆ Q.biUnion (fun i => nbhdIn (f i) x W) := by
    intro y hy
    rw [mem_nbhdIn] at hy
    obtain ⟨i, hi, hie⟩ := Finset.mem_biUnion.1 hy.2
    exact Finset.mem_biUnion.2 ⟨i, hi, mem_nbhdIn.2 ⟨hy.1, hie⟩⟩
  exact le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le

/-- The degree into a union of vertex sets is subadditive. -/
theorem degTo_le_sum_of_cover {ι : Type*} [DecidableEq ι] (Q : Finset ι) (g : ι → Finset V)
    (A : Finset (Sym2 V)) (x : V) (W : Finset V) (hW : W ⊆ Q.biUnion g) :
    degTo A x W ≤ ∑ i ∈ Q, degTo A x (g i) := by
  classical
  have hsub : nbhdIn A x W ⊆ Q.biUnion (fun i => nbhdIn A x (g i)) := by
    intro y hy
    rw [mem_nbhdIn] at hy
    obtain ⟨i, hi, hig⟩ := Finset.mem_biUnion.1 (hW hy.1)
    exact Finset.mem_biUnion.2 ⟨i, hi, mem_nbhdIn.2 ⟨hig, hy.2⟩⟩
  exact le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le

/-- An edge-disjoint union of even-degree edge sets is even. -/
theorem evenDegrees_biUnion {ι : Type*} [DecidableEq ι] (Q : Finset ι) (f : ι → Finset (Sym2 V))
    (hdisj : ∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → Disjoint (f i) (f j))
    (hev : ∀ i ∈ Q, EvenDegrees (f i)) : EvenDegrees (Q.biUnion f) := by
  classical
  induction Q using Finset.induction_on with
  | empty => intro v; simp
  | @insert a Q ha ih =>
    have hdisj' : ∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → Disjoint (f i) (f j) := fun i hi j hj =>
      hdisj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have hev' : ∀ i ∈ Q, EvenDegrees (f i) := fun i hi => hev i (Finset.mem_insert_of_mem hi)
    have hrest := ih hdisj' hev'
    have hdisja : Disjoint (f a) (Q.biUnion f) := by
      refine Finset.disjoint_left.2 fun e hea heQ => ?_
      obtain ⟨i, hi, hie⟩ := Finset.mem_biUnion.1 heQ
      have hne : a ≠ i := by rintro rfl; exact ha hi
      exact (Finset.disjoint_left.1 (hdisj a (Finset.mem_insert_self _ _) i
        (Finset.mem_insert_of_mem hi) hne)) hea hie
    rw [Finset.biUnion_insert]
    exact evenDegrees_union_of_disjoint hdisja (hev a (Finset.mem_insert_self _ _)) hrest

/-! ### The bottom cells cover every vertex set of the sequence -/

/-- **The bottom cells contained in `S` cover `S`.**  At every level the parts partition the
current vertex set, so the bottom cells inside `S` do too. -/
theorem PartSeq.bottom_cover {k : ℕ} {δ ε : ℝ} {m : ℕ} :
    ∀ (L : List (Finset (Finset V))) (c : ℝ) (Pl : Finset (Finset V)) (E : Finset (Sym2 V))
      (S : Finset V), PartSeq k c δ ε m L Pl E S → (restrictParts Pl S).biUnion id = S := by
  intro L
  induction L with
  | nil => intro c Pl E S hseq; exact hseq.1.1.cover
  | cons P rest ih =>
    intro c Pl E S hseq
    refine Finset.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨R, hR, hxR⟩ := Finset.mem_biUnion.1 hx
      exact (mem_restrictParts.1 hR).2 hxR
    · have hcov := hseq.1.1.cover
      rw [← hcov] at hx
      obtain ⟨W, hW, hxW⟩ := Finset.mem_biUnion.1 hx
      have hWS : W ⊆ S := (mem_restrictParts.1 hW).2
      have hsub := ih (δ + 2 * ε) Pl (edgesIn E W) W (hseq.2 W hW)
      rw [← hsub] at hxW
      obtain ⟨R, hR, hxR⟩ := Finset.mem_biUnion.1 hxW
      exact Finset.mem_biUnion.2 ⟨R, restrictParts_mono hWS hR, hxR⟩

/-! ### From per-cell degrees to spread along the sequence -/

/-- **A per-bottom-cell degree bound is spread along the whole sequence.**

If every vertex sends at most `η|R|` edges of `A` into every bottom cell `R` of the sequence, then
the same holds for every part of every level: a part `W` is partitioned by the bottom cells it
contains, so the degrees add up to at most `η|W|`.

This is what makes a *constant* per-cell bound enough: the maximum degree of `A` may be far larger
than `η|W|` for the small bottom cells `W`, as long as the reserved edges at a vertex are spread
over different cells. -/
theorem spreadAlong_of_percell {k : ℕ} {δ ε η : ℝ} {m : ℕ} {A : Finset (Sym2 V)} :
    ∀ (L : List (Finset (Finset V))) (c : ℝ) (Pl : Finset (Finset V)) (E : Finset (Sym2 V))
      (S : Finset V), PartSeq k c δ ε m L Pl E S →
      (∀ R ∈ restrictParts Pl S, ∀ R' ∈ restrictParts Pl S, R ≠ R' → Disjoint R R') →
      (∀ x : V, ∀ R ∈ restrictParts Pl S, (degTo A x R : ℝ) ≤ η * (R.card : ℝ)) →
      SpreadAlong η L Pl A S := by
  classical
  intro L
  induction L with
  | nil => intro c Pl E S _ _ hbd; exact hbd
  | cons P rest ih =>
    intro c Pl E S hseq hdisj hbd
    -- the bound for a part `W` of the current level, from the bottom cells inside `W`
    have hpart : ∀ W ∈ restrictParts P S, ∀ x : V, (degTo A x W : ℝ) ≤ η * (W.card : ℝ) := by
      intro W hW x
      have hWS : W ⊆ S := (mem_restrictParts.1 hW).2
      have hcov : (restrictParts Pl W).biUnion id = W :=
        PartSeq.bottom_cover rest (δ + 2 * ε) Pl (edgesIn E W) W (hseq.2 W hW)
      have hsubW : restrictParts Pl W ⊆ restrictParts Pl S := restrictParts_mono hWS
      have hdisjW : ∀ R ∈ restrictParts Pl W, ∀ R' ∈ restrictParts Pl W, R ≠ R' →
          Disjoint R R' := fun R hR R' hR' => hdisj R (hsubW hR) R' (hsubW hR')
      have h1 : degTo A x W ≤ ∑ R ∈ restrictParts Pl W, degTo A x R :=
        degTo_le_sum_of_cover (restrictParts Pl W) id A x W hcov.ge
      have h2 : ((∑ R ∈ restrictParts Pl W, degTo A x R : ℕ) : ℝ)
          ≤ ∑ R ∈ restrictParts Pl W, η * (R.card : ℝ) := by
        push_cast
        exact Finset.sum_le_sum fun R hR => hbd x R (hsubW hR)
      have h3 : ∑ R ∈ restrictParts Pl W, η * (R.card : ℝ)
          = η * ((∑ R ∈ restrictParts Pl W, R.card : ℕ) : ℝ) := by
        rw [← Finset.mul_sum]; push_cast; ring
      have h4 : (∑ R ∈ restrictParts Pl W, R.card) = W.card := by
        have hcb := Finset.card_biUnion (s := restrictParts Pl W)
          (t := (id : Finset V → Finset V)) hdisjW
        simp only [id_eq] at hcb
        rw [hcov] at hcb
        omega
      have h5 : ((degTo A x W : ℕ) : ℝ) ≤ ((∑ R ∈ restrictParts Pl W, degTo A x R : ℕ) : ℝ) := by
        exact_mod_cast h1
      rw [h3, h4] at h2
      linarith
    refine ⟨fun x W hW => hpart W hW x, fun W hW => ?_⟩
    have hWS : W ⊆ S := (mem_restrictParts.1 hW).2
    have hsubW : restrictParts Pl W ⊆ restrictParts Pl S := restrictParts_mono hWS
    exact ih (δ + 2 * ε) Pl (edgesIn E W) W (hseq.2 W hW)
      (fun R hR R' hR' => hdisj R (hsubW hR) R' (hsubW hR'))
      (fun x R hR => hbd x R (hsubW hR))

end BKLO
