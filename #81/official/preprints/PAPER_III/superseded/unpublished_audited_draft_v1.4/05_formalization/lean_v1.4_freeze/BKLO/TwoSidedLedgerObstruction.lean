/-
# What a spread discipline *forces* on the design: the strip pigeonhole.

`BKLO.LedgerSpread` (`BKLO/TwoSidedClassLedger.lean`) is the invariant that reduces the pairing
step of AX2 §10 at a two-sided grid design to a single one-link demand: no vertex `a` is paired
into the region of one cell of the grid more than `h t / 16` times.  This file proves what such an
invariant *forces*, and hence which further property the design has to have.

The point is a pigeonhole with no freedom in it: whatever pairing rule is used, the partner
`g w a` of `a` in the link of an outer vertex `w` lies in the region of `w`'s own cell, so it lies
in a class of the row `x w` **or** in a class of the column `y w`.  In the first case *every* cell
of the row `x w` sees it; in the second case *every* cell of the column `y w` does.  So each
earlier pairing of `a` loads a whole strip of `h` cells, and the strips available to `w` are
determined by `w`'s cell alone.

* `BKLO.card_le_of_regionLoad_le` — if every entry of the ledger of `a` is at most `M`, then the
  outer vertices whose link contains `a` and whose cells lie in a set of `α` rows and `β` columns
  number at most `(α + β) h M / (h - 1)`.
* `BKLO.backSpread_of_ledgerSpread` — the same statement for the invariant `BKLO.LedgerSpread`
  itself: it forces the *back-neighbourhood* of every vertex of `W'` — the outer vertices whose
  link contains it — to be spread over the rows and the columns of the grid.

The lemmas above are statements about *any* rule, and they were written when it still looked as if
the design needed an extra "spread" field.  It does not: the two-sided design already confines the
back-neighbourhood.  A vertex `a` of the class `C (α h + β)` belongs to the reserved link
`resLink R W' w` only if `x w = α` or `y w = β` (`BKLO.IsGridTwoSidedReservoir.linkSubset` together
with `BKLO.gridRegion_eq_biUnion`), so the outer vertices that can ever pair `a` already lie on the
two grid lines through `a`'s own class, and the feared concentration of the back-neighbourhood on
a `k × k` subgrid cannot happen for reserved links.  What is left to control is therefore only how
the *partners* are distributed along those two lines, and that is what the cross-side rule of
`BKLO/TwoSidedCrossSideSweep.lean` does — there the ledger bound `BKLO.LedgerSpread` is a theorem
(`BKLO.ledgerSpread_of_crossSideSweep_canon`), with no bookkeeping and no extra design field.  The
pigeonhole lemmas of this file remain valid, and they are what shows that a rule with no
directional discipline at all cannot work.

Everything here is `sorry`-free.
-/
import BKLO.TwoSidedClassLedger

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- The cells met by the strips of the outer vertices of `S`: the rows they use, and the columns
they use. -/
def stripCells (S : Finset V) (x y : V → ℕ) (h : ℕ) : Finset (ℕ × ℕ) :=
  ((S.image x) ×ˢ Finset.range h) ∪ ((Finset.range h) ×ˢ (S.image y))

omit [DecidableEq V] in
theorem card_stripCells_le (S : Finset V) (x y : V → ℕ) (h : ℕ) :
    (stripCells S x y h).card ≤ ((S.image x).card + (S.image y).card) * h := by
  classical
  refine le_trans (Finset.card_union_le _ _) ?_
  rw [Finset.card_product, Finset.card_product, Finset.card_range]
  ring_nf
  omega

/-- **One pairing loads a whole strip.**  If `a` lies in the link of `w` and its partner stays
inside the region of `w`'s cell, then at least `h - 1` cells of `stripCells` see the pairing. -/
theorem card_filter_stripCells_ge {h : ℕ} {C : ℕ → Finset V} {X : V → Finset V} {g : V → V → V}
    {S : Finset V} {x y : V → ℕ} {a w : V} (hw : w ∈ S) (haX : a ∈ X w)
    (hxw : x w < h) (hyw : y w < h) (hg : g w a ∈ gridRegion h C (x w) (y w)) :
    h - 1 ≤ ((stripCells S x y h).filter (fun c =>
      ¬ (x w = c.1 ∧ y w = c.2) ∧ a ∈ X w ∧ g w a ∈ gridRegion h C c.1 c.2)).card := by
  classical
  rw [gridRegion_eq_biUnion] at hg
  obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.1 hg
  rcases mem_gridIdx.1 hi with ⟨j, hj, rfl⟩ | ⟨l, hl, rfl⟩
  · -- the partner lies in the row part: every cell of the row `x w` sees it
    set T : Finset (ℕ × ℕ) := ((Finset.range h).erase (y w)).image (fun Q => (x w, Q)) with hT
    have hTcard : T.card = h - 1 := by
      rw [hT, Finset.card_image_of_injective _ (fun Q Q' hQ => (Prod.mk.injEq _ _ _ _ ▸ hQ).2),
        Finset.card_erase_of_mem (Finset.mem_range.2 hyw), Finset.card_range]
    refine hTcard ▸ Finset.card_le_card ?_
    intro c hc
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨hQne, hQlt⟩ := Finset.mem_erase.1 hQ
    refine Finset.mem_filter.2 ⟨?_, ?_, haX, ?_⟩
    · exact Finset.mem_union_left _ (Finset.mem_product.2
        ⟨Finset.mem_image.2 ⟨w, hw, rfl⟩, hQlt⟩)
    · rintro ⟨-, h2⟩; exact hQne h2.symm
    · rw [gridRegion_eq_biUnion]
      exact Finset.mem_biUnion.2 ⟨x w * h + j, mem_gridIdx.2 (Or.inl ⟨j, hj, rfl⟩), hai⟩
  · -- the partner lies in the column part: every cell of the column `y w` sees it
    set T : Finset (ℕ × ℕ) := ((Finset.range h).erase (x w)).image (fun P => (P, y w)) with hT
    have hTcard : T.card = h - 1 := by
      rw [hT, Finset.card_image_of_injective _ (fun P P' hP => (Prod.mk.injEq _ _ _ _ ▸ hP).1),
        Finset.card_erase_of_mem (Finset.mem_range.2 hxw), Finset.card_range]
    refine hTcard ▸ Finset.card_le_card ?_
    intro c hc
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨hPne, hPlt⟩ := Finset.mem_erase.1 hP
    refine Finset.mem_filter.2 ⟨?_, ?_, haX, ?_⟩
    · exact Finset.mem_union_right _ (Finset.mem_product.2
        ⟨hPlt, Finset.mem_image.2 ⟨w, hw, rfl⟩⟩)
    · rintro ⟨h1, -⟩; exact hPne h1.symm
    · rw [gridRegion_eq_biUnion]
      exact Finset.mem_biUnion.2 ⟨l * h + y w, mem_gridIdx.2 (Or.inr ⟨l, hl, rfl⟩), hai⟩

/-- **The strip pigeonhole.**  The ledger entries of `a` at the cells met by the strips of `S` add
up to at least `(h - 1) |S|`. -/
theorem sum_regionLoad_stripCells_ge {h : ℕ} {C : ℕ → Finset V} {X : V → Finset V} {g : V → V → V}
    {S : Finset V} {x y : V → ℕ} {a : V}
    (haX : ∀ w ∈ S, a ∈ X w) (hx : ∀ w ∈ S, x w < h) (hy : ∀ w ∈ S, y w < h)
    (hg : ∀ w ∈ S, g w a ∈ gridRegion h C (x w) (y w)) :
    (h - 1) * S.card
      ≤ ∑ c ∈ stripCells S x y h, regionLoad h C X g S x y a c.1 c.2 := by
  classical
  have hswap : ∑ c ∈ stripCells S x y h, regionLoad h C X g S x y a c.1 c.2
      = ∑ w ∈ S, ((stripCells S x y h).filter (fun c =>
          ¬ (x w = c.1 ∧ y w = c.2) ∧ a ∈ X w ∧ g w a ∈ gridRegion h C c.1 c.2)).card := by
    simp only [regionLoad, Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap, mul_comm]
  rw [← smul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun w hw =>
    card_filter_stripCells_ge hw (haX w hw) (hx w hw) (hy w hw) (hg w hw)

/-- **A bounded ledger forces the back-neighbourhood to be spread.**  If every entry of the ledger
of `a` is at most `M`, then the outer vertices already processed whose link contains `a` are, in
number, at most `(α + β) h M / (h - 1)`, where `α` and `β` are the numbers of rows and of columns
their cells use. -/
theorem card_le_of_regionLoad_le {h : ℕ} {C : ℕ → Finset V} {X : V → Finset V} {g : V → V → V}
    {S : Finset V} {x y : V → ℕ} {a : V} {M : ℕ}
    (haX : ∀ w ∈ S, a ∈ X w) (hx : ∀ w ∈ S, x w < h) (hy : ∀ w ∈ S, y w < h)
    (hg : ∀ w ∈ S, g w a ∈ gridRegion h C (x w) (y w))
    (hM : ∀ P < h, ∀ Q < h, regionLoad h C X g S x y a P Q ≤ M) :
    (h - 1) * S.card ≤ ((S.image x).card + (S.image y).card) * h * M := by
  classical
  refine le_trans (sum_regionLoad_stripCells_ge haX hx hy hg) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ M fun c hc => ?_) ?_
  · have hc1 : c.1 < h ∧ c.2 < h := by
      rcases Finset.mem_union.1 hc with hc' | hc'
      · obtain ⟨h1, h2⟩ := Finset.mem_product.1 hc'
        obtain ⟨w, hw, hwx⟩ := Finset.mem_image.1 h1
        exact ⟨hwx ▸ hx w hw, Finset.mem_range.1 h2⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_product.1 hc'
        obtain ⟨w, hw, hwy⟩ := Finset.mem_image.1 h2
        exact ⟨Finset.mem_range.1 h1, hwy ▸ hy w hw⟩
    exact hM c.1 hc1.1 c.2 hc1.2
  rw [smul_eq_mul]
  exact Nat.mul_le_mul_right M (card_stripCells_le S x y h)

/-- **The spread discipline forces a spread design.**  Along a sweep whose ledger obeys
`BKLO.LedgerSpread`, the outer vertices already processed whose link contains a given vertex `a`
of `W'` use at least `(h - 1) |S| / (h · h t / 16)` rows and columns of the grid: their cells
cannot be concentrated on a small subgrid.

`BKLO.IsGridTwoSidedReservoir` does not provide this, so it is exactly the field the design has to
gain — or the ledger has to be replaced by a finer statistic — before
`BKLO.TwoSidedClassDirectedRule` can be proved. -/
theorem backSpread_of_ledgerSpread {ε : ℝ} {K : ℕ} {W' : Finset V} {C : ℕ → Finset V}
    {X : V → Finset V} {x y : V → ℕ} {S : Finset V} {g : V → V → V} {a : V}
    (hled : LedgerSpread ε K W' C X x y S g) (ha : a ∈ W')
    (haX : ∀ w ∈ S, a ∈ X w)
    (hx : ∀ w ∈ S, x w < gridSize ε K) (hy : ∀ w ∈ S, y w < gridSize ε K)
    (hg : ∀ w ∈ S, g w a ∈ gridRegion (gridSize ε K) C (x w) (y w)) :
    (gridSize ε K - 1) * S.card
      ≤ ((S.image x).card + (S.image y).card) * gridSize ε K
        * (gridSize ε K * gridClassSize ε K W'.card / 16) :=
  card_le_of_regionLoad_le haX hx hy hg fun P hP Q hQ => hled a ha P hP Q hQ

end BKLO
