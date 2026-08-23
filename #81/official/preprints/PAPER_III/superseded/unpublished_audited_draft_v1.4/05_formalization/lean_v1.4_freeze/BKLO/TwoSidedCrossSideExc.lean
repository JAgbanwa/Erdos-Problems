/-
# The cross-side rule with leftovers: what the perturbation forces, and what is left.

The strict cross-side rule of `BKLO/TwoSidedCrossSideSweep.lean` asks that *every* vertex of the
reserved part of a link be paired inside the class the canonical shift prescribes.  That is too
much to ask of a **perturbed** link: the adversary may delete one vertex of a column class of
`resLink R W' u` and add one vertex somewhere else, and then the row class matched to it has one
vertex too many, which cannot be paired inside the prescribed class at all.  A class-size mismatch
of the perturbation always leaves such **leftovers**.

This file makes room for them, in the only way that keeps the ledger of the sweep inside its
budget:

* `BKLO.excLoad` — the load of the leftovers: for a vertex `a` and a cell `(P, Q)`, the number of
  earlier links at which `a` was a leftover *and* was paired into the region of `(P, Q)`;
* `BKLO.IsCrossSideExcSweep` — the discipline: outside a per-link exceptional set `Exc w`, each
  vertex of the reserved part of the link went to the class the canonical shift prescribes;
* `BKLO.ExcLedgerSpread` — the leftovers stay spread: `16 · excLoad ≤ h t / 16`;
* `BKLO.regionLoad_le_of_crossSide_bounds_region` — the four-term bound of
  `BKLO.regionLoad_le_crossSide`, with the rule required only at the links that actually load the
  cell, so that the leftovers can be charged cell by cell rather than link by link (charging them
  link by link is *hopeless*: a vertex can be a leftover at a constant fraction of the links that
  see it, and that is far above the budget — only the spread of their partners can be bounded);
* `BKLO.ledgerSpread_of_crossSideExcSweep_canon` — **the ledger of such a sweep is spread**.

So the class-respecting part of a link is free, exactly as in the unperturbed case, and the whole
of AX2 §10 at the two-sided design comes down to the leftovers of one link: which vertices are
left over is our choice, and where they are paired is constrained only by the classes the
perturbation left unbalanced.

Everything here is `sorry`-free.
-/
import BKLO.TwoSidedCrossSideSweep

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The four-term bound, charged cell by cell -/

/-- **The cross-side rule keeps the ledger of `a` spread**, in the form that only asks for the rule
at the links which actually load the cell `(P, Q)`.  This is what lets an exceptional set be
charged to the cell it loads. -/
theorem regionLoad_le_crossSide_region {h : ℕ} {C : ℕ → Finset V} {X : V → Finset V}
    {g : V → V → V} {S E : Finset V} {x y : V → ℕ} {a : V} {α β : ℕ} {ρ σ : V → ℕ} {P Q : ℕ}
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j))
    (hxlt : ∀ w ∈ S, x w < h) (hylt : ∀ w ∈ S, y w < h)
    (hρ : ∀ w ∈ S, ρ w < h) (hσ : ∀ w ∈ S, σ w < h) (hP : P < h) (hQ : Q < h)
    (hrule : ∀ w ∈ S, a ∈ X w → g w a ∈ gridRegion h C P Q →
      w ∈ E ∨ IsCrossSideAt h C x y α β w (g w a) (ρ w) (σ w)) :
    regionLoad h C X g S x y a P Q
      ≤ (S.filter (fun w => x w = α ∧ ρ w = P)).card
        + (S.filter (fun w => x w = α ∧ y w = Q)).card
        + ((S.filter (fun w => y w = β ∧ x w = P)).card
          + (S.filter (fun w => y w = β ∧ σ w = Q)).card) + E.card := by
  classical
  set F1 := S.filter (fun w => x w = α ∧ ρ w = P) with hF1
  set F2 := S.filter (fun w => x w = α ∧ y w = Q) with hF2
  set F3 := S.filter (fun w => y w = β ∧ x w = P) with hF3
  set F4 := S.filter (fun w => y w = β ∧ σ w = Q) with hF4
  have hsub : S.filter (fun w =>
      ¬ (x w = P ∧ y w = Q) ∧ a ∈ X w ∧ g w a ∈ gridRegion h C P Q)
      ⊆ ((F1 ∪ F2) ∪ (F3 ∪ F4)) ∪ E := by
    intro w hw
    obtain ⟨hwS, -, haX, hreg⟩ := Finset.mem_filter.1 hw
    have hreg' := hreg
    rw [gridRegion_eq_biUnion] at hreg
    obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.1 hreg
    have hilt : i < h * h := gridIdx_lt hP hQ hi
    have hyw : y w < h := hylt w hwS
    have hxw : x w < h := hxlt w hwS
    have hclass : ∀ j, j < h * h → g w a ∈ C j → i = j := by
      intro j hj haj
      by_contra hne
      exact (Finset.disjoint_left.1 (hdisj i hilt j hj hne)) hai haj
    rcases hrule w hwS haX hreg' with hwE | hcross
    · exact Finset.mem_union_right _ hwE
    rcases hcross with ⟨hxα, hmem⟩ | ⟨hyβ, hmem⟩
    · have hjlt : ρ w * h + y w < h * h := by
        have := hρ w hwS
        calc ρ w * h + y w < ρ w * h + h := by omega
          _ = (ρ w + 1) * h := by ring
          _ ≤ h * h := Nat.mul_le_mul_right h (by omega)
      have hij : i = ρ w * h + y w := hclass _ hjlt hmem
      rcases mem_gridIdx.1 hi with ⟨j, hj, hieq⟩ | ⟨l, hl, hieq⟩
      · have := gridDigits_inj hyw hj (hij ▸ hieq)
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨hwS, hxα, this.1⟩)))
      · have := gridDigits_inj hyw hQ (hij ▸ hieq)
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨hwS, hxα, this.2⟩)))
    · have hjlt : x w * h + σ w < h * h := by
        have := hσ w hwS
        calc x w * h + σ w < x w * h + h := by omega
          _ = (x w + 1) * h := by ring
          _ ≤ h * h := Nat.mul_le_mul_right h (by omega)
      have hij : i = x w * h + σ w := hclass _ hjlt hmem
      rcases mem_gridIdx.1 hi with ⟨j, hj, hieq⟩ | ⟨l, hl, hieq⟩
      · have := gridDigits_inj (hσ w hwS) hj (hij ▸ hieq)
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨hwS, hyβ, this.1⟩)))
      · have := gridDigits_inj (hσ w hwS) hQ (hij ▸ hieq)
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨hwS, hyβ, this.2⟩)))
  calc regionLoad h C X g S x y a P Q ≤ (((F1 ∪ F2) ∪ (F3 ∪ F4)) ∪ E).card :=
        Finset.card_le_card hsub
    _ ≤ ((F1 ∪ F2) ∪ (F3 ∪ F4)).card + E.card := Finset.card_union_le _ _
    _ ≤ ((F1 ∪ F2).card + (F3 ∪ F4).card) + E.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ ((F1.card + F2.card) + (F3.card + F4.card)) + E.card :=
        Nat.add_le_add_right
          (Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _)) _

/-- The budget form of `BKLO.regionLoad_le_crossSide_region`. -/
theorem regionLoad_le_of_crossSide_bounds_region {h : ℕ} {C : ℕ → Finset V} {X : V → Finset V}
    {g : V → V → V} {S E : Finset V} {x y : V → ℕ} {a : V} {α β : ℕ} {ρ σ : V → ℕ} {P Q B : ℕ}
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j))
    (hxlt : ∀ w ∈ S, x w < h) (hylt : ∀ w ∈ S, y w < h)
    (hρ : ∀ w ∈ S, ρ w < h) (hσ : ∀ w ∈ S, σ w < h) (hP : P < h) (hQ : Q < h)
    (hrule : ∀ w ∈ S, a ∈ X w → g w a ∈ gridRegion h C P Q →
      w ∈ E ∨ IsCrossSideAt h C x y α β w (g w a) (ρ w) (σ w))
    (h1 : 8 * (S.filter (fun w => x w = α ∧ ρ w = P)).card ≤ B)
    (h2 : 8 * (S.filter (fun w => x w = α ∧ y w = Q)).card ≤ B)
    (h3 : 8 * (S.filter (fun w => y w = β ∧ x w = P)).card ≤ B)
    (h4 : 8 * (S.filter (fun w => y w = β ∧ σ w = Q)).card ≤ B)
    (h5 : 8 * E.card ≤ B) :
    regionLoad h C X g S x y a P Q ≤ B := by
  have := regionLoad_le_crossSide_region (C := C) (X := X) (g := g) (S := S) (E := E) (x := x)
    (y := y) (a := a) (α := α) (β := β) (ρ := ρ) (σ := σ) (P := P) (Q := Q) hdisj hxlt hylt hρ hσ
    hP hQ hrule
  omega

/-! ### Why leftovers are unavoidable -/

/-- **The strict cross-side rule forces the classes of a link to balance.**  If every vertex of a
row class `C (α h + β)` of the link of `u` — a class off the diagonal, `β ≠ y u` — is paired inside
the prescribed column class `C (ρ h + y u)`, then the row class cannot be larger than the column
class inside the perturbed link.  An adversarial perturbation breaks that equality (delete one
vertex of the column class), so no pairing of the perturbed link can obey the rule everywhere: an
exceptional set of leftovers is unavoidable. -/
theorem crossSide_forces_class_balance {h : ℕ} {C : ℕ → Finset V} {x y : V → ℕ}
    {R : Finset (Sym2 V)} {W' Xu : Finset V} {p : V → V} {u : V} {α β ρ σ : ℕ}
    (hβ : β ≠ y u)
    (hp : ∀ a ∈ Xu, p a ∈ Xu) (hinv : ∀ a ∈ Xu, p (p a) = a)
    (hrule : ∀ a ∈ C (α * h + β), a ∈ Xu → a ∈ resLink R W' u →
      IsCrossSideAt h C x y α β u (p a) ρ σ) :
    (C (α * h + β) ∩ Xu ∩ resLink R W' u).card ≤ (C (ρ * h + y u) ∩ Xu).card := by
  classical
  refine Finset.card_le_card_of_injOn p ?_ ?_
  · intro a ha
    obtain ⟨ha1, ha3⟩ := Finset.mem_inter.1 ha
    obtain ⟨haC, haX⟩ := Finset.mem_inter.1 ha1
    rcases hrule a haC haX ha3 with ⟨-, hmem⟩ | ⟨hyu, -⟩
    · exact Finset.mem_inter.2 ⟨hmem, hp a haX⟩
    · exact absurd hyu.symm hβ
  · intro a ha a' ha' heq
    have haX : a ∈ Xu := (Finset.mem_inter.1 (Finset.mem_inter.1 ha).1).2
    have ha'X : a' ∈ Xu := (Finset.mem_inter.1 (Finset.mem_inter.1 ha').1).2
    calc a = p (p a) := (hinv a haX).symm
      _ = p (p a') := by rw [heq]
      _ = a' := hinv a' ha'X

/-! ### The discipline with leftovers -/

/-- **The load of the leftovers**: the earlier links at which `a` was a leftover and was paired
into the region of the cell `(P, Q)`. -/
def excLoad (h : ℕ) (C : ℕ → Finset V) (g : V → V → V) (S : Finset V) (Exc : V → Finset V)
    (a : V) (P Q : ℕ) : ℕ :=
  (S.filter (fun w => a ∈ Exc w ∧ g w a ∈ gridRegion h C P Q)).card

/-- **The cross-side sweep with leftovers.**  Outside the exceptional set `Exc w`, every vertex of
the reserved part of the link of `w` went to the class the shift prescribes on the other side of
the region. -/
def IsCrossSideExcSweep (h : ℕ) (C : ℕ → Finset V) (R : Finset (Sym2 V)) (W' : Finset V)
    (X : V → Finset V) (x y φ : V → ℕ) (S : Finset V) (g : V → V → V) (Exc : V → Finset V) :
    Prop :=
  ∀ (a : V) (α β : ℕ), α < h → β < h → a ∈ C (α * h + β) →
    ∀ w ∈ S, a ∈ X w → a ∈ resLink R W' w → a ∉ Exc w →
      IsCrossSideAt h C x y α β w (g w a) (crossShift h φ β w) (crossShiftInv h φ α w)

variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ}

/-- **The leftovers stay spread**: their load on any cell is at most a sixteenth of the ledger
budget. -/
def ExcLedgerSpread (ε : ℝ) (K : ℕ) (W' : Finset V) (C : ℕ → Finset V) (g : V → V → V)
    (S : Finset V) (Exc : V → Finset V) : Prop :=
  ∀ a ∈ W', ∀ P < gridSize ε K, ∀ Q < gridSize ε K,
    16 * excLoad (gridSize ε K) C g S Exc a P Q
      ≤ gridSize ε K * gridClassSize ε K W'.card / 16

/-- **The ledger of a cross-side sweep with leftovers is spread**, as soon as the leftovers
themselves are spread.  The class-respecting part of the sweep costs nothing: it is bounded by four
cell fibres of the design, exactly as in the unperturbed case. -/
theorem ledgerSpread_of_crossSideExcSweep_canon
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 0 < K)
    (hbig : 512 ≤ gridClassSize ε K W'.card)
    {X : V → Finset V} {Exc : V → Finset V}
    {S : Finset V} (hSD : S ⊆ W \ W') {g : V → V → V}
    (hXmult : ∀ a ∈ W', ((((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℕ) : ℝ)
      ≤ 2 * cleanEta ε K * (W.card : ℝ))
    (hcross : IsCrossSideExcSweep (gridSize ε K) C R W' X x y (canonShift (gridSize ε K) x y)
      S g Exc)
    (hexc : ExcLedgerSpread ε K W' C g S Exc) :
    LedgerSpread ε K W' C X x y S g := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  set φ : V → ℕ := canonShift h x y with hφdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hwide : 6400 * (K * K) ≤ h := gridSize_ge_of_eps_small hε hε' K
  have hKK : 1 ≤ K * K := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hK.ne' hK.ne')
  have ht1 : 1 ≤ t := by omega
  have hφlt : ∀ w, φ w < h := fun w => canonShift_lt hhpos x y w
  have hxlt : ∀ w ∈ W \ W', x w < h := fun w hw => hgrid.rowLt w hw
  have hylt : ∀ w ∈ W \ W', y w < h := fun w hw => hgrid.colLt w hw
  have hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j) := fun i hi j hj hij =>
    hgrid.classDisjoint i hi j hj hij
  -- the row and column fibres of the canonical shift are cell fibres
  have hφrow : ∀ p j : ℕ, (((W \ W').filter (fun w => x w = p ∧ φ w = j)).card)
      ≤ 20 * (K * K) * t + 1 + h := by
    intro p j
    rcases Finset.eq_empty_or_nonempty
      ((W \ W').filter (fun w => x w = p ∧ φ w = j)) with he | ⟨w₀, hw₀⟩
    · rw [he]; simp
    · obtain ⟨hw₀D, hw₀x, hw₀j⟩ := Finset.mem_filter.1 hw₀
      have hsub : (W \ W').filter (fun w => x w = p ∧ φ w = j)
          ⊆ (W \ W').filter (fun w => x w = p ∧ y w = y w₀) := by
        intro w hw
        obtain ⟨hwD, hwx, hwj⟩ := Finset.mem_filter.1 hw
        exact Finset.mem_filter.2 ⟨hwD, hwx, canonShift_inj_row (x := x) (y := y) (hylt w hwD)
          (hylt w₀ hw₀D) (by rw [hwx, hw₀x]) (by simp only [← hφdef]; rw [hwj, hw₀j])⟩
      have hcell := twoSided_cell_card_le hgrid (x := x) (y := y) p (y w₀)
      rw [← htdef] at hcell
      have h2 := Finset.card_le_card hsub
      omega
  have hφcol : ∀ q j : ℕ, (((W \ W').filter (fun w => y w = q ∧ φ w = j)).card)
      ≤ 20 * (K * K) * t + 1 + h := by
    intro q j
    rcases Finset.eq_empty_or_nonempty
      ((W \ W').filter (fun w => y w = q ∧ φ w = j)) with he | ⟨w₀, hw₀⟩
    · rw [he]; simp
    · obtain ⟨hw₀D, hw₀y, hw₀j⟩ := Finset.mem_filter.1 hw₀
      have hsub : (W \ W').filter (fun w => y w = q ∧ φ w = j)
          ⊆ (W \ W').filter (fun w => x w = x w₀ ∧ y w = q) := by
        intro w hw
        obtain ⟨hwD, hwy, hwj⟩ := Finset.mem_filter.1 hw
        exact Finset.mem_filter.2 ⟨hwD, canonShift_inj_col (x := x) (y := y) (hxlt w hwD)
          (hxlt w₀ hw₀D) (by rw [hwy, hw₀y]) (by simp only [← hφdef]; rw [hwj, hw₀j]), hwy⟩
      have hcell := twoSided_cell_card_le hgrid (x := x) (y := y) (x w₀) q
      rw [← htdef] at hcell
      have h2 := Finset.card_le_card hsub
      omega
  intro a ha P hP Q hQ
  -- the perturbation of `a`, and the leftovers of `a` that load the cell `(P, Q)`
  set E₀ : Finset V := (W \ W').filter (fun u => a ∈ X u \ resLink R W' u) with hE₀def
  set E₁ : Finset V := S.filter (fun w => a ∈ Exc w ∧ g w a ∈ gridRegion h C P Q) with hE₁def
  set E : Finset V := E₀ ∪ E₁ with hEdef
  have hE₀bud : 256 * E₀.card ≤ h * t := by
    have h4 : 4 * E₀.card ≤ t := twoSided_perturbation_quarter hgrid hK (hXmult a ha)
    have h64 : 64 * t ≤ h * t := Nat.mul_le_mul_right t (by omega)
    omega
  have hEbud : 8 * E.card ≤ h * t / 16 := by
    have h0 : 16 * E₀.card ≤ h * t / 16 := by
      have := eight_le_div_sixteen (x := h * t) (F := 2 * E₀.card) (by omega)
      omega
    have h1 : 16 * E₁.card ≤ h * t / 16 := hexc a ha P hP Q hQ
    have hu : E.card ≤ E₀.card + E₁.card := Finset.card_union_le _ _
    omega
  -- the class coordinates of `a`
  obtain ⟨α, β, hα, hβ, hrule⟩ : ∃ α β : ℕ, α < h ∧ β < h ∧
      ∀ w ∈ S, a ∈ X w → g w a ∈ gridRegion h C P Q → w ∈ E ∨
        IsCrossSideAt h C x y α β w (g w a) (crossShift h φ β w) (crossShiftInv h φ α w) := by
    by_cases hcls : ∃ i, i < h * h ∧ a ∈ C i
    · obtain ⟨i, hi, hai⟩ := hcls
      refine ⟨i / h, i % h, Nat.div_lt_of_lt_mul (by omega), Nat.mod_lt _ hhpos, ?_⟩
      have hid : i / h * h + i % h = i := by
        have hdm := Nat.div_add_mod i h
        rw [Nat.mul_comm h (i / h)] at hdm
        exact hdm
      intro w hwS haX hreg
      by_cases hres : a ∈ resLink R W' w
      · by_cases hexcw : a ∈ Exc w
        · exact Or.inl (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hwS, hexcw, hreg⟩))
        · exact Or.inr (hcross a (i / h) (i % h) (Nat.div_lt_of_lt_mul (by omega))
            (Nat.mod_lt _ hhpos) (by rw [hid]; exact hai) w hwS haX hres hexcw)
      · exact Or.inl (Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨hSD hwS, Finset.mem_sdiff.2 ⟨haX, hres⟩⟩))
    · refine ⟨0, 0, hhpos, hhpos, ?_⟩
      intro w hwS haX _
      refine Or.inl (Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨hSD hwS, Finset.mem_sdiff.2 ⟨haX, ?_⟩⟩))
      intro hres
      have h1 := (Finset.mem_inter.1 (hgrid.linkSubset w (hSD hwS) hres)).2
      rw [gridRegion_eq_biUnion] at h1
      obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.1 h1
      exact hcls ⟨i, gridIdx_lt (hxlt w (hSD hwS)) (hylt w (hSD hwS)) hi, hai⟩
  -- the four counts of the rule
  have hcellbud : ∀ p q : ℕ, 128 * (((W \ W').filter (fun u => x u = p ∧ y u = q)).card)
      ≤ h * t := fun p q =>
    crossSide_cell_budget hKK ht1 hwide (twoSided_cell_card_le hgrid p q)
  have hF2 : 8 * (S.filter (fun w => x w = α ∧ y w = Q)).card ≤ h * t / 16 := by
    refine eight_le_div_sixteen (le_trans (Nat.mul_le_mul_left 128 ?_) (hcellbud α Q))
    exact Finset.card_le_card fun w hw => by
      obtain ⟨hwS, hwx, hwy⟩ := Finset.mem_filter.1 hw
      exact Finset.mem_filter.2 ⟨hSD hwS, hwx, hwy⟩
  have hF3 : 8 * (S.filter (fun w => y w = β ∧ x w = P)).card ≤ h * t / 16 := by
    refine eight_le_div_sixteen (le_trans (Nat.mul_le_mul_left 128 ?_) (hcellbud P β))
    exact Finset.card_le_card fun w hw => by
      obtain ⟨hwS, hwy, hwx⟩ := Finset.mem_filter.1 hw
      exact Finset.mem_filter.2 ⟨hSD hwS, hwx, hwy⟩
  have hF1 : 8 * (S.filter (fun w => x w = α ∧ crossShift h φ β w = P)).card ≤ h * t / 16 := by
    refine eight_le_div_sixteen ?_
    rcases Finset.eq_empty_or_nonempty (S.filter (fun w => x w = α ∧ crossShift h φ β w = P))
      with he | ⟨w₀, hw₀⟩
    · rw [he]; simp
    · obtain ⟨hw₀S, hw₀x, hw₀P⟩ := Finset.mem_filter.1 hw₀
      have hsub : (S.filter (fun w => x w = α ∧ crossShift h φ β w = P))
          ⊆ (W \ W').filter (fun w => x w = α ∧ φ w = φ w₀) := by
        intro w hw
        obtain ⟨hwS, hwx, hwP⟩ := Finset.mem_filter.1 hw
        refine Finset.mem_filter.2 ⟨hSD hwS, hwx, ?_⟩
        exact crossShift_inj (hφlt w) (hφlt w₀) (by rw [hwP, hw₀P])
      refine le_trans (Nat.mul_le_mul_left 128 (Finset.card_le_card hsub)) ?_
      exact crossSide_shift_budget hKK hbig hwide (hφrow α (φ w₀))
  have hF4 : 8 * (S.filter (fun w => y w = β ∧ crossShiftInv h φ α w = Q)).card
      ≤ h * t / 16 := by
    refine eight_le_div_sixteen ?_
    rcases Finset.eq_empty_or_nonempty (S.filter (fun w => y w = β ∧ crossShiftInv h φ α w = Q))
      with he | ⟨w₀, hw₀⟩
    · rw [he]; simp
    · obtain ⟨hw₀S, hw₀y, hw₀Q⟩ := Finset.mem_filter.1 hw₀
      have hsub : (S.filter (fun w => y w = β ∧ crossShiftInv h φ α w = Q))
          ⊆ (W \ W').filter (fun w => y w = β ∧ φ w = φ w₀) := by
        intro w hw
        obtain ⟨hwS, hwy, hwQ⟩ := Finset.mem_filter.1 hw
        refine Finset.mem_filter.2 ⟨hSD hwS, hwy, ?_⟩
        exact crossShiftInv_inj (hφlt w) (hφlt w₀) (by rw [hwQ, hw₀Q])
      refine le_trans (Nat.mul_le_mul_left 128 (Finset.card_le_card hsub)) ?_
      exact crossSide_shift_budget hKK hbig hwide (hφcol β (φ w₀))
  exact regionLoad_le_of_crossSide_bounds_region (C := C) (X := X) (g := g) (S := S) (E := E)
    (x := x) (y := y) (a := a) (α := α) (β := β)
    (ρ := fun w => crossShift h φ β w) (σ := fun w => crossShiftInv h φ α w)
    hdisj (fun w hw => hxlt w (hSD hw)) (fun w hw => hylt w (hSD hw))
    (fun w _ => crossShift_lt hhpos φ β w) (fun w _ => crossShiftInv_lt hhpos φ α w) hP hQ
    hrule hF1 hF2 hF3 hF4 hEbud

end BKLO
