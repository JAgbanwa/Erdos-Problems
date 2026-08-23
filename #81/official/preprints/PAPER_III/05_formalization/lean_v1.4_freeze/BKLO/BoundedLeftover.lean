/-
# The bounded-leftover absorber: obstructions, the trivial range, and the assembly.

This file works towards `BKLO.AbsorberDenseK3BoundedLeftover`
(`BKLO/BoundedLeftoverInterface.lean`).

Three things are established here.

1. **Two hard obstructions** which rule out the naive "one absorbing gadget per potential host
   edge" construction:
   * `evenDegrees_of_absorbed` / `not_isAbsorber_singleton` — a set absorbed by a
     triangle-decomposable gadget *must have even degrees*.  In particular **no gadget absorbs a
     single edge**: the pieces of the leftover that separate gadgets can handle are exactly the
     even subgraphs, i.e. unions of cycles, which have unbounded size.
   * `card_le_edeg_of_perEdge_gadgets` — if a reservoir `R` contains a family of pairwise
     edge-disjoint gadgets, one for every potential host edge, each meeting both of its endpoints,
     then `Δ(R) ≥ |S| - 1`.  Since the reservoir is required to satisfy `Δ(R) ≤ γ|S|` with
     `γ < 1/10`, per-edge gadgets are impossible.

2. **The trivial range** `D ≤ 1` of the statement, proved (`boundedLeftoverAt_of_le_one`): an even
   edge set of maximum degree `≤ 1` is empty, so the empty reservoir works.

3. **The assembly** (`triDecomp_of_coverDown`, `absorberDenseK3BoundedLeftover_of_interfaces`):
   the full statement follows from
   * `BoundedLeftoverCoverDown` — a reservoir `R₁` of maximum degree `≤ γ|S|/2` which covers down
     every bounded-degree even leftover `H` to a remainder inside a *bounded* core `U`, and
   * `CoreAbsorberExistence` — a bounded-size reservoir `R₂` containing an absorber for every
     triangle-divisible edge set inside `U` (this is BKLO §8.1 + §5, i.e.
     `BKLO.sparseAbsorberExistence_nine` together with `BKLO.exists_placement`).

  The remaining crux is `BoundedLeftoverCoverDown`; see `BOUNDED_LEFTOVER_STATUS.md`.
-/
import BKLO.BoundedLeftoverInterface

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Elementary degree calculus -/

@[simp] theorem edeg_empty (v : V) : edeg (∅ : Finset (Sym2 V)) v = 0 := by simp [edeg]

theorem edeg_union_of_disjoint {A B : Finset (Sym2 V)} (h : Disjoint A B) (v : V) :
    edeg (A ∪ B) v = edeg A v + edeg B v := by
  classical
  unfold edeg
  rw [Finset.filter_union]
  exact Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)

theorem edeg_union_le (A B : Finset (Sym2 V)) (v : V) :
    edeg (A ∪ B) v ≤ edeg A v + edeg B v := by
  classical
  unfold edeg
  rw [Finset.filter_union]
  exact Finset.card_union_le _ _

theorem eq_empty_of_edeg_eq_zero {H : Finset (Sym2 V)} (h : ∀ v : V, edeg H v = 0) : H = ∅ := by
  classical
  by_contra hne
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.2 hne
  induction e using Sym2.ind with
  | _ x y =>
    have : s(x, y) ∈ H.filter (fun e => x ∈ e) := Finset.mem_filter.2 ⟨he, by simp⟩
    have hpos : 0 < edeg H x := Finset.card_pos.2 ⟨_, this⟩
    rw [h x] at hpos
    omega

/-- An even edge set of maximum degree at most one is empty. -/
theorem eq_empty_of_even_of_edeg_le_one {H : Finset (Sym2 V)} (heven : EvenDegrees H)
    (hD : ∀ v : V, edeg H v ≤ 1) : H = ∅ := by
  refine eq_empty_of_edeg_eq_zero fun v => ?_
  have h1 := heven v
  have h2 := hD v
  rcases h1 with ⟨k, hk⟩
  omega

theorem edeg_singleton_self {x y : V} : edeg ({s(x, y)} : Finset (Sym2 V)) x = 1 := by
  classical
  unfold edeg
  rw [Finset.filter_singleton, if_pos (by simp)]
  simp

/-! ### Obstruction 1: only even leftovers can be absorbed -/

/-- **Parity obstruction.**  If `A` is triangle-decomposable, `H` is edge-disjoint from `A`, and
`A ∪ H` is triangle-decomposable, then every vertex has even degree in `H`. -/
theorem evenDegrees_of_absorbed {A H : Finset (Sym2 V)} (hd : Disjoint A H)
    (hA : TriDecomp A) (hAH : TriDecomp (A ∪ H)) : EvenDegrees H := by
  intro v
  have h1 : Even (edeg A v) := hA.triDivisible.1 v
  have h2 : Even (edeg (A ∪ H) v) := hAH.triDivisible.1 v
  rw [edeg_union_of_disjoint hd] at h2
  rcases h1 with ⟨k, hk⟩
  rcases h2 with ⟨m, hm⟩
  exact ⟨m - k, by omega⟩

/-- An absorbed edge set has even degrees. -/
theorem EvenDegrees.of_isAbsorber {A H : Finset (Sym2 V)} (h : IsAbsorber A H) : EvenDegrees H :=
  evenDegrees_of_absorbed h.1 h.2.1 h.2.2

/-- **No gadget absorbs a single edge.**  This rules out the "one absorber per potential host edge,
activated edge by edge" construction: the parts of a leftover that separate gadgets can absorb are
precisely its *even* subgraphs. -/
theorem not_isAbsorber_singleton {A : Finset (Sym2 V)} {x y : V} :
    ¬ IsAbsorber A ({s(x, y)} : Finset (Sym2 V)) := by
  intro h
  have h1 := EvenDegrees.of_isAbsorber h x
  rw [edeg_singleton_self] at h1
  simp at h1

/-! ### Obstruction 2: there is no room for one gadget per potential host edge -/

/-- **Degree obstruction.**  Suppose the reservoir `R` contains, for every vertex `y ∈ S \ {x}`, a
gadget `Γ y ⊆ R` which meets `x`, and suppose these gadgets are pairwise edge-disjoint.  Then the
degree of `x` in `R` is at least `|S| - 1`.

Consequently a reservoir with `Δ(R) ≤ γ|S|` and `γ < 1` cannot contain an edge-disjoint gadget for
every potential host edge: each vertex lies in `|S| - 1` potential edges. -/
theorem card_le_edeg_of_perEdge_gadgets {R : Finset (Sym2 V)} {S : Finset V} {x : V}
    (hx : x ∈ S) (Γ : V → Finset (Sym2 V))
    (hsub : ∀ y ∈ S.erase x, Γ y ⊆ R)
    (hdisj : ∀ y ∈ S.erase x, ∀ z ∈ S.erase x, y ≠ z → Disjoint (Γ y) (Γ z))
    (hmeet : ∀ y ∈ S.erase x, ∃ e ∈ Γ y, x ∈ e) :
    S.card - 1 ≤ edeg R x := by
  classical
  set f : V → Sym2 V := fun y => if h : ∃ e ∈ Γ y, x ∈ e then h.choose else s(x, x) with hfdef
  have hf : ∀ y ∈ S.erase x, f y ∈ Γ y ∧ x ∈ f y := by
    intro y hy
    have h := hmeet y hy
    simp only [hfdef, dif_pos h]
    exact ⟨h.choose_spec.1, h.choose_spec.2⟩
  have hcard : (S.erase x).card ≤ (R.filter (fun e => x ∈ e)).card := by
    refine Finset.card_le_card_of_injOn f
      (fun y hy => Finset.mem_filter.2 ⟨hsub y hy (hf y hy).1, (hf y hy).2⟩) ?_
    intro y hy z hz heq
    by_contra hne
    have hd := hdisj y hy z hz hne
    exact (Finset.disjoint_left.1 hd (hf y hy).1) (heq ▸ (hf z hz).1)
  rwa [Finset.card_erase_of_mem hx] at hcard

/-! ### The statement, one `(γ, D)` at a time -/

/-- The bounded-leftover absorber statement for a fixed density slack `γ` and leftover degree
bound `D`. -/
def BoundedLeftoverAt (γ : ℝ) (D : ℕ) : Prop :=
  ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → TriDivisible E →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ R : Finset (Sym2 V), R ⊆ E ∧ EvenDegrees R ∧
        (∀ v : V, (edeg R v : ℝ) ≤ γ * (S.card : ℝ)) ∧
        ∀ H : Finset (Sym2 V), H ⊆ E \ R → EvenDegrees H → (∀ v : V, edeg H v ≤ D) →
          3 ∣ (R ∪ H).card → TriDecomp (R ∪ H)

theorem absorberDenseK3BoundedLeftover_iff :
    AbsorberDenseK3BoundedLeftover ↔ ∀ γ : ℝ, 0 < γ → ∀ D : ℕ, BoundedLeftoverAt γ D := Iff.rfl

/-- **The trivial range of the statement.**  For `D ≤ 1` an even leftover is empty, so the empty
reservoir absorbs it. -/
theorem boundedLeftoverAt_of_le_one {γ : ℝ} (hγ : 0 ≤ γ) {D : ℕ} (hD : D ≤ 1) :
    BoundedLeftoverAt γ D := by
  refine ⟨0, ?_⟩
  intro V _ E S _ _ _ _
  refine ⟨∅, Finset.empty_subset _, fun v => by simp [edeg], fun v => ?_, ?_⟩
  · simp only [edeg_empty, Nat.cast_zero]
    exact mul_nonneg hγ (Nat.cast_nonneg _)
  · intro H _ heven hdeg _
    have hH : H = ∅ :=
      eq_empty_of_even_of_edeg_le_one heven (fun v => le_trans (hdeg v) hD)
    subst hH
    simpa using (triDecomp_empty : TriDecomp (∅ : Finset (Sym2 V)))

/-! ### The assembly: cover-down to a bounded core, plus core absorbers -/

/-- `R₂` is a **core absorbing structure** for the core `U`: it contains an absorber for every
triangle-divisible edge set inside `U`, and what is left of `R₂` after removing that absorber is
itself triangle-decomposable. -/
structure CoreAbsorbers (U : Finset V) (R₂ : Finset (Sym2 V)) : Prop where
  absorb : ∀ Y ⊆ cliqueEdges U, TriDivisible Y →
    ∃ A ⊆ R₂, IsAbsorber A Y ∧ TriDecomp (R₂ \ A)

theorem CoreAbsorbers.triDecomp {U : Finset V} {R₂ : Finset (Sym2 V)}
    (h : CoreAbsorbers U R₂) : TriDecomp R₂ := by
  obtain ⟨A, hAR, habs, hrest⟩ :=
    h.absorb ∅ (Finset.empty_subset _) ⟨fun v => by simp, by simp⟩
  have hunion : A ∪ (R₂ \ A) = R₂ := Finset.union_sdiff_of_subset hAR
  rw [← hunion]
  exact TriDecomp.union Finset.disjoint_sdiff habs.2.1 hrest

/-- **The assembly step.**  If the leftover `H` together with the cover-down reservoir `R₁` is
triangle-decomposable up to a remainder `X` inside the core, and `R₂` is a core absorbing
structure edge-disjoint from `R₁` and `H`, then `(R₁ ∪ R₂) ∪ H` is triangle-decomposable. -/
theorem triDecomp_of_coverDown {R₁ R₂ H X : Finset (Sym2 V)} {U : Finset V}
    (hcore : CoreAbsorbers U R₂)
    (hR₁R₂ : Disjoint R₁ R₂) (hHR₁ : Disjoint H R₁) (hHR₂ : Disjoint H R₂)
    (hR₁even : EvenDegrees R₁) (hHeven : EvenDegrees H)
    (hXU : X ⊆ cliqueEdges U) (hXsub : X ⊆ R₁ ∪ H)
    (hdec : TriDecomp ((R₁ ∪ H) \ X))
    (hdvd : 3 ∣ ((R₁ ∪ R₂) ∪ H).card) :
    TriDecomp ((R₁ ∪ R₂) ∪ H) := by
  classical
  have hR₂div : TriDivisible R₂ := hcore.triDecomp.triDivisible
  have hdisjR₁H : Disjoint R₁ H := hHR₁.symm
  have hdisj₁ : Disjoint (R₁ ∪ H) R₂ := Finset.disjoint_union_left.2 ⟨hR₁R₂, hHR₂⟩
  -- divisibility of `R₁ ∪ H`
  have hcardsplit : ((R₁ ∪ R₂) ∪ H).card = (R₁ ∪ H).card + R₂.card := by
    have hrw : (R₁ ∪ R₂) ∪ H = (R₁ ∪ H) ∪ R₂ := by
      ext e; simp only [Finset.mem_union]; itauto
    rw [hrw, Finset.card_union_of_disjoint hdisj₁]
  have hdvdRH : 3 ∣ (R₁ ∪ H).card := by
    obtain ⟨k, hk⟩ := hdvd
    obtain ⟨m, hm⟩ := hR₂div.2
    omega
  have hdivRH : TriDivisible (R₁ ∪ H) := by
    refine ⟨fun v => ?_, hdvdRH⟩
    show Even (edeg (R₁ ∪ H) v)
    rw [edeg_union_of_disjoint hdisjR₁H]
    exact (hR₁even v).add (hHeven v)
  -- the remainder is triangle-divisible
  have hAsub : (R₁ ∪ H) \ X ⊆ R₁ ∪ H := Finset.sdiff_subset
  have hXeq : (R₁ ∪ H) \ ((R₁ ∪ H) \ X) = X := Finset.sdiff_sdiff_eq_self hXsub
  have hXdiv : TriDivisible X := by
    have := TriDivisible.sdiff hAsub hdivRH hdec.triDivisible
    rwa [hXeq] at this
  obtain ⟨A, hAR₂, habs, hrest⟩ := hcore.absorb X hXU hXdiv
  -- the three pieces
  have hXR₂ : Disjoint X R₂ := Finset.disjoint_of_subset_left hXsub hdisj₁
  have hd1 : Disjoint ((R₁ ∪ H) \ X) (A ∪ X) := by
    refine Finset.disjoint_union_right.2 ⟨?_, Finset.sdiff_disjoint⟩
    exact Finset.disjoint_of_subset_left hAsub (Finset.disjoint_of_subset_right hAR₂ hdisj₁)
  have hd2 : Disjoint (((R₁ ∪ H) \ X) ∪ (A ∪ X)) (R₂ \ A) := by
    refine Finset.disjoint_union_left.2 ⟨?_, Finset.disjoint_union_left.2 ⟨?_, ?_⟩⟩
    · exact Finset.disjoint_of_subset_left hAsub
        (Finset.disjoint_of_subset_right Finset.sdiff_subset hdisj₁)
    · exact Finset.disjoint_sdiff
    · exact Finset.disjoint_of_subset_right Finset.sdiff_subset hXR₂
  have hXsub' : ∀ e : Sym2 V, e ∈ X → e ∈ R₁ ∨ e ∈ H := fun e he => Finset.mem_union.1 (hXsub he)
  have hAR₂' : ∀ e : Sym2 V, e ∈ A → e ∈ R₂ := fun e he => hAR₂ he
  have hsplit : (R₁ ∪ R₂) ∪ H = (((R₁ ∪ H) \ X) ∪ (A ∪ X)) ∪ (R₂ \ A) := by
    ext e
    have hX' := hXsub' e
    have hA' := hAR₂' e
    simp only [Finset.mem_union, Finset.mem_sdiff]
    by_cases hX : e ∈ X <;> by_cases hA : e ∈ A <;> tauto
  rw [hsplit]
  refine TriDecomp.union hd2 (TriDecomp.union hd1 hdec ?_) hrest
  exact habs.2.2

/-- **Interface A — the remaining crux.**  A reservoir of maximum degree at most `γ|S|/2` which
covers down every even leftover of maximum degree at most `D` to a remainder inside a core `U` of
bounded size. -/
def BoundedLeftoverCoverDown : Prop :=
  ∀ γ : ℝ, 0 < γ → ∀ D : ℕ, ∃ C n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → TriDivisible E →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ (R₁ : Finset (Sym2 V)) (U : Finset V),
        R₁ ⊆ E ∧ U ⊆ S ∧ U.card ≤ C ∧ EvenDegrees R₁ ∧
        (∀ v : V, (edeg R₁ v : ℝ) ≤ γ * (S.card : ℝ) / 2) ∧
        ∀ H : Finset (Sym2 V), H ⊆ E \ R₁ → EvenDegrees H → (∀ v : V, edeg H v ≤ D) →
          ∃ X : Finset (Sym2 V), X ⊆ cliqueEdges U ∧ X ⊆ R₁ ∪ H ∧ TriDecomp ((R₁ ∪ H) \ X)

/-- **Interface B — the bounded-core absorbers.**  Inside a large dense host, and avoiding an
already reserved edge set, one can reserve a structure of maximum degree at most `γ|S|/2`
containing an absorber for every triangle-divisible edge set inside a bounded core `U`.  This is
BKLO §8.1 together with §5: `BKLO.sparseAbsorberExistence_nine` supplies a `9`-degenerate absorber
for each of the boundedly many triangle-divisible graphs on `U`, and `BKLO.exists_placement` places
them edge-disjointly inside the host. -/
def CoreAbsorberExistence : Prop :=
  ∀ (C : ℕ) (γ : ℝ), 0 < γ → ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E R₁ : Finset (Sym2 V)) (S U : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → U ⊆ S → U.card ≤ C →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) → R₁ ⊆ E →
      (∀ v : V, (edeg R₁ v : ℝ) ≤ γ * (S.card : ℝ) / 2) →
      ∃ R₂ : Finset (Sym2 V), R₂ ⊆ E \ R₁ ∧
        (∀ v : V, (edeg R₂ v : ℝ) ≤ γ * (S.card : ℝ) / 2) ∧ CoreAbsorbers U R₂

/-- **The bounded-leftover absorber from the two interfaces.** -/
theorem absorberDenseK3BoundedLeftover_of_interfaces
    (h1 : BoundedLeftoverCoverDown) (h2 : CoreAbsorberExistence) :
    AbsorberDenseK3BoundedLeftover := by
  intro γ hγ D
  obtain ⟨C, n₁, hcd⟩ := h1 γ hγ D
  obtain ⟨n₂, hca⟩ := h2 C γ hγ
  refine ⟨max n₁ n₂, ?_⟩
  intro V _ E S hn hES hdiv hdeg
  obtain ⟨R₁, U, hR₁E, hUS, hUC, hR₁even, hR₁deg, hcover⟩ :=
    hcd E S (le_trans (le_max_left _ _) hn) hES hdiv hdeg
  obtain ⟨R₂, hR₂E, hR₂deg, hcore⟩ :=
    hca E R₁ S U (le_trans (le_max_right _ _) hn) hES hUS hUC hdeg hR₁E hR₁deg
  have hR₁R₂ : Disjoint R₁ R₂ :=
    (Finset.disjoint_left.2 fun e he he' => (Finset.mem_sdiff.1 (hR₂E he')).2 he)
  have hR₂even : EvenDegrees R₂ := hcore.triDecomp.triDivisible.1
  refine ⟨R₁ ∪ R₂, ?_, ?_, ?_, ?_⟩
  · exact Finset.union_subset hR₁E (fun e he => (Finset.mem_sdiff.1 (hR₂E he)).1)
  · intro v
    rw [edeg_union_of_disjoint hR₁R₂]
    exact (hR₁even v).add (hR₂even v)
  · intro v
    have h := Nat.cast_le (α := ℝ) |>.2 (edeg_union_le R₁ R₂ v)
    have h1 := hR₁deg v
    have h2 := hR₂deg v
    push_cast at h
    linarith
  · intro H hHsub hHeven hHdeg hdvd
    have hHR₁ : Disjoint H R₁ :=
      Finset.disjoint_left.2 fun e he he' =>
        (Finset.mem_sdiff.1 (hHsub he)).2 (Finset.mem_union_left _ he')
    have hHR₂ : Disjoint H R₂ :=
      Finset.disjoint_left.2 fun e he he' =>
        (Finset.mem_sdiff.1 (hHsub he)).2 (Finset.mem_union_right _ he')
    have hHsub' : H ⊆ E \ R₁ := fun e he => by
      have := Finset.mem_sdiff.1 (hHsub he)
      exact Finset.mem_sdiff.2 ⟨this.1, fun hc => this.2 (Finset.mem_union_left _ hc)⟩
    obtain ⟨X, hXU, hXsub, hXdec⟩ := hcover H hHsub' hHeven hHdeg
    exact triDecomp_of_coverDown hcore hR₁R₂ hHR₁ hHR₂ hR₁even hHeven hXU hXsub hXdec hdvd

end BKLO
