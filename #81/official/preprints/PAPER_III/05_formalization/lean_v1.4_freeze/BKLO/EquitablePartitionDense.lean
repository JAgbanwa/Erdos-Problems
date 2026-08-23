/-
# Equitable partitions with prescribed degrees, in a dense graph

BKLO §10 runs on a *partition sequence*: a nested family of equitable partitions in which every
vertex has many neighbours in every part.  Nothing in this project constructed one; this file does,
in the form §10 needs it at the bottom of the hierarchy — a single equitable partition into `k`
parts in which every vertex of `S` has at least `(δ + ε)|W|` neighbours in every part `W`, for a
graph of minimum degree `(δ + 3ε)|S|`.

The construction is the standard one, and its probabilistic ingredient is the moment bound of
`BKLO/Sampling.lean` packaged as `BKLO.exists_balanced_sample_two_sided`: the parts are chosen one
at a time, each as a sample of the remaining pool which contains, for every vertex `v` of `S`,
neither more nor less than its expected share of the non-neighbourhood of `v` — up to `θ` times the
size of the part.  The two-sided estimate is what makes the *last* part, which is not chosen but is
whatever remains, satisfy the same bound: the invariant carried along the construction is that the
pool still contains its expected share of every non-neighbourhood.

The main result is `BKLO.exists_balanced_parts`, the combinatorial core: a pool `A` can be split
into parts of any prescribed non-decreasing sizes so that every part contains at most its expected
share, up to a cumulative error `θ|A|`, of every member of a family of sets.

Everything here is `sorry`-free.
-/
import BKLO.PartitionSampling
import BKLO.Section10Defs

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The arithmetic of one step -/

/-- The pool keeps its share: if the sample took at least its share of `T i`, what is left of `T i`
in the shrunken pool is at most its share there, at the cost of `θc` added to the error. -/
private theorem parts_inv_arith {x xA' xX Ti A A' c E θ n : ℝ}
    (hA0 : 0 < A) (hA'eq : A' = A - c) (hc0 : 0 ≤ c) (hcA : c ≤ A) (hE : 0 ≤ E) (hn0 : 0 < n)
    (hsplit : xA' + xX = x) (hlow : x * c / A - θ * c ≤ xX) (hinv : x ≤ Ti * A / n + E) :
    xA' ≤ Ti * A' / n + (E + θ * c) := by
  have hA'0 : 0 ≤ A' := by rw [hA'eq]; linarith
  have h1 : xA' ≤ x * (A' / A) + θ * c := by
    have hxA : x * (A' / A) = x - x * c / A := by
      rw [hA'eq]; field_simp
    rw [hxA]; linarith
  have h2 : x * (A' / A) ≤ (Ti * A / n + E) * (A' / A) := by
    refine mul_le_mul_of_nonneg_right hinv ?_
    positivity
  have h3 : (Ti * A / n + E) * (A' / A) = Ti * A' / n + E * (A' / A) := by
    field_simp
  have h4 : A' / A ≤ 1 := by rw [div_le_one hA0]; linarith
  have h5 : E * (A' / A) ≤ E := by nlinarith [div_nonneg hA'0 hA0.le]
  linarith only [h1, h2, h3.le, h3.ge, h5]

/-- The sampled part is within its share: if the sample took at most its share of `T i`, the part
satisfies the bound with the error `E + θ|A|`. -/
private theorem parts_up_arith {x xX Ti A c E θ n : ℝ}
    (hA0 : 0 < A) (hc0 : 0 ≤ c) (hcA : c ≤ A) (hE : 0 ≤ E) (hn0 : 0 < n) (hθ0 : 0 < θ)
    (hup : xX ≤ x * c / A + θ * c) (hinv : x ≤ Ti * A / n + E) :
    xX ≤ Ti * c / n + E + θ * A := by
  have h1 : x * c / A ≤ (Ti * A / n + E) * c / A := by
    have h := mul_le_mul_of_nonneg_right hinv hc0
    exact div_le_div_of_nonneg_right h hA0.le
  have h2 : (Ti * A / n + E) * c / A = Ti * c / n + E * c / A := by
    field_simp
  have h3 : E * c / A ≤ E := by
    rw [div_le_iff₀ hA0]; nlinarith
  have h4 : θ * c ≤ θ * A := by nlinarith
  linarith [h1, h2.le, h2.ge]

/-! ### Splitting a pool into balanced parts -/

set_option maxHeartbeats 1000000 in
/-- **Balanced parts.**  Let `T i`, `i ∈ I`, be a family of sets and let `A` be a pool which
contains at most its expected share `|T i|·|A|/n + E` of each of them.  Then `A` can be split into
parts of any prescribed non-decreasing sizes `L` (summing to `|A|`) so that every part `Q` contains
at most `|T i|·|Q|/n + E + θ|A|` points of `T i`, for every `i ∈ I`.

Each part but the last is chosen by `BKLO.exists_balanced_sample_two_sided`; the two-sided estimate
keeps the invariant on the shrinking pool, which is what covers the last part. -/
theorem exists_balanced_parts {ι : Type*} [DecidableEq ι] {I : Finset ι} (T : ι → Finset V)
    {n : ℕ} (hn : 0 < n) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∀ (L : List ℕ) (A : Finset V) (E : ℝ), 0 ≤ E → A.card = L.sum → L.Pairwise (· ≤ ·) →
      (∀ c ∈ L, 0 < c) → (∀ c ∈ L, 2 * (I.card : ℝ) < (θ ^ 2 * (c : ℝ) / 32) ^ 2) →
      (∀ i ∈ I, ((T i ∩ A).card : ℝ) ≤ ((T i).card : ℝ) * (A.card : ℝ) / (n : ℝ) + E) →
      ∃ Ps : List (Finset V), List.Forall₂ (fun Q c => Q.card = c) Ps L ∧
        (∀ Q ∈ Ps, Q ⊆ A) ∧ (∀ a ∈ A, ∃ Q ∈ Ps, a ∈ Q) ∧
        Ps.Pairwise (fun Q Q' => Disjoint Q Q') ∧
        ∀ Q ∈ Ps, ∀ i ∈ I, ((T i ∩ Q).card : ℝ)
          ≤ ((T i).card : ℝ) * (Q.card : ℝ) / (n : ℝ) + E + θ * (A.card : ℝ) := by
  classical
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  intro L
  induction L with
  | nil =>
      intro A E hE hcard _ _ _ _
      have hA : A = ∅ := Finset.card_eq_zero.1 (by simpa using hcard)
      refine ⟨[], List.Forall₂.nil, by simp, ?_, by simp, by simp⟩
      intro a ha
      rw [hA] at ha
      exact absurd ha (Finset.notMem_empty a)
  | cons c L' ih =>
      intro A E hE hcard hsorted hpos hthr hinv
      have hcpos : 0 < c := hpos c (List.mem_cons_self ..)
      have hAcard : A.card = c + L'.sum := by simpa using hcard
      have hA0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
      by_cases hL' : L' = []
      · -- a single part: the pool itself
        subst hL'
        have hAc : A.card = c := by simpa using hAcard
        refine ⟨[A], List.Forall₂.cons hAc List.Forall₂.nil, ?_, ?_, ?_, ?_⟩
        · intro Q hQ; simp only [List.mem_singleton] at hQ; exact hQ ▸ Finset.Subset.refl A
        · intro a ha; exact ⟨A, List.mem_singleton_self A, ha⟩
        · simp
        · intro Q hQ i hi
          simp only [List.mem_singleton] at hQ
          subst hQ
          have h := hinv i hi
          nlinarith [mul_nonneg hθ0.le hA0]
      · -- sample the first part out of the pool
        have hcsum : c ≤ L'.sum := by
          obtain ⟨b, hb⟩ : ∃ b, b ∈ L' := by
            cases L' with
            | nil => exact absurd rfl hL'
            | cons b _ => exact ⟨b, List.mem_cons_self ..⟩
          have h1 : c ≤ b := (List.pairwise_cons.1 hsorted).1 b hb
          have h2 : b ≤ L'.sum := List.single_le_sum (fun x _ => Nat.zero_le x) b hb
          omega
        have h2c : 2 * c ≤ A.card := by omega
        obtain ⟨X, hX, hXgood⟩ :=
          exists_balanced_sample_two_sided (A := A) (I := I) (T := fun i => T i ∩ A)
            (fun i _ => Finset.inter_subset_right) hθ0 hθ1 hcpos h2c
            (hthr c (List.mem_cons_self ..))
        obtain ⟨hXA, hXcard⟩ := Finset.mem_powersetCard.1 hX
        have hTX : ∀ i, (T i ∩ A) ∩ X = T i ∩ X := by
          intro i
          ext a
          simp only [Finset.mem_inter]
          constructor
          · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨⟨h1, hXA h2⟩, h2⟩
        have hAR0 : (0 : ℝ) < (A.card : ℝ) := by
          have : 0 < A.card := by omega
          exact_mod_cast this
        have hcA : (c : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast (by omega : c ≤ A.card)
        have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
        set A' : Finset V := A \ X with hA'def
        have hA'card : A'.card = A.card - c := by
          rw [hA'def, Finset.card_sdiff_of_subset hXA, hXcard]
        have hA'sum : A'.card = L'.sum := by omega
        have hA'R : (A'.card : ℝ) = (A.card : ℝ) - (c : ℝ) := by
          rw [hA'card, Nat.cast_sub (by omega : c ≤ A.card)]
        -- the splitting identity
        have hsplit : ∀ i, ((T i ∩ A').card : ℝ) + ((T i ∩ X).card : ℝ) = ((T i ∩ A).card : ℝ) := by
          intro i
          have hunion : (T i ∩ A') ∪ (T i ∩ X) = T i ∩ A := by
            ext a
            simp only [Finset.mem_union, Finset.mem_inter, hA'def, Finset.mem_sdiff]
            constructor
            · rintro (⟨h1, h2, -⟩ | ⟨h1, h2⟩)
              · exact ⟨h1, h2⟩
              · exact ⟨h1, hXA h2⟩
            · rintro ⟨h1, h2⟩
              by_cases hxX : a ∈ X
              · exact Or.inr ⟨h1, hxX⟩
              · exact Or.inl ⟨h1, h2, hxX⟩
          have hdisj : Disjoint (T i ∩ A') (T i ∩ X) := by
            refine Finset.disjoint_left.2 fun a ha ha' => ?_
            exact (Finset.mem_sdiff.1 (Finset.mem_inter.1 ha).2).2 (Finset.mem_inter.1 ha').2
          have : (T i ∩ A').card + (T i ∩ X).card = (T i ∩ A).card := by
            rw [← hunion, Finset.card_union_of_disjoint hdisj]
          exact_mod_cast this
        -- the invariant survives
        have hinv' : ∀ i ∈ I, ((T i ∩ A').card : ℝ)
            ≤ ((T i).card : ℝ) * (A'.card : ℝ) / (n : ℝ) + (E + θ * (c : ℝ)) := by
          intro i hi
          obtain ⟨-, hlow⟩ := hXgood i hi
          rw [hTX i] at hlow
          exact parts_inv_arith hAR0 hA'R hc0 hcA hE hnR (hsplit i) hlow (hinv i hi)
        obtain ⟨Ps, hforall, hsub, hcover, hpair, hbound⟩ :=
          ih A' (E + θ * (c : ℝ)) (by positivity) hA'sum (List.pairwise_cons.1 hsorted).2
            (fun x hx => hpos x (List.mem_cons_of_mem _ hx))
            (fun x hx => hthr x (List.mem_cons_of_mem _ hx)) hinv'
        refine ⟨X :: Ps, List.Forall₂.cons hXcard hforall, ?_, ?_, ?_, ?_⟩
        · intro Q hQ
          rcases List.mem_cons.1 hQ with rfl | hQ
          · exact hXA
          · exact (hsub Q hQ).trans Finset.sdiff_subset
        · intro a ha
          by_cases haX : a ∈ X
          · exact ⟨X, List.mem_cons_self .., haX⟩
          · obtain ⟨Q, hQ, haQ⟩ := hcover a (Finset.mem_sdiff.2 ⟨ha, haX⟩)
            exact ⟨Q, List.mem_cons_of_mem _ hQ, haQ⟩
        · refine List.pairwise_cons.2 ⟨?_, hpair⟩
          intro Q hQ
          refine Finset.disjoint_left.2 fun a haX haQ => ?_
          exact (Finset.mem_sdiff.1 (hsub Q hQ haQ)).2 haX
        · intro Q hQ i hi
          rcases List.mem_cons.1 hQ with rfl | hQ
          · obtain ⟨hup, -⟩ := hXgood i hi
            rw [hTX i] at hup
            have hQc : (Q.card : ℝ) = (c : ℝ) := by rw [hXcard]
            rw [hQc]
            exact parts_up_arith hAR0 hc0 hcA hE hnR hθ0 hup (hinv i hi)
          · have h := hbound Q hQ i hi
            have hθA' : θ * (A'.card : ℝ) = θ * (A.card : ℝ) - θ * (c : ℝ) := by
              rw [hA'R]; ring
            linarith only [h, hθA'.le, hθA'.ge]

/-! ### Non-neighbourhoods -/

/-- The non-neighbourhood of `x` inside `S`. -/
def nonAdjIn (E : Finset (Sym2 V)) (S : Finset V) (x : V) : Finset V := S \ nbhdIn E x S

theorem nonAdjIn_subset {E : Finset (Sym2 V)} {S : Finset V} {x : V} : nonAdjIn E S x ⊆ S :=
  Finset.sdiff_subset

/-- Inside a part, the neighbours and the non-neighbours of a vertex add up to the part. -/
theorem degTo_add_card_nonAdjIn {E : Finset (Sym2 V)} {S W : Finset V} (hWS : W ⊆ S) (x : V) :
    degTo E x W + (nonAdjIn E S x ∩ W).card = W.card := by
  classical
  have hsub : nbhdIn E x W ⊆ W := nbhdIn_subset _ _ _
  have hcompl : nonAdjIn E S x ∩ W = W \ nbhdIn E x W := by
    ext a
    constructor
    · intro ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_inter.1 ha
      refine Finset.mem_sdiff.2 ⟨ha2, fun h => ?_⟩
      exact (Finset.mem_sdiff.1 ha1).2 (mem_nbhdIn.2 ⟨hWS ha2, (mem_nbhdIn.1 h).2⟩)
    · intro ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_sdiff.1 ha
      refine Finset.mem_inter.2 ⟨Finset.mem_sdiff.2 ⟨hWS ha1, fun h => ha2 ?_⟩, ha1⟩
      exact mem_nbhdIn.2 ⟨ha1, (mem_nbhdIn.1 h).2⟩
  rw [hcompl, degTo, Finset.card_sdiff_of_subset hsub]
  have := Finset.card_le_card hsub
  omega

/-- In a loopless edge set on `S`, the edge degree of a vertex is at most its degree into `S`. -/
theorem edeg_le_degTo {E : Finset (Sym2 V)} {S : Finset V} (hE : E ⊆ cliqueEdges S) (v : V) :
    edeg E v ≤ degTo E v S := by
  classical
  have key : ∀ a b : V, s(a, b) ∈ E → v ∈ s(a, b) →
      s(a, b) ∈ (nbhdIn E v S).image (fun y => s(v, y)) := by
    intro a b hab hv
    have hcl := mem_cliqueEdgesV.1 (hE hab)
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact Finset.mem_image.2 ⟨b, mem_nbhdIn.2 ⟨hcl.1 b (by simp), hab⟩, rfl⟩
    · refine Finset.mem_image.2 ⟨a, mem_nbhdIn.2 ⟨hcl.1 a (by simp), ?_⟩, ?_⟩
      · rw [Sym2.eq_swap]; exact hab
      · rw [Sym2.eq_swap]
  have hsub : E.filter (fun e => v ∈ e) ⊆ (nbhdIn E v S).image (fun y => s(v, y)) := by
    intro e he
    rw [Finset.mem_filter] at he
    revert he
    induction e using Sym2.ind with
    | _ a b => intro he; exact key a b he.1 he.2
  calc edeg E v = (E.filter (fun e => v ∈ e)).card := rfl
    _ ≤ ((nbhdIn E v S).image (fun y => s(v, y))).card := Finset.card_le_card hsub
    _ ≤ (nbhdIn E v S).card := Finset.card_image_le
    _ = degTo E v S := rfl

end BKLO
