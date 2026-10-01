import PaperIV.PatternTransfer

/-!
# RC01: physical scale of one transferred pattern

This module discharges the dimensional adapter introduced by the audit of the
cleaned gate.  If every partition class has at most `t` vertices, every pair
of distinct classes contains at most `t²` graph edges.  Consequently every
served transferred pattern has mass at most `t²`.
-/

namespace PaperIV.RC01PatternMassScale

open Finset
open MixedRounding
open PaperIV.PatternTransfer

variable {V P : Type*} [Fintype V] [DecidableEq V]
  [Fintype P] [DecidableEq P]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Edges having a fixed two-colour profile inject into the Cartesian product
of the two corresponding vertex classes. -/
theorem card_crossEdges_le_mul_classCards (part : V → P) (e : Sym2 V)
    (hcard : (partsOf part e).card = 2) :
    ∃ p q : P, p ≠ q ∧ partsOf part e = {p, q} ∧
      (crossEdges G part e).card ≤
        (univ.filter (fun v => part v = p)).card *
          (univ.filter (fun v => part v = q)).card := by
  classical
  obtain ⟨p, q, hpq, hpqeq⟩ := Finset.card_eq_two.1 hcard
  refine ⟨p, q, hpq, hpqeq, ?_⟩
  let A : Finset V := univ.filter (fun v => part v = p)
  let B : Finset V := univ.filter (fun v => part v = q)
  let U : Finset (Sym2 V) := (A ×ˢ B).image (fun ab => s(ab.1, ab.2))
  have hsub : crossEdges G part e ⊆ U := by
    intro f hf
    have hprof : partsOf part f = {p, q} := by
      exact (Finset.mem_filter.1 hf).2.trans hpqeq
    induction f using Sym2.ind with
    | _ a b =>
      rw [partsOf_mk] at hprof
      have ha : part a = p ∨ part a = q := by
        have : part a ∈ ({p, q} : Finset P) := by rw [← hprof]; simp
        simpa using this
      have hb : part b = p ∨ part b = q := by
        have : part b ∈ ({p, q} : Finset P) := by rw [← hprof]; simp
        simpa using this
      rcases ha with hap | haq <;> rcases hb with hbp | hbq
      · rw [hap, hbp] at hprof
        have hcards := congrArg Finset.card hprof
        simp [hpq] at hcards
      · change s(a, b) ∈ (A ×ˢ B).image (fun ab => s(ab.1, ab.2))
        rw [Finset.mem_image]
        refine ⟨(a, b), ?_, rfl⟩
        exact Finset.mem_product.2
          ⟨Finset.mem_filter.2 ⟨Finset.mem_univ a, hap⟩,
            Finset.mem_filter.2 ⟨Finset.mem_univ b, hbq⟩⟩
      · change s(a, b) ∈ (A ×ˢ B).image (fun ab => s(ab.1, ab.2))
        rw [Finset.mem_image]
        refine ⟨(b, a), ?_, Sym2.eq_swap⟩
        exact Finset.mem_product.2
          ⟨Finset.mem_filter.2 ⟨Finset.mem_univ b, hbp⟩,
            Finset.mem_filter.2 ⟨Finset.mem_univ a, haq⟩⟩
      · rw [haq, hbq] at hprof
        have hcards := congrArg Finset.card hprof
        simp [hpq] at hcards
  calc
    (crossEdges G part e).card ≤ U.card := Finset.card_le_card hsub
    _ ≤ (A ×ˢ B).card := Finset.card_image_le
    _ = A.card * B.card := Finset.card_product A B
    _ = (univ.filter (fun v => part v = p)).card *
        (univ.filter (fun v => part v = q)).card := rfl

/-- The unnormalised density of a crossed pair is bounded by the square of
the largest partition-class size. -/
theorem densT_le_sq_of_class_card_le (part : V → P) (e : Sym2 V) (t : ℕ)
    (ht : 1 ≤ t)
    (hpart : ∀ p ∈ partsOf part e,
      (univ.filter (fun v => part v = p)).card ≤ t)
    (hcard : (partsOf part e).card = 2) :
    densT G part e ≤ (t : ℚ) ^ 2 := by
  obtain ⟨p, q, -, hpq, hcross⟩ :=
    card_crossEdges_le_mul_classCards (G := G) part e hcard
  have hp : p ∈ partsOf part e := by rw [hpq]; simp
  have hq : q ∈ partsOf part e := by rw [hpq]; simp
  have hcross' : (crossEdges G part e).card ≤ t * t :=
    hcross.trans (Nat.mul_le_mul (hpart p hp) (hpart q hq))
  have hcrossQ : ((crossEdges G part e).card : ℚ) ≤ (t : ℚ) ^ 2 := by
    simpa [pow_two] using (show ((crossEdges G part e).card : ℚ) ≤ (t * t : ℕ) by
      exact_mod_cast hcross')
  have hone : (1 : ℚ) ≤ (t : ℚ) ^ 2 := by
    have htQ : (1 : ℚ) ≤ (t : ℚ) := by exact_mod_cast ht
    nlinarith
  rw [densT]
  exact max_le hone hcrossQ

/-- Every served pattern has mass at most `t²`.  This is the concrete `D=t²`
instance consumed by the scaled cleaned-codegree theorem. -/
theorem psiT_le_sq_of_mem_serving (x : FracPacking G) (part : V → P)
    {H : Finset P} {e : Sym2 V} (t : ℕ) (ht : 1 ≤ t)
    (hpart : ∀ p ∈ H, (univ.filter (fun v => part v = p)).card ≤ t)
    (hH : H ∈ servingT part e) :
    psiT x part H ≤ (t : ℚ) ^ 2 := by
  have hcard : (partsOf part e).card = 2 := by
    by_contra hn
    simp [servingT, hn] at hH
  have hsub : partsOf part e ⊆ H := by
    rw [servingT, if_pos hcard, Finset.mem_filter] at hH
    exact hH.2
  exact (psiT_le_densT_of_mem_serving x part hH).trans
    (densT_le_sq_of_class_card_le (G := G) part e t ht
      (fun p hp => hpart p (hsub hp)) hcard)

end PaperIV.RC01PatternMassScale
