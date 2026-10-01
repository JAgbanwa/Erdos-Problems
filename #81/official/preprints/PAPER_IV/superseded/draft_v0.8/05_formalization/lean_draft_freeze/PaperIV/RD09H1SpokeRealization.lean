import PaperIV.RD09FactorCandidateAverage
import PaperIV.RD09SpokeCompatibility

/-!
# H1: canonical invalid candidates and the correctly oriented L1--L2 union

This module closes the resource-compatibility part of the local RD09 constructor.
The invalid set of a root base contains exactly the candidates that either miss
one endpoint or would reuse a phase-I spoke.  Consequently every survivor of
the L2 assignment is automatically spoke-compatible with the literal L1
packing; no root/host separation in the wrong orientation is assumed.
-/

namespace PaperIV.RD09H1SpokeRealization

open Finset PaperIV.Model PaperIV.ExteriorTriangleLift PaperIV.MultiHostTriangleLift
open PaperIV.RD09PhaseII PaperIV.RD09FactorCandidateMoments
open PaperIV.RD09FactorCandidateAverage PaperIV.RD09SpokeCompatibility

variable {V I Z Cand : Type*}
variable [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable [Fintype Z] [DecidableEq Z] [LinearOrder Z]
variable [Fintype Cand] [DecidableEq Cand]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The literal H1 invalid-candidate family.  The last disjunct is the
cross-phase resource obstruction: choosing `c` over `b` would reuse a spoke
already present in the phase-I triangle `(z i,e)`. -/
def canonicalBad (G : SimpleGraph V) [DecidableRel G.Adj]
    (core : Z ↪ V) (cand : Cand ↪ V) (z : I → V)
    (E : I → Finset (Sym2 V)) (b : Z × Z) : Finset Cand :=
  Finset.univ.filter fun c =>
    ¬ G.Adj (cand c) (core b.1) ∨
    ¬ G.Adj (cand c) (core b.2) ∨
    ∃ i, ∃ e ∈ E i, z i ∈ s(core b.1, core b.2) ∧ cand c ∈ e

@[simp] theorem mem_canonicalBad {core : Z ↪ V} {cand : Cand ↪ V}
    {z : I → V} {E : I → Finset (Sym2 V)} {b : Z × Z} {c : Cand} :
    c ∈ canonicalBad G core cand z E b ↔
      ¬ G.Adj (cand c) (core b.1) ∨
      ¬ G.Adj (cand c) (core b.2) ∨
      ∃ i, ∃ e ∈ E i, z i ∈ s(core b.1, core b.2) ∧ cand c ∈ e := by
  simp [canonicalBad]

/-- The canonical bad family supplies the geometric part of RD09-L2. -/
theorem isFactorCandidateData_canonicalBad {k : ℕ}
    (core : Z ↪ V) (cand : Cand ↪ V) (z : I → V)
    (E : I → Finset (Sym2 V)) (fac : Z × Z → Fin k)
    (hcore : ∀ x y : Z, x ≠ y → G.Adj (core x) (core y))
    (hcand : ∀ c x, cand c ≠ core x)
    (hfac : ∀ e ∈ corePairs Z, ∀ e' ∈ corePairs Z, e ≠ e' → fac e = fac e' →
      ∀ x : Z, (x = e.1 ∨ x = e.2) → (x = e'.1 ∨ x = e'.2) → False) :
    IsFactorCandidateData G core cand fac (canonicalBad G core cand z E) where
  coreClique := hcore
  candNotCore := hcand
  validHost := by
    intro e _ c hc
    rw [mem_canonicalBad] at hc
    push_neg at hc
    exact ⟨hc.1, hc.2.1⟩
  facMatching := hfac

variable {k s : ℕ} {core : Z ↪ V} {cand : Cand ↪ V}
variable {z : I → V} {E : I → Finset (Sym2 V)} {fac : Z × Z → Fin k}
variable {used : Finset (Z × Z)}
variable {α : Assign k s Cand}

/-- **The missing H1 compatibility realization.**  The surviving L2 family
built from `canonicalBad` is spoke-compatible with the actual L1 orientation.
The equivalence `roots` says that the phase-I hosts enumerate the whole core.
-/
theorem isSpokeCompatible_surviving_canonicalBad
    (h1 : IsMultiExteriorHub G z E) (roots : I ≃ Z)
    (hroot : ∀ i, z i = core (roots i))
    (hcand : ∀ c x, cand c ≠ core x) :
    IsSpokeCompatible z E
      (survivingHub s α fac (canonicalBad G core cand z E) used cand)
      (survivingBaseEdge s α fac (canonicalBad G core cand z E) used core) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hmem
    simp only [survivingHub_apply, Finset.mem_singleton] at hmem
    exact hcand _ (roots i) (hmem.symm.trans (hroot i))
  · intro i j e he
    rw [survivingBaseEdge_apply, Finset.disjoint_left]
    intro v hve hvb
    rw [Sym2.mem_toFinset] at hve hvb
    rw [Sym2.mem_iff] at hvb
    rcases hvb with hvb | hvb
    · let i' : I := roots.symm j.1.1
      have hz : z i' = core j.1.1 := by
        rw [hroot]
        simp [i']
      exact (h1.exterior i i' e he v hve) (hvb.trans hz.symm)
    · let i' : I := roots.symm j.1.2
      have hz : z i' = core j.1.2 := by
        rw [hroot]
        simp [i']
      exact (h1.exterior i i' e he v hve) (hvb.trans hz.symm)
  · intro j
    simp [survivingHub]
  · intro i j e he hzbase
    rw [Finset.disjoint_left]
    intro v hve hvhub
    simp only [survivingHub_apply, Finset.mem_singleton] at hvhub
    have hbad : hostUsed s α (canonicalBad G core cand z E j.1) (fac j.1)
        ∈ canonicalBad G core cand z E j.1 := by
      rw [mem_canonicalBad]
      right; right
      refine ⟨i, e, he, ?_, ?_⟩
      · simpa [survivingBaseEdge_apply] using hzbase
      · simpa [hvhub] using (Sym2.mem_toFinset.mp hve)
    exact (hostUsed_surviving_notMem j) hbad

/-! ## Exact finite partition of the core bases -/

/-- The ordered representatives `x < y` contain exactly one element for every
unordered pair of core vertices. -/
theorem card_corePairs : (corePairs Z).card = (Fintype.card Z).choose 2 := by
  by_cases hp0 : Fintype.card Z = 0
  · haveI : IsEmpty Z := Fintype.card_eq_zero_iff.mp hp0
    simp [corePairs]
  · have hp : 1 ≤ Fintype.card Z := Nat.one_le_iff_ne_zero.mpr hp0
    have h := sum_corePairs_defect (Z := Z) (fun _ => 1)
    simp only [sum_const, card_univ, smul_eq_mul, mul_one] at h
    have hprod : Fintype.card Z * (Fintype.card Z - 1) + Fintype.card Z =
        Fintype.card Z * Fintype.card Z := by
      calc
        Fintype.card Z * (Fintype.card Z - 1) + Fintype.card Z =
            Fintype.card Z * (Fintype.card Z - 1) + Fintype.card Z * 1 := by simp
        _ = Fintype.card Z * ((Fintype.card Z - 1) + 1) := by rw [Nat.mul_add]
        _ = Fintype.card Z * Fintype.card Z := by rw [Nat.sub_add_cancel hp]
    have hmul : (corePairs Z).card * 2 =
        Fintype.card Z * (Fintype.card Z - 1) := by omega
    rw [Nat.choose_two_right]
    exact Nat.eq_div_of_mul_eq_left (by decide) hmul

/-- With no pre-used core bases, every core base is counted exactly once:
it either survives the L2 assignment or it fails it. -/
theorem card_surviving_empty_add_card_failed
    (α : Assign k s Cand) (fac : Z × Z → Fin k) (bad : Z × Z → Finset Cand) :
    (survivingBases s α fac bad ∅).card + (failedBases s α fac bad).card =
      (corePairs Z).card := by
  simpa [survivingBases, failedBases] using
    (Finset.card_filter_add_card_filter_not (s := corePairs Z)
      (fun e => ¬ Fails s α (bad e) (fac e)))

/-- Literal two-vertex pieces representing the failed core bases. -/
def failedEdgePieces (core : Z ↪ V) (α : Assign k s Cand)
    (fac : Z × Z → Fin k) (bad : Z × Z → Finset Cand) : Finset (Finset V) :=
  (failedBases s α fac bad).image fun e => {core e.1, core e.2}

/-- Distinct ordered core bases give distinct literal two-vertex pieces. -/
theorem card_failedEdgePieces (core : Z ↪ V) (α : Assign k s Cand)
    (fac : Z × Z → Fin k) (bad : Z × Z → Finset Cand) :
    (failedEdgePieces core α fac bad).card = (failedBases s α fac bad).card := by
  classical
  apply Finset.card_image_of_injOn
  intro e he e' he' hset
  have hec := (mem_failedBases.mp he).1
  have hec' := (mem_failedBases.mp he').1
  change ({core e.1, core e.2} : Finset V) = {core e'.1, core e'.2} at hset
  apply eq_of_two_common hec hec' (ne_of_lt (mem_corePairs.mp hec))
  · exact Or.inl rfl
  · exact Or.inr rfl
  · have hm : core e.1 ∈ ({core e'.1, core e'.2} : Finset V) := by
      have : core e.1 ∈ ({core e.1, core e.2} : Finset V) := by simp
      rwa [hset] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    exact hm.elim (fun h => Or.inl (core.injective h))
      (fun h => Or.inr (core.injective h))
  · have hm : core e.2 ∈ ({core e'.1, core e'.2} : Finset V) := by
      have : core e.2 ∈ ({core e.1, core e.2} : Finset V) := by simp
      rwa [hset] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    exact hm.elim (fun h => Or.inl (core.injective h))
      (fun h => Or.inr (core.injective h))

/-! ## Exact L3 from literal counts -/

open PaperIV.PhysicalCompletion PaperIV.RD09PhysicalLedger

/-- A literal packing consisting only of triangles has gain twice its number
of pieces. -/
theorem totalGain_eq_two_mul_card_of_triangles
    {P : Finset (Finset V)} (htri : ∀ t ∈ P, t.card = 3) :
    totalGain P = 2 * P.card := by
  rw [totalGain, Finset.sum_congr rfl (fun t ht => gainOf_of_card_three (htri t ht)),
    Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **L3 without subtraction.**  The graph-edge count and the two-phase
triangle count imply the exact completion ledger.  Writing both inputs in
additive form avoids every truncated-natural subtraction.

* `hgraph` is `e(G)+A = C(p,2)+p*q+m`;
* `hphase` is `|P|+g = f+C(p,2)`;
* `hbase` is `B+C(p,2)=p*q`.
-/
theorem L3_of_literal_triangle_counts {P : Finset (Finset V)}
    (hP : IsK34Packing G P) (htri : ∀ t ∈ P, t.card = 3)
    {p q B : ℕ}
    (missingEdges rootLossEdges : Finset (Sym2 V))
    (removedPieces recoveredPieces : Finset (Finset V))
    (hgraph : (graphEdges G).card + rootLossEdges.card =
      p.choose 2 + p * q + missingEdges.card)
    (hphase : P.card + recoveredPieces.card =
      removedPieces.card + p.choose 2)
    (hbase : B + p.choose 2 = p * q) :
    (completion G P).card + rootLossEdges.card + 2 * removedPieces.card
      = B + missingEdges.card + 2 * recoveredPieces.card := by
  have hgain := totalGain_eq_two_mul_card_of_triangles htri
  have hcomp := card_completion_add_totalGain hP
  omega

/-- Literal graph and phase counts, together with L9 and L10, construct the
canonical `PhysicalAccounts`; L3 is derived above rather than received as a
ledger hypothesis. -/
def physicalAccountsOfLiteralCounts {P : Finset (Finset V)}
    (hP : IsK34Packing G P) (htri : ∀ t ∈ P, t.card = 3)
    {p q B : ℕ}
    (missingEdges rootLossEdges : Finset (Sym2 V))
    (removedPieces recoveredPieces : Finset (Finset V))
    (hgraph : (graphEdges G).card + rootLossEdges.card =
      p.choose 2 + p * q + missingEdges.card)
    (hphase : P.card + recoveredPieces.card =
      removedPieces.card + p.choose 2)
    (hbaseNat : B + p.choose 2 = p * q)
    (L9 : 1600 * missingEdges.card
      ≤ 2920 * removedPieces.card + 219 * rootLossEdges.card)
    (L10 : 200 * recoveredPieces.card
      ≤ 35 * rootLossEdges.card + 8 * removedPieces.card) :
    PhysicalAccounts G P where
  order := p + q
  split := p
  baseCount := B
  base_eq := by
    rw [PaperIV.splitBaseline]
    have h := congrArg (fun x : ℕ => (x : ℚ)) hbaseNat
    push_cast at h
    rw [Nat.cast_choose_two] at h
    have hpq : (p : ℚ) * ((p : ℚ) + (q : ℚ) - (p : ℚ)) = (p : ℚ) * (q : ℚ) := by ring
    rw [hpq]
    linarith
  missingEdges := missingEdges
  rootLossEdges := rootLossEdges
  removedPieces := removedPieces
  recoveredPieces := recoveredPieces
  L3 := L3_of_literal_triangle_counts hP htri missingEdges rootLossEdges
    removedPieces recoveredPieces hgraph hphase hbaseNat
  L9 := L9
  L10 := L10

/-! ## End-to-end H1 literal assembly -/

/-- **Gate 1, closed.**  The actual L1 triangle family and the actual L2
survivors form one physical packing.  Failed bases are represented by distinct
literal two-vertex pieces, the core bases split exactly into survivors and
failures, and therefore L3 is derived from the literal counts.  The conclusion
contains a concrete `PhysicalAccounts`, not an anonymous numeric ledger.

The hypotheses `L9` and `L10` are precisely the already separated arithmetic
consequences of the L1 and L2 estimates; all geometric compatibility and all
cardinality glue are discharged here. -/
theorem exists_h1_literal_physicalAccounts
    (h1 : IsMultiExteriorHub G z E) (roots : I ≃ Z)
    (hroot : ∀ i, z i = core (roots i))
    (hcand : ∀ c x, cand c ≠ core x)
    (hdata : IsFactorCandidateData G core cand fac (canonicalBad G core cand z E))
    {B : ℕ} (missingEdges rootLossEdges : Finset (Sym2 V))
    (hgraph : (graphEdges G).card + rootLossEdges.card =
      (Fintype.card Z).choose 2 + Fintype.card Z * Fintype.card Cand + missingEdges.card)
    (hbaseNat : B + (Fintype.card Z).choose 2 =
      Fintype.card Z * Fintype.card Cand)
    (L9 : 1600 * missingEdges.card ≤
      2920 * (multiLiftedPacking z E).card + 219 * rootLossEdges.card)
    (L10 : 200 * (failedBases s α fac (canonicalBad G core cand z E)).card ≤
      35 * rootLossEdges.card + 8 * (multiLiftedPacking z E).card) :
    let hub := survivingHub s α fac (canonicalBad G core cand z E) ∅ cand
    let base := survivingBaseEdge s α fac (canonicalBad G core cand z E) ∅ core
    let P := multiLiftedPacking z E ∪ phaseTwoPacking hub base
    ∃ acc : PhysicalAccounts G P,
      IsK34Packing G P ∧
      acc.order = Fintype.card Z + Fintype.card Cand ∧
      acc.missingEdges = missingEdges ∧
      acc.rootLossEdges = rootLossEdges ∧
      acc.removedPieces = multiLiftedPacking z E ∧
      acc.recoveredPieces =
        failedEdgePieces core α fac (canonicalBad G core cand z E) := by
  classical
  dsimp only
  let bad := canonicalBad G core cand z E
  let hub := survivingHub s α fac bad ∅ cand
  let base := survivingBaseEdge s α fac bad ∅ core
  let P := multiLiftedPacking z E ∪ phaseTwoPacking hub base
  let recovered := failedEdgePieces core α fac bad
  have h2 : IsPhaseTwoFamily G hub base := isPhaseTwoFamily_surviving hdata
  have hc : IsSpokeCompatible z E hub base :=
    isSpokeCompatible_surviving_canonicalBad h1 roots hroot hcand
  have hP : IsK34Packing G P := hc.isK34Packing_union_phases h1 h2
  have htri : ∀ t ∈ P, t.card = 3 := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact PaperIV.RD09TerminalAssembly.card_eq_three_of_mem_multiLiftedPacking h1 ht
    · rw [mem_phaseTwoPacking] at ht
      obtain ⟨j, rfl⟩ := ht
      exact h2.card_piece_eq_three (by simp [hub, survivingHub])
  have hrecovered : recovered.card = (failedBases s α fac bad).card :=
    card_failedEdgePieces core α fac bad
  have hpartition : (survivingBases s α fac bad ∅).card +
      (failedBases s α fac bad).card = (Fintype.card Z).choose 2 := by
    rw [← card_corePairs]
    exact card_surviving_empty_add_card_failed α fac bad
  have hphase : P.card + recovered.card =
      (multiLiftedPacking z E).card + (Fintype.card Z).choose 2 := by
    change (multiLiftedPacking z E ∪ phaseTwoPacking hub base).card + recovered.card =
      (multiLiftedPacking z E).card + (Fintype.card Z).choose 2
    have hu := hc.card_union_phases h1 h2
    rw [Fintype.card_coe] at hu
    have hremoved := card_multiLiftedPacking h1
    rw [hrecovered]
    omega
  have L10' : 200 * recovered.card ≤
      35 * rootLossEdges.card + 8 * (multiLiftedPacking z E).card := by
    rw [hrecovered]
    simpa [bad] using L10
  let acc := physicalAccountsOfLiteralCounts hP htri
    missingEdges rootLossEdges (multiLiftedPacking z E) recovered
    hgraph hphase hbaseNat L9 L10'
  exact ⟨acc, hP, rfl, rfl, rfl, rfl, rfl⟩

end PaperIV.RD09H1SpokeRealization
