import PaperIV.RD09PhysicalLedger
import PaperIV.SymmetrizationInvariantBarrier
import PaperIV.H1DescentBarrier

/-!
# S01–S03: local defect and contraction inequalities

The near-regime route needs three linked inequalities between the *physical
accounts* of the paid RD09 terminal and the *metric* position of a graph
relative to the critical split family.

* **S01 (local defect).**  A terminal paying the RD09 discount against a
  baseline below the near-regime target has its two visible accounts paid by
  the deficit:
  `m + 10·A ≤ 20·(target − count)`.
  This is `accounts_le_twenty_deficit`, with
  `accounts_le_twenty_sharpEnvelope_deficit` the version in which the target is
  the sharp envelope and the baseline is `splitBaseline n p`.

* **S02 (accounts → edit distance).**  If each unit of the two accounts costs
  at most one edit — i.e. `dist · scale ≤ m + A` for the normalization `scale`
  — then a defect bound `m + A ≤ 20·D` contracts the distance:
  `dist ≤ 20·D / scale`.  This is `dist_le_of_accounts`.

* **S03 (contraction with room for one copy step).**  The contracted value
  `20·D/scale` must leave room for one gated copy step of size `1/n` strictly
  inside the barrier.  `contraction_gap_thirty` is the explicit arithmetic for
  the safe window `D = n²/30`, `scale = n²`: from `n ≥ 60`,
  `20·(n²/30)/n² + 1/n = 2/3 + 1/n < 7/10`.

`local_contraction` chains S01–S03, and `hlocal_of_uniform_accounts` packages
the chain in exactly the shape consumed by the invariant-aware first-entry
barrier of `SymmetrizationInvariantBarrier`: the accounts only have to be supplied for
chordal graphs inside the defect window `F4' G ≤ F4' X ≤ F4' H`.

Finally `first_entry_of_windowed_accounts` runs the whole near-regime
localization: a windowed physical account supply plus a terminal inside the
barrier put the *original* graph inside the barrier.  It locates `G`; it does
not build a partition of `G`, and nothing here closes `NearRegimeAt`.
-/

namespace PaperIV.LocalStability

open PaperIV.RD09PhysicalLedger
open PaperIV.VertexCopyGate
open PaperIV.SymmetrizationBarrier
open PaperIV.GraphFamilyDistance

/-! ## S01: the local defect inequality -/

/-- **S01.**  A paid RD09 terminal whose baseline lies below the near-regime
target pays both visible accounts out of the target deficit. -/
theorem accounts_le_twenty_deficit {count base target m A : ℚ}
    (hpaid : count ≤ base - m / 20 - A / 2) (hbase : base ≤ target) :
    m + 10 * A ≤ 20 * (target - count) := by
  linarith

/-- The `m + A` form of S01, available once the root loss is nonnegative. -/
theorem accounts_sum_le_twenty_deficit {count base target m A : ℚ}
    (hpaid : count ≤ base - m / 20 - A / 2) (hbase : base ≤ target) (hA : 0 ≤ A) :
    m + A ≤ 20 * (target - count) := by
  have h := accounts_le_twenty_deficit hpaid hbase
  linarith

/-- **S01 against the sharp envelope.**  With a physical baseline
`splitBaseline n p` the deficit may be measured against `sharpEnvelope n`,
since the split baseline never exceeds the envelope. -/
theorem accounts_le_twenty_sharpEnvelope_deficit {n p count m A : ℚ}
    (hpaid : count ≤ splitBaseline n p - m / 20 - A / 2) :
    m + 10 * A ≤ 20 * (sharpEnvelope n - count) :=
  accounts_le_twenty_deficit hpaid (splitBaseline_le_sharpEnvelope n p)

/-- S01 for the literal physical accounts of a `K3`/`K4` packing: the missing
and root-loss families are bounded by twenty times the envelope deficit of the
completed packing. -/
theorem accounts_le_twenty_deficit_of_physicalAccounts
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finset (Finset V)} (acc : PhysicalAccounts G P) :
    (acc.missingEdges.card : ℚ) + 10 * (acc.rootLossEdges.card : ℚ)
      ≤ 20 * (sharpEnvelope acc.order
        - ((PaperIV.PhysicalCompletion.completion G P).card : ℚ)) :=
  accounts_le_twenty_sharpEnvelope_deficit acc.count_le_paid

/-! ## S02: from accounts to normalized edit distance -/

/-- **S02.**  A distance whose unnormalized value is at most the total of the
two accounts contracts proportionally to the defect bound. -/
theorem dist_le_of_accounts {dist m A scale D : ℚ} (hscale : 0 < scale)
    (hedits : dist * scale ≤ m + A) (hacc : m + A ≤ 20 * D) :
    dist ≤ 20 * D / scale := by
  rw [le_div_iff₀ hscale]
  linarith

/-! ## S03: contraction with room for one gated copy step -/

/-- **S03, general form.**  Anything bounded by the contracted value is
strictly inside a larger contraction constant. -/
theorem lt_contracted_of_le {dist contracted c : ℚ} (hdist : dist ≤ c)
    (hlt : c < contracted) : dist < contracted :=
  lt_of_le_of_lt hdist hlt

/-- **S03, explicit safe window.**  For `D = n²/30` and `scale = n²` the
contracted value is `2/3`, and from `n ≥ 60` one gated copy step of size `1/n`
still fits strictly below `7/10`. -/
theorem contraction_gap_thirty {n : ℚ} (hn : 60 ≤ n) :
    (2 : ℚ) / 3 + 1 / n < 7 / 10 := by
  have hpos : (0 : ℚ) < n := by linarith
  have h : 1 / n ≤ 1 / 60 := by
    rw [div_le_div_iff₀ hpos (by norm_num)]
    linarith
  linarith

/-- The contracted value of the safe window, computed. -/
theorem twenty_mul_div_thirty {n : ℚ} (hn : 0 < n) :
    20 * (n ^ 2 / 30) / n ^ 2 = 2 / 3 := by
  have hn2 : (n : ℚ) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-! ## Chaining S01–S03 -/

/-- **S01 + S02 + S03.**  A paid physical terminal for a graph at metric
position `dist`, whose accounts dominate the unnormalized distance, is
contracted strictly below `contracted`. -/
theorem local_contraction {count base target m A dist scale D contracted : ℚ}
    (hscale : 0 < scale)
    (hpaid : count ≤ base - m / 20 - A / 2) (hbase : base ≤ target)
    (hA : 0 ≤ A) (hdeficit : target - count ≤ D)
    (hedits : dist * scale ≤ m + A)
    (hlt : 20 * D / scale < contracted) :
    dist < contracted := by
  have hacc : m + A ≤ 20 * D := by
    have h := accounts_sum_le_twenty_deficit hpaid hbase hA
    linarith
  exact lt_contracted_of_le (dist_le_of_accounts hscale hedits hacc) hlt

/-! ## The hypothesis shape consumed by the invariant first-entry barrier -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The S01–S03 interface, in barrier form.**  If every chordal graph inside
the metric neighbourhood *and* inside the gated defect window admits physical
accounts controlling its unnormalized distance, then the local contraction
hypothesis required by `barrier_of_symmetrizationPath_invariant` holds. -/
theorem hlocal_of_uniform_accounts
    (distance : SimpleGraph V → ℚ) {G H : SimpleGraph V}
    {outer contracted scale D : ℚ} (hscale : 0 < scale)
    (haccounts : ∀ X : SimpleGraph V, PaperIV.IsChordal X →
      F4' G ≤ F4' X → F4' X ≤ F4' H → distance X < outer →
      ∃ m A : ℚ, 0 ≤ A ∧ m + A ≤ 20 * D ∧ distance X * scale ≤ m + A)
    (hlt : 20 * D / scale < contracted) :
    ∀ X : SimpleGraph V, PaperIV.IsChordal X →
      F4' G ≤ F4' X → F4' X ≤ F4' H → distance X < outer → distance X < contracted := by
  intro X hX hlow hhigh hout
  obtain ⟨m, A, -, hacc, hedits⟩ := haccounts X hX hlow hhigh hout
  exact lt_contracted_of_le (dist_le_of_accounts hscale hedits hacc) hlt

/-- **Near-regime first-entry localization.**  Windowed physical accounts
(S01–S03) plus a gated terminal inside the barrier place the *original* chordal
graph inside the barrier.

This is a statement about the position of `G` in the edit metric only.  It
produces no packing of `G`, and therefore no instance of `NearRegimeAt`. -/
theorem first_entry_of_windowed_accounts
    (F : Finset (Finset (Sym2 V))) (hF : F.Nonempty)
    {outer barrier contracted D : ℚ}
    (hn : 2 ≤ Fintype.card V)
    (hbarrierOuter : barrier ≤ outer)
    (hgap : contracted + 1 / (Fintype.card V : ℚ) < barrier)
    {G H : SimpleGraph V}
    (haccounts : ∀ X : SimpleGraph V, PaperIV.IsChordal X →
      F4' G ≤ F4' X → F4' X ≤ F4' H →
      graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) < outer →
      ∃ m A : ℚ, 0 ≤ A ∧ m + A ≤ 20 * D ∧
        graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) * (Fintype.card V : ℚ) ^ 2
          ≤ m + A)
    (hlt : 20 * D / (Fintype.card V : ℚ) ^ 2 < contracted)
    (hreach : SymmetrizationPath G H)
    (hend : graphFamDistNorm F hF H ((Fintype.card V : ℚ) ^ 2) < barrier) :
    graphFamDistNorm F hF G ((Fintype.card V : ℚ) ^ 2) < barrier := by
  have hscale : (0 : ℚ) < (Fintype.card V : ℚ) ^ 2 := by
    have : (0 : ℚ) < (Fintype.card V : ℚ) := by
      have : (2 : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast hn
      linarith
    positivity
  exact graphFamDistNorm_barrier_of_symmetrizationPath_invariant F hF hn hbarrierOuter hgap
    (hlocal_of_uniform_accounts
      (distance := fun X => graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2))
      hscale haccounts hlt)
    hreach hend

/-! ## Preferred localization: descending propagation

The theorem below is the active API for the independent H1 route.  It has the
same physical-account input as the historical minimal-index argument, but
propagates the contraction backwards by induction along the finite
symmetrization path.  In particular its statement and proof do not select a
first index.
-/

/-- **S01--S03 plus descending propagation localize the original graph.**

Windowed physical accounts give the local contraction.  The terminal is
inside `barrier`, and descending propagation puts the original chordal graph
inside the same barrier without a minimal-index construction. -/
theorem localize_original_of_windowed_accounts_descent
    (F : Finset (Finset (Sym2 V))) (hF : F.Nonempty)
    {outer barrier contracted D : ℚ}
    (hn : 2 ≤ Fintype.card V)
    (houter : barrier + 1 / (Fintype.card V : ℚ) ≤ outer)
    (hcb : contracted ≤ barrier)
    {G H : SimpleGraph V} (hG : PaperIV.IsChordal G)
    (haccounts : ∀ X : SimpleGraph V, PaperIV.IsChordal X →
      F4' G ≤ F4' X → F4' X ≤ F4' H →
      graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) < outer →
      ∃ m A : ℚ, 0 ≤ A ∧ m + A ≤ 20 * D ∧
        graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) *
          (Fintype.card V : ℚ) ^ 2 ≤ m + A)
    (hlt : 20 * D / (Fintype.card V : ℚ) ^ 2 < contracted)
    (hpath : SymmetrizationPath G H)
    (hend : graphFamDistNorm F hF H ((Fintype.card V : ℚ) ^ 2) < barrier) :
    graphFamDistNorm F hF G ((Fintype.card V : ℚ) ^ 2) < barrier := by
  have hscale : (0 : ℚ) < (Fintype.card V : ℚ) ^ 2 := by
    have hcard : (0 : ℚ) < (Fintype.card V : ℚ) := by
      have : (2 : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast hn
      linarith
    positivity
  exact PaperIV.H1DescentBarrier.graphFamDistNorm_barrier_of_symmetrizationPath_invariant_descent
    F hF hn houter hcb hG
      (hlocal_of_uniform_accounts
        (distance := fun X => graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2))
        hscale haccounts hlt)
      hpath hend

end PaperIV.LocalStability
