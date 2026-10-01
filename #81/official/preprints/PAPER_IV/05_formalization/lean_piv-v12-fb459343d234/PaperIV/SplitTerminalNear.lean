import PaperIV.SplitTriangleFactor
import PaperIV.SplitTriangleFactorOdd
import PaperIV.SplitTriangleFactorHighHost
import PaperIV.TerminalToNear

/-!
# Complete-split terminal directly supplies the near-regime witness

This is the small, literal bridge between the round-robin split constructor and
the numerical near arm.  It does not use the RD09 defect ledger: for the
complete-split terminal, the completed packing itself has an exact count.
-/

namespace PaperIV.SplitTerminalNear

open Finset PaperIV.Model PaperIV.PhysicalCompletion
open PaperIV.SplitUniformIncidence PaperIV.SplitTriangleFactor
open PaperIV.SplitTriangleFactorOdd
open PaperIV.SplitTriangleFactorHighHost
open PaperIV.TwoRegimeAssembly
open PaperIV.TerminalLedger

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The completed round-robin terminal has a count independent of the number
of available hosts.  A missing host merely replaces one triangle factor by its
`n + 1` uncovered inner edges. -/
theorem exists_split_terminal_count {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {n : ℕ} (hk : Core.card = 2 * n + 2) (hh : Hosts.card ≤ 2 * n + 1) :
    ∃ P : Finset (Finset V),
      IsK34Packing (splitGraph Core Hosts) P ∧
      IsExactPartition (splitGraph Core Hosts) (completion (splitGraph Core Hosts) P) ∧
      (completion (splitGraph Core Hosts) P).card = (n + 1) * (2 * n + 1) ∧
      totalGain P = 2 * (Hosts.card * (n + 1)) := by
  obtain ⟨P, hpacking, hexact, hcount, hgain⟩ :=
    exists_split_physical_terminal hd hk hh
  refine ⟨P, hpacking, hexact, ?_, hgain⟩
  rw [hcount, Nat.add_comm, Nat.mul_comm Hosts.card (n + 1), ← Nat.mul_add,
    Nat.sub_add_cancel hh]

/-- If the common target dominates the exact complete-split terminal count,
the literal completed packing is a near-regime certificate. -/
theorem exists_nearCertificate_of_split_target {Core Hosts : Finset V}
    (hd : Disjoint Core Hosts) {n : ℕ} (hk : Core.card = 2 * n + 2)
    (hh : Hosts.card ≤ 2 * n + 1) {Q : ℚ}
    (hQ : (((n + 1) * (2 * n + 1) : ℕ) : ℚ) ≤ Q) :
    ∃ P : Finset (Finset V),
      IsExactPartition (splitGraph Core Hosts) (completion (splitGraph Core Hosts) P) ∧
      NearCertificate Q ((completion (splitGraph Core Hosts) P).card : ℚ) := by
  obtain ⟨P, -, hexact, hcount, -⟩ := exists_split_terminal_count hd hk hh
  refine ⟨P, hexact, ⟨?_⟩⟩
  rw [hcount]
  exact hQ

/-- The exact complete-split packing can also be presented through the shared
RD09 terminal interface.  Its local ledger is neutral: its base is the actual
number of completed pieces and all three defect accounts vanish. -/
theorem exists_neutral_physicalTerminal {Core Hosts : Finset V}
    (hd : Disjoint Core Hosts) {n : ℕ} (hk : Core.card = 2 * n + 2)
    (hh : Hosts.card ≤ 2 * n + 1) :
    ∃ T : PhysicalTerminal (G := splitGraph Core Hosts),
      T.base = (((n + 1) * (2 * n + 1) : ℕ) : ℚ) ∧
      T.missing = 0 ∧ T.rootLoss = 0 ∧ T.removed = 0 ∧ T.recovered = 0 := by
  obtain ⟨P, hpacking, -, hcount, -⟩ := exists_split_terminal_count hd hk hh
  refine ⟨PhysicalTerminal.neutral P hpacking, ?_, ?_⟩
  · rw [PhysicalTerminal.neutral_base]
    exact_mod_cast hcount
  · exact PhysicalTerminal.neutral_zero_accounts P hpacking

/-- The neutral terminal above yields the same near certificate through the
common RD09 adapter, rather than only through the direct count lemma. -/
theorem exists_nearCertificate_of_neutral_terminal {Core Hosts : Finset V}
    (hd : Disjoint Core Hosts) {n : ℕ} (hk : Core.card = 2 * n + 2)
    (hh : Hosts.card ≤ 2 * n + 1) {Q : ℚ}
    (hQ : (((n + 1) * (2 * n + 1) : ℕ) : ℚ) ≤ Q) :
    ∃ T : PhysicalTerminal (G := splitGraph Core Hosts),
      IsExactPartition (splitGraph Core Hosts)
        (completion (splitGraph Core Hosts) T.packing) ∧
      NearCertificate Q ((completion (splitGraph Core Hosts) T.packing).card : ℚ) := by
  obtain ⟨T, hbase, hmissing, hroot, -, -⟩ :=
    exists_neutral_physicalTerminal hd hk hh
  refine ⟨T, T.exactPartition, ?_⟩
  apply PaperIV.TerminalToNear.nearCertificate_of_physicalTerminal T
  · linarith [hbase, hQ]
  · rw [hmissing]
  · rw [hroot]

/-- For an even split core, the low-host round-robin construction and the
high-host completion fit into one literal terminal statement.  The residue is
zero up to `k - 1` hosts and thereafter exactly one `K2` cross-edge piece per
extra core--host edge. -/
theorem exists_even_split_terminal_count_all_hosts {Core Hosts : Finset V}
    (hd : Disjoint Core Hosts) {n : ℕ} (hk : Core.card = 2 * n + 2) :
    ∃ P : Finset (Finset V),
      IsK34Packing (splitGraph Core Hosts) P ∧
      IsExactPartition (splitGraph Core Hosts) (completion (splitGraph Core Hosts) P) ∧
      (completion (splitGraph Core Hosts) P).card =
        Core.card.choose 2 + Core.card * (Hosts.card - (2 * n + 1)) := by
  obtain ⟨P, hpacking, -, hexact, hcount⟩ :=
    exists_split_completion_card hd hk
  exact ⟨P, hpacking, hexact, hcount⟩

/-- The unified even-core terminal is a near-regime witness whenever the
target dominates its exact physical completion count. -/
theorem exists_nearCertificate_of_even_split_target_all_hosts
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {n : ℕ}
    (hk : Core.card = 2 * n + 2) {Q : ℚ}
    (hQ : ((Core.card.choose 2 + Core.card * (Hosts.card - (2 * n + 1)) : ℕ) : ℚ) ≤ Q) :
    ∃ P : Finset (Finset V),
      IsExactPartition (splitGraph Core Hosts) (completion (splitGraph Core Hosts) P) ∧
      NearCertificate Q ((completion (splitGraph Core Hosts) P).card : ℚ) := by
  obtain ⟨P, -, hexact, hcount⟩ :=
    exists_even_split_terminal_count_all_hosts hd hk
  refine ⟨P, hexact, ⟨?_⟩⟩
  rw [hcount]
  exact hQ

/-- The already-constructed odd-core packing has an equally explicit completed
count.  The extra `Hosts.card` term is the linear odd-core residue. -/
theorem exists_odd_split_terminal_count {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {n : ℕ} (hk : Core.card = 2 * n + 3) (hh : Hosts.card ≤ 2 * n + 1) :
    ∃ P : Finset (Finset V),
      IsK34Packing (splitGraph Core Hosts) P ∧
      IsExactPartition (splitGraph Core Hosts) (completion (splitGraph Core Hosts) P) ∧
      (completion (splitGraph Core Hosts) P).card =
        (2 * n + 3) * (n + 1) + Hosts.card ∧
      totalGain P = 2 * (Hosts.card * (n + 1)) := by
  obtain ⟨P, hpacking, -, hcard, hgain, -, huncov⟩ :=
    exists_split_triangle_packing_odd hd hk hh
  refine ⟨P, hpacking, isExactPartition_completion hpacking.toIsPacking, ?_, hgain⟩
  rw [card_completion hpacking, hcard]
  change Hosts.card * (n + 1) +
    (graphEdges (splitGraph Core Hosts) \ coveredEdges P).card =
      (2 * n + 3) * (n + 1) + Hosts.card
  rw [huncov]
  have hle : Hosts.card * n ≤ (2 * n + 3) * (n + 1) := by
    calc
      Hosts.card * n ≤ (2 * n + 1) * n := Nat.mul_le_mul_right _ hh
      _ ≤ (2 * n + 3) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
  have hpieces : Hosts.card * (n + 1) = Hosts.card * n + Hosts.card := by ring
  rw [hpieces]
  omega

/-- The odd-core terminal also enters the shared RD09 interface with its exact
linear-residue baseline and zero local defect accounts. -/
theorem exists_neutral_physicalTerminal_odd {Core Hosts : Finset V}
    (hd : Disjoint Core Hosts) {n : ℕ} (hk : Core.card = 2 * n + 3)
    (hh : Hosts.card ≤ 2 * n + 1) :
    ∃ T : PhysicalTerminal (G := splitGraph Core Hosts),
      T.base = (((2 * n + 3) * (n + 1) + Hosts.card : ℕ) : ℚ) ∧
      T.missing = 0 ∧ T.rootLoss = 0 ∧ T.removed = 0 ∧ T.recovered = 0 := by
  obtain ⟨P, hpacking, -, hcount, -⟩ := exists_odd_split_terminal_count hd hk hh
  refine ⟨PhysicalTerminal.neutral P hpacking, ?_, ?_⟩
  · rw [PhysicalTerminal.neutral_base]
    exact_mod_cast hcount
  · exact PhysicalTerminal.neutral_zero_accounts P hpacking

/-- The established odd-core terminal yields a near certificate whenever the
target dominates its explicit linear-residue count. -/
theorem exists_nearCertificate_of_neutral_terminal_odd {Core Hosts : Finset V}
    (hd : Disjoint Core Hosts) {n : ℕ} (hk : Core.card = 2 * n + 3)
    (hh : Hosts.card ≤ 2 * n + 1) {Q : ℚ}
    (hQ : (((2 * n + 3) * (n + 1) + Hosts.card : ℕ) : ℚ) ≤ Q) :
    ∃ T : PhysicalTerminal (G := splitGraph Core Hosts),
      IsExactPartition (splitGraph Core Hosts)
        (completion (splitGraph Core Hosts) T.packing) ∧
      NearCertificate Q ((completion (splitGraph Core Hosts) T.packing).card : ℚ) := by
  obtain ⟨T, hbase, hmissing, hroot, -, -⟩ :=
    exists_neutral_physicalTerminal_odd hd hk hh
  refine ⟨T, T.exactPartition, ?_⟩
  apply PaperIV.TerminalToNear.nearCertificate_of_physicalTerminal T
  · linarith [hbase, hQ]
  · rw [hmissing]
  · rw [hroot]

end PaperIV.SplitTerminalNear
