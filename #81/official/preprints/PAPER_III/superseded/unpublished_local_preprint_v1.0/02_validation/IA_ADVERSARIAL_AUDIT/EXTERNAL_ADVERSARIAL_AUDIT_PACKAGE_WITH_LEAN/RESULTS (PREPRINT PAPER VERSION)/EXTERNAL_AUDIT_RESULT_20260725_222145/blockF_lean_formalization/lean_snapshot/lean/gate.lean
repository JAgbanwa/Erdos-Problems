/-
Block F axiom/statement gate (reference template).

Run at audit time against the FROZEN release-commit snapshot:
    lake env lean gate.lean  > results/axioms_report.txt 2>&1

F2 (axioms): read each `#print axioms` output and check it against the expected set.
  Layer E (unconditional): EXACTLY  [propext, Classical.choice, Quot.sound].
  Layer X (uses AX1/AX2):  EXACTLY  [propext, Classical.choice, Quot.sound,
                                     PaperIII.AX1, PaperIII.AX2]  (or the subset used).
  ANY other axiom, or `sorryAx`, is a BLOCKING finding.

F3 (statements): each `#check` type must match the LEDGER.md node verbatim
  (hypotheses + quantifiers included). Adjust the declaration names below to the
  final ones if the formalization renamed anything (record any rename as a finding).
-/
import PaperIII

-- ---- Layer X (must be exactly propext/Classical.choice/Quot.sound + AX1 + AX2) ----
#print axioms PaperIII.Theorem_1_1
#print axioms PaperIII.Corollary_1_2
#print axioms PaperIII.E_4_3
#print axioms PaperIII.E_8

-- ---- Layer E (must be exactly propext/Classical.choice/Quot.sound; NO AX1/AX2) ----
#print axioms PaperIII.Prop_10_1_low
#print axioms PaperIII.Prop_10_1_mid
#print axioms PaperIII.E_3_1
#print axioms PaperIII.E_4_1
#print axioms PaperIII.E_4_2
#print axioms PaperIII.E_5_1
#print axioms PaperIII.E_5_2
#print axioms PaperIII.E_6_1
#print axioms PaperIII.E_7_1
#print axioms PaperIII.pathCorrection_odd_iff          -- E-B
#print axioms PaperIII.AppendixD.konig_edge_coloring   -- E-D.3
#print axioms PaperIII.AppendixD.galvin_max_degree     -- E-D.3 (max-degree case)
#print axioms PaperIII.clique_divisible_correction     -- §8 divisibility correction

-- ---- the two intended axioms themselves ----
#print axioms PaperIII.AX1
#print axioms PaperIII.AX2

-- ---- F3: statement signatures vs LEDGER.md (spot list; extend to every node) ----
#check @PaperIII.Theorem_1_1
#check @PaperIII.Corollary_1_2
#check @PaperIII.Prop_10_1_low
#check @PaperIII.Prop_10_1_mid
#check @PaperIII.E_3_1
#check @PaperIII.E_4_2
#check @PaperIII.E_7_1
#check @PaperIII.AX1
#check @PaperIII.AX2
