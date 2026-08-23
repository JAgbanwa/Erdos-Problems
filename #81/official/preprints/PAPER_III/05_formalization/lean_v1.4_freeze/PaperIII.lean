/-
# Paper III — Split-graph linear-error theorem (Erdős #81 program)

Public aggregate root for the Lean 4 / Mathlib formalization.  A successful
`lake build PaperIII` must compile the unconditional `Theorem_1_1`, its public
API, and their complete transitive dependency closure.  The explicit final
imports at the end of this file are release gates: they prevent a successful
default build from omitting the paper's headline theorem.
-/

import PaperIII.Defs
import PaperIII.Identities
import PaperIII.Duality
import PaperIII.SplitEdges
import PaperIII.Counting
import PaperIII.E_3_1_upper
import PaperIII.E_3_1_values
import PaperIII.E_4_2_algebra
import PaperIII.E_3_1_LP
import PaperIII.E_4_agg
import PaperIII.E_4_2
import PaperIII.AXDefs
import PaperIII.AX1Bridge
import PaperIII.AX1NibbleBridge
import PaperIII.E_4_3
import PaperIII.E_D
import PaperIII.Factorization
import PaperIII.E_B
import PaperIII.CorridorDefs
import PaperIII.E_5
import PaperIII.E_6
import PaperIII.E_7
import PaperIII.DiracHamilton
import PaperIII.E_8
import PaperIII.PackingCorollaries
import PaperIII.ShiftedCenterRobust
import PaperIII.Prop_10_1
import PaperIII.CliquePartition
import PaperIII.Main
import PaperIII.MainNibble
import PaperIII.PaperImprovements
import PaperIII.Contrib.MatchingMathlib
import PaperIII.Contrib.DiracMathlib
import PaperIII.Addenda
import PaperIII.CanonicalTrianglePacking
import PaperIII.Theorem_1_1_Final
import PaperIII.PublicAPI
