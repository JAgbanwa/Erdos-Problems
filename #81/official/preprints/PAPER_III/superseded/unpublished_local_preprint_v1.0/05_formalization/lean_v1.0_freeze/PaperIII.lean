/-
# Paper III — Split-linear (Erdős #81 route) — Lean 4 / Mathlib formalization

Library root. One module per ledger node (`E_3_1`, `E_4_2`, …, `E_9`, plus the Layer-X
axioms `AX1`, `AX2`) is added per milestone; see `../LEDGER.md` (frozen spec) and
`../ARISTOTLE_AGENT_INSTRUCTIONS.md` (milestone plan M1–M4) and `../CLAUDE.md` (workflow).

Scaffold only for now: this file imports Mathlib so `lake build` confirms the toolchain
(Lean v4.28.0) and the Mathlib v4.28.0 cache are healthy before any node is formalized.
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
import PaperIII.AX
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
import PaperIII.Contrib.MatchingMathlib
import PaperIII.Contrib.DiracMathlib
import PaperIII.Addenda
