/-
Paper II — Complete-Split Extremizers for the finite fractional deficit `Φ_τ`.

Formalization target (Theorem 1.2, the ONLY claim of Paper II):
  for every `n ≥ 1`,
    max over chordal `G` with `|V(G)| = n` of `(|E(G)| − 2·τ₃*(G))` = ⌊(2n+1)²/24⌋.

Source of truth: `PAPER_II_CALCULATION_LEDGER_v1.0.md` (steps D1–D7, A1–A6, L1–L12).
This file is the library root; modules are added per sprint (S1–S4).
-/

import PaperII.Arith
import PaperII.FiniteCover
import PaperII.CoverRelabel
import PaperII.Model
import PaperII.VertexCopy
import PaperII.L1
import PaperII.CompleteSplit
import PaperII.EdgeCount
import PaperII.CloneSimplicial
import PaperII.Chordal
import PaperII.Dirac
import PaperII.IsChordal
import PaperII.IsChordalCopy
import PaperII.Dirac1
import PaperII.L9Packing
import PaperII.L9
import PaperII.L10
import PaperII.IsoInvariance
import PaperII.ConvexSeq
import PaperII.L7
import PaperII.CloneCopy
import PaperII.L5
import PaperII.L3
import PaperII.L2Family
import PaperII.L4
import PaperII.L2
import PaperII.L6
import PaperII.CompleteSplitChordal
import Pa