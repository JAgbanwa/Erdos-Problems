# Gate H — Independent Lean Build Record

## What was done
1. `lake build PaperII` in the project's `lean/` tree (toolchain
   `leanprover/lean4:v4.28.0`, lake 5.0.0), logged to `lake_build.log`.
2. An auditor-authored `AuditCheck.lean` (`#print axioms PaperII.theorem_1_2`,
   `#check @PaperII.theorem_1_2`, `#print PaperII.IsChordal`) elaborated with
   `lake env lean`, logged to `print_axioms.log`.
3. SHA-256 manifest of the exact Lean source built: `lean_source_sha256.txt`.

## Results
- **Build:** `Build completed successfully (8057 jobs).` (see `lake_build.log`).
  The log contains **no** `error`, `failed`, or `sorry`/`sorryAx` line — only
  benign `unusedSectionVars` linter warnings.
- **Sorry-free (source):** no `sorry`/`admit` tactic occurs in `lean/PaperII/*.lean`;
  the only `sorry` substrings are the words "sorry-free" inside docstrings
  (`Dirac1.lean:9`, `FiniteCover.lean:11`).
- **Statement shape (read + checked):** `PaperII.theorem_1_2`
  (`Unconditional.lean:72–79`) has hypotheses exactly `Fintype.card W = n` and
  `IsChordal G` — **no** `ChordalStructure`, **no** `A2Transfer` — and asserts
  BOTH the `∀` upper bound `phiTau G ≤ ⌊(2n+1)²/24⌋` AND the `∃` attainment.
  `phiTau` (`Model.lean:63`) `= edgeFinset.card − 2 * tau3star`.
- **`IsChordal` is standard** (`Chordal.lean:35`): every cycle walk of length
  `≥ 4` has a chord (two support vertices adjacent via an edge not on the cycle).
  Not weakened.
- **`#print axioms` footprint:** see `print_axioms.log`. Expected (and claimed by
  the project) to be exactly `[propext, Classical.choice, Quot.sound]` with no
  `sorryAx` and no project axiom.

## Residual (honest)
- The Mathlib dependency was taken from the project's pinned `lake-manifest.json`
  cache, not rebuilt from scratch in a clean-room machine.
- The SHA-256 match to commit `5f2d448` could **not** be verified in this
  environment: git history was unreachable (repo root resolved to `C:/` with no
  `HEAD`; object `5f2d448` not found) and the v1.0 release package does not bundle
  the `lean/` tree. `lean_source_sha256.txt` re