# E4 -- external Lean reproduction and axiom boundary

**Verdict: `FAIL`**, on one specific required confirmation. Everything else in this gate passes.

## What passes

Clean-room preconditions, all recorded rather than asserted: ZIP hash verified **before**
extraction; the three configuration files byte-identical to the freeze; Lean 4.28.0 and Lake
5.0.0; **9 of 9 dependencies at their exact declared revisions with empty `git status`**;
`lake exe cache get` exit 0 with nothing to download; project `.lake/build` **absent** before
and after, with zero project `.olean`/`.ilean` anywhere.

| Build | Jobs | Exit | Duration | Errors |
|---|---|---|---|---|
| `lake build PaperIII` | 8,203 | 0 | 90 min | 0 |
| the seven roots the queries import | 8,444 | 0 | 105 min | 0 |

Eight axiom queries, all exit 0: **42 surfaces, 0 `sorryAx`, 0 non-standard footprints, 0
project axioms**. One surface carries the smaller `[propext, Quot.sound]`.

The archived comparison axioms are outside the closure, verified by transitive import graph over
all **704** project modules rather than by grep: `Ax2.PartB.Axioms` and `Ax2.PartA.Wlog` are
imported by **nobody**, and no canonical root reaches either. The auditor's own initial flag --
that `Theorem_1_1_Final.lean` imports an `Ax2` module -- resolved: it imports
`Ax2.PartB.BKLO.Bridge`, not an axiom-bearing module.

The claim boundary is stated as the protocol requires: **a clean rebuild of Paper III against
the pinned, independently verified Mathlib dependency cache.** Not a rebuild of Mathlib from
source.

## What fails

The request requires confirming "that the public aggregate root and `PublicAPI` import the
intended canonical theorem path". `PaperIII.lean` imports 36 modules and imports **neither**
`PaperIII.Theorem_1_1_Final` **nor** `PaperIII.PublicAPI`. Its closure is 177 of 704 modules;
`Theorem_1_1_Final` needs 393. `lake build PaperIII` therefore succeeded without compiling
Theorem 1.1, and seven of eight queries then failed. See `EXT-V13-001`.

This also reconciles the three job counts as a target difference rather than a discrepancy:
8,203 aggregate, 8,444 canonical roots, 8,719 in the author's still larger replayed set.

Evidence: `results/03_lake_build_PaperIII.log`, `results/06_lake_build_query_roots.log`,
`results/07_*.log`, `results/import_closure.json`, `scripts/v13_import_closure.py`,
`../../10_LOGS/lean/`.
