# Author build evidence — Paper III v1.4

Verdict for internal review: `PASS_CLEAN_ORIGIN_RESUMED`.

The evidence ZIP was produced on `CCS_NOTEBOOK456` and copied into this
directory without renaming. Its SHA-256 is
`581ac8746e836052ae73f05e7feac0ebad53708abda76a7e48f96e415476f9ad`.
All 33 entries in `RESULTS/RESULTS_MANIFEST.sha256` verify.

The project began from a source-only state: no project `.lake` directory, no
compiled project object, and 704 Lean source files. `lake exe cache get`
returned exit code 0. The initial public-root process was interrupted when the
Codex desktop application restarted; the same unchanged project was resumed
incrementally. The resumed `lake build PaperIII` returned exit code 0 and
reported 8,455 jobs. The seven query roots then returned exit code 0 and
reported 8,444 jobs.

All eight axiom-query files returned exit code 0. They cover 42 surfaces,
including `PaperIII.Theorem_1_1`; no `sorryAx` or project-local axiom occurs in
those reports, and every footprint is contained in
`[propext, Classical.choice, Quot.sound]`. The import-closure record confirms
that the public root reaches both `PaperIII.Theorem_1_1_Final` and
`PaperIII.PublicAPI`, and that the two archived comparison modules containing
project axioms are unreachable from every canonical root.

This record is not represented as a single uninterrupted invocation. A later
uninterrupted run may supersede it for publication evidence, but the disclosed
interruption does not invalidate static internal review of the successful
commands and frozen outputs recorded here.
