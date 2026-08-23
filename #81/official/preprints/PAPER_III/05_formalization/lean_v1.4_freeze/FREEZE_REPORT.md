# Paper III v1.4 local source freeze report

Status: `LOCAL_SOURCE_FREEZE_WITH_RECORDED_BUILD_EVIDENCE`.

## Perimeter

This snapshot contains 704 Lean source files and the pinned Lake/toolchain
files. It excludes dependency checkouts, `.lake`, compiled objects, repository
metadata, scratch files and unrelated editorial material. The only
theorem-source change from the v1.3 formal snapshot is the public aggregate
root `PaperIII.lean`: it imports `PaperIII.Theorem_1_1_Final` and
`PaperIII.PublicAPI` and states the corresponding root contract. The package
version in `lakefile.toml` is 1.4.0. No proof body, mathematical declaration,
hypothesis, constant or dependency revision changed.

`BUILD_INPUT_METADATA.json` preserves, under a non-current name, the metadata
that accompanied the build input before the run. `FREEZE_METADATA.json` is the
authoritative post-run metadata. Audit verdicts are deliberately recorded in
the sibling validation package rather than as mutable state inside this
immutable formal snapshot.

## Recorded build result

- Initial state: source-only, 704 Lean files, no project `.lake`, no compiled
  project objects.
- Dependency cache command: exit 0.
- Public root: `lake build PaperIII`, exit 0, 8,455 jobs.
- Query roots: exit 0, 8,444 jobs.
- Configuration files: byte-identical before and after the run.
- Dependencies: nine pinned revisions, all recorded clean.
- Root closure: `PaperIII` reaches `PaperIII.Theorem_1_1_Final` and
  `PaperIII.PublicAPI`; the public API reaches the final theorem.

The desktop application restarted during the original public-root process.
The same unchanged, clean-origin project was resumed incrementally and
completed successfully. Accordingly the precise classification is
`PASS_CLEAN_ORIGIN_RESUMED`, not an uninterrupted clean-build claim. The full
disclosure and logs are retained under
`gate_logs/run_2026-08-22_CCS_NOTEBOOK456_resumed/`.

## Axiom boundary

Eight compatible query files produced 42 axiom reports, including
`PaperIII.Theorem_1_1`. Every command exited 0; `sorryAx` is absent; every
reported footprint is a subset of `propext`, `Classical.choice`, and
`Quot.sound`. The import-closure evidence also shows that the archived modules
`Ax2.PartA.Wlog` and `Ax2.PartB.Axioms` are unreachable from all canonical
build and query roots.

## Interpretation

The recorded build verifies compilation and the stated axiom boundary for the
frozen sources. It does not substitute for independent mathematical
rederivation or external reproduction. An uninterrupted run on the faster
machine may later supersede this build record without changing the Lean source
snapshot.
