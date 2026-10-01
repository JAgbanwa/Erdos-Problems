# Paper IV v1.0 — identified Lean source freeze

Freeze ID: `piv-v1.0-f1769273dd2c` (the first 12 hex digits of the SHA-256 of `SOURCES.json`). This identifies a local source cut, not a Git commit or a public release.

The source-only tree is `lean_v1.0_freeze/`. It contains exactly the 504 Lean files in `SOURCES.json`, the pinned `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, and the serial build driver `tools/paperiv_build.py`. Every copied Lean file was compared against its recorded SHA-256; all 504 matched. No `.lake` packages, compiled objects, credentials, or unrelated research files are included.

The source archive is `LEAN_SOURCE_SNAPSHOT_v1.0.zip` (SHA-256 `0a13c01cc4cf0198d5d138082d45b25df4c5ac0684c0ed85e7cc758575f8a7dd`). It has 508 entries: 504 Lean files and four build/configuration files. The recorded build and complete per-module logs are in `../03_reproducibility/build_v1.0_20260927/`; its `SOURCES.json` has SHA-256 `f1769273dd2c5ba6d3e5f9cc50874aa292879b0e19952c387bf4908c52f5f07d`.

The combined local build reported 504 PASS, zero FAIL/BLOCKED, no source changes during execution, and exit code 0. Its 13 requested targets, including the root, audit targets, explicit-threshold audit, 195 export checks, and the constructor-budget audit, each recorded exit code 0. The recorded environment is Lean 4.28.0 and Mathlib revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365`, using an existing shared dependency cache. The full audit must still examine types, logs, source-to-paper correspondence, and the final preprints; this freeze note is not that verdict.

Reproduction must use the pinned dependencies in the manifest and the target list in `RUN_META.json`. The source ZIP does not embed Mathlib. The public v0.8 draft and its historical freeze remain separate.

The §8.2 `BoundedCliqueGap` complement is supplied separately as
`lean_v1.0_gap_annex/` and `LEAN_BOUNDED_GAP_ANNEX_v1.0.zip` (SHA-256
`2847a422865e06880d457ea806aae5b9f749d22359eff325349c09c01cb4837d`).
Its 38 Lean files were compiled in the distinct, earlier 579-module
`optimized-clean-all` run, archived under
`../03_reproducibility/build_gap_annex_20260927/`. Their 12 local `PaperIV`
dependencies are byte-identical to the main freeze. The annex is not imported
by `PaperIV` and does not alter the 504-module freeze or its theorem cone.
