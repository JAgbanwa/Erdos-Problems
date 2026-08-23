# Paper III v1.4 clean uninterrupted author build

**Classification:** `PASS_CLEAN_UNINTERRUPTED`  
**Machine:** `CCS_NOTEBOOK456`  
**Raw runner result:** `PASS`  
**Validation:** 69/69 checks pass

## Received evidence

- Original results ZIP preserved byte-for-byte.
- Received ZIP SHA-256:
  `7f3d9d9a630ccc0603596a3f661211f8cafb2b49bb7b33ef20e1d2e4fcb9bc63`.
- The received sidecar matches the ZIP.
- The internal 32-entry results manifest verifies completely.

## Run result

- Continuous run from `2026-08-23T00:53:03Z` to `2026-08-23T02:11:32Z`.
- Duration: 4,709.241 seconds.
- Initial project `.lake` directory absent; initial compiled project artifacts: zero.
- Dependency cache command: exit 0.
- Clean public-root build: 8,455/8,455 jobs, exit 0.
- Query-root build: 8,444/8,444 jobs, exit 0.
- Eight axiom-query files: all exit 0.
- Forty-two theorem-level axiom surfaces.
- Axiom union exactly `[propext, Classical.choice, Quot.sound]`.
- `sorryAx`: zero; active `sorry` build warnings: zero.
- Public root reaches the final theorem and PublicAPI.
- Canonical closure excludes the archived Wlog and Axioms modules.
- All nine dependencies are clean and match their pinned revisions.
- Project configuration is byte-identical before and after the run and matches the freeze.
- All 707 freeze source/config hashes match the build-kit project manifest.

## Interpretive notes

`ENVIRONMENT.json` records a missing default Lean toolchain because the environment probe ran
outside the project directory. This does not qualify the build result: the project-local pinned
toolchain compiled both roots and all axiom queries successfully.

The raw escape-hatch scan intentionally covers all 704 project Lean files and therefore lists
textual mentions and declarations in archived/noncanonical exploration modules. The canonical
import-closure check excludes those axiom modules, and the 42 queried public surfaces have only
the foundational axiom footprint above.

This is author-side reproduction evidence. It strengthens the release record but does not
replace the already completed independent external Lean reproduction or human peer review.
