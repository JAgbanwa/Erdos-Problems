# Reproducing the Paper IV draft

## Exact source cut

The immutable mathematical source is `../05_formalization/lean_draft_freeze/`.
It is extracted byte-for-byte from the original `LEAN_SOURCE_SNAPSHOT_v0.8.zip`.
`../04_integrity/baseline/LEAN_CUT.json` records all 479 entries: 474 Lean
sources and five configuration/toolchain files. Test modules outside this
directory are release checks, not changes to the mathematical freeze.

The `lake-manifest.json` pins Mathlib and transitive Git dependencies to full
commit hashes. `PaperIIIRelease` is a relative local package included in the
freeze. Do not replace the manifest with newer dependencies when reproducing
this cut.

## Build and inspect the exported theorem

With Python 3 and elan/Lake available, from the Paper IV package directory:

```text
python 03_reproducibility/run_lean_checks.py
python 03_reproducibility/refresh_supplement.py
python 02_validation/01_INTERNAL_AUDITS/run_draft_20260921/check_release.py
```

On a machine without dependencies, first run the following in
`05_formalization/lean_draft_freeze`:

```text
lake exe cache get
```

This downloads the pinned Mathlib build cache; it is not a mathematical
hypothesis. The supplied source ZIP contains no `.lake` cache.

The runner performs these steps in order and records every exit code and log
hash:

1. `lake build PaperIV PaperIV.Audit PaperIV.ConeAudit BoundedCliqueGap.AxiomCheck`;
2. `lake env lean PaperIV/Audit.lean`;
3. `lake env lean PaperIV/ConeAudit.lean`;
4. `lake env lean` on `recorded_lean_audits/SupplementAudit.lean`;
5. `lake env lean BoundedCliqueGap/AxiomCheck.lean`;
6. `lake env lean` on `PublicContracts.lean`.

The runner checks every frozen source hash before and after execution.
`PublicContracts.lean` imports the aggregate and explicitly types the
all-orders additive theorem, the all-orders linear theorem and the sharp
eventual theorem, without an extra analytic or LP premise. It also prints the
theorem definitions and the partition, chordality and target definitions.

Building an aggregate is not the same as running a separate audit target.
The command above deliberately lists the roots. The supplementary and bounded
library results have their own compatible audit closures; their counts are
not added to the main theorem count as though all declarations were distinct.

The supplementary refresh additionally builds
`ThreeRegime.CompleteStateAllOrders` and `FarExploration.CleanupRigidVerdict`
explicitly, then reruns their audit. This prevents inherited `.olean` files
from being accepted without Lake validating that supplementary source closure.
Its authoritative results are in `author_build_evidence/SUPPLEMENT_REFRESH.json`.

## Nature of the included run

The author run uses copied project build artifacts and shared pinned package
caches, followed by Lake's dependency validation and fresh audit commands.
This avoids downloading another copy of Mathlib. It is **cache-assisted**, not
a clean-room or independent build. The cache is excluded from Git and the
source freeze. Warnings about unused section variables are retained, not
silenced or reported as proof failures.

Re-running the scripts updates evidence files locally. Such a run is a new
audit, not the original sealed evidence. Preserve the repository checkout or
use a separate copy if you wish to compare runs.

## Manuscripts

The manuscript PDFs and TeX are unchanged reviewed v0.8 artifacts, not PDFs
rebuilt from a different source. Logs are in `manuscript_build_logs/`; rendered
QA and its PDF hash binding are in `manuscript_qa/es/` and `manuscript_qa/en/`.
They contain 41 and 40 pages respectively. The differing page counts are
typographical; equations, identifiers and numbered objects match.

To compile either final TeX, keep its figure directory alongside it, use
XeLaTeX (or Tectonic) and compile twice. The series-style templates are in
`templates/`. No alteration of the mathematical Markdown is required.

## Verification boundary

Internal checks verify source integrity, emitted theorem contracts, allowed
axiom sets, the recorded namespace veto and artifact consistency. They do not
constitute a new line-by-line mathematical rederivation, a literature-priority
review, or an independent source-provenance audit.
