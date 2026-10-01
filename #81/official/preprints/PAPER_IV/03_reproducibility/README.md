# Reproduction — Paper IV v1.23

## Identity and documentary checks (no Lean build)

Run from the Paper IV directory:

```text
python 04_integrity/verify_publication.py
python 03_reproducibility/verify_logs.py
```

The first verifies the publication manifest, retained audited manuscript hashes,
frozen sources, historical ZIPs and their sidecars, and the relocation map.
The second runs the **unchanged** supplemental log verifier against the
1266 recorded logs. It fails on missing/extra/changed logs and detected errors
or sorry declarations. It is mandatory because the older frozen runners'
text scanner had a documented gap (X-28). Its PASS does not itself prove
mathematical correctness.

To restore the historical relative paths for an audit replay in an empty
directory outside this repository:

```text
python 04_integrity/verify_publication.py --restore-audit-inputs C:/temporary/paper-iv-audit-replay
```

This copies mapped inputs; it never installs dependencies or starts Lean.
Original absolute workstation paths in historical scripts remain provenance,
not portable commands. Inspect a script's inputs before invoking it.

## Formal reproduction

Selected source: [lean_piv-v12-fb459343d234](../05_formalization/lean_piv-v12-fb459343d234/).
Use a separate working copy, Lean 4.28.0 and the exact pinned dependency
revisions in lake-manifest.json. Reuse an existing matching Mathlib/package
cache; do not download a second installation on this workstation. If no
matching cache is available, stop and configure it explicitly. Do not modify
the published source freeze or its manifests.

The source's docs/PUBLICATION_AUDIT.md describes the serial entry point:

```text
python tools/audit_publication.py
```

Run it only from the configured working copy. It executes the 19 targets
listed in FREEZE_SCOPE.json; importing a cached aggregate alone is not the
same check. Maximum one heavy build at a time. After compilation, apply the
supplemental scanner to the new logs with an explicit new inventory; do not
use an inventory for older logs as if it verified a new run.

The separate bounded-gap annex has its own source and recorded 50-module
closure. It is not silently added to the main 607-module count.

## Evidence retained

- build_piv-v12-fb459343d234: original source freeze and build provenance;
- full_rebuild_v12_20260929_r2 and full_rebuild_v12_20260929_resume: fresh
  author compilation segments around the reboot;
- full_rebuild_v12_20260929_seal: consolidated evidence and ZIP;
- build_gap_annex_20260927: historical annex evidence;
- external run_v1.2_r1: the independent execution of the recorded main and
  annex build, inherited by the final editorial audit.

The final external report distinguishes 461 axiom records from 314 printed
axiom outputs and the 18 headline declarations; repeated records are not
distinct theorems. Its final cycle ran no new build or kernel replay.

## Manuscript reproduction

The v1.23 ES/EN manuscripts have an editorial-only delta from the approved r4
inputs. Figures and template are unchanged. Scripts in `editorial_v1.23/`
record preparation, cached local typesetting and checks; adapt executable paths
explicitly before reproduction. No script installs TeX, Mathlib or another cache.
The [v1.23 check record](../02_validation/03_EDITORIAL_CHECKS/v1.23/EDITORIAL_REPORT.md)
binds the final TeX and PDFs to the verification. Any regeneration creates new
artifacts whose hashes and rendered output must be checked again.
The exact [v1.22 publication backup](../02_validation/02_IA_ADVERSARIAL_AUDITS/audit_inputs/published_v1.22/)
and earlier [r4 input backup](../02_validation/02_IA_ADVERSARIAL_AUDITS/audit_inputs/01_manuscript/v1.22_editorial_candidate_r4/)
remain separate from the current manuscripts.
