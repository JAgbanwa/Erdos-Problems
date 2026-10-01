# Single entry point for the Paper IV publication checks

From the project directory, with the existing pinned Mathlib cache available:

```text
python tools/audit_publication.py
```

This reads all 19 targets from FREEZE_SCOPE.json and runs them sequentially.
Requested targets execute afresh, while unchanged dependencies reuse their
hash-validated cache. No second Mathlib is installed and no cache is cleared.
Do not run a second audit concurrently. The run directory is timestamped;
an explicit `--run-dir` must name a directory that does not already exist.

Success requires AUDIT_SUMMARY.json to report PASS, all target exit codes to
be zero, current source/configuration hashes to match, and the printed axioms
to be subsets of propext, Classical.choice, Quot.sound. The wrapper preserves
individual logs and FAIL evidence. It does not silently reduce the target list
to the subset mentioned in the manuscript's narrative.

An aggregate Lean import alone is not used as the audit entry point: importing
cached audit modules need not rerun their commands or reprint their evidence.
PaperIV remains the mathematical aggregate; ReleaseExportCheck imports it alone
and checks the 224 publication exports. The audit command does not freeze or
publish anything, and is not an internal or external manuscript audit.

## Retirement for this cut

Exactly five unused local modules were retired: E35L.Far, E35L.Gate,
E35L.Poly, E35L.Sched and FDCheck.TowerAudit. The dependency closure of all
19 targets comprises the other 607 modules. The selected E35 results replace
these older tower estimates. Other modules were not removed merely because
their names describe a historical route: they remain in the selected import
closure or in an explicit audit.

The retired files are recoverable in the historical source freeze and in
C:/Users/jtraverso/e81p4/retired_v12_20260929/. The historical freeze and its
audits were not edited. The E35L library stanza was removed from lakefile.toml.
