# R0 -- package correction and anchors

**Verdict:** `PASS`

The package-fix checker passed 17 of 17 controls. It verifies the six
publication artifacts, Lean archive, prior internal-audit archive and previous
external report against frozen SHA-256 anchors. Both integrity sidecars are
LF-only and every entry resolves and matches.

`EXT-PII-M-001` is corrected internally: no stale `Pending for v1.1` text or
missing v1.1 sidecar path remains; the v1.1 to v1.2 semantic diff is explicit;
the residual matrix preserves the nonblocking citation-access NOTE. Package
hygiene found no temporary directory, compiler residue, zero-byte file or
dollar-sign filename.

The target inventory excludes all external-audit output and this residual run.
Its canonical manifest algorithm is published verbatim in `results/summary.json`
so an external auditor can reproduce the aggregate.
