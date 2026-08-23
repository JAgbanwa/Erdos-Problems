# G0 TARGET — audit record

**Verdict:** `PASS`.

All six publication artifacts exist and their LF-only sidecar verifies. The 707-entry source
manifest and 742-entry freeze package manifest verify. The formal ZIP has SHA-256
`2eb0ff20a9dae6610a46026355374570d5afdfea89837ea7f9dd29da10b9d300`, passes ZIP CRC,
and contains 743 entries. No stale v1.1 integrity baseline is carried into this target.

Primary machine evidence: `results/internal_audit_static.json`.
