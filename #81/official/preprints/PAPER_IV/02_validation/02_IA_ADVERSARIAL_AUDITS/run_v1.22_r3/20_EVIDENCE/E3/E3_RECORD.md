# E3 — Formal correspondence (r3)

- **Lean.** 615/615 entries; source ZIP equals the manifest; annex has 40 members, CRC OK (E0). No Lean source changed.
- **Code identifiers.** The only new code spans are `run_v1.22_r1` and `run_v1.22_r2`. They are names of audit folders that exist, not Lean declarations, and none was removed (E6).
- **Supplementary static correspondence.** The 13 headers match their literal sources, namespaces and in-scope variables (E1, `E1E3_HEADERS_CHECK.json`). This is static extraction, not new elaboration: no `#check` or kernel replay was run.
- **X-27.** The disclosure is unchanged in §7 (p. 31), Table 9 (EN p. 64 / ES p. 65) and [23]. The AuditorASProbe probe is inherited because the source is identical.
- **History.** run_v1.2_r1 PASS_WITH_FINDINGS (X-27) → v1.21 PASS → r1 PASS → r2 PASS.

**E3 verdict (r3): PASS.** Inherited and revalidated by identity, plus the new static header check.
