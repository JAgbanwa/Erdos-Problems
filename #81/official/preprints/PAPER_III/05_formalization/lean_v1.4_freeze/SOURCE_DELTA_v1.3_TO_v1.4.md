# Source delta: audited v1.3 freeze to v1.4 build candidate

The v1.4 build candidate contains the same 704 Lean files as the audited v1.3
freeze. Hash comparison reports exactly one changed `.lean` file:
`PaperIII.lean`.

That file changes only:

- the obsolete scaffold docstring;
- an explicit import of `PaperIII.Theorem_1_1_Final`;
- an explicit import of `PaperIII.PublicAPI`.

No theorem statement, definition or proof body is edited. `lake-manifest.json`
and `lean-toolchain` are byte-identical to v1.3. `lakefile.toml` differs only in
the package version (`1.3.0` to `1.4.0`). Candidate metadata is new and records
all v1.4 audit/build gates as pending until evidence exists.

Static import traversal after the correction reports:

```text
Lean source files:                    704
PaperIII aggregate closure:           503 modules
All canonical/query-root closure:     521 modules
PaperIII reaches Theorem_1_1_Final:   yes
PaperIII reaches PublicAPI:           yes
Ax2.PartA.Wlog reachable:             no
Ax2.PartB.Axioms reachable:           no
```

These are source-level checks. The second-machine build and axiom-query logs
remain mandatory before the candidate can be frozen.
