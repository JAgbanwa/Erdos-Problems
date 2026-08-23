# Lean/build findings closure matrix

Source report: external adversarial audit of Paper III v1.3, SHA-256
`4b0c6d895155974e7fface2b773d64b8ae0bee796f9da405981a3c79dcdae2c8`.

| Finding | v1.4 correction | Required evidence from the second machine |
|---|---|---|
| `EXT-V13-001` | `PaperIII.lean` explicitly imports `PaperIII.Theorem_1_1_Final` and `PaperIII.PublicAPI` | clean `lake build PaperIII` exit 0; both object files produced; root import-closure assertion PASS |
| `EXT-V13-004` | the v1.4 record is required to be a clean build, not an incremental replay presented as clean | pre-cache and pre-build listings; absence of project `.lake/build`; duration, jobs and exit code recorded |
| `EXT-V13-006` | the obsolete scaffold docstring is replaced by the public-root contract | static source assertion and source hash |
| `EXT-V13-007` | the protocol builds the public root, the seven query roots, and then executes the eight query files | command logs and exit records for every stage |
| archived comparison axioms | no canonical root may reach `Ax2.PartA.Wlog` or `Ax2.PartB.Axioms` | independent source import-closure result plus all 42 axiom footprints |
| graph/Yuster bridge | retain and query all seven canonical bridge surfaces | `FreezeAxiomsCanonical.lean` exit 0 and foundational-only footprints |
| AX1 tolerances | retain the AX1 closure surfaces used by the canonical theorem | `FreezeAxiomsAX1.lean` and `FreezeAxiomsAX1Closure.lean` exit 0 |
| corridor/sparse/global formal surfaces | retain the theorem-assembly audit closure | `FreezeAxiomsAuditClosure.lean` exit 0 |
| public byproducts and obstruction certificates | keep them available without adding them as project axioms | byproduct and obstruction query logs exit 0 |

`EXT-V13-003` is a release-metadata correction rather than a Lean compilation
obligation. Candidate metadata records both audits as pending for v1.4. After
the second-machine build and the new internal audit, final freeze metadata must
record the actual results before the external residual audit package is sealed.
