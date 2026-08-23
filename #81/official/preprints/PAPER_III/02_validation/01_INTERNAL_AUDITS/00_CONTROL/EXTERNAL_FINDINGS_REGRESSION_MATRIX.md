# Paper III v1.3 — regression against the preceding external audits

**Internal verdict:** `PASS`  
**Boundary:** author-side regression, not an independent external closure

| External item | v1.3 disposition | Internal evidence | External residual |
|---|---|---|---|
| `EXT-PIII-M-001` stale v1.1 integrity baseline | `CLOSED` | v1.3 has no inherited stale baseline; all current sidecars/manifests verify | none on package provenance |
| `EXT-P3-J-001` overbroad “resolves the split case” wording | `CLOSED` | EN/ES now say that the paper determines the sharp quadratic coefficient and establishes the `n^2/6+O(n)` scale | auditor confirms wording in rendered target |
| `EXT-P3-L-001` `A_{2,J}` notation and combined citations | `CLOSED` | `A_{2J}` is uniform; `[3,8]` and `[11,17]` each occur twice in both languages and PDFs were regenerated | auditor confirms semantic/rendered synchronization |
| `EXT-P3-I-001` ten references not retrieved | `CLOSED_INTERNAL_METADATA_CHECK` | all 17 entries are resolved in the internal citation ledger against publisher, DOI, arXiv, EuDML, primary scan, or package source | independent citation and novelty review remains external |
| `EXT-P3-K-001` bounded novelty search | `OPEN_EXTERNAL_GATE`, non-blocking internally | novelty wording is explicitly corpus-bounded; full chordal problem remains distinguished | specialist/recent-work review |
| `EXT-P3-G0-001` frozen axiom file labelled v1.1 | `CLOSED` | no `FreezeAxioms*.lean` file contains `draft v1.1` or `v1.1` | auditor confirms archive bytes |
| `EXT-P3-H-001` two archived comparison-route axioms | `DISCLOSED_NONDEFECT` | both modules are unimported and absent from all canonical footprints; exact limitation is stated | independent dependency-closure check |
| `EXT-P3-C1-001` missing graph/Yuster bridge | `CLOSED_BY_V1.3_TARGET` | four two-sided canonical declarations compile and have foundational-only footprints | compare with auditor's independently constructed bridge |
| `K-EPS` | `PASS_INTERNAL_FORMAL_COVERAGE` | AX1 closure surfaces exist, compile, and are explicitly queried; fresh exact regression evidence remains consistent | independent full epsilon-ledger rederivation |
| `K-CORRIDOR` | `PASS_INTERNAL_FORMAL_COVERAGE` | Section 5–7 surfaces are explicitly queried; fresh exact ILP and corridor checks pass | independent parity/boundary rederivation |
| `K-SPARSE` | `PASS_INTERNAL_FORMAL_COVERAGE` | Section 8 and AX2 discharge surfaces are explicitly queried with foundational footprints | independent deletion/divisibility/threshold rederivation |
| `K-COVER` | `PASS_INTERNAL_FORMAL_COVERAGE` | low/mid/eventual surfaces are explicitly queried and included in the successful target | independent exhaustiveness check |
| `K-GLOBAL` | `PASS_INTERNAL_FORMAL_COVERAGE` | global induction and final theorem surfaces are explicitly queried and foundational-only | independent eventual-to-all-orders rederivation |

The five `K-*` rows pass the internal standard because this audit reviews the sealed build,
formal surfaces, axiom records, and fresh bounded mathematical regressions. They are not
reported as independently rederived. That distinction is a mandatory instruction for the
residual external audit.
