# Paper II v1.2 claim map

Status: `INTERNAL_AUDIT_PASS`

| Claim ID | Manuscript surface | Formal surface | Required future gate |
|---|---|---|---|
| `P2-MAIN-V1_2` | Exact chordal maximum and attainment | `PaperII.theorem_1_2` | Statement/hypothesis match, extremal search and proof-dependency review |
| `P2-EXTREMIZER` | Unique/tied maximizers, level sets and copy defects | `PaperII.Fsat_argmax_unique`; `Fsat_argmax_tie`; `level_set_iff`; `copyDefect_nonneg`; `copyGamma_ge_half_copyDefect` | Independent integer optimization and boundary falsification |
| `P2-ASYM-COR` | Post-freeze asymptotic and modular-arithmetic corollaries | `phiTau_max_sandwich`; `odd_sq_emod_24`; `phiTau_max_closed`; `phiTau_max_le_paperI_bound` | Consolidated build, algebraic recomputation and semantic match |
| `P2-FORMAL-CONFORMANCE` | Full v1.2 Lean surface, including reusable chordal/geodesic components | `PaperII`; `Contrib.Submission.Chordal`; `Contrib.Submission.GeodesicChordless` | Independent rebuild and theorem-level axiom audit |

The internal audit bound every test to the manuscript and freeze SHA-256
recorded at audit start. Independent reconstruction remains an external gate.
