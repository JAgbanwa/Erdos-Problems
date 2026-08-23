# Paper I v1.2 claim map

Status: `INTERNAL_AUDIT_PASS`

| Claim ID | Manuscript surface | Formal surface | Required future gate |
|---|---|---|---|
| `P1-FRAC-THM-V1_2` | Main split-graph bound, including the corrected `n^2/6+n/2` form | `PaperI.paperI_main`; `PaperI.Split.paperI_main_sharp` | Statement match, proof-dependency review, boundary falsification |
| `P1-ASSEMBLY-V1_2` | Corrected final assembly | `PaperI.assembly_sharp`; `PaperI.Split.paperI_main_sharp` | Independent algebraic recomputation and assumption trace |
| `P1-DUALITY` | Finite LP/Farkas duality used by the argument | `FiniteLPDuality.covering_packing_duality`; `PaperI.Split.residual_duality`; `Contrib.Submission.covering_packing_duality` | Hypothesis and normalization audit |
| `P1-INTERFACES` | Reusable stability and centered-Tuza interfaces, explicitly separated from premises | `Contrib.lpVal_*`; `Contrib.tuza_split_centered_scalar` | Classification as premise/byproduct and API conformance |

The internal audit bound every test to the manuscript and freeze SHA-256
recorded at audit start. Independent reconstruction remains an external gate.
