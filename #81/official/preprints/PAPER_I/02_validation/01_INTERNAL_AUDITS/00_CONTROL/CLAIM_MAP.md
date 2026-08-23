# Paper I v1.3 claim map

Status: `INTERNAL_AUDIT_IN_PROGRESS`

| Claim ID | Manuscript surface | Formal surface | Required future gate |
|---|---|---|---|
| `P1-FRAC-THM-V1_3` | Main split-graph bound `n^2/6+n/2`; theorem statement unchanged from the frozen formal target | `PaperI.paperI_main`; `PaperI.Split.paperI_main_sharp` | Statement match, proof-dependency review, boundary falsification |
| `P1-ASSEMBLY-V1_3` | Final assembly and explicit exposition of the cancellation yielding (4.7) | `PaperI.assembly_sharp`; `PaperI.Split.paperI_main_sharp` | Independent algebraic recomputation and assumption trace |
| `P1-DUALITY` | Finite LP/Farkas duality used by the argument | `FiniteLPDuality.covering_packing_duality`; `PaperI.Split.residual_duality`; `Contrib.Submission.covering_packing_duality` | Hypothesis and normalization audit |
| `P1-INTERFACES` | Reusable stability and centered-Tuza interfaces, explicitly separated from premises | `Contrib.lpVal_*`; `Contrib.tuza_split_centered_scalar` | Classification as premise/byproduct and API conformance |

Every test is bound to the v1.3 manuscript hashes and unchanged formal archive
SHA-256 recorded at audit start. The external clean-room reconstruction already
passed for the exact archive; residual manuscript review remains external.
