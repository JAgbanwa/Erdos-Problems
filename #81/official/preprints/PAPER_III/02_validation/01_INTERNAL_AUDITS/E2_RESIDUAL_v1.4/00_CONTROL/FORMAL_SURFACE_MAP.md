# Mathematical obligation to formal surface map

The mathematical derivations stand on their own.  These surfaces provide the
separate machine-checked reconciliation layer.

| Obligation | Formal surfaces |
|---|---|
| AX1 box allocation | `Nibble.AX1.boxAllocationResidual_holds` |
| AX1 coupled coarse-cell ledger | `Nibble.AX1.blockCoverResidualCoupled_holds`, `Nibble.AX1.ax1_of_boxAllocation`, `Nibble.AX1.ax1Statement_holds` |
| Manuscript AX1 consequence | `PaperIII.AX1_holds`, `PaperIII.E_4_3_of_AX1` |
| one-factor and short corridor | `PaperIII.E_5_1`, `PaperIII.cor_5_3`, `PaperIII.Prop_10_1_low` |
| double-factor and mesoscopic corridor | `PaperIII.E_5_2`, `PaperIII.Prop_10_1_mid` |
| sparse regime | `PaperIII.E_8_clique_packing_of_AX2`, `PaperIII.E_8_of_AX1_AX2`, `PaperIII.AX2_holds` |
| eventual high-degree assembly | `PaperIII.eventual_bound_of_high_degree_of_AX1_AX2` |
| global closure | `PaperIII.global_bound_from_eventual_high_degree`, `PaperIII.Theorem_1_1_of_AX1_AX2`, `PaperIII.Theorem_1_1` |

The eight frozen query files in the v1.4 clean-build kit cover these surfaces.
The second-computer result must still show their allowed foundational axiom
footprints; this E2 residual does not predeclare the build result.

