# Paper III v1.3 claim map

| Claim | Manuscript surface | Formal surface | Internal status |
|---|---|---|---|
| unconditional integral bound | Theorem 1.1 | `PaperIII.Theorem_1_1` | `PASS` |
| clique-partition corollary | Corollary 1.2 | `PaperIII.Corollary_1_2` | `PASS` |
| AX1 discharge | Sections 2, 4, 9, 11.6 | `PaperIII.AX1_holds`; `Nibble.AX1.ax1Statement_holds` | `PASS` |
| AX2 discharge | Sections 2, 8, 9, 11.6 | `PaperIII.AX2_holds`; `BKLO.triangle_decomposition_dense` | `PASS` |
| canonical packing correspondence | Sections 2.2, 11.6, 13 | `isFracPacking_iff_yuster`; `nu3Star_eq_yuster`; `tau3Star_eq_nu3Star`; `AX1Assumption_iff_packing_form` | `PASS` |
| complete-split sharpness | Section 10.2 | `PaperIII.Corollary_1_2_sharp` and packaged byproducts | `PASS` |
| five prior external kill-switch surfaces | Sections 4–9 | declarations listed in `EXTERNAL_FINDINGS_REGRESSION_MATRIX.md` | `PASS_INTERNAL`; external rederivation open |

Every row is bound to the v1.3 manuscript hashes and the formal archive SHA-256 recorded in
the final internal-audit report.
