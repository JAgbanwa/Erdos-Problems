# Paper III v1.3 internal audit final report

> **Overall verdict:** `PASS`  
> **Audit class:** internal / author-side / not independent  
> **Protocol:** `INTERNAL_AUDIT_STANDARD_v1.3`  
> **Date:** 2026-08-22  
> **Release position:** candidate for Paper III's first formal public release  
> **Lean execution during audit:** recorded consolidated build reviewed; the full build was not rerun

## Frozen target

| Item | Value |
|---|---|
| English Markdown SHA-256 | `ef410252009f55aa1e0ccbec1873f8d838cf4f9b54e7478befe71459f68440ca` |
| English TeX SHA-256 | `f08a8ecc2fb04074b5eaa54ad64b55f2f26e3e36c706382429a11c17f7a21f2b` |
| English PDF SHA-256 | `69594bb330543e101f69dace165545af863a38f733fb10cdacf56ecfb409a3f4` |
| Spanish Markdown SHA-256 | `212d03d71300a6c9b1f7a2c09c15a157c386de4b1b74e0c0282713304d360b12` |
| Spanish TeX SHA-256 | `c45786dad1485eb55e526fa8b165333e7b2ed5e907480ae0c88db8a1f27ae75e` |
| Spanish PDF SHA-256 | `58a7e37e3e2ab462de00ca1cc042d0538e71b9422f1d31070928f5c5da236883` |
| Formal archive | `PAPER_III_lean_v1.3_freeze.zip` |
| Formal archive SHA-256 | `2eb0ff20a9dae6610a46026355374570d5afdfea89837ea7f9dd29da10b9d300` |
| Toolchain | Lean `4.28.0`; Mathlib `v4.28.0` at `8f9d9cff6bd728b17a24e163c9402775d9e6a365` |
| Recorded build | exit 0; `Build completed successfully (8719 jobs)` |
| Recorded axiom footprint | exactly `[propext, Classical.choice, Quot.sound]` on every queried canonical surface |

The archive contains 704 Lean source files, a 707-entry source manifest, a 742-entry package manifest, and 743 ZIP entries. All manifests, the archive hash, and ZIP CRC verification passed.

## Gate results

| Gate | Verdict | Principal evidence |
|---|---|---|
| G0 Target and integrity | `PASS` | Six publication artifacts, LF-only sidecar, manifests, archive hash and CRC verified |
| G1 Claims | `PASS` | Main bound, sharpness roles, three regimes and exact scope aligned in EN/ES |
| G2 Mathematics | `PASS` | 12/12 identities; 351/351 LP and exact-cover cases; 78,384/78,384 margins; 372 ILPs; 180/180 packing and 180/180 corridor cases |
| G3 Formal conformance | `PASS` | Canonical graph/Yuster bridges, AX1/AX2 discharges, global induction and final theorem explicitly covered |
| G4 Recorded build | `PASS_RECORDED_BUILD` | 8,719-job build and eight axiom-query runs reviewed; no full rebuild during this internal audit |
| G5 Bilingual and semantic consistency | `PASS` | 31/31 consistency checks; 144/144 headings; protected notation and citations synchronized |
| G6 TeX/PDF | `PASS` | EN 45 / ES 46 pages; fonts embedded; all 91 pages visually inspected; no TeX residue |
| G7 Prior art | `PASS_INTERNAL_EXTERNAL_GATE_OPEN` | Claims are corpus-bounded and distinguish the still-open full chordal problem; independent novelty review remains external |
| G8 Package hygiene | `PASS` | No temporary render tree, compiled Lean artifacts, reparse entries or dependency on earlier manuscript versions |

The executable audit suite reports **133/133 checks passed** and every gate G0--G8 as `PASS`.

## Regression against the preceding external audit

The following formerly inconclusive or defective areas are internally closed in the v1.3 target:

- The overbroad wording about resolving the split case was replaced by the precise claim that the sharp quadratic coefficient is determined and the `n^2/6+O(n)` scale is established.
- `A_{2J}` notation and the combined citations `[3,8]` and `[11,17]` are synchronized in both languages and rendered outputs.
- The current freeze has no stale v1.1 axiom-file label.
- Canonical two-sided bridges now relate the paper's fractional-packing model to the Yuster-style model: `isFracPacking_iff_yuster`, `nu3Star_eq_yuster`, `tau3Star_eq_nu3Star`, and `AX1Assumption_iff_packing_form`.
- AX1 and AX2 closure surfaces and the five earlier kill-switch areas (`K-EPS`, `K-CORRIDOR`, `K-SPARSE`, `K-COVER`, `K-GLOBAL`) are present in the frozen source, included in the successful build record, and explicitly covered by foundational-only axiom queries.
- Two legacy comparison-route project axioms remain archived but unimported; they are disclosed and absent from every canonical theorem and release-interface footprint.

This is internal formal-coverage closure, not independent mathematical rederivation. The external auditor must still independently check the bridge semantics, quantitative tolerances, hypergraph-to-graph passage, Sections 4--9 analytic core, citations, novelty, and dependency closure.

## Overall verdict

`PASS`. All nine blocking internal gates pass, with no unresolved internal blocker or major finding. The package is ready to request a new external adversarial audit. External reproduction, independent rederivation, specialist prior-art review, peer review, public tagging, and publication approval remain open.
