# Paper III — Incremental ledger v0.9.1 → v0.9.2 formalization-release draft

**Date:** July 21, 2026  
**Release state:** internal draft; not publicly released  
**Source manuscript:** `PAPER_III_split_lineal_v0.9.1.md`  
**Output manuscript:** `PAPER_III_split_lineal_v0.9.2_formalization_draft.md`  
**Input SHA-256:** `45ece0d8a8139b3714c49582d3dcea976c290a8c1fd0d557d0d205ef5fdb500d`  
**Output SHA-256:** `88811a94c27e1de5056467627e1c53bfa8e48ae6b2bf0e255b8a38fa422c8b2d`

## 1. Semantic-lock certification

No theorem, lemma, proposition, corollary formula, definition, hypothesis, quantifier, constant, asymptotic order, displayed identity, proof step, numerical result, or dependency in the mathematical core was changed.

The protected mathematical core remains:

- Sections §2–§9;
- Proposition 10.1 and its constants;
- Appendices A–D;
- Theorem 1.1 and Corollary 1.2;
- Theorem 3.1, Lemma 4.1, Theorem 4.2;
- Lemmas 5.1, 5.2, 6.1, and 7.1;
- the sparse-regime construction and the final regime assembly.

This update is editorial and project-control only.

## 2. Changes applied

| ID | Location | Class | Change | Semantic risk | Status |
|---|---|---|---|---|---|
| V92-01 | Header | JOURNAL_STYLE | Version advanced to v0.9.2 formalization-release draft; v1.0 remains reserved for public release. | none | applied |
| V92-02 | Header status | CLARITY | Replaced “formalization planned” with the verified current state: full DAG builds, eight localized obligations remain, and AX1/AX2 are the only intended mathematical axioms. | low; status only | applied |
| V92-03 | §11.5 | CLARITY | Recast the companion chordal program as an intended interface rather than a completed reduction. | none; prevents forward overclaim | applied |
| V92-04 | §11.6 | STRUCTURAL_FORM | Replaced the prospective verification paragraph with a current Layer X/Layer E report and the exact release gate. | none; project metadata only | applied |
| V92-05 | §11.6 | CLARITY | Unified the audit count as 46,390 exact/LP + 91 ILP = 46,481 checks. | none | applied |
| V92-06 | §13 | STRUCTURAL_FORM | Updated the reproducibility tree to the current manuscript, authoritative ledger, incremental ledger, Lean package, and pending release artifacts. | none | applied |

## 3. Current Lean state recorded by this draft

The project compiles as a complete dependency graph under Lean 4 / Mathlib v4.28.0.

### Authorized external layer

- `AX1`: Haxell–Rödl/Yuster fractional-to-integral asymptotic packing theorem.
- `AX2`: Dross plus Barber–Kühn–Lo–Osthus dense triangle-decomposition input.

No additional mathematical axiom is authorized.

### Open Layer E leaves

| # | Lean obligation | Mathematical location | Downstream nodes |
|---:|---|---|---|
| 1 | `lp_dual_bound_small` | Theorem 3.1, degenerate cases `d<3 ∨ r<3` | E-3.1, E-4.1, E-4.2, E-4.3, Cor. 10.4 |
| 2 | `E_5_1` | Lemma 5.1 | short corridor, Prop. 10.1, Cor. 12.2 |
| 3 | `cor_5_3` | consequence (5.3) | Prop. 10.1 low corridor, Cor. 12.2 |
| 4 | `E_5_2` | Lemma 5.2 | high-dispersion corridor |
| 5 | `Prop_10_1_mid` | Proposition 10.1, middle corridor | effective-corridor release |
| 6 | `saturated_vertex_matching` | Appendix D | E-D.3 and Section 7 list coloring |
| 7 | `reserved_gain_packing_bound` | Section 7.2, three packing families | E-7.1 and low-dispersion corridor |
| 8 | `E_8_sparse_packing_estimate` | Section 8, sparse regime | E-8 and Theorem 1.1 |

Theorem 1.1 and Corollary 1.2 are **assembly-complete but transitively open** until these leaves close.

## 4. Addenda status

The v0.9.1 addenda remain downstream and do not alter the core DAG:

- Corollary 10.4 repackages Theorem 3.1.
- Corollary 10.4b specializes Theorem 1.1 to threshold graphs.
- Corollary 12.2 packages the effective corridor as an algorithmic consequence.
- The cloning, stability, and companion-program remarks are expository only.

## 5. Release gate for v1.0

Before replacing this draft by the first public preprint, require:

1. zero `sorry` in Layer E;
2. clean full build;
3. final axiom report showing exactly AX1 and AX2 as project-level mathematical axioms;
4. no `admit`, `native_decide`, `unsafe`, or undeclared axiom;
5. frozen Lean commit, toolchain, Lake manifest, and build log;
6. semantic diff confirming no change to protected mathematics;
7. synchronized manuscript, ledger, theorem names, and repository paths;
8. SHA-256 manifest for the release package.

## 6. Prepared final-status replacement

After the release gate is satisfied, replace the working status by a statement of the following form, filling the bracketed fields from the frozen build:

> Theorem 1.1 and the elementary core are formally verified in Lean 4 with Mathlib v4.28.0 at commit `[COMMIT]`. The development is `sorry`-free. Its project-level mathematical assumptions are exactly the two named external asymptotic inputs AX1 and AX2; the axiom report otherwise contains only Lean's standard foundational axioms. The complete source, toolchain, manifest, build log, and axiom report are included in the release repository.

This prepared wording is not yet asserted in the draft manuscript.

## 7. Semantic integrity report

```text
Input hash:  45ece0d8a8139b3714c49582d3dcea976c290a8c1fd0d557d0d205ef5fdb500d
Output hash: 88811a94c27e1de5056467627e1c53bfa8e48ae6b2bf0e255b8a38fa422c8b2d
Protected elements changed: none
Quantifier changes: none
Assumption changes: none
Constant changes: none
Asymptotic-order changes: none
Proof-dependency changes: none
Citation-scope changes: none
Novelty-scope changes: one forward-looking paragraph narrowed to avoid overclaim
Unresolved content queries: none for this editorial update
Verdict: EDITORIALLY_READY_WITH_FORMALIZATION_GATE
```
