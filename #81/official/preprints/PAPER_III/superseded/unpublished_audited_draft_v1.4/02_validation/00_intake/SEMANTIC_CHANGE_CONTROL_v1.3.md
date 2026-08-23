# Paper III v1.3 semantic change control

Date: 2026-08-22  
Verdict: PASS for the authorized v1.3 initialization changes  
Editorial state: `EDITORIAL_DRAFT_WITH_OPEN_GATES`

## Baselines and outputs

| Artifact | SHA-256 |
|---|---|
| English v1.2 intake baseline | `d4ca630d0966928b5b4d71ba6afcd34043fc33507757e8a817e3f42f245c80a1` |
| English v1.3 Markdown | `4e8f4927a834a924eb0f8e405457599d828d3816c61d24f7c25bb0cbefd04f90` |
| Spanish v1.2 source baseline | `6f39baf2e5cbf551993932aeac2ed4ce82f93a5407b0117bf297180d777669ca` |
| Spanish v1.3 Markdown | `dd3c77a236da9370747279da354c049d8717601caaf6f80f4f09e2ea69b048b9` |

## Authorized changes

- version, date, and release-state metadata;
- Section 11.6 formalization description and status table;
- Section 13 reproducibility record and open-gate language;
- English/Spanish synchronized description of the canonical packing interface;
- no claim that a v1.3 freeze, archive hash, consolidated build, or internal audit
  already exists.

## Protected-content checks

| Check | English | Spanish |
|---|---:|---:|
| heading count, baseline → v1.3 | 144 → 144 | 144 → 144 |
| theorem-like heading count, baseline → v1.3 | 42 → 42 | 45 → 45 |
| long duplicate paragraph groups in v1.3 | 0 | 0 |
| stale v1.2/archive/job-count references in current manuscript | 0 | 0 |

The table-row count changes only in the formalization-status and reproducibility tables,
where additional candidate gates are listed. Inspection of the zero-context semantic
diff found changes only in the front-matter status, Section 11.6, and Section 13.

No theorem statement, hypothesis, equation, constant, proof branch, citation, novelty
claim, asymptotic conclusion, or mathematical dependency was changed. This report does
not validate the future TeX/PDF render or the consolidated Lean build; those remain
separate gates.
