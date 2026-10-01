# Gate E1 report — run_v1.21_r1 (Paper IV v1.21)

Verdict: **PASS (1 MINOR)**. Evidence: `20_EVIDENCE/E1/`.

---

## E1 — Claims revalidation (v1.21)

Basis: the auditor's diff v1.2 → v1.21 (EN and ES), the E1 claim map of run_v1.2_r1 (reused for unchanged
statements), and the E6 automated parity results.

- **Statements, hypotheses, constants, tags and Lean blocks:** unchanged. Every theorem block (A, B, C, C′,
  3.1, 3.5, 5.0, 6.1, 6.1a, 6.2, 6.3, 6.3a, 6.4, 6.5, 6.6, D.1–D.3, F.3a/b, G.1) is identical. The display
  formulas are identical except for the declared subscripts N_far (formerly N_lej, N_lejano), e_cross,
  x^clean and E_covered, plus the defined abbreviation mis_c. These renamings are semantically neutral: each
  denotes the same object as before, and N_far was already the name used in (C.4) and (F.1). The run_v1.2_r1
  claim map therefore stands.
- **Abstract / Theorem A remark:** now cites [5] and [15, Cor. 1.2] for the all-orders unrestricted bound.
  Accurate.
- **Front-matter status and §7 / A.1 status paragraphs:** they say the v1.2 external run was INCONCLUSIVE
  overall with formal reproduction PASS (607 modules, 19 targets, 50-module annex, 607 byte-identical
  objects), and that v1.21 needs its own review. Accurate per run_v1.2_r1.
- **New expository passages** (C.2, C.3, E.1): they introduce no new claim beyond the derivations reviewed
  in E2.
- **A.2 scope paragraph:** "the remaining tower iteration is a symbolic comparison with the recurrence in
  §6.3". §6.3 contains no recurrence, only T and h, so this cross-reference is inaccurate (part of A2-4 /
  X-05r).
- **NEW-01 (MINOR):** ordinary words have been set as code identifiers in headings, apparently by the
  monospacing pass:
  - EN §5.1 heading "`Regularization` on the original graph" and the A.2 table row "`Regularization` mass,
    degree, …". In v1.2 both were plain words.
  - ES Lemma 3.2 heading "`Nibble` de rango acotado…", whereas the EN heading says "Bounded-rank nibble"
    in plain text.

  The headings then read as if they referred to the Lean module `PaperIV.Regularization` or the library
  `Nibble`. It also creates an EN/ES heading inconsistency. Conversely, "bounded gain function from Model"
  lost the backticks it had on `Model` in v1.2 (§7.2), although it refers to the Lean namespace `Model`
  (OBSERVATION).

**E1 verdict: PASS with one MINOR finding (NEW-01).** No semantic change to any claim.
