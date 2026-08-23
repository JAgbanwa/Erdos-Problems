# PAPER_I_EXT_AUDIT_2026-07-10 — External Adversarial Audit of Paper I

Independent external audit (adversarial-math-audit protocol) of Theorem 1.1 of
*Affine Profile Reduction for Fractional Triangle Packings in Split Graphs*:

> For every split graph `G` on `n` vertices, `|E(G)| − 2·ν₃*(G) ≤ n²/6 + n`.

**Verdict: PASS** (intermediate AI-assurance tier — not human peer review).

## Contents

- `FINAL_AUDIT_REPORT.md` / `.pdf` — executive verdict, gate table (A–J), computational
  audit, falsification log, coverage declaration, recommendation.
- `ENVIRONMENT.md` / `.pdf` — independent environment + reproducibility record.
- `scripts/` — four self-contained scripts, each with its `.py`, `results.txt`, English
  `report.md`/`.pdf`, a `.zip` of the folder, and `.zip.sha256`:
  - `01_algebraic_identities` — exact symbolic check of every ledger identity (Gate E).
  - `02_orbit_lp_and_reduction` — orbit LP = closed form, orbit symmetrization lossless,
    affine reduction + uniform bound (Gates B, C).
  - `03_split_falsification` — `ν₃*` LP falsification on 622 split graphs + extremal
    tightness (Gate F).
  - `04_lean_certificate` — independent Lean rebuild + `#print axioms` + SHA + statement
    match (Gate H); includes `independent_build.log`.
- `_lib/` — `pdfgen.py` (PDF renderer), `package.py` (packager).
- `SHA256_MANIFEST.txt` — digests of all package files.

## Result summary

| Gate | Result |
|---|---|
| A definitions consistent | VERIFIED |
| B affine reduction | VERIFIED |
| C orbit symmetrization + finite LP | VERIFIED |
| D finite LP duality in-hypotheses | VERIFIED |
| E deficit identity + R(p,q) constant | VERIFIED (9/9 identities exact) |
| F conversion to n + tightness | VERIFIED (0/622 violations; extremal attains n²/6+n/6) |
| G assembly, no circularity | VERIFIED |
| H Lean certificate | VERIFIED (indep. build 8027 jobs, axioms clean, SHA match) |
| I citations | VERIFIED_WITH_RESIDUAL_RISK (duality standard + Lean-derived) |
| J scope / no over-claim | VERIFIED |

No counterexample, circularity, or over-claim found. Human/journal peer review remains
the appropriate next tier.

## Reproduce

```
cd scripts/01_algebraic_identities && python 01_algebraic_identities.py
cd ../02_orbit_lp_and_reduction   && python 02_orbit_lp_and_reduction.py
cd ../03_split_falsification      && python 03_split_falsification.py
# Gate H (independent Lean build): copy 05_formalization/lean sources to a SHORT path,
#   enable git core.longpaths, `lake exe cache get`, `lake build PaperI.PaperI_Statement`,
#   then: cd scripts/04_lean_certificate && python 04_lean_certificate.py
python _lib/package.py            # render PDFs, zip + SHA, manifest
```
Requires Python 3.14 (sympy, scipy/HiGHS, numpy, reportlab); Lean v4.28.0