# Paper III — INTERNAL AUDIT

Independent computational / symbolic audit of the load-bearing finite and closed-form
claims of *Linear-Error Clique Partitions of Split Graphs* (Erdős #81, Paper III).

> **Final consolidated report:** [`AUDIT_FINAL_REPORT.pdf`](AUDIT_FINAL_REPORT.pdf) /
> [`AUDIT_FINAL_REPORT.md`](AUDIT_FINAL_REPORT.md) — overall verdict, per-block results,
> methodology, and hashes in one document. **OVERALL VERDICT: ALL AUDITED BLOCKS PASS.**

This audit is **independent** of both the manuscript's own audit scripts and of the Lean 4
/ Mathlib formalization: every claim below is re-derived from scratch here. It complements
the machine-checked formalization (which certifies the full logical chain relative to the
two named external axioms AX1, AX2); this audit certifies the numeric/symbolic facts by
exact arithmetic and by exact/floating linear & integer programming.

## Methodology (shared)
- **Exact rational arithmetic** (`fractions.Fraction`) for all numeric grid checks — no
  floating point in the closed-form comparisons.
- **Symbolic proof** (SymPy) for algebraic identities: `simplify(LHS − RHS) = 0`, exact
  rational (in)equalities, or explicit sum-of-squares certificates.
- **Direct LP** (SciPy HiGHS) for fractional triangle-packing optima on the actual graphs.
- **Exact ILP** (PuLP + CBC) for integral triangle-packing numbers `ν₃(G)`.
- Every script **writes its full log** to `results/…` and returns a nonzero exit code on
  any failure.

## Blocks

| Block | Scope (paper node) | Method | Result |
|-------|--------------------|--------|--------|
| [01](block01_algebraic_identities/) | Algebraic identities (T-identity, (9.12), (9.19), (9.20), δ≥7/8, threshold 2304, μ, (4.5) forms) | SymPy exact symbolic | **12/12 PASS** |
| [02](block02_common_profile_LP/) | ν₃*(H(p,q,d)) = F(p,q,d) — Theorem 3.1 / E-3.1 | Direct triangle LP (HiGHS) vs closed form | **351/351 PASS** |
| [03](block03_unified_margin/) | Unified margin (4.5) — Theorem 4.2 / E-4.2 | Exact-rational grid (78,384 cases) | **78,384/78,384 PASS** |
| [04](block04_corridor_ILP/) | E-5.1 & Corollary 5.3 (corridor) | Exact ILP for ν₃ (CBC) + rational bounds | **PASS** (E-5.1 180/180, Cor 5.3 180/180, 372 instances) |

Each block folder contains: `README.md`, the `verify_*.py` script, `results/…` output
file(s), and a PDF certificate `certificate_blockNN.pdf` (English). Each block is also
packaged as `blockNN_*.zip` with its `.zip.sha256`. See `SHA256_MANIFEST.txt` for all
hashes.

## Layout
```
INTERNAL_AUDIT/
  README.md                     ← this file
  SHA256_MANIFEST.txt           ← verdicts + SHA-256 of every results file and block zip
  build_audit_artifacts.py      ← regenerates certificates, zips, and the manifest
  common/
    audit_formulas.py           ← shared exact-rational F, μ, C_α, T, r_p
    make_certificate.py         ← PDF certificate generator (reportlab)
  block01_algebraic_identities/ … block04_corridor_ILP/
  blockNN_*.zip  +  blockNN_*.zip.sha256
```

## Reproduce everything
```
python block01_algebraic_identities/verify_identities.py
python block02_common_profile_LP/verify_common_profile_LP.py
python block03_unified_margin/verify_margin.py
python block04_corridor_ILP/verify_corridor_ILP.py
python build_audit_artifacts.py     # certificates + zips + SHA manifest
```

## Scope & honesty
This audit covers the **finite / closed-form** perimeter (Layers verifiable by exact
computation). It does **not** attempt to verify the two external asymptotic inputs (AX1
Haxell–Rödl/Yuster, AX2 Dross+BKLO) — those are the paper's declared axioms and are out of
scope for computational audit. The near-extremal corridor (Prop 10.1) and the algebraic
core are fully within scope and pass.
