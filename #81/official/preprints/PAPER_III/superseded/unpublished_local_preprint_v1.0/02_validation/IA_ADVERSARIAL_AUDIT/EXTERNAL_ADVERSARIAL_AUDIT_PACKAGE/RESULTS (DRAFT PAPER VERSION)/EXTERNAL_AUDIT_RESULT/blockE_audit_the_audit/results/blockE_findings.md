# Block E — Audit of `OUR_INTERNAL_AUDIT/` (findings record)

## E1 — Reproducibility

All four internal blocks were re-run from a pristine copy (original `results/`
preserved as `results_orig/`), same OS/toolchain (Windows 11, Python 3.14.4,
SymPy 1.14.0, SciPy 1.17.1, PuLP 3.3.2 + CBC):

| Internal block | Re-run exit | Output vs shipped | Claimed counts reproduced |
|---|---|---|---|
| block01 identities | 0 | **BIT-IDENTICAL** | 12/12 PASS |
| block02 common-profile LP | 0 | **BIT-IDENTICAL** | 351/351, max dev 3.9e-14 |
| block03 unified margin | 0 | **BIT-IDENTICAL** | 78,384/78,384 |
| block04 corridor ILP | 0 | **BIT-IDENTICAL** | 372 instances; E-5.1 180/180; Cor 5.3 180/180 |

Grid-size arithmetic independently re-derived: block02 total = Σ_{p=3..8} 9(p+1) = 351 ✔;
block03 total = Σ_{p=3..48} 2p(p+1) = 78,384 ✔; block04 total = Σ_{p=3..5} 6·(2^p+2) = 372,
applicable (q ≥ r_p) = 40+72+68 = 180 ✔. Counts are as claimed, not inflated.

## E2 — Adversarial script reading (defects found)

- **FINDING E-1 (minor, documentation overclaim).** `block02/verify_common_profile_LP.py`
  docstring promises a second per-instance verification — "(EXACT) F equals the min of
  the three cover-vertex values AND that value is a feasible fractional cover" — that
  is **not implemented anywhere in the code**; only the float LP comparison runs. The
  final report/README do not repeat the overclaim, so no reported number is wrong, but
  the advertised exact check is vacuous. (This deliverable's Block C1 supplies that
  exact check, and more, independently.)
- **FINDING E-2 (minor, masking-capable design).** block02 compares a floating-point
  HiGHS LP optimum with tolerance 1e-7. A hypothetical discrepancy below 1e-7 would be
  masked by design. Observed max deviation 3.9e-14 and our exact-rational certificates
  (C1) confirm no such discrepancy exists — the defect is real but did not bite.
  Also, its docstring says it "reproduces the paper's 245/245 (Appendix C, part A)"
  while the grid actually has 351 instances — a stale provenance note.
- **FINDING E-3 (minor, robustness; fail-safe direction).** `block04/verify_corridor_ILP.py`
  never checks the CBC solver status (`prob.status`); a non-optimal/failed solve would
  be consumed silently (`int(round(...))` would crash only if the value were None).
  Direction-of-error analysis: ν₃ is maximized and both audited inequalities are LOWER
  bounds on ν₃, so a premature CBC value can only produce a spurious FAIL, never a
  spurious PASS — the defect cannot have masked a violation. Our C3 re-ran CBC with
  explicit status checks (40/40 'Optimal', values equal to our independent
  branch-and-bound).
- **OBS E-4.** block01's inequality items I4/I6/I7 verify the algebraic backbone
  identity symbolically but carry the sign reasoning in comments/prose rather than as
  machine-checked nonnegativity certificates. Not vacuous, but weaker than advertised
  ("symbolic proof"). Our Block D replaces them with substitution certificates with
  nonnegative coefficients (D12, D13) and exact grids.
- **OBS E-5.** block03's "third-branch dominance" output is bookkeeping (a histogram
  of which branch attains the min), not a check of the Appendix A dominance claim.
  The margin verdict itself is unaffected (the (4.5) check quantifies over the min,
  hence over all branches). Our D07 verifies the actual dominance statement on 401
  exact rational points of [0,2].
- **OBS E-6.** block04's `profiles()` can emit duplicate profiles (families (b)/(c)
  can coincide with (a) members); duplicates inflate instance counts slightly but
  cannot flip a verdict. Our C3 deduplicates (821 distinct instances).

None of E-1…E-6 invalidates any internal verdict; all four internal verdicts were
independently re-obtained with stronger methods in Blocks C/D.

## E3 — Boundary stress (see `e3_boundary_stress.py`, results/e3_boundary_results.txt)

Their shared formula module (`common/audit_formulas.py` — single point of failure for
blocks 02–04) was diffed against this audit's independently written closed forms:
F on 20,319 boundary+random cases (d=0, d=p, q=0, q=2p±1, p=2304, p=10^6),
μ/C_α on 601 exact rationals, r_p on 0≤t<5000 (boundary conventions included),
T on 2000 random cases — **0 mismatches**. Their grid blind spots (block02 q≤8,
block03 p≤48, block04 p≤5) are covered by Blocks C1/C2/C3 of this deliverable.

## Verdict

**E1 PASS (bit-identical reproduction) · E2: three minor script defects + three
observations, none verdict-affecting · E3 PASS.** The internal audit's *claims* hold;
its *evidence quality* has the specific weaknesses listed above, all of which this
external audit repaired with exact/independent methods.
