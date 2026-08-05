# Script 02 — Orbit LP, Symmetrization, Affine Reduction (Gates B & C)

**Audit:** PAPER_I_EXT_AUDIT · **Script:** `02_orbit_lp_and_reduction.py`
**Environment:** Python 3.14.4, scipy 1.17.1 (HiGHS LP), numpy · seed 20260710

## Purpose

Solve, from scratch with an independent LP solver, the linear programs behind the
reduction core (§5–7 / ledger L34–L45) and confirm the manuscript's closed forms.

## Checks and results

**(C0) `q = 0` branch.** The full residual-cover LP gives `M(0) = 0` for `p ≤ 2` and
`p(p−1)/6` for `p ≥ 3`, and `M(0) ≥ R(p,0) − p/2`, for `p = 2..8`. **VERIFIED.**

**(C1) Orbit LP = closed form.** For `p = 2..11`, `s = 2..p`, `q = 1..12` (660 pure
profiles), the 3-variable orbit LP `min Aα+Bβ+Cγ` over the existing triangle
constraints equals `min{U,D}` (`o ≤ 2`) / `min{U,D,H}` (`o ≥ 3`). **0 mismatches.**

**(C2) Orbit symmetrization is lossless.** For `p = 2..8`, the **full** `C(p,2)`-variable
residual-cover LP (no symmetry assumed) equals the 3-orbit closed form on all 280 pure
profiles, `max |fullLP − formula| = 5.3e−15`. This confirms that averaging an optimum
over `Sym(S)×Sym(K∖S)` loses nothing — the crux of Gate C. **0 mismatches.**

**(B) Affine reduction / "candidates suffice".** For 400 random **mixed** neighborhood
profiles on `K_p`, the full residual-cover LP value `M(κ)` satisfies both
`M(κ) ≥ min_s M(κ^{S})` (concavity reduction, L34) and `M(κ) ≥ R(p,q) − p/2` (uniform
bound, L55). **0 violations**; minimum slack `M(κ) − (R−p/2) = 0.0000` (the bound is
attained — tight — on some mixed profiles, consistent with the extremal family).

| Check | Verdict |
|---|---|
| (C0) q=0 branch | VERIFIED |
| (C1) orbit LP = min{U,D,H} | VERIFIED (0/660) |
| (C2) orbit symmetrization lossless | VERIFIED (0/280, err 5e-15) |
| (B) affine reduction + uniform bound | VERIFIED (0/400) |

## Auditor correction (CORR-02-01)

The first run compared the closed form `min{U,D,H}` against the LP at `q = 0` and
reported a mismatch at `p=2, q=0`. That was an auditor domain error: the closed form
(ledger L45) is the **pure-profile** optimum, and the manuscript (Appendix A.3) states
pure profiles have `q > 0`; the `q = 0` case is the separate §7.5 branch. The test was
corrected to run C1/C2 over `q ≥ 1` and to verify the `q = 0` branch separately (C0).
This is not a paper defect — the manuscript is explicit and correct on this point.

## Verdict

**ALL VERIFIED — no counterexample.** The orbit LP closed form, the losslessness of the
orbit symmetrization (full LP = 3-orbit LP), and the affine/concavity reduction with its
uniform bound `R(p,q) − p/2` are all confirmed numerically. Combined with Script 01's
exact algebra, Gates B, C, E 