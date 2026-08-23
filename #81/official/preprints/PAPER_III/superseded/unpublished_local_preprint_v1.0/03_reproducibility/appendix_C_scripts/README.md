# Appendix C computational audits (recreated)

Self-contained Python re-implementations of the Appendix C checks, recreated from the manuscript
descriptions. Each writes a `*_results.txt` (included). None is a logical premise of any theorem;
they are supplementary regression tests.

| Script | Verifies | Result |
|---|---|---|
| `verify_fractional_margin.py` | Theorem 4.2 (uniform fractional margin), exact rational, 3≤p≤80, 1≤q≤2p, 0≤d≤p | PASS (354224 cases, 0 violations) |
| `verify_factor_rounding.py` | Lemma 5.1 (averaged factorization) and Lemma 5.2 / (5.4) (double-factor inequality), exact-ILP `nu_3` | PASS |
| `verify_shifted_center.py` | Lemma 7.1 / (7.6) (shifted-center gain completion), exact-ILP `nu_3` | PASS |
| `verify_polarization.py` | Lemma 6.1 / (6.2) (polarization inequality), exhaustive + randomized, exact integers | PASS (21844 cases) |
| `verify_divisibility_correction.py` | triangle-divisibility of `K_n` for n≤18, exact-ILP decomposition on small orders, and the parity/mod-3 correction on random dense residuals | PASS |

Requirements: Python 3, `pulp` (bundled CBC) for the ILP scripts. Run any script directly, e.g.
`python3 verify_fractional_margin.py`.

**Scope note (honest).** The ILP-based scripts (`verify_factor_rounding`, `verify_shifted_center`)
run a **fast regression subset** by default (small clique orders p≤8–9) so they finish quickly; the
closed-form checks (`verify_fractional_margin`, `verify_polarization`, divisibility pattern) run the
full stated ranges. Widen the `p` ranges in the ILP scripts to reproduce the manuscript's larger audit.
These recreated scripts still need to be **reconciled with the exact Appendix C script names/counts**
(open editorial gate) before the package is frozen.
