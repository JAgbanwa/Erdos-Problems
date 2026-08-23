# Block D — Independent re-derivation of the algebra

**Attacked:** every algebraic identity/inequality the paper's corridor chains rely on
(D1 of the checklist), and the three cover-vertex values of F (D2).

**Method — independence:** NO computer-algebra system is used (the internal audit used
SymPy). `rederive_algebra.py` implements its own exact multivariate polynomial class
over `fractions.Fraction`; identities are verified by exact expansion of LHS−RHS;
inequalities by explicit certificates (perfect-square factorizations, substitution
u≥0 with all-nonnegative coefficients) or exact-rational grids at and beyond the
paper's boundaries.

**Coverage (38 checks):** T-identity; three cover values of F + their feasibility
(D2); C(d,2)+dr+C(r,2)=C(p,2); exact (4.5) residuals for all three branches incl. the
branch-3 square completion and its boundary case (auditor-derived, sharper than the
paper's Appendix A sketch); Appendix A minima + third-branch dominance; μ continuity;
the (5.2) identity and (5.3) parabola completion; (9.5) integrality; (9.10) δ≥7/8 both
parities; (9.11) nonneg-coefficient certificate; (9.12) −5/288; (9.16)/(9.17) exact
grids at p∈{2304..2339, …, 10^5}; (9.18); (9.19); (9.20) −1/64; threshold p=2304;
Prop 10.1(i) chain on p∈[36,600] exhaustive; Lemma 6.1 counting identity (exhaustive
p=7) + V-identity + inequality on 400 random exact instances; sharpness closed form;
and the **Lemma 7.1 assembly identity (D23)** — the (7.6) expansion the paper does not
display, reconstructed by the auditor and machine-verified.

**Reproduce:** `python rederive_algebra.py` → `results/algebra_results.txt`, exit 0
iff 38/38.

**Result: 38/38 PASS.** Two auditor-side scripting errors occurred during development
(a wrong guessed square center; a malformed check) — both were defects of the audit
script, corrected with exact certificates; recorded here for symmetric transparency.

**Verdict: PASS** (all load-bearing algebra independently re-derived, no CAS).
