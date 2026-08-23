#!/usr/bin/env python3
"""Paper III v1.3, gate E2 -- independent rederivation of Section 9.

The request forbids reading Lean declarations in place of mathematics, so every item below
is rederived from the manuscript's own displayed inequalities, in exact symbolic algebra.
Two things are decided:

  K-COVER   is the case split of Section 9 exhaustive, with no uncovered cell?
  the numbered inequalities (9.5), (9.10), (9.11), (9.12), (9.16), (9.17), (9.18),
            (9.19), (9.20) and the constants of (9.4)

Manuscript structure (Section 9):
  Suppose no absolute constant works; pick minimal counterexamples G_k with
  Phi(G_k) > n_k^2/6 + k n_k, so n_k -> infinity, and minimality gives
  d(v) > (2 n_k - 1)/6 + k    (9.2)
  Case A   q >= 2p-1                      -> Lemma 5.1
  otherwise alpha = q/p in [0,2), subsequence:
  Case B   eps <= alpha <= 2-eps          -> Section 9.1, Theorem 4.2 + Haxell-Rodl
  Case C   alpha -> 0                     -> Section 9.2, Section 8
  Case D   alpha -> 2, q = 2p-s, s=o(p)   -> Section 9.3
     D1    s = O(sqrt p)                  -> (5.3)
     D2    sqrt p << s = o(p), with (9.4)
       D2a high dispersion  D >= q s^2/12
       D2b low dispersion   D <  q s^2/12
"""
import json

import sympy as sp

OUT = "C:/erdos_audit/v14/E2/section9.json"

p, q, s, m, k, rho, M, S2, D, x, eps, t = sp.symbols(
    "p q s m k rho M S2 D x epsilon t", positive=True)


def rec(name, claim, verdict, detail):
    return {"item": name, "claim": claim, "verdict": verdict, "detail": detail}


def main():
    out = {"gate": "E2", "section": 9, "arithmetic": "exact symbolic (sympy)",
           "random_seeds": 0, "items": []}
    A = out["items"].append

    # ---------------- K-COVER: exhaustiveness of the case split
    A(rec("K-COVER, top-level split",
          "either q >= 2p-1 (Case A) or alpha = q/p in [0,2) (Cases B-D)",
          "PASS",
          "q >= 2p-1 and q < 2p-1 are complementary over the integers, and q < 2p-1 with "
          "q, p >= 1 gives alpha = q/p < 2 - 1/p < 2, so alpha lies in [0,2). No cell is "
          "left out and the two cells do not overlap."))

    A(rec("K-COVER, subsequence trichotomy",
          "every sequence alpha_k in [0,2) admits a subsequence falling under B, C or D",
          "PASS",
          "The sequence (alpha_k) lies in the compact [0,2], so by Bolzano-Weierstrass it "
          "has a convergent subsequence with limit L in [0,2]. If L is interior, i.e. "
          "0 < L < 2, then for eps = min(L, 2-L)/2 > 0 the tail satisfies "
          "eps <= alpha_k <= 2-eps, which is Case B. If L = 0 it is Case C, and if L = 2 "
          "it is Case D. The three limits are mutually exclusive and exhaust [0,2], so the "
          "trichotomy is complete. The argument is a contradiction argument over "
          "subsequences, so covering every subsequential limit is exactly what is needed."))

    A(rec("K-COVER, split inside Case D",
          "s = O(sqrt p) (D1) or sqrt p << s = o(p) (D2)",
          "PASS",
          "Case D fixes s = 2p - q with s = o(p). The two subcases are 's bounded by a "
          "constant multiple of sqrt p' and its negation, which is 's/sqrt p -> infinity'. "
          "Complementary by construction. s = Theta(p) cannot occur because alpha -> 2 "
          "forces s = o(p)."))

    A(rec("K-COVER, dispersion dichotomy",
          "D >= q s^2/12 (high) or D < q s^2/12 (low)",
          "PASS",
          "A real number is either at least q s^2/12 or below it. Exhaustive and disjoint "
          "by trichotomy of the reals."))

    # ---------------- (9.4): why p >= 2304
    cond = sp.solve(sp.Eq(6 * sp.sqrt(p), p / 8), p)
    A(rec("(9.4) constants",
          "p >= 2304 together with 6 sqrt p <= s <= p/8",
          "PASS",
          f"The window 6 sqrt p <= s <= p/8 is non-empty exactly when 6 sqrt p <= p/8, "
          f"i.e. 48 <= sqrt p, i.e. p >= 2304. Solving 6 sqrt p = p/8 gives p = {cond}. "
          f"So the constant 2304 is forced by the two constraints being simultaneously "
          f"satisfiable; it is not a free choice."))

    # ---------------- (9.5): 3m <= s-3
    A(rec("(9.5) integrality step",
          "m_i < s/3 + 1/6 - k and k >= 1 imply 3m <= s-3 for integer m",
          "PASS",
          "With k >= 1, m < s/3 + 1/6 - 1 = s/3 - 5/6, hence 3m < s - 5/2. Since s and m "
          "are integers, 3m is an integer strictly below s - 5/2, so 3m <= s - 3. The "
          "rounding is valid: the next integer below s - 5/2 is s - 3."))

    # ---------------- (9.10): delta >= 7/8, both parities
    odd = sp.simplify((p - s) / p - sp.Rational(7, 8))
    even = sp.simplify((p + 1 - s) / (p - 1) - sp.Rational(7, 8))
    odd_at = sp.simplify(odd.subs(s, p / 8))
    even_sol = sp.solve(sp.Eq((p + 1 - s) / (p - 1), sp.Rational(7, 8)), s)
    A(rec("(9.10) delta >= 7/8",
          "p odd: delta = (p-s)/p; p even: delta = (p+1-s)/(p-1); both >= 7/8 when s <= p/8",
          "PASS",
          f"Odd p: (p-s)/p - 7/8 = {sp.simplify(odd)}, which at the extreme s = p/8 equals "
          f"{odd_at}, i.e. exactly zero, so the bound holds with equality at the boundary "
          f"and strictly inside. Even p: (p+1-s)/(p-1) >= 7/8 iff s <= {even_sol[0]} = "
          f"(p+15)/8, and s <= p/8 <= (p+15)/8, so it holds with room to spare. Both "
          f"parities are covered and the odd case is the binding one."))

    # ---------------- (9.11): parabola bound
    expr = (s - 1) * x - x ** 2
    vertex = sp.solve(sp.diff(expr, x), x)[0]
    at_end = sp.simplify(expr.subs(x, (s - 3) / 3))
    target = sp.simplify(2 * s * (s - 3) / 9)
    A(rec("(9.11) ((s-1)M - S2)/q <= 2s(s-3)/9",
          "using S2 >= M^2/q and M/q <= m <= (s-3)/3",
          "PASS" if sp.simplify(at_end - target) == 0 else "FAIL",
          f"Write x = M/q. Then ((s-1)M - S2)/q <= (s-1)x - x^2. That parabola has vertex "
          f"at x = {vertex} and is increasing on [0, {vertex}]. The admissible range ends "
          f"at x = (s-3)/3, and (s-3)/3 <= (s-1)/2 for all s >= -3, so the maximum over "
          f"the range is attained at the right endpoint. Evaluating there gives "
          f"{sp.factor(at_end)}, and the claimed bound is {sp.factor(target)}; their "
          f"difference is {sp.simplify(at_end - target)}. The step is exact, not an "
          f"estimate."))

    # ---------------- (9.12) -> contradiction in high dispersion
    # substitute the extreme s = 6 sqrt p on BOTH sides: a bare subs(s**2, 36*p) also
    # rewrites the linear -2s/3 term and produces a spurious residual.
    lhs = p / 2 - 5 * s ** 2 / 288 - 2 * s / 3
    claim12 = -p / 8 - 2 * s / 3
    sub = sp.simplify(lhs.subs(s, 6 * sp.sqrt(p)))
    claim12_at = sp.simplify(claim12.subs(s, 6 * sp.sqrt(p)))
    A(rec("(9.12) high-dispersion contradiction",
          "Phi - n^2/6 <= p/2 - 5s^2/288 - 2s/3 and s^2 >= 36p give <= -p/8 - 2s/3 < 0",
          "PASS" if sp.simplify(sub - claim12_at) == 0 else "FAIL",
          f"At the extreme s = 6 sqrt p, i.e. s^2 = 36p, the manuscript bound evaluates to "
          f"{sub} and the claimed form -p/8 - 2s/3 evaluates to {claim12_at}; the "
          f"difference is {sp.simplify(sub - claim12_at)}. The coefficient arithmetic is "
          f"exact: 5*36/288 = {sp.Rational(5*36,288)} and 1/2 - 5/8 = "
          f"{sp.Rational(1,2)-sp.Rational(5,8)}, so p/2 - 5s^2/288 = -p/8 at the boundary "
          f"and is more negative beyond it, while -2s/3 only helps. Auditor note: a first "
          f"version of this check used subs(s**2, 36*p), which also rewrites the linear "
          f"term and reported a spurious FAIL; the corrected substitution is applied to "
          f"both sides."))

    # ---------------- theta_R and (9.16), (9.17)
    theta_bound = sp.simplify(((s / 3) / (p - s / 3)).subs(s, p / 8))
    A(rec("theta_R <= 8s/(23p)",
          "from rho <= m <= (s-3)/3 and s <= p/8",
          "PASS" if sp.simplify(theta_bound - 8 * (p / 8) / (23 * p)) == 0 else "FAIL",
          f"theta_R <= rho/(p-rho) is increasing in rho, so it is largest at rho = s/3, "
          f"giving (s/3)/(p - s/3). That is largest when s is largest, i.e. s = p/8, where "
          f"it equals {theta_bound} = 1/23, matching 8s/(23p) at s = p/8. So the bound "
          f"8s/(23p) is exactly the value at the two extreme substitutions."))

    kappa = sp.simplify(s / (15 * p / 8) + 2 * (8 * s / (23 * p)))
    A(rec("(9.16) kappa_R <= 5s/(4p)",
          "kappa_R <= s/q + 2 theta_R with q >= 15p/8 and theta_R <= 8s/(23p)",
          "PASS" if sp.simplify(5 * s / (4 * p) - kappa) >= 0 else "FAIL",
          f"s/q <= 8s/(15p) since q >= 15p/8. Adding 2 theta_R <= 16s/(23p) gives "
          f"{sp.nsimplify(kappa)} = {sp.nsimplify(sp.simplify(kappa/(s/p)))} s/p, which is "
          f"about {float(sp.simplify(kappa/(s/p))):.5f} s/p, below the claimed 1.25 s/p. "
          f"The margin is {sp.nsimplify(sp.simplify(5*s/(4*p) - kappa))}, so the bound "
          f"holds but is not generous."))

    # ---------------- (9.18)
    cond18 = sp.solve(sp.Eq(5 * s ** 3 / (24 * p), 5 * s ** 2 / 192), s)
    A(rec("(9.18) 5s^3/(24p) <= 5s^2/192",
          "the total positive deviation bound",
          "PASS",
          f"5s^3/(24p) <= 5s^2/192 reduces to s <= 24p/192 = p/8, and s <= p/8 is exactly "
          f"hypothesis (9.4). Solving for equality gives s = {cond18}. So the step consumes "
          f"the whole of the s <= p/8 budget and is tight at the boundary."))

    # ---------------- (9.19) exact identity
    ident = sp.expand(2 * (rho - s / 4) ** 2 + s ** 2 / 24
                      - (s ** 2 / 6 - s * rho + 2 * rho ** 2))
    A(rec("(9.19) completion of the square",
          "s^2/6 - s rho + 2 rho^2 = 2(rho - s/4)^2 + s^2/24",
          "PASS" if sp.simplify(ident) == 0 else "FAIL",
          f"Expanding the difference gives {sp.simplify(ident)}. The identity is exact, so "
          f"the lower bound s^2/24 is attained at rho = s/4 and the step loses nothing."))

    # ---------------- (9.20)
    lhs20 = p / 2 - s ** 2 / 64
    sub20 = sp.simplify(lhs20.subs(s ** 2, 36 * p))
    A(rec("(9.20) low-dispersion contradiction",
          "Phi - n^2/6 <= p/2 - s^2/64 and s^2 >= 36p give <= -p/16 < 0",
          "PASS" if sp.simplify(sub20 - (-p / 16)) == 0 else "FAIL",
          f"With s^2 = 36p, p/2 - s^2/64 = {sp.simplify(sub20)}, and 36/64 = 9/16 so "
          f"p/2 - 9p/16 = -p/16 exactly; the difference from the claim is "
          f"{sp.simplify(sub20 - (-p/16))}."))

    # ---------------- q >= 15p/8, b >= p - s/3
    A(rec("Lemma 7.1 hypotheses in the low-dispersion branch",
          "q >= 15p/8, b = p - rho >= p - s/3, b >= 2, q >= r_b, b >= chi'(K_rho), "
          "b - t_i >= max{rho, u}",
          "PASS on the arithmetic, PARTIAL on the combinatorial hypotheses",
          "q = 2p - s with s <= p/8 gives q >= 2p - p/8 = 15p/8, exact. rho <= m <= "
          "(s-3)/3 < s/3 gives b = p - rho > p - s/3, exact. With p >= 2304 and s <= p/8, "
          "b > p - p/24 = 23p/24 >= 2, so b >= 2 holds with enormous room. The chain "
          "2 rho + t_i + 1 <= 3m + 1 <= s - 2 follows from (9.5) provided rho <= m and "
          "t_i <= m, which is how R = S_j and t_i are defined; the auditor verified the "
          "arithmetic but did not re-derive the definitional facts rho <= m and t_i <= m "
          "from Section 7, so this row is PARTIAL rather than PASS."))

    # ---------------- what E2 does NOT cover
    out["not_covered"] = {
        "K-EPS": ("the AX1/nibble epsilon ledger: positivity and permitted ranges of every "
                  "parameter, real/natural conversions, exceptional-set and rounding terms, "
                  "and the accumulation of all losses inside eps n^2. NOT attempted."),
        "K-CORRIDOR": ("Sections 5-7 themselves: one-factor averaging, the short-corridor "
                       "inequality and its parity cases, double-factor sampling and the "
                       "dispersion correction, the polarization identity, and the "
                       "shifted-center construction. Section 9 USES Lemmas 5.1, 5.2, 6.1 "
                       "and 7.1 as inputs; this gate verified how Section 9 combines them, "
                       "not that those lemmas are true. NOT attempted."),
        "K-SPARSE": ("Section 8, which discharges the alpha -> 0 endpoint and supplies the "
                     "absolute C_0. Section 9.2 is one sentence long and defers entirely to "
                     "it, so Case C of the cover is closed only modulo Section 8. NOT "
                     "attempted."),
        "K-GLOBAL": ("the minimal-counterexample induction is the frame of Section 9 and "
                     "was read and checked for structure, including the step from "
                     "minimality to (9.2); but the auditor did not verify the base cases at "
                     "small orders nor that Phi(G) <= Phi(G-v) + d(v) holds for every "
                     "vertex of every split graph. PARTIAL."),
        "Sections 4-9 analytic core": ("Section 4 and Section 9 were rederived; Sections "
                                       "5-8 were not.")}

    json.dump(out, open(OUT, "w"), indent=1)

    for it in out["items"]:
        print(f"[{it['verdict']:>7}] {it['item']}")
        print(f"          {it['claim']}")
    print("\n=== no cubierto por E2")
    for k2, v in out["not_covered"].items():
        print(f"  {k2}: {v[:120]}...")
    npass = sum(1 for i in out["items"] if i["verdict"] == "PASS")
    print(f"\nitems verificados: {len(out['items'])}, PASS: {npass}, "
          f"otros: {len(out['items']) - npass}")


if __name__ == "__main__":
    main()
