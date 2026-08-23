#!/usr/bin/env python3
"""RESIDUAL AUDIT, PAPER_I v1.3, general mathematical regression (spec Section 6).

Reruns the proportionate mathematical regression against the v1.3 manuscript and adds
the identity that is NEW in v1.3: the explicit H-slack accounting introduced in the
derivation of (4.7) (v1.3 EN Markdown L303-317).

Everything is checked as an EXACT symbolic polynomial identity or by exact-rational
enumeration. No sampling, no seeds.
"""
import json
from fractions import Fraction as Fr
from itertools import combinations
from sympy import symbols, expand, Rational

p, q, s, o, n, b1, j, u, v, d = symbols("p q s o n b1 I0 u v d_v", integer=True)
kap, H1 = symbols("kappa_sum SumH", positive=True)

results = []


def chk(tag, name, lhs, rhs, note=""):
    r = expand(lhs - rhs)
    results.append({"tag": tag, "name": name, "holds": bool(r == 0),
                    "residual": str(r), "note": note})


# ---------------------------------------------------------------- new in v1.3
# (4.3)  |w_1| = |H| + sum_{e in L} kappa_e
# v1.3 L308 asserts |w_1| = b_{>=2}/2 + sum_{e in H}(1 - kappa_e)
# These must agree, given Lemma 3.1: sum over ALL e of kappa_e = b_{>=2}/2.
# Write:  SH = sum_{e in H} kappa_e,  SL = sum_{e in L} kappa_e,  cardH = |H|
SH, SL, cardH, bge = symbols("SH SL cardH b_ge2", nonnegative=True)
chk("v13-4.3/4.8",
    "v1.3 |w_1| = b/2 + sum_H (1-kappa_e) agrees with (4.3) |w_1| = |H| + sum_L kappa_e",
    (bge / 2 + (cardH - SH)).subs(bge, 2 * (SH + SL)),
    cardH + SL,
    "uses Lemma 3.1: sum_all kappa_e = b_{>=2}/2, i.e. SH + SL = b/2")

# v1.3 L314 asserts |w_2| = M(kappa) - sum_{e in H}(1 - kappa_e)
# Adding the two displayed identities must give (4.7): V_com = b/2 + M(kappa)
M = symbols("M")
chk("v13-4.7",
    "adding the two v1.3 identities yields (4.7) V_com = b/2 + M(kappa)",
    (bge / 2 + (cardH - SH)) + (M - (cardH - SH)),
    bge / 2 + M,
    "the sum_H(1-kappa_e) terms cancel exactly; this is the accounting v1.2 omitted")

# ---------------------------------------------------------------- unchanged core
chk("L3.1", "per-vertex contribution C(d,2)/(d-1) = d/2",
    (d * (d - 1) / 2) / (d - 1), d / 2)

A = s * (s - 1 - q) / 2
B = s * o
C = o * (o - 1) / 2
chk("6.3", "A+B+C = (p^2-p-s q)/2 with p = s+o",
    (A + B + C).subs(o, p - s), (p**2 - p - s * q) / 2)

U = (A + B + C) / 3
D = A + C
Hh = A + (B + C) / 3
R = (2 * p**2 - 2 * p * q - q**2) / 12

chk("7.2", "12(U-R) = q(2o+q) - 2p",
    (12 * (U - R)).subs(o, p - s), q * (2 * (p - s) + q) - 2 * p)
chk("7.4", "12(D-R) = 12o^2 - 6o(2p-q) + (2p-q)^2 - 6p",
    (12 * (D - R)).subs(s, p - o),
    12 * o**2 - 6 * o * (2 * p - q) + (2 * p - q)**2 - 6 * p)
chk("7.4c", "12u^2 - 6uv + v^2 = 12(u - v/4)^2 + v^2/4",
    12 * u**2 - 6 * u * v + v**2, 12 * (u - v / 4)**2 + v**2 / 4)
chk("7.6", "12(H-R) = (2s-q)^2 + 2q(p-s) - 2p - 4s",
    (12 * (Hh - R)).subs(o, p - s),
    (2 * s - q)**2 + 2 * q * (p - s) - 2 * p - 4 * s)
chk("8.2", "binom(p,2) - 2R + p = (p+q)^2/6 + p/2",
    p * (p - 1) / 2 - 2 * R + p, (p + q)**2 / 6 + p / 2)

lhs_asm = (n**2 / 6 + n / 2) - ((p + q)**2 / 6 + p / 2 + b1)
rhs_asm = (b1**2 + j**2 + 2 * b1 * j + 2 * (b1 + j) * (p + q)
           + 3 * j + 3 * q - 3 * b1) / 6
chk("8.3", "assembly difference identity",
    lhs_asm.subs(n, p + q + b1 + j), rhs_asm)
chk("8.res", "residual regime p=1,q=0",
    rhs_asm.subs({p: 1, q: 0}),
    (b1 * (b1 - 1) + j**2 + 2 * b1 * j + 5 * j) / 6)
chk("9.cs", "complete-split family LHS = n^2/6 + n/6 at n = 3p",
    (p * (p - 1) / 2 + 2 * p**2) - 2 * (p * (p - 1) / 2),
    (3 * p)**2 / 6 + (3 * p) / 6)

# ---------------------------------------------------------------- A.2 domain, v1.3
v_o3 = B * Rational(1, 2) + C * Rational(1, 3)
v_lo = B * Rational(1, 2)
chk("A.2-o>=3", "v1.3 A.2 excess (B-2A)/6 is exact at the o>=3 endpoint (0,1/2,1/3)",
    v_o3 - U, (B - 2 * A) / 6,
    "v1.3 now states 'If A>=0 and o>=3', which is exactly this domain")
chk("A.2-o<=2", "at the o<=2 endpoint (0,1/2,0) the excess is (B-2A-2C)/6",
    v_lo - U, (B - 2 * A - 2 * C) / 6,
    "v1.3 routes o=0,1,2 through A.3 instead; the restriction is now correct")


# ---------------------------------------------------------------- orbit LP rerun
def orbit_lp(pp, qq, ss):
    oo = pp - ss
    AA = Fr(ss * (ss - 1 - qq), 2)
    BB = Fr(ss * oo)
    CC = Fr(oo * (oo - 1), 2)
    cons = []
    if ss >= 3:
        cons.append(((Fr(3), Fr(0), Fr(0)), Fr(1)))
    if ss >= 2 and oo >= 1:
        cons.append(((Fr(1), Fr(2), Fr(0)), Fr(1)))
    if ss >= 1 and oo >= 2:
        cons.append(((Fr(0), Fr(2), Fr(1)), Fr(1)))
    if oo >= 3:
        cons.append(((Fr(0), Fr(0), Fr(3)), Fr(1)))
    for i in range(3):
        e = [Fr(0)] * 3
        e[i] = Fr(1)
        cons.append((tuple(e), Fr(0)))
        e = [Fr(0)] * 3
        e[i] = Fr(-1)
        cons.append((tuple(e), Fr(-1)))
    obj = (AA, BB, CC)

    def feas(x):
        return all(sum(r[i] * x[i] for i in range(3)) >= b for r, b in cons)

    best = None
    for tri in combinations(range(len(cons)), 3):
        Mx = [list(cons[i][0]) + [cons[i][1]] for i in tri]
        rk = 0
        piv = []
        for c in range(3):
            pr = next((rr for rr in range(rk, 3) if Mx[rr][c] != 0), None)
            if pr is None:
                continue
            Mx[rk], Mx[pr] = Mx[pr], Mx[rk]
            pv = Mx[rk][c]
            Mx[rk] = [t / pv for t in Mx[rk]]
            for rr in range(3):
                if rr != rk and Mx[rr][c] != 0:
                    f = Mx[rr][c]
                    Mx[rr] = [Mx[rr][k] - f * Mx[rk][k] for k in range(4)]
            piv.append(c)
            rk += 1
        if rk < 3:
            continue
        x = [Fr(0)] * 3
        for i, c in enumerate(piv):
            x[c] = Mx[i][3]
        if not feas(x):
            continue
        val = sum(obj[i] * x[i] for i in range(3))
        if best is None or val < best:
            best = val
    return best


def closed(pp, qq, ss):
    oo = pp - ss
    AA = Fr(ss * (ss - 1 - qq), 2)
    BB = Fr(ss * oo)
    CC = Fr(oo * (oo - 1), 2)
    UU = (AA + BB + CC) / 3
    DD = AA + CC
    HH = AA + (BB + CC) / 3
    return min(UU, DD) if oo <= 2 else min(UU, DD, HH)


def Rf(pp, qq):
    return Fr(2 * pp * pp - 2 * pp * qq - qq * qq, 12)


mism = []
viol = []
eqc = []
reg = {}
cases = 0
for pp in range(2, 19):
    for qq in range(1, 45):
        for ss in range(2, pp + 1):
            cases += 1
            g = orbit_lp(pp, qq, ss)
            e = closed(pp, qq, ss)
            if g != e:
                mism.append((pp, qq, ss, str(g), str(e)))
            sl = g - (Rf(pp, qq) - Fr(pp, 2))
            if sl < 0:
                viol.append((pp, qq, ss, str(sl)))
            if sl == 0:
                eqc.append({"p": pp, "q": qq, "s": ss, "o": pp - ss,
                            "q_eq_2p": qq == 2 * pp})
            oo = pp - ss
            for nm, cond in (("s>=3,o>=3", ss >= 3 and oo >= 3),
                             ("s==2,o>=1", ss == 2 and oo >= 1),
                             ("o==1", oo == 1), ("o==2", oo == 2),
                             ("o==0", oo == 0)):
                if cond and (nm not in reg or sl < reg[nm][0]):
                    reg[nm] = (sl, {"p": pp, "q": qq, "s": ss})

g224 = orbit_lp(2, 4, 2)
sl224 = g224 - (Rf(2, 4) - Fr(2, 2))

print(json.dumps({
    "spec": "RESIDUAL_AUDIT_REQUEST_SPEC.md",
    "section": "6 general mathematical regression",
    "target": "preprint_draft_v1.3",
    "arithmetic": "exact sympy symbolic and exact Fraction enumeration; no seeds",
    "symbolic": {"checked": len(results),
                 "all_hold": all(r["holds"] for r in results),
                 "failures": [r for r in results if not r["holds"]],
                 "detail": results},
    "orbit_program": {"domain": {"p": [2, 18], "q": [1, 44], "s": [2, "p"]},
                      "cases": cases,
                      "closed_form_mismatches": len(mism),
                      "bound_7_8_violations": len(viol),
                      "mismatch_detail": mism[:8]},
    "tightness_remark": {
        "mandated_point_2_4_2": {"lp": str(g224), "slack": str(sl224),
                                 "verdict": "CONFIRMED equality" if sl224 == 0 else "CONTRADICTED"},
        "regime_minima": {k: {"min_slack": str(v0), "at": v1} for k, (v0, v1) in reg.items()},
        "claims": {
            "s>=3,o>=3 slack>=9/4": bool(reg["s>=3,o>=3"][0] >= Fr(9, 4)),
            "s==2,o>=1 slack>=1/4": bool(reg["s==2,o>=1"][0] >= Fr(1, 4)),
            "o==1 slack>=1/4": bool(reg["o==1"][0] >= Fr(1, 4)),
            "o==2 slack>=1/4": bool(reg["o==2"][0] >= Fr(1, 4)),
            "equality_only_o0_and_q2p": all(e["o"] == 0 and e["q_eq_2p"] for e in eqc),
        },
        "equality_cases": len(eqc)},
}, indent=1))
