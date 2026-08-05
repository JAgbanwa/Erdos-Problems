"""
02 — Orbit LP, orbit symmetrization, and affine profile reduction (Paper I, Gates B & C).

Three independent numerical checks of the reduction core (§5-7 / ledger L34-L45),
solving the linear programs from scratch with scipy HiGHS.

(C1) ORBIT LP = closed form.  For each (p,s,q), solve the 3-variable orbit LP
     min A a + B b + C g  s.t. the EXISTING triangle constraints
        3a>=1 (s>=3), a+2b>=1 (o>=1), 2b+g>=1 (o>=2), 3g>=1 (o>=3),  0<=a,b,g<=1,
     and compare to the paper's closed form
        M = min{U,D}          if o<=2
          = min{U,D,H}        if o>=3            (ledger L45).

(C2) ORBIT SYMMETRIZATION.  For each (p,s,q), solve the FULL residual-cover LP over
     ALL C(p,2) clique-edge variables z_e in [0,1] with z(T)>=1 for every clique
     triangle T, objective sum_e (1 - kappa^S_e) z_e, kappa^S_e = q/(s-1) on e⊆S else 0.
     Its optimum is M(kappa^S) with NO symmetry assumed. Compare to the closed form.
     Agreement confirms the orbit averaging loses nothing (Gate C).

(B)  AFFINE REDUCTION / "candidates suffice".  For random MIXED neighbourhood
     profiles on K_p, solve the full residual-cover LP for M(kappa) and check
        M(kappa) >= min_s M(kappa^{S,|S|=s})    (concavity reduction, L34)
        M(kappa) >= R(p,q) - p/2                (uniform bound, L55)
     Kill-switch: any violation (beyond 1e-6) refutes the reduction / bound.
"""
import sys, os, io, itertools
import numpy as np
from scipy.optimize import linprog

TOL = 1e-6

def clique_edges(p):
    return [(i, j) for i in range(p) for j in range(i + 1, p)]

def clique_triangles(p):
    return [(i, j, k) for i in range(p) for j in range(i + 1, p) for k in range(j + 1, p)]

def residual_cover_lp(p, cobj):
    """min sum_e cobj[e]*z_e, z in [0,1]^E, for each clique triangle z(T)>=1."""
    E = clique_edges(p); eidx = {e: i for i, e in enumerate(E)}
    T = clique_triangles(p)
    c = np.array([cobj[e] for e in E], float)
    if not T:                     # p<3: no triangle constraints; min is 0 on nonneg coords
        # optimum: set z_e=0 where c_e>=0, z_e=0 anyway (z>=0); if c_e<0 push to 1
        return float(sum(min(0.0, ce) for ce in c))
    A = np.zeros((len(T), len(E)))
    for r, (a, b, d) in enumerate(T):
        for e in ((a, b), (a, d), (b, d)):
            A[r, eidx[e]] = 1.0
    res = linprog(c, A_ub=-A, b_ub=-np.ones(len(T)), bounds=[(0, 1)] * len(E), method="highs")
    assert res.success, res.message
    return float(res.fun)

def kappaS_obj(p, S, q):
    s = len(S); Sset = set(S)
    val = (q / (s - 1)) if s >= 2 else 0.0
    return {e: (1.0 - (val if (e[0] in Sset and e[1] in Sset) else 0.0)) for e in clique_edges(p)}

def orbit_lp(p, s, q):
    o = p - s
    A = s*(s - 1 - q)/2.0; B = s*o; C = o*(o - 1)/2.0
    c = np.array([A, B, C], float)
    rows = []; rhs = []
    def add(coef):  # coef . (a,b,g) >= 1  ->  -coef . x <= -1
        rows.append([-coef[0], -coef[1], -coef[2]]); rhs.append(-1.0)
    if s >= 3: add((3, 0, 0))
    if o >= 1: add((1, 2, 0))
    if o >= 2: add((0, 2, 1))
    if o >= 3: add((0, 0, 3))
    res = linprog(c, A_ub=(np.array(rows) if rows else None),
                  b_ub=(np.array(rhs) if rhs else None),
                  bounds=[(0, 1)]*3, method="highs")
    assert res.success, res.message
    return float(res.fun)

def closed_form(p, s, q):
    o = p - s
    A = s*(s - 1 - q)/2.0; B = s*o; C = o*(o - 1)/2.0
    U = (A + B + C)/3.0; D = A + C; H = A + (B + C)/3.0
    return (min(U, D) if o <= 2 else min(U, D, H))

def Rpq(p, q):
    return (2*p*p - 2*p*q - q*q)/12.0

def run():
    log = io.StringIO()
    def P(*a):
        t = " ".join(str(x) for x in a); print(t); print(t, file=log)
    P("="*78); P("02 — ORBIT LP / SYMMETRIZATION / AFFINE REDUCTION (Paper I, Gates B,C)"); P("="*78)

    # NOTE (auditor domain fix, CORR-02-01): the closed form min{U,D,H} (ledger L45)
    # is the PURE-PROFILE orbit optimum; the manuscript (App A.3) states pure profiles
    # have q>0. The q=0 case is the separate §7.5 branch. C1/C2 run over q>=1; q=0 is
    # verified separately in (C0).

    # ---- (C0) q=0 branch ----
    P("\n(C0) q=0 branch:  M(0) = 0 (p<=2) or p(p-1)/6 (p>=3)  and  M(0) >= R(p,0)-p/2")
    c0_fail = 0
    for p in range(2, 9):
        M0 = residual_cover_lp(p, {e: 1.0 for e in clique_edges(p)})   # kappa=0 => c_e=1
        expect = 0.0 if p <= 2 else p*(p - 1)/6.0
        bound = Rpq(p, 0) - p/2.0
        ok = abs(M0 - expect) <= 1e-6 and M0 >= bound - 1e-6
        if not ok: c0_fail += 1
        P(f"   p={p}: M(0)={M0:.4f} expect={expect:.4f} R(p,0)-p/2={bound:.4f}  ok={ok}")

    # ---- (C1) orbit LP vs closed form (pure profiles, q>=1) ----
    P("\n(C1) orbit LP  ==  closed form min{U,D}/min{U,D,H}   (pure profiles, q>=1)")
    c1_fail = 0; c1_n = 0
    for p in range(2, 12):
        for s in range(2, p + 1):
            for q in range(1, 13):
                lp = orbit_lp(p, s, q); cf = closed_form(p, s, q); c1_n += 1
                if abs(lp - cf) > 1e-6:
                    c1_fail += 1
                    if c1_fail <= 10: P(f"   MISMATCH p={p} s={s} q={q}: LP={lp:.6f} formula={cf:.6f}")
    P(f"   instances={c1_n}  mismatches={c1_fail}")

    # ---- (C2) full residual-cover LP vs closed form (orbit symmetrization), q>=1 ----
    P("\n(C2) full C(p,2)-variable residual-cover LP  ==  closed form  (orbit averaging lossless)")
    c2_fail = 0; c2_n = 0; c2_maxerr = 0.0
    for p in range(2, 9):
        for s in range(2, p + 1):
            S = tuple(range(s))
            for q in range(1, 11):
                full = residual_cover_lp(p, kappaS_obj(p, S, q))
                cf = closed_form(p, s, q); c2_n += 1
                err = abs(full - cf); c2_maxerr = max(c2_maxerr, err)
                if err > 1e-6:
                    c2_fail += 1
                    if c2_fail <= 10: P(f"   MISMATCH p={p} s={s} q={q}: fullLP={full:.6f} formula={cf:.6f}")
    P(f"   instances={c2_n}  mismatches={c2_fail}  max|fullLP-formula|={c2_maxerr:.2e}")

    # ---- (B) affine reduction on random mixed profiles ----
    P("\n(B) mixed profiles:  M(kappa) >= min_s M(kappa^S)  and  M(kappa) >= R(p,q)-p/2")
    rng = np.random.default_rng(20260710)
    b_fail_red = 0; b_fail_bound = 0; b_n = 0; worst_slack = 1e9
    for trial in range(400):
        p = int(rng.integers(3, 9))
        # random mixture: choose a few subsets S_i (|S|>=2) with multiplicities -> neighborhoods
        nsub = int(rng.integers(1, 5))
        subs = []
        for _ in range(nsub):
            s = int(rng.integers(2, p + 1))
            subs.append(tuple(sorted(rng.choice(p, size=s, replace=False).tolist())))
        mult = [int(rng.integers(1, 5)) for _ in subs]
        q = sum(mult)
        # kappa_e = sum over active v with e ⊆ N(v) of 1/(d_v-1); here each S_i has d=|S_i|
        E = clique_edges(p); kappa = {e: 0.0 for e in E}
        for S, m in zip(subs, mult):
            d = len(S); Sset = set(S)
            for e in E:
                if e[0] in Sset and e[1] in Sset:
                    kappa[e] += m * (1.0 / (d - 1))
        cobj = {e: 1.0 - kappa[e] for e in E}
        Mk = residual_cover_lp(p, cobj)
        min_pure = min(closed_form(p, s, q) for s in range(2, p + 1))
        bound = Rpq(p, q) - p/2.0
        b_n += 1
        if Mk < min_pure - 1e-6: b_fail_red += 1
        if Mk < bound - 1e-6:    b_fail_bound += 1
        worst_slack = min(worst_slack, Mk - bound)
    P(f"   trials={b_n}  reduction-violations(M<min_pure)={b_fail_red}  "
      f"bound-violations(M<R-p/2)={b_fail_bound}")
    P(f"   min slack (M(kappa) - (R(p,q)-p/2)) over trials = {worst_slack:.4f}  (>=0 required)")

    P("-"*78)
    ok = (c0_fail == 0 and c1_fail == 0 and c2_fail == 0 and b_fail_red == 0 and b_fail_bound == 0)
    P(f"(C0) q=0 branch M(0) & bound          : {'VERIFIED' if c0_fail==0 else 'FAILED'} ({c0_fail} fail)")
    P(f"(C1) orbit LP = closed form          : {'VERIFIED' if c1_fail==0 else 'FAILED'} ({c1_fail} mismatch)")
    P(f"(C2) orbit symmetrization lossless   : {'VERIFIED' if c2_fail==0 else 'FAILED'} ({c2_fail} mismatch)")
    P(f"(B)  affine reduction + uniform bound: {'VERIFIED' if (b_fail_red==0 and b_fail_bound==0) else 'FAILED'}")
    P(f"OVERALL: {'ALL VERIFIED (no counterexample)' if ok else 'DISCREPANCY'}")
    P("="*78)
    with 