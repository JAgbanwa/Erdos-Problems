"""
Paper III — internal audit: shared EXACT-RATIONAL formula definitions.

Everything here uses `fractions.Fraction` (exact rational arithmetic) so that every
numeric audit is exact, not floating point. Mirrors the definitions of
PAPER_III_split_lineal_v0.9.x §0, §3, §4.
"""
from fractions import Fraction as Q


def C2(x):
    """Binomial(x, 2) = x(x-1)/2, as an exact rational (x may be a Fraction/int)."""
    x = Q(x)
    return x * (x - 1) / 2


def C3(x):
    """Binomial(x, 3) = x(x-1)(x-2)/6, exact."""
    x = Q(x)
    return x * (x - 1) * (x - 2) / 6


def F(p, q, d):
    """E-3.1 common-profile fractional optimum F(p,q,d), exact rational.
    r = p - d;  min of the three cover-vertex values."""
    p, q, d = Q(p), Q(q), Q(d)
    r = p - d
    t1 = (C2(p) + q * d) / 3
    t2 = C2(d) + C2(r)
    t3 = C2(d) + (d * r + C2(r)) / 3
    return min(t1, t2, t3), (t1, t2, t3)


def mu(alpha):
    """E-4.2 unified fractional margin mu(alpha), exact rational.
    alpha in [0,2]; alpha^2/12 on [0,2/3], (2-alpha)^2/48 on [2/3,2]."""
    alpha = Q(alpha)
    if alpha <= Q(2, 3):
        return alpha ** 2 / 12
    return (2 - alpha) ** 2 / 48


def Ca(alpha):
    """C_alpha = (2 - 2*alpha - alpha^2)/12, exact rational."""
    alpha = Q(alpha)
    return (2 - 2 * alpha - alpha ** 2) / 12


def T_of_edges(edge_count, p, q):
    """T(G) = ( |E| - (p+q)^2/6 ) / 2, exact rational."""
    return (Q(edge_count) - (Q(p) + Q(q)) ** 2 / 6) / 2


def rp(t):
    """r_p = chi'(K_t): 0 if t<=1, t-1 if t even, t if t odd."""
    if t <= 1:
        return 0
    return t - 1 if t % 2 == 0 else t
