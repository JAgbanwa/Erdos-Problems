"""E5 supplement (auditor-written, run_v1.22_r1): negative controls for the six C.3 checks of e5_v122_c3.py
that had none (C3c, C3e, C3g, C3j, C3l, C3n). Each perturbed claim must be FALSE. No Lean."""
from fractions import Fraction as F
import json, sys
X = 9 * 10**19; a = F(1, X); delta = a**21 / 2208; k0 = 3 * 10**19 + 1
neg = {
 'C3c': ('1/delta = 2208*(9e19)^20', 1 / delta == 2208 * X**20),
 'C3e': ('50/xi = 10^17 at xi=eta0/2', 50 / (F(1, 10**16) / 2) == 10**17),
 'C3g': ('k0 >= 10^20', k0 >= 10**20),
 'C3j': ('term bounds sum to 6', 1 + 1 + 1 + 3 + 1 == 6),
 'C3l': ('4(x4^x) <= 2^(3x) for x in 1..300', all(4 * x * 4**x <= 2**(3 * x) for x in range(1, 301))),
 'C3n': ('30R <= 7q when q=4R, R in 1..999', all(30 * R <= 7 * (4 * R) for R in range(1, 1000))),
}
out = {k: {'negative_claim': c, 'holds': bool(v), 'rejected': not v} for k, (c, v) in neg.items()}
out['all_rejected'] = all(not v for _, v in neg.values())
json.dump(out, open(sys.argv[1], 'w', encoding='utf-8'), indent=1); print(json.dumps(out, indent=1))
