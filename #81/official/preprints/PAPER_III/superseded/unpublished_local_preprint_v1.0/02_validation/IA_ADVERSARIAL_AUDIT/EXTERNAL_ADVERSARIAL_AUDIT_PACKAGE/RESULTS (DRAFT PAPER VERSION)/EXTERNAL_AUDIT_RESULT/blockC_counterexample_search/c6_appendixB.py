r"""
EXTERNAL ADVERSARIAL AUDIT — Block C, attack on Appendix B (E-B, claim C-11).

Path parity construction: P = x_1...x_p a path, O ⊆ V(P) with |O| even,
    J = { x_j x_{j+1} : |O ∩ {x_1..x_j}| is odd }.
Claims: Odd(J) = O ;  |E(J)| <= p-1 ;  Delta(J) <= 2.

EXHAUSTIVE check for 2 <= p <= 16 over ALL even-cardinality subsets O
(sum over p of 2^(p-1) subsets ~ 65,000 cases), plus the mod-3 cycle
correction bookkeeping: removing a C4 changes |E| by 4 = 1 (mod 3), a C5 by
5 = 2 (mod 3), and every affected degree drops by exactly 2 (parity kept).

Output: results/c6_appendixB_results.txt
"""
import sys, os
from itertools import combinations

OUT = []
def emit(x=''): OUT.append(str(x))

bad = []
total = 0
for p in range(2, 17):
    for k in range(0, p + 1, 2):
        for O in combinations(range(p), k):
            total += 1
            Oset = set(O)
            J = []
            pref = 0
            for j in range(p - 1):          # edge x_j x_{j+1}, 0-indexed
                pref += 1 if j in Oset else 0
                if pref % 2 == 1:
                    J.append((j, j + 1))
            deg = [0]*p
            for (a, b) in J:
                deg[a] += 1; deg[b] += 1
            odd = {v for v in range(p) if deg[v] % 2 == 1}
            if odd != Oset or len(J) > p - 1 or max(deg, default=0) > 2:
                bad.append((p, O, sorted(odd), len(J), max(deg, default=0)))
emit(f'Exhaustive path-parity construction check, 2<=p<=16, all even O: '
     f'{total} cases, {len(bad)} violations')
if bad:
    emit('VIOLATIONS (first 10):')
    for b in bad[:10]: emit(f'    {b}')

# cycle-correction bookkeeping (finite facts)
ok_cyc = (4 % 3 == 1) and (5 % 3 == 2) and all((d - 2) % 2 == d % 2 for d in range(2, 10))
emit(f'C4/C5 mod-3 and degree-parity bookkeeping: {"PASS" if ok_cyc else "FAIL"}')

ok = (not bad) and ok_cyc
emit('='*72)
emit(f"VERDICT C6 (Appendix B / E-B): {'PASS' if ok else 'FAIL'}")
emit('='*72)
rep = '\n'.join(OUT)
print(rep)
here = os.path.dirname(os.path.abspath(__file__))
os.makedirs(os.path.join(here, 'results'), exist_ok=True)
with open(os.path.join(here, 'results', 'c6_appendixB_results.txt'), 'w', encoding='utf-8') as f:
    f.write(rep + '\n')
sys.exit(0 if ok else 1)
