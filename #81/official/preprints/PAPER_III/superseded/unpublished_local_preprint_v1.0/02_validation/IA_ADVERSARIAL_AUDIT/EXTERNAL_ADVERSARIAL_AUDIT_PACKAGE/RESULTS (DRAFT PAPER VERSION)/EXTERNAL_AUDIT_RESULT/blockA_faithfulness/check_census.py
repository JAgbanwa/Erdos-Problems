r"""
EXTERNAL ADVERSARIAL AUDIT — Block A (mechanical component): anchor & census checks.

A1 anchors: every ledger node's key hypothesis/constant strings must appear in the
manuscript (LaTeX-normalized). This is PRESENCE evidence; the statement-level
verbatim-equivalence audit is the human-readable table in results/ (auditor reading).

A3 census: every occurrence of an external-theorem name in the manuscript is listed
with its line number, so the "usage localization" claims (AX1 only bulk, AX2 only
sparse, Thm 2.2 only Section 7.2 + Appendix D) are mechanically auditable.

Output: results/blockA_census_results.txt
"""
import sys, os, re

HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.normpath(os.path.join(HERE, '..', '..',
      'EXTERNAL_ADVERSARIAL_AUDIT_PACKAGE'))
PAPER = os.path.join(PKG, 'CLAIMS', 'PAPER_v0.9.5', 'en',
                     'PAPER_III_split_lineal_v0.9.5_review_en.md')
LEDGER = os.path.join(PKG, 'CLAIMS', 'LEDGER.md')

paper = open(PAPER, encoding='utf-8').read()
plines = paper.splitlines()
OUT = []
def emit(x=''): OUT.append(str(x))

ANCHORS = [
    # (node, string that must appear in the manuscript)
    ('E-3.1  F formula',        r'\frac{\binom p2+qd}{3}'),
    ('E-3.1  hypothesis',       r'For \(p\ge3\)'),
    ('E-4.1  cloning',          r'\frac1q\sum_{i=1}^qF(p,q,d_i)'),
    ('E-4.2  hypothesis',       r'Assume \(0<q\le2p\)'),
    ('E-4.2  margin',           r'T(G)+\mu(\alpha)p^2-\frac p4'),
    ('E-4.2  mu low',           r'\alpha^2/12'),
    ('E-4.2  mu high',          r'(2-\alpha)^2/48'),
    ('E-4.2  C_alpha',          r'C_\alpha=\frac{2-2\alpha-\alpha^2}{12}'),
    ('E-5.1  hypothesis',       r'If \(q\ge r_p\)'),
    ('E-5.1  bound',            r'\frac1q\sum_i\binom{d_i}{2}'),
    ('Cor5.3 closed form',      r'\frac{s^2-6s+3}{12}'),
    ('E-5.2  delta',            r'h=\min\{r_p,q-r_p\}'),
    ('E-5.2  V',                r'V=\sum_{e\in E(K)}b_e(q-b_e)'),
    ('E-6.1  hypothesis',       r'If \(2p-3m-1\ge0\)'),
    ('E-6.1  bound',            r'\frac{2p-3m-1}{4}'),
    ('E-7.1  (7.1)',            r'b\ge\chi'),
    ('E-7.1  (7.2)',            r'b-t_i\ge\max\{\rho,u\}'),
    ('E-7.1  theta',            r'\theta_R=\frac{\max\{\rho-1,0\}}{b}'),
    ('E-7.1  kappa',            r'1-2(1-\theta_R)\frac{u}{q}'),
    ('E-7.1  bound',            r'+s\rho-2\rho^2'),
    ('E-8   degree bound',      r'\frac{2n-1}{6}+k'),
    ('E-B   parity set',        r'|O\cap\{x_1,\ldots,x_j\}|'),
    ('E-D.1 kernel lemma',      r'|L(v)|\ge d^+_D(v)+1'),
    ('E-D.3 Galvin max-degree', r'|L(e)|\ge\Delta'),
    ('E-9   contradiction',     r'\frac{n_k^2}{6}+kn_k'),
    ('P10.1 (i) hyp',           r'0\le s\le6\sqrt p'),
    ('P10.1 (i) bound',         r'\frac{n^2}{6}+2n'),
    ('P10.1 (ii) hyp p',        r'p\ge2304'),
    ('P10.1 (ii) hyp s',        r'6\sqrt p\le s\le\frac p8'),
    ('P10.1 (ii) hyp deg',      r'd(v)>\frac{2n-1}{6}+1'),
    ('AX1   statement',         r'\nu_H^*(G)-\nu_H(G)=o(|V(G)|^2)'),
    ('AX2   threshold',         r'\delta(H)\ge(0.9+\varepsilon)|V(H)|'),
    ('Cor1.2 statement',        r'\operatorname{cp}(G)'),
    ('Sharp  family',           r'K_p\vee\overline K_{2p}'),
    ('Sharp  value',            r'\frac{n^2}{6}+\frac n6'),
]

emit('='*76)
emit('Block A — A1 anchor presence check (ledger node -> manuscript string)')
emit('='*76)
miss = 0
norm = paper.replace(' ', '').replace('\n', '')
for name, a in ANCHORS:
    ok = a.replace(' ', '') in norm
    if not ok: miss += 1
    emit(f"[{'PASS' if ok else 'FAIL'}] {name:26s} : {a}")
emit(f'--- anchors present: {len(ANCHORS)-miss}/{len(ANCHORS)}')
emit()

emit('='*76)
emit('Block A/B — A3/B3 census: external-theorem mentions with line numbers')
emit('='*76)
NAMES = ['Theorem 2.1', 'Haxell', 'Theorem 2.3', 'Dross', 'Barber', 'Theorem 2.2',
         'Galvin', 'König', 'Gale', 'Dirac', 'Turán', 'Borodin', 'Yuster', 'Keevash']
for nm in NAMES:
    hits = [i+1 for i, ln in enumerate(plines) if nm in ln]
    emit(f'  {nm:14s}: lines {hits}')
emit()
emit('Interpretation (auditor): load-bearing uses —')
emit('  Thm 2.1 (AX1): line ~594 (Section 4.3) and ~1248 (Section 9.1) ONLY -> bulk only, as claimed.')
emit('  Thm 2.3 (AX2): lines ~1142-1149 (Section 8.3) ONLY -> sparse only, as claimed.')
emit('  Thm 2.2: line ~930 (Section 7.2); proved in Appendix D -> not external, as claimed.')
emit('  Dirac: lines ~1039, ~1078 (Section 8) — classical external input NOT covered by AX1/AX2.')
emit('  Turán: Section 8.3 / Appendix B — classical external input NOT covered by AX1/AX2.')
emit('  chi-prime(K_t) 1-factorization (Section 2.3, eq. 2.2): classical, stated without proof;')
emit('    load-bearing for Lemmas 5.1/5.2/7.1 and hence for Proposition 10.1.')
emit('  Borodin-Kostochka-Woodall: mentioned only to say it is NOT needed -> confirmed not load-bearing.')
emit()

ok_all = (miss == 0)
emit(f"VERDICT (mechanical component): {'PASS' if ok_all else 'FAIL'} "
     f"({len(ANCHORS)-miss}/{len(ANCHORS)} anchors)")
rep = '\n'.join(OUT)
print(rep)
os.makedirs(os.path.join(HERE, 'results'), exist_ok=True)
with open(os.path.join(HERE, 'results', 'blockA_census_results.txt'), 'w', encoding='utf-8') as f:
    f.write(rep + '\n')
sys.exit(0 if ok_all else 1)
