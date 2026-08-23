r"""
EXTERNAL ADVERSARIAL AUDIT — Block C, attack C3 (+C5): Lemmas 5.1/5.2/6.1/7.1,
Corollary 5.3, and the sharpness family, on concrete split graphs.

All the audited lemmas assert LOWER bounds on nu3(G) (equivalently upper bounds
on Phi(G) = |E| - 2 nu3(G)). Logic of the attack, per instance:

  1. Compute the claimed bound exactly (rationals).
  2. Search for an edge-disjoint triangle packing of the required size
     (greedy + randomized restarts + local (1-out, 2-in) improvement).
     If found: the claim is CONFIRMED for that instance by an explicit
     packing certificate (verified edge-disjoint, verified subgraph).
  3. If NOT found: escalate to my own EXACT branch-and-bound for nu3(G)
     (independent of PuLP/CBC). If exact nu3 violates the bound -> genuine
     COUNTEREXAMPLE (reported, exits nonzero). Else the instance is confirmed.
  4. Additionally, on every instance where the exact B&B ran, cross-check
     nu3 against PuLP+CBC (the internal audit's tool), verifying solver
     status is 'Optimal' — this doubles as Block E tool validation.

Instance families (adversarial):
  - all common-profile graphs, p in 3..6, q in 1..7, every d
  - staircase, alternating, nested-chain, sunflower, complement-pairs profiles
  - 300 random profiles p in 3..7, q in 1..8 (uniform random N_i)
  - dispersion extremes: all S_i equal (low D) vs spread singleton S_i (high D)
  - Lemma 7.1: every candidate center R = S_j and R = emptyset for instances
    satisfying (7.1)-(7.2), exact hypothesis check before applying.
  - C5 sharpness: K_p v bar-K_{2p} for p in 3..24: constructive factorization
    packing gives nu3 >= C(p,2); the split structure forces nu3 <= C(p,2)
    (every triangle of a split graph contains a clique edge — verified per
    triangle); hence nu3 = C(p,2) and Phi = n^2/6 + n/6 exactly.

Every claim check states its hypothesis test explicitly; instances failing a
lemma's hypothesis are counted as NOT-APPLICABLE, never as PASS.

Output: results/c3_lemmas_results.txt
"""
import sys, os, random, time
from fractions import Fraction as Q
from itertools import combinations

random.seed(8181)
OUT = []
def emit(x=''): OUT.append(str(x))
def C2i(x): return x*(x-1)//2

def rp_of(t):
    if t <= 1: return 0
    return t-1 if t % 2 == 0 else t

# ------------------------------------------------------------ graph machinery
class Split:
    def __init__(self, p, neigh):
        self.p = p
        self.neigh = [frozenset(N) for N in neigh]
        self.q = len(neigh)
        self.edges = [frozenset(e) for e in combinations(range(p), 2)]
        for i, N in enumerate(self.neigh):
            v = p + i
            for x in N:
                self.edges.append(frozenset((x, v)))
        self.eset = set(self.edges)
        self.tris = [frozenset(t) for t in combinations(range(p), 3)]
        for i, N in enumerate(self.neigh):
            v = p + i
            for a, b in combinations(sorted(N), 2):
                self.tris.append(frozenset((a, b, v)))
        self.E = len(self.edges)

    def tri_edges(self, t):
        return [frozenset(e) for e in combinations(sorted(t), 2)]

def verify_packing(G, pack):
    used = set()
    for t in pack:
        for e in G.tri_edges(t):
            if e not in G.eset or e in used:
                return False
            used.add(e)
    return True

def greedy_packing(G, target, tries=60):
    """Randomized greedy + (1-out,2-in) local search; returns packing or None."""
    tris = G.tris
    best = []
    for it in range(tries):
        order = list(range(len(tris)))
        random.shuffle(order)
        used = set()
        pack = []
        for ti in order:
            te = G.tri_edges(tris[ti])
            if all(e not in used for e in te):
                pack.append(tris[ti]); used.update(te)
        # local improvement: remove 1, add 2
        improved = True
        while improved and len(pack) < target:
            improved = False
            for k in range(len(pack)):
                rem = pack[k]
                used2 = set(used)
                for e in G.tri_edges(rem): used2.discard(e)
                adds = []
                for t in tris:
                    if t == rem: continue
                    te = G.tri_edges(t)
                    if all(e not in used2 for e in te):
                        adds.append((t, te))
                        used2.update(te)
                        if len(adds) == 2: break
                if len(adds) == 2:
                    pack.pop(k)
                    for t, te in adds: pack.append(t)
                    used = set()
                    for t in pack: used.update(G.tri_edges(t))
                    improved = True
                    break
        if len(pack) > len(best): best = pack
        if len(best) >= target: return best
    return best if len(best) >= target else None

def nu3_exact_bb(G, ub_hint=None):
    """Exact nu3 by branch and bound over triangles (bitmask edges)."""
    eid = {e: i for i, e in enumerate(G.edges)}
    tmask = []
    for t in G.tris:
        mk = 0
        for e in G.tri_edges(t): mk |= 1 << eid[e]
        tmask.append(mk)
    tmask.sort(key=lambda mk: -bin(mk).count('1'))
    ntri = len(tmask)
    best = len(greedy_packing(G, 10**9, tries=20) or [])
    # DFS
    def ub(i, used):
        cnt = 0
        for j in range(i, ntri):
            if not (tmask[j] & used): cnt += 1
        return cnt
    import sys as _s
    _s.setrecursionlimit(10000)
    def dfs(i, used, cur):
        nonlocal best
        if cur > best: best = cur
        if i >= ntri: return
        # cheap bound
        rem = 0
        free_e = 0
        for j in range(i, ntri):
            if not (tmask[j] & used): rem += 1
        if cur + rem <= best: return
        for j in range(i, ntri):
            if not (tmask[j] & used):
                dfs(j + 1, used | tmask[j], cur + 1)
                # also allow skipping implicitly via loop; prune:
                rem -= 1
                if cur + rem <= best: return
    dfs(0, 0, 0)
    return best

def nu3_cbc(G):
    try:
        import pulp
    except ImportError:
        return None, 'no-pulp'
    prob = pulp.LpProblem('nu3', pulp.LpMaximize)
    x = [pulp.LpVariable(f'x{i}', cat='Binary') for i in range(len(G.tris))]
    prob += pulp.lpSum(x)
    eid = {}
    for ti, t in enumerate(G.tris):
        for e in G.tri_edges(t):
            eid.setdefault(e, []).append(x[ti])
    for e, xs in eid.items():
        prob += pulp.lpSum(xs) <= 1
    status = prob.solve(pulp.PULP_CBC_CMD(msg=0))
    return int(round(pulp.value(prob.objective) or 0)), pulp.LpStatus[status]

# ------------------------------------------------------------ claimed bounds
def bounds_for(G):
    p, q = G.p, G.q
    d = [len(N) for N in G.neigh]
    m_list = [p - di for di in d]
    M = sum(m_list); S2v = sum(x*x for x in m_list); mmax = max(m_list) if m_list else 0
    n = p + q; s = 2*p - q
    r_p = rp_of(p)
    out = {}
    if q >= r_p and q >= 1:
        out['E-5.1'] = Q(sum(C2i(x) for x in d), q)              # nu3 >= this
        out['Cor5.3_Phi'] = Q(n*n, 6) + Q(p, 2) + Q(s*s - 6*s + 3, 12)
        # Lemma 5.2
        b_e = {}
        for e in combinations(range(p), 2):
            b_e[e] = sum(1 for N in G.neigh if not set(e) <= N)
        V = sum(be*(q - be) for be in b_e.values())
        h = min(r_p, q - r_p); delta = Q(h, r_p)
        out['L5.2_Phi'] = (Q(n*n, 6) + Q(p, 2) - Q(s*s, 6)
                           + Q((s-1)*M - S2v, q) - 2*delta*Q(V, q*(q-1)) if q >= 2 else None)
        out['V'] = V
    out['meta'] = (p, q, d, m_list, M, S2v, mmax, n, s)
    return out

def lemma71_bound(G, R):
    """Check (7.1)-(7.2) for center R; return Phi bound or None if hypotheses fail."""
    p, q = G.p, G.q
    n = p + q; s = 2*p - q
    rho = len(R); b = p - rho
    r_b = rp_of(b); u = q - r_b
    if not (b >= 2 and q >= r_b and b >= rp_of(rho)):
        return None
    t_list = [len((set(range(p)) - N) - R) for N in G.neigh]      # t_i = |S_i \ R|
    g_list = [len(R - (set(range(p)) - N)) for N in G.neigh]      # g_i = |R \ S_i|
    if any(b - ti < max(rho, u) for ti in t_list):
        return None
    A_R = sum(t_list); A2R = sum(x*x for x in t_list); B_R = sum(g_list)
    theta = Q(max(rho - 1, 0), b)
    kappa = 1 - 2*(1 - theta)*Q(u, q)
    return (Q(n*n, 6) + Q(p, 2) - Q(s*s, 6) + s*rho - 2*rho*rho
            + kappa*B_R + Q(1, q)*((s - 2*rho - 1)*A_R - A2R))

# ------------------------------------------------------------ instance families
def gen_instances():
    inst = []
    for p in range(3, 7):
        Ksub = [frozenset(c) for k in range(p + 1) for c in combinations(range(p), k)]
        for q in range(1, 8):
            if p >= 6 and q >= 6: continue          # size control
            for N in (Ksub if p <= 5 else random.sample(Ksub, min(12, len(Ksub)))):
                inst.append(('common', p, [N]*q))
            inst.append(('stair', p, [frozenset(range(i % (p + 1))) for i in range(q)]))
            half = frozenset(range((p + 1)//2))
            full = frozenset(range(p))
            inst.append(('alt', p, [ [full, frozenset(), half][i % 3] for i in range(q)]))
            inst.append(('nested', p, [frozenset(range(min(p, i + 1))) for i in range(q)]))
            # sunflower: common core + distinct petals
            core = frozenset(range(p//2))
            inst.append(('sunflower', p, [core | {p//2 + (i % max(1, p - p//2))} if p//2 + (i % max(1, p-p//2)) < p else core for i in range(q)]))
            # complement pairs
            inst.append(('comp', p, [frozenset(range(p)) - frozenset({i % p}) if i % 2 == 0 else frozenset({i % p}) for i in range(q)]))
            # dispersion extremes
            inst.append(('lowD', p, [full - frozenset({0}) for _ in range(q)]))
            inst.append(('highD', p, [full - frozenset({i % p}) for i in range(q)]))
    for _ in range(300):
        p = random.randint(3, 7); q = random.randint(1, 8)
        if p >= 6 and q >= 6: continue
        inst.append(('rand', p, [frozenset(x for x in range(p) if random.random() < random.random())
                                 for _ in range(q)]))
    # dedupe
    seen = set(); out = []
    for tag, p, neigh in inst:
        key = (p, tuple(sorted(tuple(sorted(N)) for N in neigh)))
        if key in seen: continue
        seen.add(key); out.append((tag, p, neigh))
    return out

# ------------------------------------------------------------ main loop
counters = {k: [0, 0, 0] for k in ('E-5.1', 'Cor5.3', 'L5.2', 'L7.1')}  # [applicable, confirmed, refuted]
counterexamples = []
exact_runs = 0
cbc_checked = 0
cbc_mismatch = []
t0 = time.time()
instances = gen_instances()
emit(f'Generated {len(instances)} distinct split-graph instances.')

for (tag, p, neigh) in instances:
    G = Split(p, neigh)
    B = bounds_for(G)
    checks = []                                        # (name, nu3_lower_needed)
    if 'E-5.1' in B:
        checks.append(('E-5.1', B['E-5.1']))
        checks.append(('Cor5.3', (Q(G.E) - B['Cor5.3_Phi'])/2))
        if B['L5.2_Phi'] is not None:
            checks.append(('L5.2', (Q(G.E) - B['L5.2_Phi'])/2))
    # Lemma 7.1 candidate centers
    l71 = []
    cands = {frozenset()} | {frozenset(set(range(p)) - N) for N in G.neigh}
    for R in cands:
        bound = lemma71_bound(G, set(R))
        if bound is not None:
            l71.append((R, (Q(G.E) - bound)/2))
    for R, need in l71:
        checks.append(('L7.1', need))

    if not checks: continue
    need_max = max(need for _nm, need in checks)
    import math
    target = max(0, math.ceil(need_max))
    pack = greedy_packing(G, target)
    nu3 = None
    if pack is None:
        nu3 = nu3_exact_bb(G)
        exact_runs += 1
        v_cbc, st = nu3_cbc(G)
        if v_cbc is not None:
            cbc_checked += 1
            if st != 'Optimal' or v_cbc != nu3:
                cbc_mismatch.append((tag, p, [sorted(N) for N in neigh], nu3, v_cbc, st))
    else:
        assert verify_packing(G, pack), 'internal error: invalid packing certificate'
    got = Q(len(pack)) if pack is not None else Q(nu3)
    for nm, need in checks:
        key = nm
        counters[key][0] += 1
        if got >= need:
            counters[key][1] += 1
        else:
            counters[key][2] += 1
            counterexamples.append((nm, tag, p, [sorted(N) for N in neigh],
                                    'nu3=' + str(got), 'needed>=' + str(need)))

emit(f'Instance loop done in {time.time()-t0:.0f}s; exact B&B escalations: {exact_runs}; '
     f'CBC cross-checks: {cbc_checked}, mismatches: {len(cbc_mismatch)}')
emit()
for k, (ap, cf, rf) in counters.items():
    emit(f'  {k:8s}: applicable {ap:5d}  confirmed {cf:5d}  REFUTED {rf}')
emit()

# ---------------------------------------------------------- forced exact sample
# The greedy certificates above CONFIRM the bounds but never exercise the exact
# path. Here we force exact nu3 (own B&B) on a subsample, re-test every
# applicable bound against the EXACT optimum (maximum refutation power), and
# cross-validate PuLP+CBC (status must be 'Optimal' and values must agree).
t0 = time.time()
sample = [inst for inst in instances if inst[1] <= 5 and len(inst[2]) <= 6]
random.shuffle(sample)
sample = sample[:40]
exact_viol = []
vac = 0; nonvac = 0
for (tag, p, neigh) in sample:
    G = Split(p, neigh)
    nu3 = nu3_exact_bb(G)
    v_cbc, st = nu3_cbc(G)
    if v_cbc is not None:
        cbc_checked += 1
        if st != 'Optimal' or v_cbc != nu3:
            cbc_mismatch.append((tag, p, [sorted(N) for N in neigh], nu3, v_cbc, st))
    B = bounds_for(G)
    todo = []
    if 'E-5.1' in B:
        todo.append(('E-5.1', B['E-5.1']))
        todo.append(('Cor5.3', (Q(G.E) - B['Cor5.3_Phi'])/2))
        if B['L5.2_Phi'] is not None:
            todo.append(('L5.2', (Q(G.E) - B['L5.2_Phi'])/2))
    cands = {frozenset()} | {frozenset(set(range(p)) - N) for N in G.neigh}
    for R in cands:
        bnd = lemma71_bound(G, set(R))
        if bnd is not None:
            todo.append(('L7.1', (Q(G.E) - bnd)/2))
    for nm, need in todo:
        if need <= 0: vac += 1
        else: nonvac += 1
        if Q(nu3) < need:
            exact_viol.append((nm, tag, p, [sorted(N) for N in neigh], nu3, str(need)))
emit(f'Forced exact-nu3 sample: {len(sample)} instances re-tested against the EXACT '
     f'optimum  [{time.time()-t0:.0f}s]')
emit(f'    exact violations: {len(exact_viol)}')
emit(f'    bound-target vacuity on the sample: {vac} targets <= 0 (trivially met), '
     f'{nonvac} strictly positive (informative)')
emit(f'    CBC cross-checks total: {cbc_checked}, mismatches: {len(cbc_mismatch)}')
counterexamples.extend(exact_viol)
emit()

# ------------------------------------------------------------ C5 sharpness
def factorization_Kp(p):
    """1-factorization (p even, p-1 rounds) or near-1-fact. (p odd, p rounds), circle method."""
    if p % 2 == 0:
        rounds = []
        arr = list(range(p))
        for r_ in range(p - 1):
            pairs = [(arr[0], arr[-1])] + [(arr[i], arr[-1 - i]) for i in range(1, p//2)]
            rounds.append([tuple(sorted(pr)) for pr in pairs])
            arr = [arr[0]] + [arr[-1]] + arr[1:-1]
        return rounds
    rounds_ = factorization_Kp(p + 1)
    return [[e for e in rd if p not in e] for rd in rounds_]

sharp_fail = []
maxratio = None
for p in range(3, 25):
    q = 2*p
    rounds = factorization_Kp(p)
    assert len(rounds) == rp_of(p)
    # each factor -> a distinct independent vertex (full neighborhood)
    pack = []
    for j, rd in enumerate(rounds):
        v = p + j
        for (a, b) in rd:
            pack.append(frozenset((a, b, v)))
    G = Split(p, [frozenset(range(p))]*q)
    okpack = verify_packing(G, pack) and len(pack) == C2i(p)
    # upper bound: every triangle contains a clique edge (I independent) => nu3 <= C(p,2)
    tri_ok = all(sum(1 for v_ in t if v_ < p) >= 2 for t in G.tris)
    n = 3*p
    phi = G.E - 2*C2i(p)
    closed = (Q(phi) == Q(n*n, 6) + Q(n, 6))
    if not (okpack and tri_ok and closed):
        sharp_fail.append((p, okpack, tri_ok, closed))
    ratio = (Q(phi) - Q(n*n, 6)) / n
    maxratio = ratio if maxratio is None else max(maxratio, ratio)
emit(f'C5 sharpness K_p v bar-K_2p, p=3..24: '
     f'{"PASS — nu3 = C(p,2) certified (packing + clique-edge argument), Phi = n^2/6 + n/6 exact" if not sharp_fail else "FAIL"}')
if sharp_fail: emit(f'    failures: {sharp_fail}')
emit(f'    (Phi - n^2/6)/n on the family: {maxratio} (= 1/6, the claimed linear term)')
emit()

# exact nu3 on tiny extremal instances (independent confirmation nu3 == C(p,2))
tiny_ok = True
for p in (3, 4):
    G = Split(p, [frozenset(range(p))]*(2*p))
    v = nu3_exact_bb(G)
    if v != C2i(p): tiny_ok = False; emit(f'    exact nu3 mismatch at p={p}: {v} != {C2i(p)}')
emit(f'C5b exact B&B confirms nu3(K_p v bar-K_2p) == C(p,2) for p=3,4: {"PASS" if tiny_ok else "FAIL"}')
emit()

ok = (not counterexamples) and (not cbc_mismatch) and (not sharp_fail) and tiny_ok
if counterexamples:
    emit('COUNTEREXAMPLES:')
    for c in counterexamples[:20]: emit(f'    {c}')
if cbc_mismatch:
    emit('CBC MISMATCHES (Block E tool validation):')
    for c in cbc_mismatch[:20]: emit(f'    {c}')
emit('='*72)
emit(f"VERDICT C3/C5: {'PASS — no counterexample to E-5.1 / Cor 5.3 / L5.2 / L7.1 / sharpness' if ok else 'FAIL'}")
emit('='*72)

rep = '\n'.join(OUT)
print(rep)
here = os.path.dirname(os.path.abspath(__file__))
os.makedirs(os.path.join(here, 'results'), exist_ok=True)
with open(os.path.join(here, 'results', 'c3_lemmas_results.txt'), 'w', encoding='utf-8') as f:
    f.write(rep + '\n')
sys.exit(0 if ok else 1)
