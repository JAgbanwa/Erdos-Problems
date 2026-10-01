"""E5 exhaustive small-graph tests on the networkx atlas (all graphs up to isomorphism, n<=7):
T12 (Lemma F.3a), T13 (F.7), T14 (F.9), T15 (Prop 6.4 with exact LP certificates), T20 (combinatorial claim),
T21b ((1.3a) on random partitions, (2.4) on exact W*), T23 ((G.4) chordal K4-free n<=8), and a supplementary
(non-predeclared) check S1 of identity (6.7b) and inequality (6.16) on random clique partitions."""
import sys, os, time, random, itertools
from fractions import Fraction as Fr
import networkx as nx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e5lib import *

OUT = {}
T0 = time.time()
atlas = nx.graph_atlas_g()
graphs = [from_nx(g) for g in atlas]
print('graphs', len(graphs))

# ---------------------------------------------------------------- rsd for all atlas graphs (+ chordal cross-check)
t0 = time.time()
RSD = []
chordal_mismatch = []
for i, (n, adj) in enumerate(graphs):
    r = rsd(n, adj)
    RSD.append(r)
    ch = nx.is_chordal(atlas[i]) if n > 0 else True
    if (r == 0) != ch:
        chordal_mismatch.append(i)
dist = {}
for r in RSD:
    dist[r] = dist.get(r, 0) + 1
t_rsd = time.time() - t0
print('rsd done', dist, 'chordal mismatches', chordal_mismatch, round(t_rsd, 1))
# a few named sanity values
named = {}
for name, g in [('C4', nx.cycle_graph(4)), ('C5', nx.cycle_graph(5)), ('K33', nx.complete_bipartite_graph(3, 3)),
                ('octahedron', nx.complete_multipartite_graph(2, 2, 2)), ('C6', nx.cycle_graph(6)), ('K7', nx.complete_graph(7))]:
    named[name] = rsd(*from_nx(g))
print('named rsd', named)
OUT['RSD_atlas'] = {'distribution': dist, 'chordal_iff_rsd0_mismatches': chordal_mismatch, 'named': named, 'runtime_s': round(t_rsd, 2)}
dump('atlas_rsd.json', {'rsd': RSD})

# ---------------------------------------------------------------- T12  Lemma F.3a
t0 = time.time()
viol, negfail, checked = [], [], 0
tight = 0
for i, (n, adj) in enumerate(graphs):
    s = RSD[i]
    om = Omega(adj)
    for D in range(1 << n):
        w = om(D)
        o = ordNE(D, adj)
        k = popcount(D)
        checked += 1
        lhs = max(k - w - s, 0) ** 2
        if lhs > o:
            viol.append((i, D))
        if lhs == o and lhs > 0:
            tight += 1
        if s >= 1:
            lhs2 = max(k - w - (s - 1), 0) ** 2
            if lhs2 > o:
                negfail.append((i, D, n, s, k, w, o))
OUT['T12'] = dict(id='T12', claim='Lemma F.3a (F.5a): rsd<=s => every D contains a clique C with (|D|-|C|-s)_+^2 <= ordNE(G,D)',
                  manuscript_lines='2190-2209', method='all atlas graphs n<=7, s=rsd(G) (strongest admissible s; larger s is weaker), all 2^n subsets D, C = maximum clique of G[D]',
                  evidence_type='finite exhaustive', parameters={'n': [0, 7], 'graphs': len(graphs)},
                  details={'pairs_checked': checked, 'violations': viol[:10], 'nontrivial_equality_cases': tight},
                  result='PASS' if not viol else 'FAIL',
                  negative_control={'description': 'replace s by s-1 (graphs with rsd>=1) must fail somewhere', 'failures_found': len(negfail),
                                    'examples(i,D,n,s,|D|,omega,ordNE)': negfail[:5],
                                    'result': 'PASS (rejected)' if negfail else 'FAIL (accepted) -> test lacks power at n<=7'},
                  runtime_s=round(time.time() - t0, 2))
print('T12', OUT['T12']['result'], OUT['T12']['negative_control']['result'])

# ---------------------------------------------------------------- T13  (F.7)
t0 = time.time()
viol, maxratio, nonzero = [], Fr(0), 0
for i, (n, adj) in enumerate(graphs):
    s = RSD[i]
    for k in range(4, n + 1):
        cyc = 0
        for S in itertools.combinations(range(n), k):
            mask = sum(1 << v for v in S)
            if all(popcount(adj[v] & mask) == 2 for v in S):
                # connected?
                seen = 1 << S[0]; frontier = seen
                while frontier:
                    nb = 0
                    for v in bits(frontier):
                        nb |= adj[v] & mask
                    frontier = nb & ~seen
                    seen |= nb
                if seen == mask:
                    cyc += 1
        emb = 2 * k * cyc
        bound = 2 * k * s * n ** (k - 1)
        if emb > bound:
            viol.append((i, k, emb, bound))
        if emb:
            nonzero += 1
            maxratio = max(maxratio, Fr(emb, bound))
OUT['T13'] = dict(id='T13', claim='(F.7) indCopies(C_k,G) <= 2ks n^{k-1} (labelled induced embeddings), k>=4', manuscript_lines='2261-2266',
                  method='all atlas graphs n<=7, s=rsd(G), all k=4..n; induced k-cycles counted by vertex subsets x 2k labellings', evidence_type='finite exhaustive (weak test)',
                  parameters={'n': [0, 7]}, details={'violations': viol[:10], 'instances_with_induced_cycles': nonzero, 'max_ratio_emb/bound': str(maxratio),
                                                     'note': 'for s=0 the bound forces zero induced cycles (chordal); ratio far below 1 so the test has little power'},
                  result='PASS' if not viol else 'FAIL', negative_control={'description': 'none predeclared (weak test)', 'result': 'N/A'},
                  runtime_s=round(time.time() - t0, 2))
print('T13', OUT['T13']['result'])

# ---------------------------------------------------------------- T14  (F.9)
t0 = time.time()
viol, neg, checked = [], [], 0
for i, (n, adj) in enumerate(graphs):
    if RSD[i] != 0:
        continue
    om = Omega(adj)
    for D in range(1 << n):
        d = popcount(D); w = om(D)
        Mne = ordNE(D, adj) // 2
        checked += 1
        if (d - w) ** 2 > 2 * Mne:
            viol.append((i, D))
        if (d - w) ** 2 > Mne:
            neg.append((i, D))
OUT['T14'] = dict(id='T14', claim='(F.9) G[D] chordal => D contains a clique C with (d-|C|)^2 <= 2M (M unordered nonedges)', manuscript_lines='2275-2280',
                  method='all chordal atlas graphs n<=7 (chordality = rsd 0, cross-checked with networkx), all subsets D (induced subgraphs chordal), C=max clique',
                  evidence_type='finite exhaustive', parameters={'n': [0, 7], 'chordal_graphs': sum(1 for r in RSD if r == 0)},
                  details={'pairs_checked': checked, 'violations': viol[:10]},
                  result='PASS' if not viol else 'FAIL',
                  negative_control={'description': '(not predeclared; added) factor 1 instead of 2 must fail somewhere', 'failures': len(neg),
                                    'result': 'PASS (rejected)' if neg else 'FAIL (accepted)'},
                  runtime_s=round(time.time() - t0, 2))
print('T14', OUT['T14']['result'])

# ---------------------------------------------------------------- T15  Prop 6.4 with exact W*
t0 = time.time()
WS = []
status_count = {}
viol22, viol23, inconcl = [], [], []
slack22, slack23 = None, None
neg23 = []
checked22 = checked23 = 0
for i, (n, adj) in enumerate(graphs):
    W, x, y, st = exact_Wstar(n, adj)
    status_count[st] = status_count.get(st, 0) + 1
    e = len(edges_of(n, adj))
    WS.append((str(W), st))
    if st != 'exact':
        inconcl.append(i)
        continue
    F4 = e - W
    for s in range(RSD[i], n + 1):
        b22 = M(n - s) + n * s
        checked22 += 1
        if F4 > b22:
            viol22.append((i, s, str(F4), b22))
        sl = b22 - F4
        slack22 = sl if slack22 is None else min(slack22, sl)
        if 4 * s <= n:
            b23 = b22 - C2(s + 1)
            checked23 += 1
            if F4 > b23:
                viol23.append((i, s, str(F4), b23))
            sl = b23 - F4
            slack23 = sl if slack23 is None else min(slack23, sl)
        else:
            # control: the refined bound outside its band
            if F4 > M(n - s) + n * s - C2(s + 1):
                neg23.append((i, n, s, str(F4)))
res = 'PASS' if (not viol22 and not viol23 and not inconcl) else ('FAIL' if (viol22 or viol23) else 'INCONCLUSIVE')
OUT['T15'] = dict(id='T15', claim='Prop 6.4: rsd<=s<=n => F_4 <= M(n-s)+ns (6.22); 4s<=n => F_4 <= M(n-s)+ns-C(s+1,2) (6.23)', manuscript_lines='1058-1070, 2148-2177',
                  method='all atlas graphs n<=7; W* by HiGHS then exact rational reconstruction of primal x and dual y, both verified exactly with equal objective; all s in [rsd(G), n]',
                  evidence_type='finite exhaustive; each LP value exact (verified primal+dual certificate)', parameters={'n': [0, 7]},
                  details={'lp_status_counts': status_count, 'checked_6.22': checked22, 'checked_6.23': checked23, 'viol_6.22': viol22[:5], 'viol_6.23': viol23[:5],
                           'min_slack_6.22': str(slack22), 'min_slack_6.23': str(slack23), 'inconclusive_graph_indices': inconcl[:10]},
                  result=res,
                  negative_control={'description': '(not predeclared) power check: refined bound (6.23) applied outside its band 4s<=n; violations there show the band is not vacuous',
                                    'violations_outside_band': len(neg23), 'examples(i,n,s,F4)': neg23[:5],
                                    'result': 'INFO (violations outside band exist)' if neg23 else 'INFO (no violations outside band at n<=7)'},
                  runtime_s=round(time.time() - t0, 2))
print('T15', res, status_count, 'slack', slack22, slack23, 'neg23', len(neg23))
dump('atlas_Wstar.json', {'Wstar': WS})

# ---------------------------------------------------------------- T21b  (1.3a) on random partitions; (2.4) on exact W*
t0 = time.time()
rng = random.Random(20260930)


def random_clique_partition(n, adj, rng):
    E = edges_of(n, adj)
    unc = set(E)
    pieces = []
    order = E[:]
    rng.shuffle(order)
    for (u, v) in order:
        if (u, v) not in unc:
            continue
        K = (1 << u) | (1 << v)
        cand = [w for w in range(n) if w not in (u, v)]
        rng.shuffle(cand)
        for w in cand:
            if rng.random() < 0.7 and all((min(w, z), max(w, z)) in unc for z in bits(K)):
                K |= 1 << w
        for p in pairs_of(K):
            unc.discard(p)
        pieces.append(K)
    return pieces


bad13a, bad24, nrand = [], [], 0
for i, (n, adj) in enumerate(graphs):
    W = Fr(WS[i][0]); e = len(edges_of(n, adj))
    if WS[i][1] == 'exact' and not (6 * W <= 5 * e):
        bad24.append(i)
    for rep in range(3):
        P = random_clique_partition(n, adj, rng)
        ok, why = verify_partition(n, adj, P)
        assert ok, why
        nrand += 1
        if sum(C2(popcount(K)) - 1 for K in P) + len(P) != e:
            bad13a.append(i)
OUT['T21b'] = dict(id='T21b', claim='(1.3a) g(Q)+|Q|=e(G) for clique partitions; (2.4) W*<=5e/6', manuscript_lines='128-138, 234-238',
                   method='random clique partitions (3 per atlas graph, exactly verified) and all exact W* values', evidence_type='finite (random sample) / exact',
                   parameters={'random_partitions': nrand}, details={'fail_1.3a': bad13a[:5], 'fail_2.4': bad24[:5]},
                   result='PASS' if not bad13a and not bad24 else 'FAIL', negative_control={'description': 'none', 'result': 'N/A'}, runtime_s=round(time.time() - t0, 2))
print('T21b', OUT['T21b']['result'])

# ---------------------------------------------------------------- T20  combinatorial claim of CoreCliqueAlternative
t0 = time.time()
viol = []
maxe = {1: 0, 2: 0}
cnt = {1: 0, 2: 0}
for i, (n, adj) in enumerate(graphs):
    g = atlas[i]
    Delta = max((d for _, d in g.degree()), default=0)
    nu = len(nx.max_weight_matching(g, maxcardinality=True)) if g.number_of_edges() else 0
    e = g.number_of_edges()
    for s in (1, 2):
        if Delta <= 2 * s and nu <= s:
            cnt[s] += 1
            maxe[s] = max(maxe[s], e)
            if e > (4 * s + 1) * s:
                viol.append((i, s, e))
# information: (E.12) directly on missing graphs F on c<=7 vertices, ignoring c>=20(s+1)^2
e12_fail = []
for i, (c, adj) in enumerate(graphs):
    g = atlas[i]
    if c == 0:
        continue
    nu = len(nx.max_weight_matching(g, maxcardinality=True)) if g.number_of_edges() else 0
    # G[S] = complement of F ; clique of G[S] of size c-s  <=> independent set of F of size c-s
    alpha = max(popcount(I) for I in all_cliques(c, [((1 << c) - 1) & ~adj[v] & ~(1 << v) for v in range(c)], 1, None)) if c else 0
    eS = C2(c) - g.number_of_edges()
    for s in range(0, 3):
        if nu <= s:
            if not (alpha >= c - s or c - s <= 2 * (eS - C2(c - s))):
                e12_fail.append((i, c, s))
OUT['T20b'] = dict(id='T20b', claim='CoreCliqueAlternative step (E.12 proof): missing graph with max degree <=2s and no matching of size s+1 has <=(4s+1)s edges',
                   manuscript_lines='2076-2081', method='all atlas graphs n<=7 as missing graphs, s in {1,2}; for s=1 this is complete (edges lie in a vertex cover of size <=2s with degrees <=2s, so <=2s+4s^2=6 non-isolated vertices); s=2 continued by SAT in t_sat.py',
                   evidence_type='finite exhaustive (complete for s=1; n<=7 for s=2)', parameters={'n': [0, 7], 's': [1, 2]},
                   details={'graphs_satisfying_hypothesis': cnt, 'max_edges_found': maxe, 'bounds': {1: 5, 2: 18}, 'violations': viol[:5],
                            'INFO_(E.12)_without_size_hypothesis_failures(i,c,s)': e12_fail[:10], 'INFO_(E.12)_failures_count': len(e12_fail)},
                   result='PASS' if not viol else 'FAIL',
                   negative_control={'description': '(added, not predeclared) corrupted bound e<=2s must fail somewhere (e.g. triangle for s=1, K5 for s=2); note the true maxima found are far below (4s+1)s, so the test has limited power',
                                     'result': 'PASS (rejected)' if (maxe[1] > 2 and maxe[2] > 4) else 'FAIL (accepted)'},
                   runtime_s=round(time.time() - t0, 2))
print('T20b', OUT['T20b']['result'], maxe, 'E12 info fails', len(e12_fail))

# ---------------------------------------------------------------- T23  (G.4) chordal K4-free n<=8
t0 = time.time()
viol, neg, cnt, maxe = [], [], 0, {}
base7 = []
for i, (n, adj) in enumerate(graphs):
    if RSD[i] != 0:
        continue
    if all_cliques(n, adj, 4, 4):
        continue
    e = len(edges_of(n, adj))
    cnt += 1
    maxe[n] = max(maxe.get(n, 0), e)
    if n >= 2 and e > 2 * n - 3:
        viol.append((n, i))
    if n >= 2 and e > 2 * n - 4:
        neg.append((n, i))
    if n == 7:
        base7.append(adj)
# n = 8 by simplicial extension (every chordal graph has a simplicial vertex; K4-free => its neighbourhood is a clique of size <=2)
cnt8 = 0
for adj in base7:
    n = 7
    attach = [0] + [1 << v for v in range(n)] + [(1 << u) | (1 << v) for u in range(n) for v in range(u + 1, n) if adj[u] >> v & 1]
    for A in attach:
        adj8 = adj[:] + [A]
        for v in bits(A):
            adj8[v] |= 1 << 7
        e = len(edges_of(8, adj8))
        cnt8 += 1
        maxe[8] = max(maxe.get(8, 0), e)
        if e > 2 * 8 - 3:
            viol.append((8, A))
        if e > 2 * 8 - 4:
            neg.append((8, A))
# sanity: extension graphs are chordal
g8_sample_chordal = True
for adj in base7[:50]:
    A = [(1 << u) | (1 << v) for u in range(7) for v in range(u + 1, 7) if adj[u] >> v & 1][:1] or [0]
    adj8 = adj[:] + [A[0]]
    for v in bits(A[0]):
        adj8[v] |= 1 << 7
    g8 = nx.Graph(); g8.add_nodes_from(range(8)); g8.add_edges_from(edges_of(8, adj8))
    g8_sample_chordal &= nx.is_chordal(g8)
OUT['T23'] = dict(id='T23', claim='(G.4) chordal K4-free, n>=2 => e<=2n-3; (G.5) algebra => n<=20/eps', manuscript_lines='2390-2402',
                  method='all chordal K4-free atlas graphs n<=7; n=8 by all simplicial extensions of 7-vertex ones (complete up to isomorphism); (G.5) by z3 in t_integer.py',
                  evidence_type='finite exhaustive + exact (NRA)', parameters={'n': [2, 8]},
                  details={'graphs_n<=7': cnt, 'extensions_n=8': cnt8, 'max_edges_by_n': maxe, 'violations': viol[:5], 'sample_extensions_chordal': g8_sample_chordal},
                  result='PASS' if not viol else 'FAIL',
                  negative_control={'description': 'bound 2n-4 must fail (2-trees attain 2n-3)', 'failures': len(neg), 'result': 'PASS (rejected)' if neg else 'FAIL (accepted)'},
                  runtime_s=round(time.time() - t0, 2))
print('T23', OUT['T23']['result'], maxe)

# ---------------------------------------------------------------- S1 supplementary: (6.7b) and (6.16) on random partitions
t0 = time.time()
bad67b, bad616, n67, n616 = [], [], 0, 0
for trial in range(4000):
    n = rng.randint(4, 9)
    p = rng.choice([0.3, 0.5, 0.7, 0.85])
    E = [(u, v) for u in range(n) for v in range(u + 1, n) if rng.random() < p]
    n, adj = from_edges(n, E)
    P = random_clique_partition(n, adj, rng)
    assert verify_partition(n, adj, P)[0]
    cls = all_cliques(n, adj, 1, None) + [0]
    R = rng.choice(cls)
    pR = popcount(R)
    ext = ((1 << n) - 1) & ~R
    m = sum(popcount(adj[v] & ext) for v in bits(ext)) // 2
    A = sum(popcount(ext & ~adj[v]) for v in bits(R))
    lhs = sum(1 + C2(popcount(K & R)) + 3 * C2(popcount(K & ext)) - popcount(K & R) * popcount(K & ext) for K in P)
    n67 += 1
    if lhs != len(P) - Bn(n, pR) + A + 3 * m:
        bad67b.append(trial)
    # (6.16): V = C u D u H, C clique of G, |D|=s, 2<=|C|<=|H|
    Cs = [K for K in cls if popcount(K) >= 2]
    if not Cs:
        continue
    Cm = rng.choice(Cs)
    rest = [v for v in range(n) if not Cm >> v & 1]
    rng.shuffle(rest)
    for s in range(0, len(rest) + 1):
        Dm = sum(1 << v for v in rest[:s]); Hm = sum(1 << v for v in rest[s:])
        if not (popcount(Cm) <= popcount(Hm)):
            continue
        k = popcount(Cm) + s
        X = Cm | Dm
        # template T(C,D,H)
        Tedges = set()
        for u in bits(Cm):
            for v in bits(Cm):
                if u < v: Tedges.add((u, v))
        for u in bits(X):
            for v in bits(Hm):
                Tedges.add((min(u, v), max(u, v)))
        dE = len(set(edges_of(n, adj)) ^ Tedges)
        Nbad = Ebad = 0
        for K in P:
            a_ = popcount(K & X); b_ = popcount(K & Hm)
            canon = (a_ == 1 and b_ == 1) or (b_ == 1 and a_ == 2 and popcount(K & Cm) == 2)
            if not canon:
                Nbad += 1; Ebad += C2(popcount(K))
        n616 += 1
        rhs = len(P) - Bsn(s, n, k) + 3 * dE
        if not (Nbad <= rhs and Ebad <= 10 * rhs):
            bad616.append((trial, s))
OUT['S1'] = dict(id='S1 (supplementary, not predeclared)', claim='(6.7b) sum d_R(K)=|Q|-B_n(|R|)+A+3m for every clique R; (6.16) N_bad<=|Q|-B_{s,n}(k)+3d_E(G,T), E_bad<=10(...) for every template root',
                 manuscript_lines='872-877, 981-989', method='4000 random graphs n=4..9, random exactly-verified clique partitions (unrestricted order), random clique roots / template roots (all s)',
                 evidence_type='finite random sample (exact arithmetic)', parameters={'trials': 4000},
                 details={'checked_6.7b': n67, 'checked_6.16': n616, 'fail_6.7b': bad67b[:5], 'fail_6.16': bad616[:5]},
                 result='PASS' if not bad67b and not bad616 else 'FAIL', negative_control={'description': 'none', 'result': 'N/A'},
                 runtime_s=round(time.time() - t0, 2))
print('S1', OUT['S1']['result'], n67, n616)
OUT['total_runtime_s'] = round(time.time() - T0, 1)
dump('graph_tests.json', OUT)
