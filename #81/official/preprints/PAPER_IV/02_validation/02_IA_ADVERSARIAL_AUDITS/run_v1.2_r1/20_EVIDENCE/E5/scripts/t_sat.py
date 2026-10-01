"""T20 (continued): SAT search for a graph on N vertices with max degree <= 2s, no matching of size s+1
and more than (4s+1)s edges (a counterexample to the CoreCliqueAlternative counting step).  UNSAT = no counterexample on N vertices."""
import sys, os, time, itertools, json
from pysat.formula import CNF
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e5lib import dump

res = {}
for (s, N, target) in [(1, 8, None), (2, 8, None), (3, 8, None), (2, 8, 'max')]:
    t0 = time.time()
    pairs = list(itertools.combinations(range(N), 2))
    var = {p: i + 1 for i, p in enumerate(pairs)}
    top = len(pairs)
    cnf = CNF()
    for v in range(N):
        lits = [var[p] for p in pairs if v in p]
        enc = CardEnc.atmost(lits=lits, bound=2 * s, top_id=top, encoding=EncType.seqcounter)
        top = max(top, enc.nv); cnf.extend(enc.clauses)
    # no matching of size s+1
    nm = 0
    for combo in itertools.combinations(pairs, s + 1):
        vs = [x for p in combo for x in p]
        if len(set(vs)) == 2 * (s + 1):
            cnf.append([-var[p] for p in combo]); nm += 1
    if target is None:
        bound = (4 * s + 1) * s + 1
        if bound > len(pairs):
            res[f's={s},N={N}'] = {'query': f'exists graph with >= {bound} edges', 'sat': False, 'note': 'trivially impossible: bound exceeds C(N,2)'}
            continue
        enc = CardEnc.atleast(lits=list(var.values()), bound=bound, top_id=top, encoding=EncType.seqcounter)
        cnf.extend(enc.clauses)
        with Cadical153(bootstrap_with=cnf.clauses) as S:
            r = S.solve()
        res[f's={s},N={N}'] = {'query': f'exists graph with >= {bound} edges', 'sat': r, 'matching_clauses': nm, 'sec': round(time.time() - t0, 2)}
    else:
        # find the true maximum on N vertices (for information): increase bound until UNSAT
        best = 0
        for bound in range(1, (4 * s + 1) * s + 2):
            c2 = CNF(from_clauses=cnf.clauses)
            enc = CardEnc.atleast(lits=list(var.values()), bound=bound, top_id=top, encoding=EncType.seqcounter)
            c2.extend(enc.clauses)
            with Cadical153(bootstrap_with=c2.clauses) as S:
                if S.solve():
                    best = bound
                else:
                    break
        res[f's={s},N={N} max'] = {'max_edges': best, 'sec': round(time.time() - t0, 2)}
    print(res)
dump('T20_sat.json', res)
