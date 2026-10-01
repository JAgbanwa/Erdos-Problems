"""Aggregate E5 raw results into E5_RESULTS.json (one record per predeclared test T01-T25, plus supplementary items)."""
import json, os, hashlib, datetime
E5 = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
R = os.path.join(E5, 'results')


def load(name):
    with open(os.path.join(R, name), encoding='utf-8') as f:
        return json.load(f)


sc = load('scalar_tests.json'); it = load('integer_tests.json'); gr = load('graph_tests.json')
tp = {}
for k in ('T10', 'T11', 'T16', 'T17', 'T06s'):
    tp.update(load(f'templates_{k}.json'))
sat = load('T20_sat.json'); info = load('info_c4.json')


def nc(d):
    x = d.get('negative_control') or {}
    return {'description': x.get('description'), 'result': x.get('result')}


def base(d, src, reduced=None, notes=None):
    return {'id': d['id'], 'claim': d['claim'], 'manuscript_lines': d['manuscript_lines'], 'method': d['method'], 'evidence_type': d['evidence_type'],
            'parameters': d.get('parameters'), 'result': d['result'], 'negative_control': nc(d), 'runtime_s': d.get('runtime_s'),
            'raw_result_file': src, 'range_reduction': reduced, 'notes': notes}


tests = []
tests.append(base(sc['T01'], 'results/scalar_tests.json', notes='exact crossover n*=3672542735043: (4.6a) fails for all n<n*, consistent with "fails for n<=3.6e12"'))
tests.append(base(sc['T02'], 'results/scalar_tests.json'))
tests.append(base(sc['T03'], 'results/scalar_tests.json'))
tests.append(base(sc['T04'], 'results/scalar_tests.json', notes='conditional on the premises (5.12); the premises themselves (regularisation bounds (5.4),(5.7)) are not finite-checkable here'))
tests.append(base(sc['T05'], 'results/scalar_tests.json', notes='|n-3a|<=a/64 is not needed for the size window'))
t06 = base(sc['T06'], 'results/scalar_tests.json', notes='supplementary T06s: exact LP of F_4(K_r v I_h) against (5.1a) for 4<=r<=11, r+h<=12: '
           + tp['T06s']['result'] + '. First T06s run: 2/36 LPs (K_12 and K_10 v I_2) had no exact certificate from limit_denominator reconstruction and the first script version '
           'mislabelled this as FAIL (protocol: INCONCLUSIVE; no bound was violated). After adding exact reconstruction from the HiGHS optimal basis (verification method only, no threshold change) all 36 are exactly certified.')
t06['supplementary'] = {'T06s': {'result': tp['T06s']['result'], 'method': tp['T06s']['method'], 'violations': tp['T06s']['details']['violations'], 'inexact_lp': tp['T06s']['details'].get('inexact_lp')}}
tests.append(t06)
tests.append(base(it['T07'], 'results/integer_tests.json', notes='(E.3) increment identity holds for every n>=1 in range (manuscript states it for sufficiently large n)'))
tests.append(base(it['T08'], 'results/integer_tests.json'))
tests.append(base(it['T09'], 'results/integer_tests.json'))
tests.append(base(tp['T10'], 'results/templates_T10.json', reduced='brute-force rsd / exact cp only for 11 instances with n<=16 (s<=2); formulas checked for s<=20, q<=200'))
tests.append(base(tp['T11'], 'results/templates_T11.json', reduced='n<=14, s<=3'))
tests.append(base(gr['T12'], 'results/graph_tests.json'))
tests.append(base(gr['T13'], 'results/graph_tests.json', notes='weak test: max ratio embeddings/bound = ' + gr['T13']['details']['max_ratio_emb/bound']))
tests.append(base(gr['T14'], 'results/graph_tests.json'))
t15 = base(gr['T15'], 'results/graph_tests.json', notes='all 1253 LPs exactly certified; min slack 0 for both (6.22) and (6.23). Power note: at n<=7 the refined bound (6.23) was never violated even outside its band 4s<=n, so the band condition is not exercised.')
tests.append(t15)
tests.append(base(tp['T16'], 'results/templates_T16.json', reduced='D.2: second (infeasibility) ILP solve skipped at n=16 after exceeding the time budget; parity lower bound + verified partition certify c3(K_16)=46=M(16)+1 exactly'))
tests.append(base(tp['T17'], 'results/templates_T17.json', reduced='2<=k<=7, k<=h, k+h<=13'))
tests.append(base(sc['T18'], 'results/scalar_tests.json'))
tests.append(base(sc['T19'], 'results/scalar_tests.json'))
t20 = {'id': 'T20', 'claim': '(E.2e) and (E.13) arithmetic; CoreCliqueAlternative counting step: missing graph with max degree <=2s and no matching of size s+1 has <=(4s+1)s edges',
       'manuscript_lines': '1931-1940, 2076-2086', 'method': 'exhaustive integers + z3 (E.2e/E.13); all atlas graphs n<=7 as missing graphs (s=1,2); SAT (CaDiCaL) on N=8 vertices for s=1,2,3',
       'evidence_type': 'finite exhaustive + exact LRA; SAT UNSAT is solver-dependent', 'parameters': {'E.2e': it['T20a']['parameters'], 'graphs': 'n<=7 atlas, N=8 SAT'},
       'result': 'PASS' if (it['T20a']['result'] == 'PASS' and gr['T20b']['result'] == 'PASS' and not any(v.get('sat') for k, v in sat.items() if 'max' not in k)) else 'FAIL',
       'negative_control': {'description': it['T20a']['negative_control']['description'] + '; ' + gr['T20b']['negative_control']['description'],
                            'result': 'PASS (rejected)' if (it['T20a']['negative_control']['result'].startswith('PASS') and gr['T20b']['negative_control']['result'].startswith('PASS')) else 'FAIL (accepted)'},
       'runtime_s': round(it['T20a']['runtime_s'] + gr['T20b']['runtime_s'] + sum(v.get('sec', 0) for v in sat.values()), 2),
       'raw_result_file': ['results/integer_tests.json', 'results/graph_tests.json', 'results/T20_sat.json'], 'range_reduction': None,
       'notes': 'max edges found: s=1 -> 3, s=2 -> 10 (bound 5, 18). The step also follows analytically: endpoints of a maximum missing matching (<=2s vertices, degree <=2s) cover all missing edges, so e<=4s^2<=(4s+1)s. (E.12) itself (hypothesis c>=20(s+1)^2) is out of exhaustive range; without the size hypothesis it fails for small c (INFO, expected).',
       'details': {'T20a': it['T20a']['details'], 'T20b': {k: v for k, v in gr['T20b']['details'].items()}, 'sat': sat}}
tests.append(t20)
t21 = {'id': 'T21', 'claim': sc['T21']['claim'], 'manuscript_lines': sc['T21']['manuscript_lines'], 'method': sc['T21']['method'] + ' + ' + gr['T21b']['method'],
       'evidence_type': 'symbolic + finite', 'parameters': gr['T21b']['parameters'], 'result': 'PASS' if (sc['T21']['result'] == 'PASS' and gr['T21b']['result'] == 'PASS') else 'FAIL',
       'negative_control': {'description': 'none predeclared (trivial)', 'result': 'N/A'}, 'runtime_s': round(sc['T21']['runtime_s'] + gr['T21b']['runtime_s'], 2),
       'raw_result_file': ['results/scalar_tests.json', 'results/graph_tests.json'], 'range_reduction': None, 'notes': None}
tests.append(t21)
tests.append(base(sc['T22'], 'results/scalar_tests.json'))
t23 = base(gr['T23'], 'results/graph_tests.json')
g5 = it['T23_G5']
t23['result'] = 'PASS' if (gr['T23']['result'] == 'PASS' and g5['z3'] == 'unsat') else 'FAIL'
t23['negative_control'] = {'description': gr['T23']['negative_control']['description'] + '; (G.5) with 19/eps must be refutable', 'result': 'PASS (rejected)' if (gr['T23']['negative_control']['result'].startswith('PASS') and g5['neg_19'] == 'sat') else 'FAIL (accepted)'}
t23['details'] = {'G.4': gr['T23']['details'], 'G.5': g5}
tests.append(t23)
tests.append(base(sc['T24'], 'results/scalar_tests.json'))
tests.append({'id': 'T25', 'claim': 'Certo certificates', 'manuscript_lines': '2414, 2444', 'method': 'binding check', 'evidence_type': 'n/a', 'parameters': None,
              'result': 'NOT_APPLICABLE', 'negative_control': {'description': 'n/a', 'result': 'N/A'}, 'runtime_s': 0, 'raw_result_file': None, 'range_reduction': None,
              'notes': 'The manuscript mentions Certo [13] only as an exploration tool and states "The version used in the experiments must be fixed together with its certificates in the supplement" (l.2444); no Certo certificate is bound as an input of any claim, and Certo files are outside the E5 reading boundary: not bound / not accessible; not audited.'})
supp = [{'id': 'S1', 'result': gr['S1']['result'], 'claim': gr['S1']['claim'], 'manuscript_lines': gr['S1']['manuscript_lines'], 'method': gr['S1']['method'], 'details': gr['S1']['details'], 'note': 'supplementary, not predeclared'},
        {'id': 'INFO_c4', 'result': 'INFO', 'claim': info['claim'], 'graphs': info['graphs'], 'graphs_with_c4>Q_rsd(n)': len(info['graphs_with_c4_greater_than_Q_rsd']),
         'c4_exact_by_LP_ceiling': info['c4_certified_by_LP_ceiling'], 'c4_solver_dependent': info['c4_solver_dependent_only'],
         'note': 'upper bounds c4<=Q_rsd(n) are exact (verified partitions) for all 1253 graphs n<=7; in particular c4<=M(n) for every chordal graph with n<=7 (relevant to the open b=0 question, G.1). Not predeclared.'},
        {'id': 'RSD_atlas', 'result': 'INFO', 'details': gr['RSD_atlas'], 'note': 'self-test of the rsd implementation: rsd=0 iff chordal on all 1253 atlas graphs'}]
summary = {}
for t in tests:
    summary[t['result']] = summary.get(t['result'], 0) + 1
man = 'C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.2_full_rebuild_candidate/PAPER_IV_preprint_v1.2_en.md'
doc = {'gate': 'E5', 'title': 'Independent falsification by exact computation', 'generated_utc': datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),
       'target_manuscript': {'path': man, 'sha256': hashlib.sha256(open(man, 'rb').read()).hexdigest()},
       'predeclaration_sha256': hashlib.sha256(open(os.path.join(E5, 'E5_PREDECLARATION.md'), 'rb').read()).hexdigest(),
       'summary': summary, 'tests': tests, 'supplementary': supp,
       'limits': 'Finite tests never establish universal (for all n) claims; exact LP values are certified per instance; ILP optimality is solver-dependent unless certified by an exact lower bound (weight certificate, parity argument, or LP ceiling), as recorded per instance.'}
with open(os.path.join(E5, 'E5_RESULTS.json'), 'w', encoding='utf-8') as f:
    json.dump(doc, f, indent=1, default=str)
print(summary)
for t in tests:
    print(t['id'], t['result'], '|', t['negative_control']['result'], '|', t['runtime_s'])
