"""E8 (auditor-written): independent validation of the author's two-segment reconstruction evidence.
Read-only. Writes E8_AUTHOR_BUILD_CHECK.json."""
import json, re, hashlib, pathlib, collections
B = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/03_reproducibility')
S1 = B / 'full_rebuild_v12_20260929_r2/combined'; S2 = B / 'full_rebuild_v12_20260929_resume/combined'
HERE = pathlib.Path(__file__).parent
J = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
out = {}
targets = J(pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/05_formalization/lean_piv-v12-fb459343d234/FREEZE_SCOPE.json'))['targets']
man = {e['path']: e['sha256'] for e in J(pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json'))}
r1 = J(S1 / 'RESULTS.json'); r2 = J(S2 / 'RESULTS.json')
m1 = {r['module']: r for r in r1}; m2 = {r['module']: r for r in r2}
meta1 = J(S1 / 'RUN_META.json'); meta2 = J(S2 / 'RUN_META.json')
out['seg1_rows'] = len(r1); out['seg1_status_counts'] = dict(collections.Counter(r['status'] for r in r1))
out['seg2_rows'] = len(r2); out['seg2_status_counts'] = dict(collections.Counter(r['status'] for r in r2))
out['seg1_status_file'] = (S1 / 'BUILD.status').read_text().strip()
out['seg2_status_file'] = (S2 / 'BUILD.status').read_text().strip()[:200]
out['seg2_exit'] = (S2 / 'BUILD.exit').read_text().strip()
keys = ['lean', 'leanBinary', 'toolchain', 'leanOptions', 'threads', 'dependencyPins', 'leanPathDependencies', 'targets', 'recheckTargets', 'clean']
out['meta_diff'] = {k: (meta1.get(k), meta2.get(k)) for k in keys if meta1.get(k) != meta2.get(k)}
out['seg1_clean'] = meta1.get('clean'); out['seg2_clean'] = meta2.get('clean')
out['seg1_artifactDir'] = meta1.get('artifactDir'); out['seg2_artifactDir'] = meta2.get('artifactDir')
# source hashes vs manifest
bad_src = [r['module'] for r in r2 if man.get(r['path']) != r['sourceSha256']]
out['seg2_source_hash_mismatch_vs_manifest'] = bad_src
bad_src1 = [r['module'] for r in r1 if man.get(r['path']) != r.get('sourceSha256')]
out['seg1_source_hash_mismatch_vs_manifest'] = bad_src1
# reused objects
reused = [r['module'] for r in r2 if r['status'] == 'UP-TO-DATE']
fresh2 = [r['module'] for r in r2 if r['status'] == 'PASS']
out['reused_count'] = len(reused); out['fresh_seg2_count'] = len(fresh2)
problems = []
for m in reused:
    a = m1.get(m)
    if not a or a['status'] != 'PASS': problems.append((m, 'no PASS in seg1')); continue
    if a['sourceSha256'] != m2[m]['sourceSha256']: problems.append((m, 'source differs'))
    if a.get('lib') != m2[m].get('lib'): problems.append((m, 'lib differs'))
    ex = S1 / 'modules' / f'{m}.exit'
    if not ex.exists() or ex.read_text().strip() != 'EXIT_CODE=0': problems.append((m, 'seg1 exit'))
    lg = S1 / 'modules' / f'{m}.log'
    if not lg.exists(): problems.append((m, 'seg1 log missing'))
    else:
        t = lg.read_text(encoding='utf-8', errors='replace')
        if "declaration uses 'sorry'" in t or re.search(r'^\S*: error', t, re.M) or re.search(r'error:', t): problems.append((m, 'seg1 log error/sorry'))
out['reuse_problems'] = problems[:50]; out['reuse_problems_n'] = len(problems)
# direct deps of reused modules: they must all be reused (seg1) too, else a fresh-in-seg2 dependency under a reused object
graph = J(S2 / 'SOURCES.json') if (S2 / 'SOURCES.json').exists() else None
# fresh seg2 modules: logs/exits
p2 = []
for m in fresh2:
    ex = S2 / 'modules' / f'{m}.exit'; lg = S2 / 'modules' / f'{m}.log'
    if not ex.exists() or ex.read_text().strip() != 'EXIT_CODE=0': p2.append((m, 'exit'))
    if not lg.exists(): p2.append((m, 'log missing')); continue
    t = lg.read_text(encoding='utf-8', errors='replace')
    if "declaration uses 'sorry'" in t or 'sorryAx' in t: p2.append((m, 'sorry'))
    if re.search(r'\berror\b', t) and not re.search(r'error', m, re.I): p2.append((m, 'error word in log'))
out['seg2_fresh_problems'] = p2[:50]; out['seg2_fresh_problems_n'] = len(p2)
out['union_distinct_modules'] = len(set(reused) | set(fresh2)); out['overlap'] = sorted(set(reused) & set(fresh2))
out['seg1_pass_not_reused'] = sorted(m for m, r in m1.items() if r['status'] == 'PASS' and m not in reused)
# targets
tstat = {}; records = 0; axioms = collections.Counter(); per_target = {}
for t in targets:
    r = m2[t]; lg = (S2 / 'modules' / f'{t}.log').read_text(encoding='utf-8', errors='replace')
    recs = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", lg)
    no_ax = len(re.findall(r"does not depend on any axioms", lg))
    for v in recs:
        s = frozenset(x.strip() for x in v.split(',') if x.strip()); axioms[tuple(sorted(s))] += 1
    records += len(recs); per_target[t] = {'status': r['status'], 'exit': r.get('exitCode'), 'axiom_records': len(recs), 'no_axiom_records': no_ax,
        'sorry': ('sorryAx' in lg) or ("declaration uses 'sorry'" in lg), 'has_error_word': bool(re.search(r'\berror\b', lg)), 'PASS_lines': len(re.findall(r'PASS', lg))}
out['targets'] = per_target
out['axiom_record_total_depends_on'] = records
out['axiom_sets'] = {','.join(k): v for k, v in axioms.items()}
out['nonstandard_axiom_sets'] = [k for k in axioms if not set(k) <= {'propext', 'Classical.choice', 'Quot.sound'}]
json.dump(out, open(HERE / 'E8_AUTHOR_BUILD_CHECK.json', 'w'), indent=1)
print(json.dumps({k: v for k, v in out.items() if k not in ('targets',)}, indent=1)[:6000])
for t, v in per_target.items(): print(t, v)
