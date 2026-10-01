"""E4 documentary closure (auditor-written, run_v1.21_r1): re-verify the run_v1.2_r1 E4 evidence
without running Lean. Uses records.jsonl, console logs, module logs and the sealed manifest; does
NOT rely on 10_LOGS/E4_main/SUMMARY.json (overwritten by the AuditorChecks invocation, C-06)."""
import json, re, pathlib, hashlib, sys, collections
P = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1')
SRC = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/05_formalization/lean_piv-v12-fb459343d234')
out = {}
T = json.loads((SRC / 'FREEZE_SCOPE.json').read_text())['targets']
recs = [json.loads(l) for l in (P / '10_LOGS/E4_main/records.jsonl').read_text(encoding='utf-8').splitlines()]
last = {}
for r in recs: last[r['module']] = r
own_modules = {'.'.join(p.relative_to(SRC).with_suffix('').parts) for p in SRC.rglob('*.lean')}
out['records_total'] = len(recs); out['distinct_modules'] = len(last)
out['status_counts'] = dict(collections.Counter(r['status'] for r in last.values()))
out['cut_modules'] = len(own_modules)
out['cut_modules_with_PASS'] = sum(1 for m in own_modules if last.get(m, {}).get('status') == 'PASS')
out['non_cut_records'] = sorted(set(last) - own_modules)
out['exit_nonzero'] = [m for m, r in last.items() if r.get('exit') not in (0, None)]
out['sorry_flag'] = [m for m, r in last.items() if r.get('sorry_warning')]
# source hashes in records equal the manifest
man = {e['path']: e['sha256'] for e in json.loads((pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json')).read_text())}
bad = []
for m in own_modules:
    p = '/'.join(m.split('.')) + '.lean'
    if last[m]['key']['source'] != man[p]: bad.append(m)
out['record_source_hash_mismatch_vs_manifest'] = bad
# console log: final summary of the main run
con = (P / '10_LOGS/E4_main_console.log').read_text(encoding='utf-8')
m = re.search(r'\{\s*"finished_utc".*?\}\s*\}', con, re.S)
cs = json.loads(m.group(0)); out['console_summary'] = {k: cs[k] for k in ('modules_planned', 'pass', 'fail_or_blocked', 'finished_utc')}
out['console_targets_all_PASS'] = all(v == 'PASS' for v in cs['targets_status'].values()) and set(cs['targets_status']) == set(T)
out['console_EXIT'] = con.strip().splitlines()[-1]
out['console_PASS_lines'] = len(re.findall(r'^PASS \d+ 607 ', con, re.M))
# module logs
logs = list((P / '10_LOGS/E4_main/modules').glob('*.log'))
out['module_logs'] = len(logs)
sorry_any = [l.name for l in logs if re.search(r'sorry', l.read_text(encoding='utf-8', errors='replace'), re.I) and 'AuditorNeg' not in l.name]
out['logs_with_sorry_text'] = sorry_any
# target logs: axiom sets
recsum = 0; pa = 0; nonstd = []
for t in T:
    s = (P / '10_LOGS/E4_main/modules' / f'{t}.log').read_text(encoding='utf-8', errors='replace')
    for v in re.findall(r'(?:depends on axioms:|axioms)\s*\[([^\]]*)\]', s):
        recsum += 1
        st = {x.strip() for x in v.replace('\n', ' ').split(',') if x.strip()}
        if not st <= {'propext', 'Classical.choice', 'Quot.sound'}: nonstd.append((t, sorted(st)))
    pa += len(re.findall(r'depends on axioms:', s))
out['axiom_records_author_rule'] = recsum; out['print_axioms'] = pa; out['nonstandard'] = nonstd
out['export_checks_in_source'] = len(re.findall(r'^#check ', (SRC / 'ReleaseExportCheck.lean').read_text(encoding='utf-8'), re.M))
rel = (P / '10_LOGS/E4_main/modules/ReleaseExportCheck.log').read_text(encoding='utf-8', errors='replace')
out['ReleaseExportCheck_error_lines'] = len(re.findall(r'\berror\b', rel))
# annex
ar = [json.loads(l) for l in (P / '10_LOGS/E4_annex/records.jsonl').read_text(encoding='utf-8').splitlines()]
out['annex_records'] = len(ar); out['annex_pass'] = sum(1 for r in ar if r['status'] == 'PASS')
ac = (P / '10_LOGS/E4_annex/modules/BoundedCliqueGap.AxiomCheck.log').read_text(encoding='utf-8', errors='replace')
out['annex_audit_line'] = [l for l in ac.splitlines() if l.startswith('BoundedCliqueGap:')]
out['annex_axioms'] = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", ac)
# olean identity and cones
out['olean_vs_author'] = json.loads((P / '20_EVIDENCE/E4/olean_vs_author.json').read_text())
ck = (P / '20_EVIDENCE/E4/AuditorChecks.log').read_text(encoding='utf-8')
out['auditor_cone_summary'] = re.findall(r'AUDITOR CONE SUMMARY[^\n]*', ck)
out['cache_diff'] = json.loads((P / '20_EVIDENCE/E4/cache_diff.json').read_text())
json.dump(out, open(sys.argv[1], 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
print(json.dumps(out, indent=1, ensure_ascii=False)[:4000])
