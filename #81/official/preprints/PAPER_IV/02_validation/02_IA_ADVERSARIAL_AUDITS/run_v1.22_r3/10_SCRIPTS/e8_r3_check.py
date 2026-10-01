"""E8 (auditor-written, run_v1.22_r3): compare the auditor's regenerated inventory/test outputs with the sealed author
files; independent checks of pattern semantics against the frozen runner rule; independent inventory recount. Read-only."""
import json, re, sys, pathlib, hashlib, collections
B = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV')
O = B / '01_manuscript/v1.22_editorial_candidate_r3'
E = pathlib.Path(sys.argv[1])
out = {}
ai = json.loads((O / 'LOG_INVENTORY.json').read_text(encoding='utf-8')); mi = json.loads((E / 'testcopy/LOG_INVENTORY.json').read_text(encoding='utf-8'))
out['inventory_regenerated_equals_sealed'] = ai == mi
out['groups'] = [(g['directory'], len(g['logs'])) for g in ai['groups']]
out['expected_total'] = ai['expected_total']
names = collections.Counter((g['directory'], e['name']) for g in ai['groups'] for e in g['logs'])
out['duplicate_entries'] = [k for k, v in names.items() if v > 1]
# independent hash check of every inventory entry
bad = [f"{g['directory']}/{e['name']}" for g in ai['groups'] for e in g['logs'] if hashlib.sha256((B / g['directory'] / e['name']).read_bytes()).hexdigest() != e['sha256']]
out['independent_hash_mismatch'] = bad
# same 1266 set as run_v1.21_r1 / r2 detector scan directories
out['groups_equal_historical_E8_dirs'] = sorted(d for d, _ in out['groups']) == sorted([
 '02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1/10_LOGS/E4_main/modules', '02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1/10_LOGS/E4_annex/modules',
 '03_reproducibility/full_rebuild_v12_20260929_r2/combined/modules', '03_reproducibility/full_rebuild_v12_20260929_resume/combined/modules'])
at = json.loads((O / 'LOG_VERIFIER_TESTS.json').read_text(encoding='utf-8')); mt = json.loads((E / 'testcopy/LOG_VERIFIER_TESTS.json').read_text(encoding='utf-8'))
out['unit_cases_equal_sealed'] = at['unit_cases'] == mt['unit_cases']
strip = lambda r: {k: v for k, v in r.items() if k not in ('errors',)} 
out['cli_negative_cases_sealed'] = [(c['case'], c['exit_code'], c['result']['status'], [x.get('error', 'set/count') for x in c['result']['errors']]) for c in at['cli_negative_cases']]
out['cli_negative_cases_auditor'] = [(c['case'], c['exit_code'], c['result']['status'], [x.get('error', 'set/count') for x in c['result']['errors']]) for c in mt['cli_negative_cases']]
out['historical_scan_sealed_vs_auditor'] = (at['historical_scan']['status'], at['historical_scan']['logs_checked'], mt['historical_scan']['status'], mt['historical_scan']['logs_checked'])
# pattern semantics
src = (O / 'verify_frozen_logs.py').read_text(encoding='utf-8')
ns = {}; exec(compile(src.split('def sha')[0].replace("ROOT=Path(__file__).resolve().parent\nPAPER=ROOT.parents[1]\n", ''), 'v', 'exec'), ns)
SORRY, ERROR = ns['SORRY'], ns['ERROR']
FROZEN = re.compile(r"sorryAx|declaration uses 'sorry'|^.*error(?:\(|:)", re.M)  # tools/audit_publication.py:52 (literal)
FROZEN_BUILD = lambda t: "declaration uses 'sorry'" in t  # tools/paperiv_build.py:400
out['error_rule_flags'] = {'ignorecase': bool(ERROR.flags & re.I), 'multiline': bool(ERROR.flags & re.M), 'pattern_equals_frozen_error_alternative': ERROR.pattern == r'^.*error(?:\(|:)'}
probes = {'error: x': None, 'f.lean:1:2: error: x': None, 'ERROR: x': None, 'Error: x': None, 'error(foo)': None, 'no errors here': None,
          "declaration uses 'sorry'": None, 'declaration uses `sorry`': None, 'Declaration uses `sorry`': None, 'sorryAx': None, 'sorryax': None}
out['error_case_sensitivity_identical_to_frozen'] = all(bool(ERROR.search(p)) == bool(re.search(r'^.*error(?:\(|:)', p, re.M)) for p in probes)
out['probe_table'] = {p: {'new_sorry': bool(SORRY.search(p)), 'new_error': bool(ERROR.search(p)), 'frozen_audit_publication': bool(FROZEN.search(p)), 'frozen_build': FROZEN_BUILD(p)} for p in probes}
neg = (B / '02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1/20_EVIDENCE/E4/AuditorNegControl.log').read_text(encoding='utf-8')
out['real_negative_log'] = {'new_detects': bool(SORRY.search(neg)), 'frozen_audit_publication_detects': bool(FROZEN.search(neg)), 'frozen_build_detects': FROZEN_BUILD(neg), 'sha256': hashlib.sha256(neg.encode('utf-8')).hexdigest()}
json.dump(out, open(E / 'E8_R3_CHECK.json', 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
print(json.dumps(out, indent=1, ensure_ascii=False))
