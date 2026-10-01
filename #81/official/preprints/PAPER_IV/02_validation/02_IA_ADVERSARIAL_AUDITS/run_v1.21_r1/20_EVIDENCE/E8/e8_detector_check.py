"""E8 (auditor-written): independent check of the author's proposed sorry detector pattern (copied
literally from sorry_log_recheck.py, not imported), against the captured real Lean 4.28 warning,
variants, negative controls, and all existing logs of both segments + auditor runs. No Lean."""
import re, pathlib, json, sys, hashlib
PATTERN = r"sorryAx|declaration\s+uses\s+[`'\"‘’“”]*sorry\b"
det = lambda t: bool(re.search(PATTERN, t, re.I))
B = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV')
P = B / '02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1'
neg = (P / '20_EVIDENCE/E4/AuditorNegControl.log').read_text(encoding='utf-8')
cases = {
  'real_captured_negative_log': (neg, True),
  'backticks': ('warning: declaration uses `sorry`', True),
  'single_quotes': ("warning: declaration uses 'sorry'", True),
  'double_quotes': ('warning: declaration uses "sorry"', True),
  'curly': ('declaration uses \u2018sorry\u2019', True),
  'sorryAx_axiom_list': ("'x' depends on axioms: [sorryAx]", True),
  'two_spaces_newline': ('declaration  uses\n`sorry`', True),
  'clean_axioms': ('depends on axioms: [propext, Classical.choice, Quot.sound]', False),
  'word_sorry_in_identifier_not_warning': ('theorem no_sorry_used : True', False),
  'sorry_prefix_word': ('declaration uses `sorryish`', False),
}
res = {k: {'expected': e, 'got': det(t), 'ok': det(t) == e} for k, (t, e) in cases.items()}
dirs = [P / '10_LOGS/E4_main/modules', P / '10_LOGS/E4_annex/modules',
        B / '03_reproducibility/full_rebuild_v12_20260929_r2/combined/modules',
        B / '03_reproducibility/full_rebuild_v12_20260929_resume/combined/modules']
scan = {}
for d in dirs:
    fs = sorted(d.glob('*.log'))
    scan[str(d)] = {'logs': len(fs), 'detector_hits': [f.name for f in fs if det(f.read_text(encoding='utf-8', errors='replace'))],
                    'broad_sorry_hits': [f.name for f in fs if re.search('sorry', f.read_text(encoding='utf-8', errors='replace'), re.I)]}
runners_frozen = {n: hashlib.sha256((B / '05_formalization/lean_piv-v12-fb459343d234' / n).read_bytes()).hexdigest() for n in ['tools/paperiv_build.py', 'tools/audit_publication.py']}
out = {'pattern': PATTERN, 'cases': res, 'all_cases_ok': all(v['ok'] for v in res.values()), 'scan': scan, 'frozen_runner_sha256': runners_frozen}
json.dump(out, open(sys.argv[1], 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
print(json.dumps({'all_cases_ok': out['all_cases_ok'], 'cases': {k: v['ok'] for k, v in res.items()}, 'scan': {k.split('\\')[-3] + '/' + k.split('\\')[-2]: (v['logs'], len(v['detector_hits']), len(v['broad_sorry_hits'])) for k, v in scan.items()}}, indent=1))
