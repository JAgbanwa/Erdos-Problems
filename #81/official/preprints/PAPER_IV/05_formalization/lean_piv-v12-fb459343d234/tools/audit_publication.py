"""Single serial entry point for every target in FREEZE_SCOPE.json.

Reuses pinned dependencies; does not fetch, clean caches, publish or freeze.
All requested targets are freshly executed. This is a local formal audit,
not the independent manuscript audit. Use a new run directory for every run.
"""
from pathlib import Path
from datetime import datetime
import argparse
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
CONFIG = ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
          'FREEZE_SCOPE.json', 'tools/paperiv_build.py', 'tools/audit_publication.py')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def check(condition, message):
    if not condition:
        raise RuntimeError(message)

def validate(run, config):
    summary, results, sources, meta = [read(run / name) for name in
        ('SUMMARY.json', 'RESULTS.json', 'SOURCES.json', 'RUN_META.json')]
    targets = read(ROOT / 'FREEZE_SCOPE.json')['targets']
    check(summary['status'] == 'PASS' and not summary['fail'] and not summary['blocked']
          and not summary['notRun'] and not summary['sourcesChangedDuringRun'], 'Incomplete build')
    check((run / 'BUILD.exit').read_text().strip() == 'EXIT_CODE=0', 'Build exit')
    check(meta['targets'] == targets and meta['recheckTargets'], 'Target scope changed')
    check(len(results) == len(sources) == summary['modulesPlanned'], 'Incomplete records')
    check({p: sha(ROOT / p) for p in CONFIG} == config, 'Configuration changed during run')
    rows = {r['module']: r for r in results}
    check(all(r['status'] in ('PASS', 'UP-TO-DATE') and not r.get('sorryWarning')
              for r in results), 'Failed module or sorry warning')
    for s in sources:
        check(sha(ROOT / s['path']) == s['sha256'], 'Source changed: ' + s['path'])
    records = 0
    for target in targets:
        row = rows[target]
        check(row['status'] == 'PASS' and row['exitCode'] == 0, 'Target not reexecuted: ' + target)
        log = (run / 'modules' / (target + '.log')).read_text(encoding='utf-8')
        check((run / 'modules' / (target + '.exit')).read_text().strip() == 'EXIT_CODE=0', target)
        check(not re.search(r"sorryAx|declaration uses 'sorry'|^.*error(?:\(|:)", log, re.M),
              'Error or sorry in ' + target)
        for values in re.findall(r'(?:depends on axioms:|axioms)\s*\[([^\]]*)\]', log):
            check({v.strip() for v in values.split(',') if v.strip()} <= ALLOWED,
                  'Unapproved axiom in ' + target)
            records += 1
    check(records > 0, 'No axiom output')
    return {'status': 'PASS', 'targets': targets, 'target_count': len(targets),
            'modules': len(sources), 'axiom_records': records,
            'export_checks': len(re.findall(r'^#check ',
                (ROOT / 'ReleaseExportCheck.lean').read_text(encoding='utf-8'), re.M)),
            'config_sha256': config, 'build_summary': summary,
            'scope': 'Local formal checks only; not a manuscript audit or release.'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir', default='build-logs/publication-' + datetime.now().strftime('%Y%m%d-%H%M%S'))
    args = parser.parse_args()
    run = (ROOT / args.run_dir).resolve()
    check(not run.exists(), 'Run directory already exists; evidence must not be overwritten')
    config = {p: sha(ROOT / p) for p in CONFIG}
    run.mkdir(parents=True)
    (run / 'CONFIG_BEFORE.json').write_text(json.dumps(config, indent=2), encoding='utf-8')
    command = [sys.executable, '-u', str(ROOT / 'tools/paperiv_build.py'),
               '--scope', 'freeze', '--recheck-targets', '--threads', '1', '--run-dir', str(run)]
    code = subprocess.call(command, cwd=ROOT)
    try:
        check(code == 0, 'Build failed; inspect per-module logs')
        verdict = validate(run, config)
    except Exception as error:
        verdict = {'status': 'FAIL', 'reason': str(error), 'runner_exit': code}
    (run / 'AUDIT_SUMMARY.json').write_text(json.dumps(verdict, indent=2), encoding='utf-8')
    print(json.dumps(verdict, indent=2))
    return 0 if verdict['status'] == 'PASS' else 1

if __name__ == '__main__':
    sys.exit(main())
