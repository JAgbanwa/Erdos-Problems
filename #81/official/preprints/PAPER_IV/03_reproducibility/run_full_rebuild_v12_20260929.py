"""Fresh serial reconstruction; never freezes, edits proofs or starts internal audit."""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone

PAPER = Path(__file__).resolve().parent.parent
SOURCE = PAPER / '05_formalization/lean_piv-v12-fb459343d234'
MANIFEST = PAPER / '03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json'
WORK = Path('C:/Users/jtraverso/e81p4/piv_v12_full_rebuild_20260929')
RUN = PAPER / '03_reproducibility/full_rebuild_v12_20260929_r2'
REQUIRED = ['PaperIV.DefectExplicitPublication', 'E34.L11Main', 'E35.Theorem',
            'ExplicitFixedStability', 'PaperIV.OptimalTemplateObstruction']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def save(name, value):
    (RUN / name).write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8')

def main():
    require(not RUN.exists(), 'Run exists; do not overwrite previous evidence')
    RUN.mkdir()
    started = datetime.now(timezone.utc).isoformat()
    try:
        entries = read(MANIFEST)
        require(len(entries) == 615, 'Unexpected source manifest')
        for row in entries:
            require(sha(SOURCE / row['path']) == row['sha256'], 'Frozen source mismatch')
            require(sha(WORK / row['path']) == row['sha256'], 'Working copy mismatch')
        require(not (WORK / '.lake/runner').exists(), 'Project artifact cache is not empty')
        require(not (WORK / '.lake/build/lib/lean').exists(), 'Old project objects present')
        spec = importlib.util.spec_from_file_location('buildplan', WORK / 'tools/paperiv_build.py')
        planner = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(planner)
        modules = planner.discover(WORK)
        targets = read(WORK / 'FREEZE_SCOPE.json')['targets']
        require(len(modules) == 607 and len(targets) == 19, 'Unexpected scope')
        require(planner.closure(modules, targets) == set(modules), 'Targets omit source modules')
        require(all(x in modules for x in REQUIRED), 'Required interface missing')
        # Verify installed dependencies before any Lake environment resolution.
        dependency_cache = {}
        for pkg in read(WORK / 'lake-manifest.json')['packages']:
            directory = WORK / '.lake/packages' / pkg['name']
            head = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
            require(head == pkg['rev'], 'Dependency revision mismatch: ' + pkg['name'])
            dirty = subprocess.check_output(['git', '-C', str(directory), 'status', '--porcelain', '--untracked-files=no'], text=True)
            require(not dirty.strip(), 'Dependency modified: ' + pkg['name'])
            present = (directory / '.lake/build/lib/lean').is_dir()
            dependency_cache[pkg['name']] = present
            if not present:
                # Cli is a Lake tooling dependency with no compiled library in
                # this installation. It is not imported by these Lean sources.
                require(pkg['name'] == 'Cli' and not any(
                    i == 'Cli' or i.startswith('Cli.')
                    for m in modules.values() for i in m['imports']),
                    'Required dependency cache missing: ' + pkg['name'])
        save('REQUEST.json', {'status': 'RUNNING', 'started': started,
             'source_manifest_sha256': sha(MANIFEST), 'modules': len(modules),
             'targets': targets, 'required_fresh_interfaces': REQUIRED,
             'project_cache_initially_empty': True, 'reuse_third_party_cache': True,
             'work': str(WORK), 'threads': 1, 'dependency_cache': dependency_cache})
        env = dict(os.environ, PYTHONIOENCODING='utf-8', PYTHONDONTWRITEBYTECODE='1', LEAN_NUM_THREADS='1')
        env.pop('LEAN_PATH', None)
        with (RUN / 'runner_console.log').open('w', encoding='utf-8') as log:
            code = subprocess.call([sys.executable, '-B', '-u', str(WORK / 'tools/audit_publication.py'),
                    '--run-dir', str(RUN / 'combined')], cwd=WORK, env=env, stdout=log, stderr=subprocess.STDOUT)
        require(code == 0, 'Build/target validator failed; inspect runner_console.log')
        rows = read(RUN / 'combined/RESULTS.json')
        summary = read(RUN / 'combined/SUMMARY.json')
        require(summary['status'] == 'PASS' and summary['pass'] == 607 and summary['upToDate'] == 0,
                'Not all modules were freshly compiled')
        require(not summary['notRun'] and not summary['sourcesChangedDuringRun'], 'Incomplete or changed run')
        axiom_records = 0
        for row in rows:
            require(row['status'] == 'PASS' and row['exitCode'] == 0 and not row['sorryWarning'], 'Bad module row')
            log = (RUN / 'combined/modules' / (row['module'] + '.log')).read_text(encoding='utf-8')
            require('sorryAx' not in log and "declaration uses 'sorry'" not in log, 'Sorry in module log')
            for values in re.findall(r'(?:depends on axioms:|axioms)\s*\[([^\]]*)\]', log):
                require({v.strip() for v in values.split(',') if v.strip()} <= ALLOWED, 'Unapproved axiom')
                axiom_records += 1
        for row in entries:
            require(sha(WORK / row['path']) == row['sha256'], 'Source changed during build')
            require(sha(SOURCE / row['path']) == row['sha256'], 'Frozen source changed')
        audit = read(RUN / 'combined/AUDIT_SUMMARY.json')
        require(audit['status'] == 'PASS' and audit['export_checks'] == 224, 'Audit/export count mismatch')
        save('FULL_REBUILD_VALIDATION.json', {'status': 'PASS', 'started': started,
             'finished': datetime.now(timezone.utc).isoformat(), 'modules_fresh': len(rows),
             'project_cache_hits': 0, 'all_module_axiom_records': axiom_records,
             'source_manifest_sha256': sha(MANIFEST), 'required_fresh_interfaces': REQUIRED,
             'internal_audit': 'NOT_STARTED', 'manuscript_reseal': 'PENDING'})
        return 0
    except Exception as error:
        save('FULL_REBUILD_VALIDATION.json', {'status': 'FAIL', 'reason': str(error),
             'started': started, 'finished': datetime.now(timezone.utc).isoformat(),
             'internal_audit': 'NOT_STARTED', 'freeze': 'BLOCKED'})
        raise

if __name__ == '__main__':
    sys.exit(main())
