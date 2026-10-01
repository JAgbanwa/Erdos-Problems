"""Verify and resume the fresh reconstruction interrupted by the PC restart.

No proof/configuration edits, cache deletion, dependency installation or freeze.
Preserve the interrupted run; bind each reused object to its fresh PASS record.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys

BASE = Path(__file__).resolve().parent
PAPER = BASE.parent
OLD = BASE / 'full_rebuild_v12_20260929_r2'
RUN = BASE / 'full_rebuild_v12_20260929_resume'
WORK = Path('C:/Users/jtraverso/e81p4/piv_v12_full_rebuild_20260929')
FROZEN = PAPER / '05_formalization/lean_piv-v12-fb459343d234'
MANIFEST = BASE / 'build_piv-v12-fb459343d234/SOURCE_MANIFEST.json'
ART = WORK / '.lake/runner/lib/lean'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def read(p):
    return json.loads(p.read_text(encoding='utf-8-sig'))

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def save(name, data):
    (RUN / name).write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')

def checked_log(directory, row):
    name = row['module']
    require(row['status'] == 'PASS' and row['exitCode'] == 0 and not row['sorryWarning'], name + ': no successful compilation')
    logfile = directory / 'modules' / (name + '.log')
    require((directory / 'modules' / (name + '.exit')).read_text().strip() == 'EXIT_CODE=0', name + ': bad exit record')
    text = logfile.read_text(encoding='utf-8')
    require(not re.search(r"sorryAx|declaration uses 'sorry'|^.*error(?:\(|:)", text, re.M), name + ': bad log')
    for values in re.findall(r'(?:depends on axioms:|axioms)\s*\[([^\]]*)\]', text):
        require({v.strip() for v in values.split(',') if v.strip()} <= ALLOWED, name + ': unapproved axiom')
    return sha(logfile)

def verify():
    source = read(MANIFEST)
    require(len(source) == 615, 'Unexpected source manifest')
    for row in source:
        require(sha(WORK / row['path']) == sha(FROZEN / row['path']) == row['sha256'], 'Source mismatch: ' + row['path'])
    oldmeta = read(OLD / 'combined/RUN_META.json')
    request = read(OLD / 'REQUEST.json')
    require(request['project_cache_initially_empty'] and request['source_manifest_sha256'] == sha(MANIFEST), 'Original fresh-run identity missing')
    spec = importlib.util.spec_from_file_location('runner', WORK / 'tools/paperiv_build.py')
    planner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(planner)
    planner.ROOT = WORK
    pins, problems = planner.dependency_pins()
    require(not problems and pins == oldmeta['dependencyPins'], 'Dependency pins changed')
    version = subprocess.check_output([oldmeta['leanBinary'], '--version'], text=True).strip()
    require(version == oldmeta['lean'], 'Lean version changed')
    modules = planner.discover(WORK)
    targets = read(WORK / 'FREEZE_SCOPE.json')['targets']
    require(len(modules) == 607 and targets == oldmeta['targets'], 'Scope changed')
    opts, libs = planner.parse_lakefile(WORK / 'lakefile.toml')
    oldrows = read(OLD / 'combined/RESULTS.json')
    validated = {}
    pins_key = hashlib.sha256(json.dumps(pins, sort_keys=True).encode()).hexdigest()
    for row in oldrows:
        name = row['module']
        objectfile = ART / Path(*name.split('.')).with_suffix('.olean')
        require(sha(objectfile) == row['oleanSha256'], name + ': compiled object mismatch')
        require(sha(WORK / row['path']) == row['sourceSha256'], name + ': source record mismatch')
        lib = planner.owning_lib(name, libs)
        options = ['-j', '1'] + (list(lib['moreLeanArgs']) if lib else [])
        for k, v in opts.items():
            options += ['-D', f'{k}={v}']
        deps = {i: sha(ART / Path(*i.split('.')).with_suffix('.olean')) for i in modules[name]['local']}
        expected = {'source': row['sourceSha256'], 'deps': deps, 'options': options, 'lean': version, 'pins': pins_key}
        require(read(objectfile.with_suffix('.runner-trace.json')) == expected, name + ': trace mismatch')
        validated[name] = {'source_sha256': row['sourceSha256'], 'olean_sha256': row['oleanSha256'],
                           'log_sha256': checked_log(OLD / 'combined', row)}
    # A completed trace without a recorded PASS could otherwise be silently reused.
    trace_names = {'.'.join(p.relative_to(ART).as_posix().removesuffix('.runner-trace.json').split('/'))
                   for p in ART.rglob('*.runner-trace.json')}
    require(trace_names == set(validated), 'Unrecorded cache trace; investigate before reuse')
    oldfiles = {p.relative_to(OLD).as_posix(): sha(p) for p in OLD.rglob('*') if p.is_file()}
    return validated, oldfiles, oldmeta

def main():
    RUN.mkdir(exist_ok=True)
    require(not (RUN / 'combined').exists(), 'Resume evidence already exists; do not duplicate run')
    try:
        validated, oldfiles, oldmeta = verify()
        save('RECOVERY_CHECK.json', {'status': 'PASS', 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
             'original_run': str(OLD), 'source_manifest_sha256': sha(MANIFEST),
             'validated_fresh_modules': len(validated), 'remaining': 607 - len(validated),
             'interrupted_module': 'E34.SampleBound', 'modules': validated, 'original_evidence': oldfiles})
        print('RECOVERY PASS: ' + str(len(validated)) + '/607 freshly compiled objects verified', flush=True)
        if '--resume' not in sys.argv:
            return 0
        env = dict(os.environ, PYTHONIOENCODING='utf-8', PYTHONDONTWRITEBYTECODE='1', LEAN_NUM_THREADS='1')
        env.pop('LEAN_PATH', None)
        with (RUN / 'runner_console.log').open('w', encoding='utf-8') as log:
            code = subprocess.call([sys.executable, '-B', '-u', str(WORK / 'tools/audit_publication.py'),
                    '--run-dir', str(RUN / 'combined')], cwd=WORK, env=env, stdout=log, stderr=subprocess.STDOUT)
        require(code == 0, 'Resumed build or target validation failed')
        meta = read(RUN / 'combined/RUN_META.json')
        require(meta['dependencyPins'] == oldmeta['dependencyPins'] and meta['lean'] == oldmeta['lean'], 'Environment changed')
        rows = read(RUN / 'combined/RESULTS.json')
        require(len(rows) == 607, 'Incomplete resumed records')
        joined = []
        for row in rows:
            name = row['module']
            objectfile = ART / Path(*name.split('.')).with_suffix('.olean')
            if row['status'] == 'UP-TO-DATE':
                require(name in validated and sha(objectfile) == validated[name]['olean_sha256'], 'Unproven cache reuse: ' + name)
                origin = OLD / 'combined'
            else:
                checked_log(RUN / 'combined', row)
                require(sha(objectfile) == row['oleanSha256'], 'New object mismatch: ' + name)
                origin = RUN / 'combined'
            joined.append({'module': name, 'fresh_compilation_run': str(origin), 'olean_sha256': sha(objectfile)})
        for row in read(MANIFEST):
            require(sha(WORK / row['path']) == sha(FROZEN / row['path']) == row['sha256'], 'Sources changed')
        require(all(sha(OLD / path) == value for path, value in oldfiles.items()), 'Interrupted evidence modified')
        audit = read(RUN / 'combined/AUDIT_SUMMARY.json')
        require(audit['status'] == 'PASS' and audit['export_checks'] == 224 and audit['target_count'] == 19, 'Audit/export mismatch')
        save('COMBINED_FRESH_PROVENANCE.json', joined)
        save('FULL_REBUILD_VALIDATION.json', {'status': 'PASS', 'scope': 'Fresh project reconstruction in two verified segments',
             'unique_modules_fresh': 607, 'preexisting_project_cache_used': False,
             'resumed_reuse_from_first_segment': sum(r['status'] == 'UP-TO-DATE' for r in rows),
             'source_manifest_sha256': sha(MANIFEST), 'finished_at_utc': datetime.now(timezone.utc).isoformat(),
             'internal_audit': 'NOT_STARTED', 'manuscript_reseal': 'PENDING'})
        return 0
    except Exception as error:
        save('RECOVERY_FAILURE.json', {'status': 'FAIL', 'reason': str(error), 'freeze': 'BLOCKED'})
        raise

if __name__ == '__main__':
    sys.exit(main())
