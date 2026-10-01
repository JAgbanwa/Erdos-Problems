"""Recheck the frozen local build evidence, without invoking Lean or changing caches."""
import csv
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

RUN = Path(__file__).resolve().parents[1]
PAPER = RUN.parents[2]
REPRO = PAPER / '03_reproducibility'
SOURCE = PAPER / '05_formalization/lean_piv-v12-fb459343d234'
OLD = REPRO / 'full_rebuild_v12_20260929_r2'
NEW = REPRO / 'full_rebuild_v12_20260929_resume'
OUT = RUN / '20_EVIDENCE/G4_LEAN'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def read(p):
    return json.loads(p.read_text(encoding='utf-8-sig'))

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def save(p, obj):
    p.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')

def main():
    OUT.mkdir(parents=True, exist_ok=True)
    assert not (OUT / 'RESULTS.json').exists(), 'Preserve completed attempts.'
    checks = []
    def check(name, ok, detail=None):
        checks.append({'check': name, 'pass': bool(ok), 'detail': detail})
    manifest_path = REPRO / 'build_piv-v12-fb459343d234/SOURCE_MANIFEST.json'
    manifest = read(manifest_path)
    check('source inventory', len(manifest) == 615)
    for row in manifest:
        check('source hash: ' + row['path'], sha(SOURCE / row['path']) == row['sha256'])
    validation = read(NEW / 'FULL_REBUILD_VALIDATION.json')
    recovery = read(NEW / 'RECOVERY_CHECK.json')
    check('original validation status', validation['status'] == recovery['status'] == 'PASS')
    check('validation source binding', validation['source_manifest_sha256'] == sha(manifest_path))
    check('no preexisting project cache', validation['preexisting_project_cache_used'] is False)
    for p, h in recovery['original_evidence'].items():
        check('recovery evidence hash: ' + p, sha(OLD / p) == h)
    first = {r['module']: r for r in read(OLD / 'combined/RESULTS.json')}
    last_rows = read(NEW / 'combined/RESULTS.json')
    last = {r['module']: r for r in last_rows}
    provenance = {r['module']: r for r in read(NEW / 'COMBINED_FRESH_PROVENANCE.json')}
    targets = read(SOURCE / 'FREEZE_SCOPE.json')['targets']
    check('607 unique module results', len(last) == len(last_rows) == len(provenance) == 607)
    check('same module keys', set(last) == set(provenance))
    check('19 distinct targets present', len(targets) == len(set(targets)) == 19 and set(targets) <= set(last))
    axioms, modules, target_logs, cone_records = [], [], {}, []
    pattern = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]")
    for name, r in last.items():
        reused = r['status'] == 'UP-TO-DATE'
        origin = (OLD if reused else NEW) / 'combined'
        fresh = first.get(name, {}) if reused else r
        check(name + ': fresh exit', fresh.get('status') == 'PASS' and fresh.get('exitCode') == 0 and fresh.get('sorryWarning') is False)
        check(name + ': identical source', fresh.get('sourceSha256') == r['sourceSha256'] == sha(SOURCE / r['path']))
        check(name + ': object provenance', provenance[name]['olean_sha256'] == fresh.get('oleanSha256'))
        check(name + ': origin', Path(provenance[name]['fresh_compilation_run']).resolve() == origin.resolve())
        log_path = origin / 'modules' / (name + '.log')
        exit_path = origin / 'modules' / (name + '.exit')
        check(name + ': exit file', exit_path.read_text().strip() == 'EXIT_CODE=0')
        text = log_path.read_text(encoding='utf-8-sig')
        bad = re.findall(r"sorryAx|declaration uses 'sorry'|^.*error(?:\(|:)", text, re.M)
        check(name + ': complete log scan', not bad, bad)
        lists = re.findall(r'(?:depends on axioms:|axioms)\s*\[([^\]]*)\]', text)
        check(name + ': every axiom list allowed', all({v.strip() for v in vs.split(',') if v.strip()} <= ALLOWED for vs in lists))
        if reused:
            check(name + ': reused log binding', sha(log_path) == recovery['modules'][name]['log_sha256'])
        if name in targets:
            check(name + ': target rerun', not reused)
            target_logs[name] = text
            for decl, values in pattern.findall(text):
                axioms.append({'target': name, 'declaration': decl, 'axioms': [v.strip() for v in values.split(',') if v.strip()]})
            for decl in re.findall(r"'([^']+)' does not depend on any axioms", text):
                axioms.append({'target': name, 'declaration': decl, 'axioms': []})
            for line in text.splitlines():
                if line.startswith(('PASS ', 'OK ', 'CONE ', 'HISTORICAL ')):
                    cone_records.append({'target': name, 'record': line})
        modules.append({'module': name, 'source_sha256': r['sourceSha256'], 'fresh_origin': str(origin), 'reused_on_resume': reused, 'log_sha256': sha(log_path), 'olean_sha256': fresh.get('oleanSha256'), 'exit_code': fresh.get('exitCode')})
    summary = read(NEW / 'combined/SUMMARY.json')
    audit = read(NEW / 'combined/AUDIT_SUMMARY.json')
    check('final exit', (NEW / 'combined/BUILD.exit').read_text().strip() == 'EXIT_CODE=0')
    check('summaries PASS', summary['status'] == audit['status'] == 'PASS')
    for k in ('fail', 'blocked', 'notRun', 'sourcesChangedDuringRun'):
        check('summary zero: ' + k, not summary[k])
    check('resume counts', summary['pass'] == 186 and summary['upToDate'] == 421)
    check('literal target order', audit['targets'] == targets)
    list_count = sum(len(re.findall(r'(?:depends on axioms:|axioms)\s*\[([^\]]*)\]', t)) for t in target_logs.values())
    check('461 axiom list records', list_count == audit['axiom_records'] == 461)
    exports = re.findall(r'^#check\s+(\S+)', (SOURCE / 'ReleaseExportCheck.lean').read_text(encoding='utf-8'), re.M)
    check('224 export commands', len(exports) == audit['export_checks'] == 224)
    export_log = target_logs['ReleaseExportCheck']
    export_types = []
    for name in exports:
        match = re.search(r'^' + re.escape(name) + r'(?=[.{\s:(])', export_log, re.M)
        check('export printed: ' + name, match is not None)
        export_types.append({'declaration': name, 'present_in_log': match is not None})
    dependencies = read(NEW / 'combined/RUN_META.json')
    save(OUT / 'RUN_META_COPY.json', dependencies)
    save(OUT / 'MODULE_PROVENANCE.json', modules)
    save(OUT / 'AXIOM_RECORDS.json', axioms)
    save(OUT / 'CONE_RECORDS.json', cone_records)
    save(OUT / 'EXPORT_RECORDS.json', export_types)
    (OUT / 'EXPORT_TYPES.txt').write_text(export_log, encoding='utf-8')
    failures = [c for c in checks if not c['pass']]
    result = {'status': 'PASS' if not failures else 'FAIL', 'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'scope': 'Independent author-side revalidation of the frozen local build records; no additional Lean execution.', 'module_count': len(modules), 'targets': targets, 'export_commands': len(exports), 'axiom_list_records': list_count, 'named_axiom_records': len(axioms), 'distinct_audited_declarations': len({r['declaration'] for r in axioms}), 'checks': checks, 'failures': failures}
    save(OUT / 'RESULTS.json', result)
    state_path = RUN / '00_CONTROL/AUDIT_STATE.json'
    state = read(state_path)
    state['gates']['G4'] = result['status']
    state['updated_at_utc'] = result['checked_at_utc']
    save(state_path, state)
    print(json.dumps({k: v for k, v in result.items() if k != 'checks'}, indent=2))
    raise SystemExit(bool(failures))

if __name__ == '__main__':
    main()
