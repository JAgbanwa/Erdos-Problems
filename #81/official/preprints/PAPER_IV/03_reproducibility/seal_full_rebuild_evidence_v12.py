"""Read-only validation of completed runs, then a separate evidence seal. No Lean."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import zipfile

BASE = Path(__file__).resolve().parent
PAPER = BASE.parent
OLD = BASE / 'full_rebuild_v12_20260929_r2'
RUN = BASE / 'full_rebuild_v12_20260929_resume'
SOURCE = PAPER / '05_formalization/lean_piv-v12-fb459343d234'
OUT = BASE / 'full_rebuild_v12_20260929_seal'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def read(p):
    return json.loads(p.read_text(encoding='utf-8-sig'))

def encode(obj):
    return (json.dumps(obj, indent=2) + '\n').encode()

def main():
    assert not OUT.exists(), 'Preserve existing seals; do not overwrite.'
    source_manifest = BASE / 'build_piv-v12-fb459343d234/SOURCE_MANIFEST.json'
    manifest = read(source_manifest)
    assert len(manifest) == 615
    assert all(sha(SOURCE / r['path']) == r['sha256'] for r in manifest)
    source_zip = PAPER / '05_formalization/LEAN_SOURCE_piv-v12-fb459343d234.zip'
    assert sha(source_zip) == 'cb2741454380736ffe01b59933057b5079fa9f865d5bbdd3f67534bf808a62e6'
    validation = read(RUN / 'FULL_REBUILD_VALIDATION.json')
    recovery = read(RUN / 'RECOVERY_CHECK.json')
    assert validation['status'] == recovery['status'] == 'PASS'
    assert validation['source_manifest_sha256'] == sha(source_manifest)
    assert not validation['preexisting_project_cache_used']
    assert all(sha(OLD / p) == h for p, h in recovery['original_evidence'].items())
    first = {r['module']: r for r in read(OLD / 'combined/RESULTS.json')}
    last = {r['module']: r for r in read(RUN / 'combined/RESULTS.json')}
    provenance = {r['module']: r for r in read(RUN / 'COMBINED_FRESH_PROVENANCE.json')}
    assert len(last) == len(provenance) == validation['unique_modules_fresh'] == 607
    assert set(last) == set(provenance)
    targets = read(SOURCE / 'FREEZE_SCOPE.json')['targets']
    axiom_records = 0
    for name, r in last.items():
        reused = r['status'] == 'UP-TO-DATE'
        origin = OLD / 'combined' if reused else RUN / 'combined'
        fresh = first[name] if reused else r
        assert fresh['status'] == 'PASS' and fresh['exitCode'] == 0 and not fresh['sorryWarning']
        assert fresh['sourceSha256'] == r['sourceSha256'] == sha(SOURCE / r['path'])
        assert provenance[name]['olean_sha256'] == fresh['oleanSha256']
        assert Path(provenance[name]['fresh_compilation_run']).resolve() == origin.resolve()
        log = origin / 'modules' / (name + '.log')
        assert (origin / 'modules' / (name + '.exit')).read_text().strip() == 'EXIT_CODE=0'
        text = log.read_text(encoding='utf-8')
        assert not re.search(r"sorryAx|declaration uses 'sorry'|^.*error(?:\(|:)", text, re.M)
        for values in re.findall(r'(?:depends on axioms:|axioms)\s*\[([^\]]*)\]', text):
            assert {v.strip() for v in values.split(',') if v.strip()} <= ALLOWED
        if reused:
            assert sha(log) == recovery['modules'][name]['log_sha256']
        if name in targets:
            assert not reused
            axiom_records += len(re.findall(r'(?:depends on axioms:|axioms)\s*\[([^\]]*)\]', text))
    summary = read(RUN / 'combined/SUMMARY.json')
    audit = read(RUN / 'combined/AUDIT_SUMMARY.json')
    assert (RUN / 'combined/BUILD.exit').read_text().strip() == 'EXIT_CODE=0'
    assert summary['status'] == audit['status'] == 'PASS'
    assert not any(summary[k] for k in ('fail', 'blocked', 'notRun', 'sourcesChangedDuringRun'))
    assert summary['pass'] == 186 and summary['upToDate'] == 421
    assert audit['targets'] == targets and len(targets) == 19
    assert axiom_records == audit['axiom_records'] == 461
    assert len(re.findall(r'^#check ', (SOURCE / 'ReleaseExportCheck.lean').read_text(encoding='utf-8'), re.M)) == audit['export_checks'] == 224
    files = [p for root in (OLD, RUN) for p in root.rglob('*') if p.is_file()]
    files += [BASE / n for n in ('REBOOT_RECOVERY_v12_20260929.md',
              'run_full_rebuild_v12_20260929.py', 'resume_full_rebuild_v12_20260929.py', Path(__file__).name)]
    assert all(p.suffix not in ('.olean', '.ilean') and '.env' not in p.name for p in files)
    rows = [{'path': p.relative_to(BASE).as_posix(), 'sha256': sha(p), 'bytes': p.stat().st_size}
            for p in sorted(files)]
    payload = encode({'source_manifest_sha256': sha(source_manifest), 'files': rows})
    OUT.mkdir()
    (OUT / 'EVIDENCE_MANIFEST.json').write_bytes(payload)
    archive = OUT / 'FULL_REBUILD_EVIDENCE_v1.2.zip'
    with zipfile.ZipFile(archive, 'x', zipfile.ZIP_DEFLATED, compresslevel=6) as z:
        z.writestr('EVIDENCE_MANIFEST.json', payload)
        for row in rows:
            z.write(BASE / row['path'], row['path'])
    with zipfile.ZipFile(archive) as z:
        assert z.testzip() is None
        assert set(z.namelist()) == {'EVIDENCE_MANIFEST.json'} | {r['path'] for r in rows}
        assert all(hashlib.sha256(z.read(r['path'])).hexdigest() == r['sha256'] for r in rows)
    record = {'status': 'PASS_LOCAL_RECORDED_BUILD_REVALIDATION',
              'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'source_cut': 'piv-v12-fb459343d234', 'source_manifest_sha256': sha(source_manifest),
              'unique_fresh_modules': 607, 'resumed_fresh': 186, 'resumed_verified_reuse': 421,
              'targets': targets, 'export_checks': 224, 'axiom_records': axiom_records,
              'manifest_sha256': sha(OUT / 'EVIDENCE_MANIFEST.json'), 'evidence_files': len(rows),
              'archive': str(archive), 'archive_sha256': sha(archive),
              'scope': 'Author-side identity and full-log recheck; not internal manuscript audit or external reproduction.',
              'internal_audit': 'NOT_STARTED', 'external_audit': 'NOT_STARTED'}
    (OUT / 'EVIDENCE_SEAL.json').write_bytes(encode(record))
    archive.with_suffix('.zip.sha256').write_text(sha(archive) + '  ' + archive.name + '\n', encoding='utf-8')
    print(json.dumps(record, indent=2))

if __name__ == '__main__':
    main()
