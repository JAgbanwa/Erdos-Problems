"""Seal an already validated publication run; never builds or overwrites a cut.

Uses the current source closure, fresh target logs and the provenance of every
cached object. The output is a local source freeze, not a publication verdict.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import re
import shutil
import zipfile
import audit_publication as audit
import paperiv_build as builder

ROOT = Path(__file__).resolve().parent.parent

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def read(p):
    return json.loads(p.read_text(encoding='utf-8-sig'))

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def lean_code(text):
    """Remove nested comments and strings for a supplementary source scan."""
    depth, i, out = 0, 0, []
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth and text.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if text.startswith('--', i):
            i = text.find('\n', i)
            if i < 0:
                break
            continue
        if text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2; continue
                if text[i] == '"':
                    i += 1; break
                i += 1
            continue
        out.append(text[i]); i += 1
    return ''.join(out)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir', required=True)
    parser.add_argument('--publication-root', required=True)
    parser.add_argument('--historical-run', action='append', default=[])
    parser.add_argument('--validate-only', action='store_true')
    args = parser.parse_args()
    run = (ROOT / args.run_dir).resolve()
    pub = Path(args.publication_root).resolve()
    result = audit.validate(run, read(run / 'CONFIG_BEFORE.json'))
    require(read(run / 'AUDIT_SUMMARY.json') == result, 'Audit summary changed')
    meta, sources, rows = [read(run / name) for name in
                          ('RUN_META.json', 'SOURCES.json', 'RESULTS.json')]
    current_pins, pin_errors = builder.dependency_pins()
    require(not pin_errors and current_pins == meta['dependencyPins'],
            'Pinned dependency checkout changed')
    require(meta['threads'] == '1' and not meta['profile'], 'Unexpected build mode')
    mods = builder.discover(ROOT)
    selected = builder.closure(mods, result['targets'])
    require(selected == set(mods) == {s['module'] for s in sources},
            'Source closure is not the whole selected tree')
    require(result['export_checks'] == 224 and result['target_count'] == 19,
            'Publication scope changed')
    require(builder.header_imports((ROOT / 'ReleaseExportCheck.lean').read_text(encoding='utf-8')) == ['PaperIV'],
            'Export check has extra imports')
    historical = sorted((ROOT / 'build-logs').rglob('RESULTS.json'))
    historical += [Path(p) / 'RESULTS.json' for p in args.historical_run]
    history = {}
    for record in historical:
        for row in read(record):
            if row['status'] == 'PASS' and row.get('exitCode') == 0 and row.get('oleanSha256'):
                history[(row['module'], row['sourceSha256'], row['oleanSha256'])] = record.parent
    options, libs = builder.parse_lakefile(ROOT / 'lakefile.toml')
    base_options = [x for k, v in options.items() for x in ('-D', f'{k}={v}')]
    pins = hashlib.sha256(json.dumps(meta['dependencyPins'], sort_keys=True).encode()).hexdigest()
    artifacts = Path(meta['artifactDir'])
    provenance = []
    objects = {s['module']: artifacts / Path(*s['module'].split('.')).with_suffix('.olean') for s in sources}
    object_hashes = {m: digest(p) for m, p in objects.items()}
    for item in sources:
        module, path = item['module'], ROOT / item['path']
        require(digest(path) == item['sha256'], 'Source changed: ' + module)
        require(not re.search(r'\b(?:sorry|admit)\b|^\s*(?:private\s+)?axiom\s',
                              lean_code(path.read_text(encoding='utf-8')), re.M),
                'Placeholder or new axiom: ' + module)
        lib = builder.owning_lib(module, libs)
        expected = {'source': item['sha256'],
                    'deps': {d: object_hashes[d] for d in mods[module]['local']},
                    'options': ['-j', meta['threads']] + (list(lib['moreLeanArgs']) if lib else []) + base_options,
                    'lean': meta['lean'], 'pins': pins}
        require(read(objects[module].with_suffix('.runner-trace.json')) == expected,
                'Artifact trace mismatch: ' + module)
        origin = history.get((module, item['sha256'], object_hashes[module]))
        require(origin is not None, 'No successful provenance for object: ' + module)
        log, code = origin / 'modules' / (module + '.log'), origin / 'modules' / (module + '.exit')
        require(code.read_text().strip() == 'EXIT_CODE=0', 'Historical exit mismatch')
        require(not re.search(r"sorryAx|declaration uses 'sorry'|^.*error(?:\(|:)",
                              log.read_text(encoding='utf-8'), re.M), 'Historical build error: ' + module)
        provenance.append({'module': module, 'source_sha256': item['sha256'],
                           'object_sha256': object_hashes[module], 'origin_run': str(origin),
                           'log_sha256': digest(log), 'trace': expected})
    config = list(audit.CONFIG) + ['tools/freeze_publication.py', 'docs/PUBLICATION_AUDIT.md']
    manifest = sorted([{'path': s['path'], 'sha256': s['sha256']} for s in sources]
                      + [{'path': p, 'sha256': digest(ROOT / p)} for p in config], key=lambda x: x['path'])
    manifest_bytes = (json.dumps(manifest, indent=2, ensure_ascii=False) + '\n').encode()
    identity = hashlib.sha256(manifest_bytes).hexdigest()
    cut = 'piv-v12-' + identity[:12]
    if args.validate_only:
        print(json.dumps({'status': 'VALIDATED', 'freeze_id': cut, 'entries': len(manifest),
                          'modules': len(sources), 'axiom_records': result['axiom_records']}))
        return
    dest = pub / '05_formalization' / ('lean_' + cut)
    evidence = pub / '03_reproducibility' / ('build_' + cut)
    archive = pub / '05_formalization' / ('LEAN_SOURCE_' + cut + '.zip')
    record_path = pub / '04_integrity' / ('FREEZE_' + cut + '.json')
    require(not any(p.exists() for p in (dest, evidence, archive, record_path)), 'Cut already exists')
    for item in manifest:
        target = dest / item['path']
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / item['path'], target)
        require(digest(target) == item['sha256'], 'Source copy mismatch')
    shutil.copytree(run, evidence / 'combined')
    (evidence / 'SOURCE_MANIFEST.json').write_bytes(manifest_bytes)
    (evidence / 'CACHE_PROVENANCE.json').write_text(json.dumps(provenance, indent=2), encoding='utf-8')
    history_dir = evidence / 'cache_evidence'
    for entry in provenance:
        origin, module = Path(entry['origin_run']), entry['module']
        sub = history_dir / hashlib.sha256(str(origin).encode()).hexdigest()[:12]
        sub.mkdir(parents=True, exist_ok=True)
        for name in ('RESULTS.json', 'RUN_META.json', 'SUMMARY.json'):
            if (origin / name).exists() and not (sub / name).exists():
                shutil.copy2(origin / name, sub / name)
        for ext in ('.log', '.exit'):
            shutil.copy2(origin / 'modules' / (module + ext), sub / (module + ext))
    with zipfile.ZipFile(archive, 'x', compression=zipfile.ZIP_DEFLATED) as z:
        for item in manifest:
            z.write(dest / item['path'], item['path'])
    with zipfile.ZipFile(archive) as z:
        require(z.testzip() is None and len(z.namelist()) == len(manifest), 'ZIP CRC/scope mismatch')
        for item in manifest:
            require(hashlib.sha256(z.read(item['path'])).hexdigest() == item['sha256'], 'ZIP hash mismatch')
    record = {'freeze_id': cut, 'created_at_utc': datetime.now(timezone.utc).isoformat(),
              'source_tree': str(dest), 'manifest_sha256': identity, 'source_entries': len(manifest),
              'archive': str(archive), 'archive_sha256': digest(archive), 'lean_modules': len(sources),
              'targets': result['targets'], 'export_checks': result['export_checks'],
              'axiom_records_checked': result['axiom_records'], 'build_summary': result['build_summary'],
              'cache_provenance': 'All objects matched successful source/object hashes and complete traces.',
              'retired_modules': ['E35L.Far', 'E35L.Gate', 'E35L.Poly', 'E35L.Sched', 'FDCheck.TowerAudit'],
              'status': 'LOCAL_SOURCE_FREEZE', 'publication_status': 'NOT PUBLISHED; manuscript audits pending.'}
    encoded = json.dumps(record, indent=2) + '\n'
    record_path.write_text(encoded, encoding='utf-8')
    (evidence / 'FREEZE_RECORD.json').write_text(encoded, encoding='utf-8')
    # Seal evidence separately from source identity; neither contains dependency caches.
    hashes = [{'path': p.relative_to(evidence).as_posix(), 'sha256': digest(p)}
              for p in sorted(evidence.rglob('*')) if p.is_file()]
    (evidence / 'EVIDENCE_MANIFEST.json').write_text(json.dumps(hashes, indent=2), encoding='utf-8')
    print(encoded)

if __name__ == '__main__':
    main()
