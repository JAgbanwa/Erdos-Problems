"""E0 identity check (auditor-written). Recomputes every hash bound in AUDIT_TARGET_v1.2.json,
tests ZIP CRCs, member path safety, and compares source ZIP/dir/manifest.
Writes E0_IDENTITY.json next to this script. Read-only on targets."""
import hashlib, json, os, sys, zipfile, datetime, pathlib, re
BASE = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV')
HERE = pathlib.Path(__file__).parent
TARGET = BASE/'02_validation/02_IA_ADVERSARIAL_AUDITS/AUDIT_TARGET_v1.2.json'
def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''): h.update(b)
    return h.hexdigest()
t = json.loads(TARGET.read_text(encoding='utf-8'))
out = {'run_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'target_sha256': sha(TARGET), 'files': [], 'zips': {}}
entries = []
for e in t['verified_source_files']: entries.append(('source', e))
rb = t['required_final_bindings']
for k in ['manuscript_manifest','manuscript_freeze_record','manuscript_archive','internal_audit_package','internal_audit_final_report','internal_audit_report_pdf','internal_audit_package_verification']:
    entries.append((k, rb[k]))
for e in rb['six_manuscript_files']: entries.append(('manuscript', e))
for e in rb['author_full_build_evidence']: entries.append(('author_build_evidence', e))
for e in rb['supplementary_annex_reproduction_inputs']['files']: entries.append(('annex_input', e))
for e in rb['mandate_and_scope_hashes']: entries.append(('mandate', e))
entries.append(('author_evidence_manifest', t['author_reconstruction']['evidence_manifest']))
ok = True
for kind, e in entries:
    p = BASE/e['path']
    r = {'kind': kind, 'path': e['path'], 'expected_sha256': e['sha256'], 'exists': p.exists()}
    if p.exists():
        r['actual_sha256'] = sha(p); r['bytes'] = p.stat().st_size
        r['sha_match'] = r['actual_sha256'] == e['sha256']
        if 'bytes' in e: r['bytes_match'] = r['bytes'] == e['bytes']
        r['mtime_utc'] = datetime.datetime.fromtimestamp(p.stat().st_mtime, datetime.timezone.utc).isoformat()
    ok &= bool(r.get('sha_match')) and r.get('bytes_match', True)
    out['files'].append(r)
# ZIP integrity
def zipcheck(p):
    z = zipfile.ZipFile(p)
    bad = z.testzip()
    names = z.namelist()
    unsafe = [n for n in names if n.startswith('/') or n.startswith(chr(92)) or '..' in pathlib.PurePosixPath(n.replace(chr(92),'/')).parts or re.match(r'^[A-Za-z]:', n)]
    dup = len(names) - len(set(names))
    return z, {'members': len(names), 'first_bad_crc': bad, 'unsafe_paths': unsafe, 'duplicate_names': dup,
               'symlinks': [i.filename for i in z.infolist() if (i.external_attr >> 16) & 0o170000 == 0o120000]}
zips = {'source_zip': '05_formalization/LEAN_SOURCE_piv-v12-fb459343d234.zip',
        'annex_zip': '05_formalization/LEAN_BOUNDED_GAP_ANNEX_v1.0.zip',
        'v1_0_base_zip': '05_formalization/LEAN_SOURCE_SNAPSHOT_v1.0.zip',
        'manuscript_zip': rb['manuscript_archive']['path'],
        'author_evidence_zip': rb['author_full_build_evidence'][2]['path'],
        'internal_audit_zip': rb['internal_audit_package']['path']}
member_lists = {}
for k, rel in zips.items():
    z, info = zipcheck(BASE/rel)
    out['zips'][k] = info
    member_lists[k] = {i.filename: (i.CRC, i.file_size) for i in z.infolist()}
    ok &= info['first_bad_crc'] is None and not info['unsafe_paths'] and info['duplicate_names'] == 0
# Source ZIP vs directory vs manifest
src_dir = BASE/'05_formalization/lean_piv-v12-fb459343d234'
man = json.loads((BASE/'03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json').read_text(encoding='utf-8'))
out['source_manifest_top_keys'] = list(man.keys()) if isinstance(man, dict) else type(man).__name__
json.dump(member_lists['source_zip'], open(HERE/'source_zip_members.json','w'), indent=0)
z = zipfile.ZipFile(BASE/zips['source_zip'])
zfiles = {}
for i in z.infolist():
    if i.is_dir(): continue
    zfiles[i.filename] = hashlib.sha256(z.read(i)).hexdigest()
dfiles = {}
for p in src_dir.rglob('*'):
    if p.is_file():
        rel = p.relative_to(src_dir).as_posix()
        if '/.lake/' in '/'+rel or rel.startswith('.lake/'): continue
        dfiles[rel] = sha(p)
# zip may have a top-level prefix
prefixes = {n.split('/')[0] for n in zfiles}
out['source_zip_top_prefixes'] = sorted(prefixes)[:5]
def strip(n):
    parts = n.split('/')
    return '/'.join(parts[1:]) if len(prefixes) == 1 and len(parts) > 1 else n
zf2 = {strip(n): h for n, h in zfiles.items()}
out['source_zip_file_count'] = len(zf2)
out['source_dir_file_count_excl_lake'] = len(dfiles)
out['zip_only'] = sorted(set(zf2) - set(dfiles))
out['dir_only'] = sorted(set(dfiles) - set(zf2))
out['content_mismatch'] = sorted(n for n in set(zf2) & set(dfiles) if zf2[n] != dfiles[n])
out['lean_files_in_zip'] = sum(1 for n in zf2 if n.endswith('.lean'))
json.dump({'zip': zf2, 'dir': dfiles}, open(HERE/'source_file_hashes.json','w'), indent=0)
out['all_bound_hashes_match'] = ok
json.dump(out, open(HERE/'E0_IDENTITY.json','w'), indent=1)
print(json.dumps({k: v for k, v in out.items() if k != 'files'}, indent=1))
for r in out['files']:
    if not (r.get('sha_match') and r.get('bytes_match', True)): print('MISMATCH', r)
print('ALL_OK', ok)
