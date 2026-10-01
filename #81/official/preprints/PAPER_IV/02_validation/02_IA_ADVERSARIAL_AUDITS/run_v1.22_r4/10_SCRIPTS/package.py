"""Seal the run: per-gate ZIPs, final ZIP (everything except 05_BUILD and 40_PACKAGE), file manifest and
detached sha256 sidecars. Written after the last packaged edit."""
import zipfile, hashlib, json, pathlib, datetime
R = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.22_r4')
P = R / '40_PACKAGE'; P.mkdir(exist_ok=True)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def files_under(*dirs):
    out = []
    for d in dirs:
        d = R / d
        out += [p for p in d.rglob('*') if p.is_file()] if d.is_dir() else ([d] if d.exists() else [])
    return sorted(set(out))
def mkzip(name, files):
    z = P / name
    with zipfile.ZipFile(z, 'w', zipfile.ZIP_DEFLATED) as zf:
        for f in files: zf.write(f, f.relative_to(R).as_posix())
    with zipfile.ZipFile(z) as zf: assert zf.testzip() is None
    h = sha(z); (P / (name + '.sha256')).write_text(f'{h}  {name}\n', encoding='utf-8')
    return {'zip': name, 'sha256': h, 'members': len(files), 'bytes': z.stat().st_size}
res = {'sealed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'gate_zips': []}
for g in ['E0', 'E1', 'E2', 'E3', 'E4', 'E5', 'E6', 'E7', 'E8']:
    fl = files_under(f'20_EVIDENCE/{g}', f'30_REPORT/gates/{g}_REPORT.md', f'30_REPORT/gates/{g}_REPORT.tex', f'30_REPORT/gates/{g}_REPORT.pdf')
    pass
    res['gate_zips'].append(mkzip(f'GATE_{g}_run_v1.22_r4.zip', sorted(set(fl))))
allf = files_under('00_CONTROL', '10_SCRIPTS', '20_EVIDENCE', '30_REPORT')
manifest = [{'path': f.relative_to(R).as_posix(), 'sha256': sha(f), 'bytes': f.stat().st_size} for f in allf]
(P / 'RUN_MANIFEST.json').write_text(json.dumps(manifest, indent=0), encoding='utf-8')
res['final_zip'] = mkzip('EXTERNAL_REVALIDATION_run_v1.22_r4.zip', allf + [P / 'RUN_MANIFEST.json'])
res['manifest_sha256'] = sha(P / 'RUN_MANIFEST.json'); res['manifest_files'] = len(manifest)
res['historical_packages_linked_not_duplicated'] = {'run_v1.2_r1': '886ed7f033bca42a530944d48f91ef45e79f6be4cb0d74080c5d8d6efc4f5e2b', 'run_v1.21_r1': '11659a97b0a4f2bffadb6968159cc5b66562b4470053939a45c1e8a42db7a638', 'run_v1.22_r1': '9c74d673206ab17a5b4586209ececca30536f1768fcc91ffdd39db551193a1fa', 'run_v1.22_r2': '626571be12839325a918109b446fe3e6f8d446d7f5c5911c6407af2f1e480684', 'run_v1.22_r3': '8ca5a69a1fdbb96823bf415de8de89265d14a8d2897acfed01a86c2a70fd3ddd'}
res['excluded'] = ['05_BUILD (compiled objects, extracted sources)', 'shared Mathlib/packages', 'runtimes', 'credentials (none present)']
(P / 'PACKAGE_INDEX.json').write_text(json.dumps(res, indent=1), encoding='utf-8')
print(json.dumps(res, indent=1))
import zipfile as _z
zf=_z.ZipFile(P/'EXTERNAL_REVALIDATION_run_v1.22_r4.zip'); man=json.loads((P/'RUN_MANIFEST.json').read_text())
bad=[e['path'] for e in man if hashlib.sha256(zf.read(e['path'])).hexdigest()!=e['sha256']]
print('post-check: testzip',zf.testzip(),'members',len(zf.namelist()),'manifest',len(man),'mismatch',bad, 'sidecar_ok', (P/'EXTERNAL_REVALIDATION_run_v1.22_r4.zip.sha256').read_text().split()[0]==sha(P/'EXTERNAL_REVALIDATION_run_v1.22_r4.zip'))

idx=json.loads((P/'PACKAGE_INDEX.json').read_text()); idx['final_zip_members']=sorted(zf.namelist()); idx['final_zip_crc_ok']=zf.testzip() is None
(P/'PACKAGE_INDEX.json').write_text(json.dumps(idx,indent=1),encoding='utf-8')
