"""Seal the run: per-gate ZIPs, final ZIP (everything except 05_BUILD and 40_PACKAGE), file manifest and
detached sha256 sidecars. Written after the last packaged edit."""
import zipfile, hashlib, json, pathlib, datetime
R = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.21_r1')
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
    res['gate_zips'].append(mkzip(f'GATE_{g}_run_v1.21_r1.zip', sorted(set(fl))))
allf = files_under('00_CONTROL', '10_LOGS', '20_EVIDENCE', '30_REPORT')
manifest = [{'path': f.relative_to(R).as_posix(), 'sha256': sha(f), 'bytes': f.stat().st_size} for f in allf]
(P / 'RUN_MANIFEST.json').write_text(json.dumps(manifest, indent=0), encoding='utf-8')
res['final_zip'] = mkzip('EXTERNAL_REVALIDATION_run_v1.21_r1.zip', allf + [P / 'RUN_MANIFEST.json'])
res['manifest_sha256'] = sha(P / 'RUN_MANIFEST.json'); res['manifest_files'] = len(manifest)
res['excluded'] = ['05_BUILD (compiled objects, extracted sources)', 'shared Mathlib/packages', 'runtimes', 'credentials (none present)']
(P / 'PACKAGE_INDEX.json').write_text(json.dumps(res, indent=1), encoding='utf-8')
print(json.dumps(res, indent=1))
