"""Verify the prepared publication; optionally restore audit inputs outside it."""
from pathlib import Path
import argparse,hashlib,json,shutil,zipfile
PAPER=Path(__file__).resolve().parents[1]
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''): h.update(b)
    return h.hexdigest()
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--restore-audit-inputs',type=Path)
    args=ap.parse_args()
    manifest=PAPER/'04_integrity/RELEASE_MANIFEST.json'
    assert sha(manifest)==manifest.with_name(manifest.name+'.sha256').read_text().split()[0]
    entries=read(manifest)['files']
    assert all(sha(PAPER/e['path'])==e['sha256'] and (PAPER/e['path']).stat().st_size==e['bytes'] for e in entries)
    expected={e['path'] for e in entries}|{'04_integrity/RELEASE_MANIFEST.json','04_integrity/RELEASE_MANIFEST.json.sha256'}
    observed={x.relative_to(PAPER).as_posix() for x in PAPER.rglob('*') if x.is_file()}
    assert observed==expected,{'missing':sorted(expected-observed),'extra':sorted(observed-expected)}
    mapping=read(PAPER/'04_integrity/RELOCATION_MAP_v1.22.json')['files']
    delta=read(PAPER/'04_integrity/RELOCATION_DELTA_v1.23.json')['paths']
    for e in mapping: assert sha(PAPER/delta.get(e['published'],e['published']))==e['sha256']
    main=read(PAPER/'03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json')
    assert len(main)==615 and all(sha(PAPER/'05_formalization/lean_piv-v12-fb459343d234'/e['path'])==e['sha256'] for e in main)
    audits=PAPER/'02_validation/02_IA_ADVERSARIAL_AUDITS'
    summary=read(audits/'run_v1.22_r4/30_REPORT/SUMMARY.json')
    assert summary['overall_verdict']=='PASS' and not summary['open_actions']
    baseline=audits/'audit_inputs/published_v1.22/01_manuscript'
    for name,digest in summary['target']['six_sha256'].items(): assert sha(baseline/name)==digest
    editorial=read(PAPER/'02_validation/03_EDITORIAL_CHECKS/v1.23/SEMANTIC_CHECKS.json')
    assert editorial['status']=='PASS' and not editorial['lean_executed']
    for record in editorial['languages']:
        for ext,digest in record['files'].items():
            assert sha(PAPER/f"01_manuscript/PAPER_IV_preprint_v1.23_{record['language']}.{ext}")==digest
    zipped=0
    for sidecar in PAPER.rglob('*.zip.sha256'):
        z=sidecar.with_suffix(''); assert sha(z)==sidecar.read_text().split()[0]
        with zipfile.ZipFile(z) as archive: assert archive.testzip() is None
        zipped+=1
    if args.restore_audit_inputs:
        dest=args.restore_audit_inputs.resolve()
        assert not dest.is_relative_to(PAPER.parent.parent),'Use a directory outside the repository'
        assert not dest.exists(),'Destination must not exist'
        for e in mapping:
            rel=Path(e['original']); assert not rel.is_absolute() and '..' not in rel.parts
            out=dest/rel
            if out.exists(): assert sha(out)==e['sha256']
            else:
                out.parent.mkdir(parents=True,exist_ok=True); shutil.copy2(PAPER/delta.get(e['published'],e['published']),out)
    print(json.dumps({'status':'PASS','release_files':len(entries),'mapped_artifacts':len(mapping),'formal_entries':len(main),'zip_sidecars_and_crc':zipped,'external_verdict_v122':summary['overall_verdict'],'editorial_v123':editorial['status'],'lean_executed':False,'restored_to':str(args.restore_audit_inputs) if args.restore_audit_inputs else None},indent=2))
if __name__=='__main__': main()
