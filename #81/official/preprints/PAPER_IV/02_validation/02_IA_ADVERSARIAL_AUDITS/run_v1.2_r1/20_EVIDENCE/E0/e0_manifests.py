"""E0 part 3 (auditor-written): manuscript manifest vs directory and ZIP; author evidence
manifest vs ZIP (hash-only, no verdict reading); annex manifest vs annex ZIP; v1.0 base config
vs bound freeze config. Read-only. Writes E0_MANIFESTS.json."""
import json, hashlib, pathlib, zipfile, re
BASE = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV')
HERE = pathlib.Path(__file__).parent
H = lambda b: hashlib.sha256(b).hexdigest()
def fsha(p): return H(pathlib.Path(p).read_bytes())
out = {}
# manuscript
MD = BASE / '01_manuscript/v1.2_full_rebuild_candidate'
mm = json.load(open(MD / 'MANUSCRIPT_MANIFEST.json', encoding='utf-8'))
files = {e['path']: e for e in mm['files']}
out['ms_manifest_files'] = len(files)
bad = []
for p, e in files.items():
    q = MD / p
    if not q.exists(): bad.append((p, 'missing')); continue
    b = q.read_bytes()
    if H(b) != e['sha256'] or len(b) != e['bytes']: bad.append((p, 'hash/bytes mismatch'))
out['ms_manifest_vs_dir_bad'] = bad
dir_files = sorted(p.relative_to(MD).as_posix() for p in MD.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
out['ms_dir_files_not_in_manifest'] = sorted(set(dir_files) - set(files))
z = zipfile.ZipFile(BASE / '01_manuscript/frozen_manuscripts/piv-v12-manuscripts-2451d43bface.zip')
zn = {i.filename: H(z.read(i)) for i in z.infolist() if not i.is_dir()}
prefixes = {n.split('/')[0] for n in zn}
out['ms_zip_prefixes'] = sorted(prefixes)[:5]
def strip(n):
    return n.split('/', 1)[1] if len(prefixes) == 1 and '/' in n else n
zs = {strip(n): h for n, h in zn.items()}
out['ms_zip_members_files'] = len(zs)
out['ms_zip_only'] = sorted(set(zs) - set(files))
out['ms_manifest_only'] = sorted(set(files) - set(zs))
out['ms_zip_hash_mismatch'] = sorted(p for p in files if p in zs and zs[p] != files[p]['sha256'])
if 'MANUSCRIPT_MANIFEST.json' in zs:
    out['ms_zip_manifest_equals_bound'] = zs['MANUSCRIPT_MANIFEST.json'] == fsha(MD / 'MANUSCRIPT_MANIFEST.json')
# figures
out['ms_figure_entries'] = sorted(p for p in files if p.startswith('figures'))
# author evidence manifest vs zip (identity only)
SE = BASE / '03_reproducibility/full_rebuild_v12_20260929_seal'
em = json.load(open(SE / 'EVIDENCE_MANIFEST.json', encoding='utf-8'))
out['ev_manifest_type'] = type(em).__name__
out['ev_manifest_keys'] = list(em.keys()) if isinstance(em, dict) else None
ev_files = em['files'] if isinstance(em, dict) and 'files' in em else em
evmap = {e['path']: e['sha256'] for e in ev_files}
out['ev_manifest_files'] = len(evmap)
z2 = zipfile.ZipFile(SE / 'FULL_REBUILD_EVIDENCE_v1.2.zip')
zn2 = {i.filename: H(z2.read(i)) for i in z2.infolist() if not i.is_dir()}
out['ev_zip_files'] = len(zn2)
# try to match by suffix
def match(evmap, zmap):
    zbyname = {}
    for n, h in zmap.items(): zbyname.setdefault(h, []).append(n)
    miss = [p for p, h in evmap.items() if h not in zbyname]
    return miss
out['ev_manifest_entries_without_matching_zip_content'] = match(evmap, zn2)[:20]
zset = set(zn2)
out['ev_zip_names_sample'] = sorted(zset)[:8]
# on-disk check of evidence manifest paths
missing_disk = []; mism_disk = []
for p, h in evmap.items():
    cands = [BASE / '03_reproducibility' / p, BASE / p]
    q = next((c for c in cands if c.exists()), None)
    if q is None: missing_disk.append(p); continue
    if fsha(q) != h: mism_disk.append(p)
out['ev_manifest_disk_missing'] = missing_disk[:20]; out['ev_manifest_disk_missing_n'] = len(missing_disk)
out['ev_manifest_disk_mismatch'] = mism_disk[:20]; out['ev_manifest_disk_mismatch_n'] = len(mism_disk)
# annex
AZ = zipfile.ZipFile(BASE / '05_formalization/LEAN_BOUNDED_GAP_ANNEX_v1.0.zip')
az = {i.filename: H(AZ.read(i)) for i in AZ.infolist() if not i.is_dir()}
out['annex_zip_members'] = sorted(az)
man = (BASE / '05_formalization/lean_v1.0_gap_annex/SOURCE_MANIFEST.sha256').read_text(encoding='utf-8')
am = {}
for line in man.splitlines():
    m = re.match(r'([0-9a-f]{64})\s+\*?(.+)', line.strip())
    if m: am[m.group(2).strip()] = m.group(1)
out['annex_manifest_entries'] = len(am)
def norm(n): return n.replace('\\', '/')
azs = {}
for n, h in az.items():
    azs[norm(n)] = h
unmatched = []
for p, h in am.items():
    hits = [n for n in azs if n.endswith(norm(p)) and azs[n] == h]
    if not hits: unmatched.append(p)
out['annex_manifest_unmatched_in_zip'] = unmatched
out['annex_bcg_lean_files'] = len([n for n in azs if n.endswith('.lean') and 'BoundedCliqueGap' in n])
# v1.0 base
BZ = zipfile.ZipFile(BASE / '05_formalization/LEAN_SOURCE_SNAPSHOT_v1.0.zip')
bz = {i.filename: BZ.read(i) for i in BZ.infolist() if not i.is_dir()}
FR = BASE / '05_formalization/lean_v1.0_freeze'
for n in ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain']:
    hits = [k for k in bz if k.split('/')[-1] == n and k.count('/') <= 1]
    out[f'base_{n}_zip_paths'] = hits
    out[f'base_{n}_equals_bound_freeze'] = [H(bz[k]) == fsha(FR / n) for k in hits]
out['base_has_BoundedCliqueGap_files'] = len([k for k in bz if 'BoundedCliqueGap' in k])
out['base_lean_files'] = len([k for k in bz if k.endswith('.lean')])
lmb = json.loads((FR / 'lake-manifest.json').read_text())
lmv = json.loads((BASE / '05_formalization/lean_piv-v12-fb459343d234/lake-manifest.json').read_text())
out['base_vs_v12_package_revs_equal'] = {p['name']: p['rev'] for p in lmb['packages']} == {p['name']: p['rev'] for p in lmv['packages']}
out['base_toolchain'] = (FR / 'lean-toolchain').read_text().strip()
out['base_lakefile_has_BCG'] = 'BoundedCliqueGap' in (FR / 'lakefile.toml').read_text()
json.dump(out, open(HERE / 'E0_MANIFESTS.json', 'w'), indent=1)
print(json.dumps(out, indent=1))
