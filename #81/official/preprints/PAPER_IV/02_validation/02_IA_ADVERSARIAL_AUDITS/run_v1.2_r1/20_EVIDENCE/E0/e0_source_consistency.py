"""E0 part 2 (auditor-written): source manifest vs ZIP, configuration consistency,
import graph closure of the 19 targets, dependency HEADs vs frozen lake-manifest.
Read-only. Writes E0_SOURCE_CONSISTENCY.json."""
import json, hashlib, pathlib, re, subprocess, os
BASE = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV')
HERE = pathlib.Path(__file__).parent
SRC = BASE / '05_formalization/lean_piv-v12-fb459343d234'
out = {}
man = json.load(open(BASE / '03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json'))
hz = json.load(open(HERE / 'source_file_hashes.json'))['zip']
mm = {e['path']: e['sha256'] for e in man}
out['manifest_entries'] = len(mm)
out['manifest_vs_zip_missing_in_zip'] = sorted(set(mm) - set(hz))
out['manifest_vs_zip_extra_in_zip'] = sorted(set(hz) - set(mm))
out['manifest_vs_zip_hash_mismatch'] = sorted(p for p in mm if p in hz and mm[p] != hz[p])
non_lean = sorted(p for p in mm if not p.endswith('.lean'))
out['non_lean_entries'] = non_lean
# configuration
cfg = {}
for n in ['lakefile.toml', 'lakefile.lean', 'lean-toolchain', 'lake-manifest.json']:
    p = SRC / n
    if p.exists(): cfg[n] = p.read_text(encoding='utf-8')
out['config_files_present'] = list(cfg)
out['lean_toolchain'] = cfg.get('lean-toolchain', '').strip()
lm = json.loads(cfg['lake-manifest.json'])
out['lake_manifest_packages'] = [{k: p.get(k) for k in ('name', 'rev', 'inputRev', 'url', 'type', 'scope')} for p in lm['packages']]
out['lakefile_text'] = cfg.get('lakefile.toml') or cfg.get('lakefile.lean')
# module graph
mods = {}
for p in SRC.rglob('*.lean'):
    rel = p.relative_to(SRC).as_posix()
    if rel.startswith('.lake/'): continue
    name = rel[:-5].replace('/', '.')
    txt = p.read_text(encoding='utf-8')
    # CORRECTION (run 2): also match `public import` / `meta import` / `private import` (Lean module system)
    imps = re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_.«»]+)', txt, re.M)
    mods[name] = imps
out['own_module_count'] = len(mods)
tg = json.load(open(SRC / 'FREEZE_SCOPE.json'))['targets']
out['targets'] = tg
out['targets_missing_as_modules'] = [t for t in tg if t not in mods]
closure = set()
per_target = {}
for t in tg:
    seen = set(); st = [t]
    while st:
        m = st.pop()
        if m in seen or m not in mods: continue
        seen.add(m); st.extend(mods[m])
    per_target[t] = len(seen); closure |= seen
out['per_target_own_closure_size'] = per_target
out['union_closure_size'] = len(closure)
out['modules_not_in_any_target_closure'] = sorted(set(mods) - closure)
ext = sorted({i.split('.')[0] for v in mods.values() for i in v if i not in mods})
out['external_import_roots'] = ext
# text scans
scan = {'sorry': [], 'admit': [], 'axiom_decl': [], 'unsafe': [], 'implemented_by': [], 'extern': [], 'native_decide': [], 'opaque': [], 'debug_skipKernelTC': [], 'ofReduceBool': []}
pats = {'sorry': r'\bsorry\b', 'admit': r'\badmit\b', 'axiom_decl': r'^\s*(private\s+|protected\s+)?axiom\s', 'unsafe': r'\bunsafe\b',
        'implemented_by': r'implemented_by', 'extern': r'@\[extern', 'native_decide': r'native_decide', 'opaque': r'^\s*(private\s+)?opaque\s',
        'debug_skipKernelTC': r'skipKernelTC|debug\.', 'ofReduceBool': r'ofReduceBool|reduceBool'}
for p in SRC.rglob('*.lean'):
    rel = p.relative_to(SRC).as_posix()
    if rel.startswith('.lake/'): continue
    for i, line in enumerate(p.read_text(encoding='utf-8').splitlines(), 1):
        code = line.split('--')[0]
        for k, pat in pats.items():
            if re.search(pat, code): scan[k].append(f'{rel}:{i}: {line.strip()[:160]}')
out['text_scan_counts'] = {k: len(v) for k, v in scan.items()}
out['text_scan'] = scan
# dependencies
PK = pathlib.Path('C:/Users/jtraverso/e81p4/preprints/PAPER_IV/05_formalization/lean/.lake/packages')
out['packages_root'] = str(PK)
out['packages_root_resolved'] = os.path.realpath(PK)
deps = []
for p in lm['packages']:
    d = PK / p['name']
    r = {'name': p['name'], 'manifest_rev': p['rev'], 'exists': d.exists(), 'resolved': os.path.realpath(d) if d.exists() else None}
    if d.exists():
        try:
            r['head'] = subprocess.run(['git', '-C', str(d), 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
            st = subprocess.run(['git', '-C', str(d), 'status', '--porcelain', '--untracked-files=no'], capture_output=True, text=True).stdout
            r['tracked_changes'] = len([l for l in st.splitlines() if l.strip()])
        except Exception as e:
            r['err'] = str(e)
        r['head_match'] = r.get('head') == p['rev']
    deps.append(r)
out['dependencies'] = deps
tc = SRC / 'lean-toolchain'
out['elan_toolchains'] = subprocess.run(['elan', 'toolchain', 'list'], capture_output=True, text=True).stdout
json.dump(out, open(HERE / 'E0_SOURCE_CONSISTENCY.json', 'w'), indent=1)
json.dump(mods, open(HERE / 'import_graph.json', 'w'), indent=0)
s = {k: v for k, v in out.items() if k not in ('text_scan', 'lakefile_text')}
print(json.dumps(s, indent=1)[:9000])
print(out['lakefile_text'])
