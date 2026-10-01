"""Auditor-written serial Lean build for E4 (does NOT use the author's runner or Lake).

- Sources: a fresh extraction of the bound source ZIP (or a prepared overlay dir for the annex).
- Third-party dependencies: the pinned shared package build dirs, READ-ONLY, via LEAN_PATH.
- Own objects: written only under OBJ (inside run_v1.2_r1/05_BUILD); no author .olean/.ilean used.
- Options: for each module, the package [leanOptions] as -D flags plus moreLeanArgs of the first lean_lib
  (lakefile order) whose roots/globs match (same rule Lake uses); modules in no lib get package options only.
- One lean process at a time; per-module command, exit code, wall time, log, olean sha256 recorded.
- A log containing "declaration uses 'sorry'" or an "error:" line counts as FAIL.
- Resumable only from this auditor's own records (records.jsonl), revalidating source/dep/option hashes.

usage: python auditor_build.py SRC_DIR OBJ_DIR LOG_DIR TARGET [TARGET ...] [--threads N]
"""
import sys, os, re, json, hashlib, subprocess, time, datetime, pathlib, tomllib

LEAN = pathlib.Path(os.path.expanduser('~/.elan/toolchains/leanprover--lean4---v4.28.0/bin/lean.exe'))
PKG = pathlib.Path('C:/Users/jtraverso/e81p4/preprints/PAPER_IV/05_formalization/lean/.lake/packages')
DEPS = ['mathlib', 'plausible', 'LeanSearchClient', 'importGraph', 'proofwidgets', 'aesop', 'Qq', 'batteries', 'Cli']
IMPORT_RE = re.compile(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$')

def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''): h.update(b)
    return h.hexdigest()

def header_imports(text):
    text = re.sub(r'/-.*?-/', lambda m: '\n' * m.group(0).count('\n'), text, flags=re.S)
    out = []
    for line in text.splitlines():
        line = line.split('--', 1)[0].strip()
        if not line or line == 'module' or line.startswith('prelude'):
            continue
        m = IMPORT_RE.match(line)
        if m:
            out += m.group(1).split(); continue
        break
    return out

def glob_match(g, mod):
    if g.endswith('.+'): return mod.startswith(g[:-2] + '.')
    if g.endswith('.*'): return mod == g[:-2] or mod.startswith(g[:-2] + '.')
    return mod == g

def owning_lib(mod, libs):
    for lib in libs:
        roots = lib.get('roots', [lib['name']])
        globs = lib.get('globs', roots)
        if any(glob_match(g, mod) for g in globs):
            return lib
        # Lake's isBuildableModule second clause: a module under a root is buildable if the root matches a glob
        for r in roots:
            if (mod == r or mod.startswith(r + '.')) and any(glob_match(g, r) for g in globs):
                return lib
    return None

def main():
    args = sys.argv[1:]
    threads = '1'
    if '--threads' in args:
        i = args.index('--threads'); threads = args[i + 1]; del args[i:i + 2]
    src, obj, logd = map(pathlib.Path, args[:3]); targets = args[3:]
    obj.mkdir(parents=True, exist_ok=True); (logd / 'modules').mkdir(parents=True, exist_ok=True)
    cfg = tomllib.loads((src / 'lakefile.toml').read_text(encoding='utf-8'))
    base = []
    # CORRECTION (attempt 2): tomllib nests dotted keys (pp.unicode.fun) -> flatten to dotted names
    def flat(prefix, d):
        for k, v in d.items():
            key = f'{prefix}.{k}' if prefix else k
            if isinstance(v, dict): yield from flat(key, v)
            else: yield key, v
    for k, v in flat('', cfg.get('leanOptions', {})):
        base += ['-D', f'{k}={str(v).lower() if isinstance(v, bool) else v}']
    libs = cfg.get('lean_lib', [])
    mods = {}
    for p in sorted(src.rglob('*.lean')):
        rel = p.relative_to(src)
        if rel.parts[0].startswith('.') or rel.parts[0] == 'tools': continue
        m = '.'.join(rel.with_suffix('').parts)
        mods[m] = {'path': rel.as_posix(), 'imports': header_imports(p.read_text(encoding='utf-8'))}
    for m in mods.values():
        m['local'] = [i for i in m['imports'] if i in mods]
        m['external'] = [i for i in m['imports'] if i not in mods]
    # closure + topo
    seen, st = set(), list(targets)
    while st:
        m = st.pop()
        if m in seen: continue
        if m not in mods: raise SystemExit('unknown target ' + m)
        seen.add(m); st += mods[m]['local']
    order, state = [], {}
    sys.setrecursionlimit(100000)
    def visit(m):
        if state.get(m) == 2: return
        if state.get(m) == 1: raise SystemExit('cycle at ' + m)
        state[m] = 1
        for i in sorted(mods[m]['local']): visit(i)
        state[m] = 2; order.append(m)
    for m in sorted(seen): visit(m)
    ext_roots = sorted({i.split('.')[0] for m in seen for i in mods[m]['external']})
    lean_path = [str(PKG / d / '.lake' / 'build' / 'lib' / 'lean') for d in DEPS
                 if (PKG / d / '.lake' / 'build' / 'lib' / 'lean').is_dir()] + [str(obj)]
    env = dict(os.environ); env['LEAN_PATH'] = os.pathsep.join(lean_path); env['LEAN_NUM_THREADS'] = threads
    ver = subprocess.run([str(LEAN), '--version'], capture_output=True, text=True).stdout.strip()
    meta = {'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'src': str(src), 'obj': str(obj),
            'targets': targets, 'modules_planned': len(order), 'lean': ver, 'lean_binary': str(LEAN),
            'lean_sha256': sha(LEAN), 'LEAN_PATH': lean_path, 'threads': threads, 'package_options': base,
            'external_import_roots': ext_roots, 'runner': 'auditor_build.py (auditor-written)',
            'runner_sha256': sha(pathlib.Path(__file__))}
    (logd / 'RUN_META.json').write_text(json.dumps(meta, indent=1), encoding='utf-8')
    json.dump({'order': order, 'graph': {m: mods[m] for m in order}}, open(logd / 'PLAN.json', 'w'), indent=0)
    recf = logd / 'records.jsonl'
    done = {}
    if recf.exists():
        for line in recf.read_text(encoding='utf-8').splitlines():
            r = json.loads(line); done[r['module']] = r
    failed = set()
    t_all = time.time()
    for idx, m in enumerate(order, 1):
        info = mods[m]
        lib = owning_lib(m, libs)
        extra = list(lib.get('moreLeanArgs', [])) if lib else []
        rel = pathlib.Path(*m.split('.'))
        olean = obj / rel.with_suffix('.olean'); ilean = obj / rel.with_suffix('.ilean')
        olean.parent.mkdir(parents=True, exist_ok=True)
        cmd = [str(LEAN), '-j', threads] + extra + base + [info['path'], '-o', str(olean), '-i', str(ilean)]
        if any(i in failed for i in info['local']):
            failed.add(m)
            rec = {'module': m, 'status': 'BLOCKED'}
            with open(recf, 'a', encoding='utf-8') as f: f.write(json.dumps(rec) + '\n')
            print('BLOCKED', idx, len(order), m, flush=True); continue
        key = {'source': sha(src / info['path']), 'deps': {i: done[i]['olean_sha256'] for i in info['local'] if i in done and 'olean_sha256' in done[i]},
               'cmd': cmd[1:], 'lean': ver}
        prev = done.get(m)
        if prev and prev.get('status') == 'PASS' and prev.get('key') == key and olean.exists() and sha(olean) == prev.get('olean_sha256') and m not in targets:
            print('REUSE-OWN', idx, len(order), m, flush=True); continue
        t0 = time.time()
        p = subprocess.run(cmd, cwd=src, env=env, capture_output=True, text=True, encoding='utf-8', errors='replace')
        wall = time.time() - t0
        log = p.stdout + p.stderr
        (logd / 'modules' / f'{m}.log').write_text('$ ' + ' '.join(cmd) + '\n' + log, encoding='utf-8')
        # CORRECTION C-07: Lean 4.28 prints "declaration uses `sorry`" (backticks); match any quoting
        sorry = bool(re.search(r"declaration uses .?sorry", log))
        err = bool(re.search(r'^[^\n]*\berror\b[^\n]*:', log, re.M)) and p.returncode != 0
        ok = p.returncode == 0 and not sorry and olean.exists()
        rec = {'module': m, 'index': idx, 'status': 'PASS' if ok else 'FAIL', 'exit': p.returncode, 'wall_s': round(wall, 2),
               'sorry_warning': sorry, 'error_line_and_nonzero_exit': err, 'key': key, 'lib': lib['name'] if lib else None,
               'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
        if ok: rec['olean_sha256'] = sha(olean)
        done[m] = rec
        with open(recf, 'a', encoding='utf-8') as f: f.write(json.dumps(rec) + '\n')
        print(rec['status'], idx, len(order), m, f'{wall:.1f}s', 'exit', p.returncode, flush=True)
        if not ok: failed.add(m)
    summ = {'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'modules_planned': len(order),
            'pass': sum(1 for m in order if done.get(m, {}).get('status') == 'PASS'),
            'fail_or_blocked': sorted(failed), 'wall_s_total_this_invocation': round(time.time() - t_all, 1),
            'targets_status': {t: done.get(t, {}).get('status') for t in targets}}
    (logd / 'SUMMARY.json').write_text(json.dumps(summ, indent=1), encoding='utf-8')
    print(json.dumps(summ, indent=1))
    return 0 if not failed and summ['pass'] == len(order) else 1

if __name__ == '__main__':
    sys.exit(main())
