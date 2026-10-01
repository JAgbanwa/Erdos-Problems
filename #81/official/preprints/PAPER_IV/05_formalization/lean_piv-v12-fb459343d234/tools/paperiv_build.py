#!/usr/bin/env python3
"""Cache-aware, serial, reproducible build/audit runner for the Paper IV tree.

Build-engineering tool only: it never edits sources, never touches the shared
Mathlib/package build directories, and never weakens a check.  See
BUILD_OPTIMIZATION_REPORT.md ("Runner") for the full description.

Key properties
  * The Lake environment is resolved ONCE per run (`lake env printenv LEAN_PATH`
    and `lake env lean --print-prefix`); afterwards the pinned `lean` binary is
    invoked directly, one module at a time, in topological order.  The original
    Windows driver paid a full `lake env` start-up for every module.
  * Every module gets exactly the options Lake would pass: the package
    `[leanOptions]` as `-D` flags plus the `moreLeanArgs` of the owning
    `lean_lib` (first library, in lakefile order, that can build the module).
    `ReleaseExportCheck` belongs to no library and gets the package options only.
  * Artifacts go to `.lake/runner/lib/lean` (never to Lake's own
    `.lake/build`, never to a dependency).  `--clean` removes only that
    directory.
  * Incremental mode keys each module on: SHA-256 of its source, SHA-256 of the
    `.olean` of every direct local import, the exact command-line options, the
    Lean version and the dependency pins.  Unchanged modules are skipped.
  * Failure propagation: a failing module stops the run (exit 1) unless
    `--keep-going`, in which case its dependents are reported as BLOCKED and the
    exit code is still 1.  A log containing "declaration uses 'sorry'" is a
    failure.  Per-module logs, exit codes, wall times and source hashes are
    written to the run directory.
  * Only one Lean process is ever active.  LEAN_NUM_THREADS defaults to 1.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
IS_WIN = os.name == "nt"

# ----------------------------------------------------------------------------
# lakefile.toml (minimal parser for the keys this project uses)
# ----------------------------------------------------------------------------

def _toml_value(raw: str):
    raw = raw.strip()
    if raw.startswith("["):
        return re.findall(r'"((?:[^"\\]|\\.)*)"', raw)
    if raw.startswith('"'):
        return raw.strip('"')
    return raw


def parse_lakefile(path: Path):
    try:
        import tomllib  # Python >= 3.11
        data = tomllib.loads(path.read_text(encoding="utf-8"))
        opts = {}

        def flat(prefix, d):
            for k, v in d.items():
                key = f"{prefix}.{k}" if prefix else k
                if isinstance(v, dict):
                    flat(key, v)
                else:
                    opts[key] = str(v).lower() if isinstance(v, bool) else str(v)
        flat("", data.get("leanOptions", {}))
        libs = []
        for lib in data.get("lean_lib", []):
            libs.append({
                "name": lib["name"],
                "roots": lib.get("roots", [lib["name"]]),
                "globs": lib.get("globs", None),
                "moreLeanArgs": lib.get("moreLeanArgs", []),
            })
        return opts, libs
    except ModuleNotFoundError:
        pass
    opts, libs, section, cur = {}, [], None, None
    for line in path.read_text(encoding="utf-8").splitlines():
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        if s == "[leanOptions]":
            section = "opts"; continue
        if s == "[[lean_lib]]":
            cur = {"roots": None, "globs": None, "moreLeanArgs": []}
            libs.append(cur); section = "lib"; continue
        if s.startswith("["):
            section = None; continue
        if "=" in s:
            k, v = s.split("=", 1)
            k = k.strip().strip('"'); v = _toml_value(v)
            if section == "opts":
                opts[k] = v
            elif section == "lib":
                cur[k] = v
    for lib in libs:
        if lib.get("roots") is None:
            lib["roots"] = [lib["name"]]
    return opts, libs


def _glob_matches(glob: str, mod: str) -> bool:
    if glob.endswith(".+"):
        return mod.startswith(glob[:-2] + ".")
    if glob.endswith(".*"):
        base = glob[:-2]
        return mod == base or mod.startswith(base + ".")
    return mod == glob


def owning_lib(mod: str, libs):
    """Mirror Lake's `LeanLibConfig.isBuildableModule`, first match wins."""
    for lib in libs:
        globs = lib["globs"] if lib["globs"] is not None else list(lib["roots"])
        if any(_glob_matches(g, mod) for g in globs):
            return lib
        for r in lib["roots"]:
            if (mod == r or mod.startswith(r + ".")) and any(_glob_matches(g, r) for g in globs):
                return lib
    return None

# ----------------------------------------------------------------------------
# module graph
# ----------------------------------------------------------------------------

_IMPORT_RE = re.compile(r"^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(.+)$")


def header_imports(text: str):
    """Imports of a Lean file header (comments before/among imports allowed)."""
    text = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.S)
    imps = []
    for line in text.splitlines():
        line = line.split("--", 1)[0].strip()
        if not line or line == "module" or line.startswith("prelude"):
            continue
        m = _IMPORT_RE.match(line)
        if m:
            imps += m.group(1).split()
            continue
        break
    return imps


def discover(root: Path):
    mods = {}
    for p in sorted(root.rglob("*.lean")):
        rel = p.relative_to(root)
        if rel.parts[0].startswith(".") or rel.parts[0] in ("tools", "build-logs"):
            continue
        if rel.name == "lakefile.lean":
            continue
        mod = ".".join(rel.with_suffix("").parts)
        mods[mod] = {"path": rel.as_posix(), "imports": header_imports(p.read_text(encoding="utf-8"))}
    for m in mods.values():
        m["local"] = [i for i in m["imports"] if i in mods]
    return mods


def closure(mods, targets):
    seen, stack = set(), list(targets)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        if m not in mods:
            raise SystemExit(f"unknown target module {m}")
        seen.add(m)
        stack.extend(mods[m]["local"])
    return seen


def topo(mods, subset):
    order, state = [], {}

    def visit(m, path):
        st = state.get(m)
        if st == 2:
            return
        if st == 1:
            raise SystemExit("import cycle: " + " -> ".join(path + [m]))
        state[m] = 1
        for i in sorted(mods[m]["local"]):
            visit(i, path + [m])
        state[m] = 2
        order.append(m)

    sys.setrecursionlimit(max(10000, sys.getrecursionlimit()))
    for m in sorted(subset):
        visit(m, [])
    return order

# ----------------------------------------------------------------------------
# helpers
# ----------------------------------------------------------------------------

def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def run_capture(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, **kw)


def scope_targets(scope: str, mods):
    freeze = json.loads((ROOT / "FREEZE_SCOPE.json").read_text(encoding="utf-8"))["targets"]
    if scope == "publication":
        return ["PaperIV", "ReleaseExportCheck"]
    if scope == "freeze":
        return list(freeze)
    if scope == "all":
        return sorted(mods)
    raise SystemExit(f"unknown scope {scope}")


def dependency_pins():
    man = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    pins, problems = [], []
    for pkg in man["packages"]:
        d = ROOT / ".lake" / "packages" / pkg["name"]
        r = run_capture(["git", "-C", str(d), "rev-parse", "HEAD"])
        head = r.stdout.strip() if r.returncode == 0 else None
        dirty = run_capture(["git", "-C", str(d), "status", "--porcelain", "--untracked-files=no"])
        tracked = bool(dirty.stdout.strip()) if dirty.returncode == 0 else None
        pins.append({"name": pkg["name"], "manifestRev": pkg["rev"], "head": head,
                     "trackedChanges": tracked})
        if head != pkg["rev"]:
            problems.append(f"{pkg['name']}: HEAD {head} != manifest {pkg['rev']}")
        if tracked:
            problems.append(f"{pkg['name']}: tracked edits present")
    return pins, problems

# ----------------------------------------------------------------------------
# main
# ----------------------------------------------------------------------------

PROFILE_LINE = re.compile(r"^\s+(.+?)\s+([0-9.]+(?:e[+-]?[0-9]+)?)(ms|s)\s*$")


def parse_profile(log: str):
    out, in_cum = {}, False
    for line in log.splitlines():
        if line.startswith("cumulative profiling times"):
            in_cum = True; continue
        if in_cum:
            m = PROFILE_LINE.match(line)
            if m:
                v = float(m.group(2)) * (0.001 if m.group(3) == "ms" else 1.0)
                out[m.group(1)] = round(v, 4)
            else:
                in_cum = False
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--scope", default="freeze", choices=["publication", "freeze", "all"],
                    help="publication = PaperIV + ReleaseExportCheck; freeze = every FREEZE_SCOPE.json "
                         "target (required validation); all = every source module (supplementary)")
    ap.add_argument("--targets", nargs="*", help="explicit target modules (overrides --scope)")
    ap.add_argument("--recheck-targets", action="store_true",
                    help="execute each requested target even if its dependency cache is valid")
    ap.add_argument("--clean", action="store_true", help="delete ONLY the runner artifact dir before building")
    ap.add_argument("--keep-going", action="store_true", help="continue with independent modules after a failure")
    ap.add_argument("--profile", action="store_true", help="pass -Dprofiler=true and record per-module categories")
    ap.add_argument("--profile-threshold", type=int, default=100)
    ap.add_argument("--threads", default="1", help="LEAN_NUM_THREADS / -j for each Lean process (default 1)")
    ap.add_argument("--run-dir", help="log directory (default build-logs/<timestamp>-<scope>)")
    ap.add_argument("--artifact-dir", default=".lake/runner", help="runner artifact root (inside .lake)")
    ap.add_argument("--allow-pin-mismatch", action="store_true")
    ap.add_argument("--dry-run", action="store_true", help="print the plan and the exact commands only")
    args = ap.parse_args(argv)

    t_run0 = time.perf_counter()
    mods = discover(ROOT)
    targets = args.targets if args.targets else scope_targets(args.scope, mods)
    subset = closure(mods, targets)
    order = topo(mods, subset)
    stamp = _dt.datetime.now().strftime("%Y%m%d-%H%M%S")
    label = args.scope if not args.targets else "custom"
    run_dir = Path(args.run_dir) if args.run_dir else ROOT / "build-logs" / f"{stamp}-{label}"
    if not run_dir.is_absolute():
        run_dir = ROOT / run_dir
    (run_dir / "modules").mkdir(parents=True, exist_ok=True)

    lean_opts, libs = parse_lakefile(ROOT / "lakefile.toml")

    # --- sources identity (before) ---
    src_hash = {m: sha256_file(ROOT / mods[m]["path"]) for m in order}

    # --- environment, once ---
    t_env0 = time.perf_counter()
    if IS_WIN:
        r = run_capture(["lake", "env", sys.executable, "-c",
                         "import os; print(os.environ.get('LEAN_PATH', ''))"])
    else:
        r = run_capture(["lake", "env", "printenv", "LEAN_PATH"])
    if r.returncode != 0:
        print(r.stdout, r.stderr); raise SystemExit("could not resolve Lake environment")
    lean_path_entries = [e for e in r.stdout.strip().split(os.pathsep) if e]
    pr = run_capture(["lake", "env", "lean", "--print-prefix"])
    if pr.returncode != 0:
        raise SystemExit("could not locate pinned lean")
    lean_bin = str(Path(pr.stdout.strip()) / "bin" / ("lean.exe" if IS_WIN else "lean"))
    ver = run_capture([lean_bin, "--version"]).stdout.strip()
    t_env = time.perf_counter() - t_env0
    tc = (ROOT / "lean-toolchain").read_text().strip()
    if "4.28.0" not in ver or "4.28.0" not in tc:
        raise SystemExit(f"toolchain mismatch: {ver} / {tc}")
    pins, problems = dependency_pins()
    if problems and not args.allow_pin_mismatch:
        raise SystemExit("dependency pin problems: " + "; ".join(problems))

    art_root = (ROOT / args.artifact_dir).resolve()
    if (ROOT / ".lake").resolve() not in art_root.parents:
        raise SystemExit("artifact dir must be inside the project's .lake directory")
    if art_root.name in ("build", "packages"):
        raise SystemExit("refusing to use Lake's own build/packages directory")
    lib_dir = art_root / "lib" / "lean"
    if args.clean and art_root.exists():
        shutil.rmtree(art_root)
    lib_dir.mkdir(parents=True, exist_ok=True)
    own_build = str((ROOT / ".lake" / "build" / "lib" / "lean").resolve())
    dep_entries = [e for e in lean_path_entries if str(Path(e).resolve()) != own_build]
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join(dep_entries + [str(lib_dir)])
    env["LEAN_NUM_THREADS"] = str(args.threads)
    pins_key = hashlib.sha256(json.dumps(pins, sort_keys=True).encode()).hexdigest()

    base_opts = []
    for k, v in lean_opts.items():
        base_opts += ["-D", f"{k}={v}"]

    meta = {"started": stamp, "scope": label, "targets": targets, "modules": len(order),
            "lean": ver, "leanBinary": lean_bin, "toolchain": tc, "dependencyPins": pins,
            "leanOptions": lean_opts, "threads": args.threads, "profile": args.profile,
            "clean": args.clean, "recheckTargets": args.recheck_targets,
            "envResolveSeconds": round(t_env, 3), "artifactDir": str(lib_dir),
            "leanPathDependencies": dep_entries, "python": sys.version.split()[0],
            "platform": sys.platform}
    (run_dir / "RUN_META.json").write_text(json.dumps(meta, indent=1), encoding="utf-8")

    results, failed, blocked = [], set(), set()
    status_file = run_dir / "BUILD.status"
    n = len(order)
    for idx, m in enumerate(order, 1):
        info = mods[m]
        lib = owning_lib(m, libs)
        extra = list(lib["moreLeanArgs"]) if lib else []
        rel = Path(*m.split("."))
        olean = lib_dir / rel.with_suffix(".olean")
        ilean = lib_dir / rel.with_suffix(".ilean")
        olean.parent.mkdir(parents=True, exist_ok=True)
        cmd = [lean_bin, "-j", str(args.threads)] + extra + base_opts
        # Trace key: everything that can influence the produced .olean (profiling is excluded).
        opts_key = cmd[1:]
        if args.profile:
            cmd += ["-D", "profiler=true", "-D", f"profiler.threshold={args.profile_threshold}"]
        cmd += [info["path"], "-o", str(olean), "-i", str(ilean)]
        row = {"index": idx, "module": m, "path": info["path"], "lib": lib["name"] if lib else None,
               "sourceSha256": src_hash[m]}
        if any(i in failed or i in blocked for i in info["local"]):
            blocked.add(m); row["status"] = "BLOCKED"; results.append(row)
            print(f"BLOCKED {idx}/{n} {m}", flush=True); continue
        if args.dry_run:
            print(" ".join(cmd)); continue
        dep_hashes = {i: sha256_file(lib_dir / Path(*i.split(".")).with_suffix(".olean")) for i in info["local"]}
        trace = {"source": src_hash[m], "deps": dep_hashes, "options": opts_key, "lean": ver, "pins": pins_key}
        trace_file = olean.with_suffix(".runner-trace.json")
        if olean.exists() and trace_file.exists() and not (args.recheck_targets and m in targets):
            try:
                if json.loads(trace_file.read_text(encoding="utf-8")) == trace:
                    row.update(status="UP-TO-DATE", wallSeconds=0.0)
                    results.append(row); print(f"UP-TO-DATE {idx}/{n} {m}", flush=True); continue
            except json.JSONDecodeError:
                pass
        if trace_file.exists():
            trace_file.unlink()
        status_file.write_text(f"RUNNING {idx}/{n} {m} {_dt.datetime.now().isoformat()}\n", encoding="utf-8")
        t0 = time.perf_counter()
        p = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True,
                           encoding="utf-8", errors="replace")
        wall = time.perf_counter() - t0
        log = p.stdout + p.stderr
        log_file = run_dir / "modules" / f"{m}.log"
        log_file.write_text("$ " + " ".join(cmd) + "\n" + log, encoding="utf-8")
        (run_dir / "modules" / f"{m}.exit").write_text(f"EXIT_CODE={p.returncode}\n", encoding="utf-8")
        sorry = "declaration uses 'sorry'" in log
        ok = p.returncode == 0 and not sorry and olean.exists()
        row.update(status="PASS" if ok else "FAIL", exitCode=p.returncode, wallSeconds=round(wall, 3),
                   sorryWarning=sorry)
        if args.profile:
            row["profile"] = parse_profile(log)
        if ok:
            row["oleanSha256"] = sha256_file(olean)
            trace_file.write_text(json.dumps(trace, indent=0), encoding="utf-8")
            print(f"PASS {idx}/{n} {m} {wall:.1f}s", flush=True)
        else:
            failed.add(m)
            print(f"FAIL {idx}/{n} {m} exit={p.returncode} sorry={sorry}; see {log_file}", flush=True)
        results.append(row)
        (run_dir / "RESULTS.json").write_text(json.dumps(results, indent=1), encoding="utf-8")
        if not ok and not args.keep_going:
            break

    if args.dry_run:
        return 0
    # --- sources identity (after) ---
    changed = [m for m in order if sha256_file(ROOT / mods[m]["path"]) != src_hash[m]]
    total = time.perf_counter() - t_run0
    built = [r for r in results if r.get("status") == "PASS"]
    summary = {
        "modulesPlanned": n, "pass": len(built),
        "upToDate": sum(1 for r in results if r.get("status") == "UP-TO-DATE"),
        "fail": sorted(failed), "blocked": sorted(blocked),
        "notRun": n - len(results), "sourcesChangedDuringRun": changed,
        "sumModuleWallSeconds": round(sum(r.get("wallSeconds", 0) for r in results), 2),
        "runWallSeconds": round(total, 2),
    }
    ok = not failed and not blocked and not changed and len(results) == n
    summary["status"] = "PASS" if ok else "FAIL"
    (run_dir / "RESULTS.json").write_text(json.dumps(results, indent=1), encoding="utf-8")
    (run_dir / "SUMMARY.json").write_text(json.dumps(summary, indent=1), encoding="utf-8")
    (run_dir / "SOURCES.json").write_text(json.dumps(
        [{"module": m, "path": mods[m]["path"], "sha256": src_hash[m]} for m in order], indent=0),
        encoding="utf-8")
    status_file.write_text(f"{summary['status']} {json.dumps(summary)}\n", encoding="utf-8")
    (run_dir / "BUILD.exit").write_text(f"EXIT_CODE={0 if ok else 1}\n", encoding="utf-8")
    print(json.dumps(summary, indent=1))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
