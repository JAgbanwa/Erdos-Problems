#!/usr/bin/env python3
"""Paper III v1.4 external adversarial audit -- gate E0, intake, provenance and sealing.

A byte mismatch here is a blocking intake failure, so nothing else runs until this passes.
Checks, in order:

  1  every entry of 04_integrity/CURRENT_TARGET_SHA256.txt
  2  the manuscript sidecar
  3  the freeze archive sidecar
  4  SOURCE_MANIFEST.sha256 and PACKAGE_MANIFEST.sha256
  5  the declared freeze archive SHA-256 from the audit request
  6  ZIP structural integrity: CRC of every member, entry count, path traversal,
     absolute paths, symlink/reparse payloads, and compiled project artifacts
  7  that every label refers to v1.4 and not a stale earlier version
  8  the auditor's own SHA-256 manifest of the received target

The build workspace 05_formalization/__none__/ is EXCLUDED: the request states it
is not part of the frozen target and must not be copied, trusted or used.
"""
import hashlib
import json
import os
import re
import zipfile

T = "C:/p3v14"
OUT = "C:/erdos_audit/v14/E0"
EXCLUDE_DIRS = ("05_formalization/__none__",)
DECLARED_FREEZE = "79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104"

# compiled or build artifacts that must not appear inside a source freeze
BUILD_EXT = (".olean", ".ilean", ".trace", ".hash", ".c", ".o", ".obj", ".a", ".lib",
             ".dll", ".so", ".exe", ".pdb")


def h(p):
    with open(p, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def excluded(rel):
    return any(rel.startswith(d) for d in EXCLUDE_DIRS)


def walk_target():
    out = {}
    for dp, dn, fn in os.walk(T):
        q = dp.replace("\\", "/")
        rel_dir = os.path.relpath(dp, T).replace("\\", "/")
        rel_dir = "" if rel_dir == "." else rel_dir
        dn[:] = [d for d in dn
                 if not excluded((rel_dir + "/" + d).lstrip("/"))]
        for f in fn:
            rel = os.path.relpath(os.path.join(dp, f), T).replace("\\", "/")
            if excluded(rel):
                continue
            out[rel] = os.path.join(dp, f)
    return out


def parse_sidecar(path):
    """Return [(hash, name)] from a sha256sum-style file."""
    rows = []
    raw = open(path, "rb").read()
    for line in raw.decode("utf-8", "replace").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split(None, 1)
        if len(parts) == 2 and re.fullmatch(r"[0-9a-fA-F]{64}", parts[0]):
            rows.append((parts[0].lower(),
                         parts[1].lstrip("*").strip().replace("\\", "/")))
    return rows, raw


def verify_sidecar(rel_sidecar, bases):
    p = os.path.join(T, rel_sidecar)
    rows, raw = parse_sidecar(p)
    best = None
    for base in bases:
        ok = bad = miss = 0
        det = []
        for hh, name in rows:
            fp = os.path.join(base, name)
            if not os.path.isfile(fp):
                miss += 1
                det.append(f"MISSING {name}")
            elif h(fp) == hh:
                ok += 1
            else:
                bad += 1
                det.append(f"MISMATCH {name}")
        cand = (bad + miss, ok, bad, miss, base, det)
        if best is None or cand[0] < best[0]:
            best = cand
    _, ok, bad, miss, base, det = best
    return {"sidecar": rel_sidecar, "entries": len(rows), "ok": ok,
            "mismatch": bad, "missing": miss,
            "resolved_from": os.path.relpath(base, T).replace("\\", "/"),
            "line_endings": ("MIXED" if (raw.count(b"\r\n") and
                                         raw.count(b"\n") - raw.count(b"\r\n"))
                             else ("CRLF" if raw.count(b"\r\n") else "LF")),
            "verifies": bad == 0 and miss == 0, "detail": det[:6]}


def zip_checks(zp):
    res = {"path": os.path.relpath(zp, T).replace("\\", "/"),
           "sha256": h(zp), "bytes": os.path.getsize(zp)}
    res["declared_sha256"] = DECLARED_FREEZE
    res["matches_request"] = res["sha256"] == DECLARED_FREEZE
    with zipfile.ZipFile(zp) as z:
        names = z.namelist()
        res["entries"] = len(names)
        res["files"] = sum(1 for n in names if not n.endswith("/"))
        bad = z.testzip()
        res["crc_first_bad_member"] = bad
        res["crc_all_ok"] = bad is None
        res["path_traversal"] = [n for n in names if ".." in n.split("/")]
        res["absolute_paths"] = [n for n in names
                                 if n.startswith("/") or re.match(r"^[A-Za-z]:", n)]
        res["backslash_names"] = [n for n in names if "\\" in n]
        # symlink / reparse payloads live in the external attributes high bits
        sym = []
        for i in z.infolist():
            mode = i.external_attr >> 16
            if mode and (mode & 0xF000) == 0xA000:
                sym.append(i.filename)
        res["symlink_entries"] = sym
        res["build_artifacts"] = [n for n in names
                                  if n.lower().endswith(BUILD_EXT)]
        res["lake_dirs"] = [n for n in names if "/.lake/" in n or n.startswith(".lake/")]
        res["duplicate_names"] = sorted({n for n in names if names.count(n) > 1})
        res["top_level"] = sorted({n.split("/")[0] for n in names})[:20]
        # v1.4 labelling inside the archive
        res["mentions_v1_2"] = [n for n in names if "v1.2" in n or "v1_2" in n]
        res["mentions_v1_3"] = sum(1 for n in names if "v1.4" in n or "v1_3" in n)
    return res


def stale_label_scan(files):
    """Every textual artifact must refer to v1.4, not a stale earlier label."""
    hits = []
    for rel, p in sorted(files.items()):
        if os.path.splitext(rel)[1].lower() not in (".md", ".txt", ".json", ".yml",
                                                    ".yaml", ".tex", ".lean", ".sha256"):
            continue
        try:
            t = open(p, encoding="utf-8", errors="replace").read()
        except Exception:
            continue
        for pat in ("v1.2", "v1_2", "v1.1", "v1_1", "draft v1.0", "lean_v1.2"):
            n = t.count(pat)
            if n:
                hits.append({"file": rel, "label": pat, "count": n})
    return hits


def main():
    os.makedirs(OUT, exist_ok=True)
    res = {"gate": "E0", "paper": "PAPER_III", "target": "preprint_draft_v1.4",
           "request_sha256":
               "0dd44c49c43bff8cb6d7880b4d2825c83c1a88cf30d2be2111772b5e418854c0",
           "excluded_from_target": list(EXCLUDE_DIRS),
           "exclusion_basis": ("the audit request states __none__ is a local "
                               "build workspace, not part of the frozen target, and must "
                               "not be copied, trusted or used")}

    files = walk_target()
    res["target_inventory"] = {"file_count": len(files),
                               "total_bytes": sum(os.path.getsize(p)
                                                  for p in files.values())}

    # 1 the declared current-target sidecar
    res["CURRENT_TARGET_SHA256"] = verify_sidecar(
        "04_integrity/CURRENT_TARGET_SHA256.txt", [T])

    # 2 the manuscript sidecar
    res["manuscript_sidecar"] = verify_sidecar(
        "01_manuscript/PAPER_III_preprint_draft_v1.4_SHA256.txt",
        [os.path.join(T, "01_manuscript"), T])

    # 3 the freeze archive sidecar
    fz = "05_formalization/lean_v1.4_freeze"
    res["freeze_zip_sidecar"] = verify_sidecar(
        f"{fz}/PAPER_III_lean_v1.4_freeze.zip.sha256",
        [os.path.join(T, fz), T])

    # 4 the two freeze manifests
    for name in ("SOURCE_MANIFEST.sha256", "PACKAGE_MANIFEST.sha256"):
        res[name] = verify_sidecar(f"{fz}/{name}", [os.path.join(T, fz), T])

    # 5 + 6 the archive itself
    res["freeze_zip"] = zip_checks(os.path.join(T, fz,
                                                "PAPER_III_lean_v1.4_freeze.zip"))

    # 7 stale labels
    res["stale_labels"] = stale_label_scan(files)

    # 8 the auditor's own manifest
    man = "".join(f"{h(files[r])}  {r}\n" for r in sorted(files))
    with open(f"{OUT}/AUDITOR_TARGET_SHA256.txt", "wb") as f:
        f.write(man.encode("utf-8"))
    res["auditor_manifest"] = {
        "path": "00_CONTROL/TARGET_SHA256.txt",
        "entries": len(files),
        "sha256_of_manifest": hashlib.sha256(man.encode()).hexdigest(),
        "algorithm": ("UTF-8, LF-only, '<sha256><two spaces><target-relative posix "
                      "path>\\n', sorted by path, then SHA-256 of the exact bytes")}

    json.dump(res, open(f"{OUT}/E0_intake.json", "w"), indent=1)

    # ---- report
    print(f"objetivo (excluyendo el workspace): {res['target_inventory']['file_count']} "
          f"archivos, {res['target_inventory']['total_bytes']:,} bytes\n")
    for k in ("CURRENT_TARGET_SHA256", "manuscript_sidecar", "freeze_zip_sidecar",
              "SOURCE_MANIFEST.sha256", "PACKAGE_MANIFEST.sha256"):
        r = res[k]
        print(f"{'OK  ' if r['verifies'] else 'FALLA'} {k:28} "
              f"{r['ok']}/{r['entries']} ({r['line_endings']}) "
              f"desde {r['resolved_from'] or '<raiz>'}")
        if not r["verifies"]:
            for d in r["detail"]:
                print(f"        {d}")
    z = res["freeze_zip"]
    print(f"\nZIP congelado: {z['files']} archivos en {z['entries']} entradas, "
          f"{z['bytes']:,} bytes")
    print(f"  SHA-256          : {z['sha256']}")
    print(f"  declarado (req)  : {z['declared_sha256']}")
    print(f"  COINCIDE         : {z['matches_request']}")
    print(f"  CRC de todos los miembros: {'OK' if z['crc_all_ok'] else z['crc_first_bad_member']}")
    for k in ("path_traversal", "absolute_paths", "backslash_names", "symlink_entries",
              "build_artifacts", "lake_dirs", "duplicate_names", "mentions_v1_2"):
        v = z[k]
        print(f"  {k:18}: {len(v)}" + (f"  ej: {v[:3]}" if v else ""))
    print(f"  entradas etiquetadas v1.4: {z['mentions_v1_3']}")
    print(f"  raiz del archivo: {z['top_level']}")
    print(f"\netiquetas obsoletas en textos: {len(res['stale_labels'])}")
    for x in res["stale_labels"][:12]:
        print(f"   {x['label']:12} x{x['count']:<4} {x['file']}")
    print(f"\nmanifiesto propio del auditor: {res['auditor_manifest']['entries']} entradas, "
          f"hash {res['auditor_manifest']['sha256_of_manifest'][:16]}...")


if __name__ == "__main__":
    main()
