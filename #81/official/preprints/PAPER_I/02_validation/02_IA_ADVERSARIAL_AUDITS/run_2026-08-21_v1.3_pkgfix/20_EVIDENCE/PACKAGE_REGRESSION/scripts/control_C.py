#!/usr/bin/env python3
"""FINAL RESIDUAL AUDIT, PAPER_I v1.3 pkgfix — Control C, general package regression.

Checks, in order:
 1. every sidecar in the input target verifies by content;
 2. the internal residual audit ZIP verifies against its sidecar and against its own
    SHA256 list, and its members are byte-identical to the loose files;
 3. the delta against the PREVIOUS external freeze is exactly the four changes the spec
    authorizes in Section 4 - i.e. no unannounced target delta;
 4. no stale version, path or hash string;
 5. no truncated Markdown or script;
 6. the manuscript remains self-contained.
"""
import hashlib
import json
import os
import zipfile

ROOT = "C:/v13"
EXCL = "02_validation/02_IA_ADVERSARIAL_AUDITS"
PREV_INV = ("C:/ERDOS/erdos81/_worktrees/papers-i-iii-preprint-drafts-v1.1/preprints/"
            "PAPER_I/active/preprint_draft_v1.3/02_validation/02_IA_ADVERSARIAL_AUDITS/"
            "run_2026-08-21_v1.3/00_REQUEST/INPUT_INVENTORY.json")


def h(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def targets():
    out = []
    for dp, dn, fn in os.walk(ROOT):
        q = dp.replace("\\", "/")
        if EXCL in q:
            continue
        dn[:] = [d for d in dn if EXCL not in (q + "/" + d)]
        for f in fn:
            p = os.path.join(dp, f)
            out.append((p, os.path.relpath(p, ROOT).replace("\\", "/")))
    return out


def sidecars(files):
    rows = []
    for p, r in files:
        b = os.path.basename(r).lower()
        if not (b.endswith(".sha256") or "sha256" in b or "manifest" in b and b.endswith(".txt")):
            continue
        if not (b.endswith(".txt") or b.endswith(".sha256")):
            continue
        raw = open(p, "rb").read()
        crlf = raw.count(b"\r\n")
        lf = raw.count(b"\n") - crlf
        entries = []
        for line in raw.decode("utf-8", "replace").splitlines():
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split(None, 1)
            if len(parts) == 2:
                entries.append((parts[0].lower(),
                                parts[1].lstrip("*").strip().replace(chr(92), "/")))
        d = os.path.dirname(p)
        bases = [d]
        cur = d
        for _ in range(5):
            cur = os.path.dirname(cur)
            bases.append(cur)
        best = None
        for base in bases:
            ok = bad = miss = 0
            det = []
            for hh, fn in entries:
                fp = os.path.join(base, fn)
                if not os.path.isfile(fp):
                    miss += 1
                    det.append("MISSING " + fn)
                elif h(fp) == hh:
                    ok += 1
                else:
                    bad += 1
                    det.append("MISMATCH " + fn)
            cand = (miss + bad, ok, bad, miss, det)
            if best is None or cand[0] < best[0]:
                best = cand
        _, ok, bad, miss, det = best
        rows.append({"sidecar": r, "entries": len(entries), "ok": ok, "mismatch": bad,
                     "missing": miss,
                     "line_endings": "MIXED" if (crlf and lf) else ("CRLF" if crlf else "LF"),
                     "verifies": bad == 0 and miss == 0, "detail": det[:3]})
    return rows


def residual_zip():
    base = (ROOT + "/02_validation/01_INTERNAL_AUDITS/"
            "residual_run_2026-08-21_v1.3_pkgfix/40_PACKAGE")
    zp = base + "/INTERNAL_RESIDUAL_AUDIT_PACKAGE.zip"
    out = {"zip": os.path.relpath(zp, ROOT).replace("\\", "/")}
    if not os.path.isfile(zp):
        out["present"] = False
        return out
    out["present"] = True
    out["sha256"] = h(zp)
    sc = zp + ".sha256"
    if os.path.isfile(sc):
        declared = open(sc, encoding="utf-8").read().split()[0].lower()
        out["sidecar_declared"] = declared
        out["sidecar_matches"] = declared == out["sha256"]
    runroot = os.path.dirname(base)
    bad = []
    with zipfile.ZipFile(zp) as z:
        names = [n for n in z.namelist() if not n.endswith("/")]
        for n in names:
            cand = os.path.join(runroot, n.replace("/", os.sep))
            if os.path.isfile(cand):
                if hashlib.sha256(z.read(n)).hexdigest() != h(cand):
                    bad.append(n)
    out["members"] = len(names)
    out["member_hash_mismatches_vs_loose_files"] = bad[:5]
    out["members_consistent"] = not bad
    return out


def delta_vs_previous(files):
    now = {r: h(p) for p, r in files}
    if not os.path.isfile(PREV_INV):
        return {"previous_inventory_found": False}
    prev = {i["path"]: i["sha256"]
            for i in json.load(open(PREV_INV))["files"]}
    added = sorted(set(now) - set(prev))
    removed = sorted(set(prev) - set(now))
    changed = sorted(k for k in set(now) & set(prev) if now[k] != prev[k])

    def classify(paths, kind):
        buckets = {"authorized_1_scratch_removed": [],
                   "authorized_2_changelog_corrected": [],
                   "authorized_3_matrix_and_internal_residual_evidence": [],
                   "authorized_4_readme_metadata_status": [],
                   "UNANNOUNCED": []}
        for r in paths:
            if r.startswith("tmp/"):
                buckets["authorized_1_scratch_removed"].append(r)
            elif r == "CHANGELOG_v1.3.md":
                buckets["authorized_2_changelog_corrected"].append(r)
            elif ("residual_run_2026-08-21_v1.3_pkgfix" in r
                  or "RESIDUAL_MATRIX" in r.upper()
                  or "CORRECTION_MATRIX" in r.upper()):
                buckets["authorized_3_matrix_and_internal_residual_evidence"].append(r)
            elif os.path.basename(r) in ("README.md", "DRAFT_METADATA.yml",
                                         "DRAFT_NOTES.md") \
                    or "CURRENT_TARGET_SHA256" in r or "SEMANTIC_INTEGRITY" in r:
                buckets["authorized_4_readme_metadata_status"].append(r)
            else:
                buckets["UNANNOUNCED"].append(r)
        return {"kind": kind, "count": len(paths), **buckets}

    return {"previous_inventory_found": True,
            "previous_file_count": len(prev), "current_file_count": len(now),
            "added": classify(added, "added"),
            "removed": classify(removed, "removed"),
            "changed": classify(changed, "changed")}


def stale_and_truncation(files):
    stale = []
    trunc = []
    for p, r in files:
        ext = os.path.splitext(r)[1].lower()
        if ext not in (".md", ".tex", ".txt", ".json", ".py", ".yml", ".yaml"):
            continue
        try:
            t = open(p, encoding="utf-8", errors="replace").read()
        except Exception:
            continue
        if r.startswith("01_manuscript/"):
            for bad in ("v1.0.1", "lean_v1.1_freeze", "PAPER_I_LEAN_v1.1_FREEZE"):
                if bad in t:
                    stale.append({"file": r, "term": bad})
        if t and not t.rstrip().endswith((".", "}", ")", "]", "`", ">", "|", ":", "0",
                                          "1", "2", "3", "4", "5", "6", "7", "8", "9",
                                          '"', "'", "-", "*")):
            trunc.append({"file": r, "tail": t.rstrip()[-60:]})
    return {"stale_version_strings_in_manuscripts": stale,
            "possible_truncations": trunc[:10]}


def self_contained():
    bad = {}
    for lang, path in (("EN", "01_manuscript/PAPER_I_preprint_draft_v1.3.md"),
                       ("ES", "01_manuscript/PAPER_I_preprint_draft_v1.3_es.md")):
        t = open(os.path.join(ROOT, path), encoding="utf-8").read()
        hits = [x for x in ("v1.1.4", "v1.1.5", "supersede", "CORRECTION_MATRIX",
                            "EXTERNAL_AUDIT", "INTERNAL_AUDIT_FINAL", "CHANGELOG",
                            "EXT-P1-", "RES-V13-", "residual audit")
                if x.lower() in t.lower()]
        bad[lang] = hits
    return bad


def main():
    files = targets()
    sc = sidecars(files)
    out = {
        "spec": "FINAL_RESIDUAL_AUDIT_REQUEST_SPEC.md",
        "target": "preprint_draft_v1.3 (corrected)",
        "files_in_target": len(files),
        "sidecars": {"checked": len(sc),
                     "verifying": sum(1 for x in sc if x["verifies"]),
                     "failing": [x for x in sc if not x["verifies"]]},
        "internal_residual_zip": residual_zip(),
        "delta_vs_previous_external_freeze": delta_vs_previous(files),
        "stale_and_truncation": stale_and_truncation(files),
        "manuscript_self_containment_violations": self_contained(),
    }
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
