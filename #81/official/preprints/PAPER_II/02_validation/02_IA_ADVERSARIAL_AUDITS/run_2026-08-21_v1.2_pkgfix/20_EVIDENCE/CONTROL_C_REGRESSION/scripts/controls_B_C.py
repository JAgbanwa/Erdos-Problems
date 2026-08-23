#!/usr/bin/env python3
"""PAPER_II v1.2 pkgfix — Control B (inspect the internal residual evidence, do not
trust its PASS label) and Control C (general package regression).

Control B is deliberately adversarial about one thing in particular: specification
Section 5 says R4 consists of external raw logs COPIED into the internal run. Those are
this auditor's own logs from run_2026-08-21_v1.2, so byte-consistency can be checked
directly rather than taken on faith.
"""
import hashlib
import json
import os
import zipfile

ROOT = "C:/p2t"
EXCL = "02_validation/02_IA_ADVERSARIAL_AUDITS"
IR = ROOT + "/02_validation/01_INTERNAL_AUDITS/residual_run_2026-08-21_v1.2_pkgfix"
PREV_EXT = (ROOT + "/02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-21_v1.2")
PREV_INV = PREV_EXT + "/00_REQUEST/INPUT_INVENTORY.json"

REPORT_MD = "3fac92e65b2a9f44bafb81e959f7ed46be041ddcd467d72a1b54ab13ec3a0fe0"
REPORT_PDF = "dfdfe4f6316c8707b2c9f260feddc77b095b1fc5c02b859dc76f2897c90a6761"

AUTH_CHANGED = {"04_integrity/INITIAL_SOURCE_SHA256.txt",
                "04_integrity/INITIALIZATION_DIFF.md",
                "04_integrity/README.md",
                "DRAFT_METADATA.yml", "DRAFT_NOTES.md", "README.md"}
AUTH_ADDED_FILES = {"04_integrity/CURRENT_TARGET_SHA256.txt",
                    "04_integrity/SEMANTIC_INTEGRITY_REPORT_v1.2.md",
                    "04_integrity/EXTERNAL_AUDIT_V1.2_RESIDUAL_MATRIX.md"}
AUTH_ADDED_PREFIX = ("02_validation/01_INTERNAL_AUDITS/"
                     "residual_run_2026-08-21_v1.2_pkgfix/")
SCRATCH = {".aux", ".toc", ".out", ".fls", ".fdb_latexmk", ".nav", ".snm",
           ".synctex", ".synctex.gz", ".bbl", ".blg", ".idx", ".ilg", ".ind",
           ".lof", ".lot", ".spl", ".bcf", ".run.xml"}


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


def control_B():
    o = {}
    # the internal report hashes
    md = IR + "/30_REPORT/INTERNAL_RESIDUAL_AUDIT_REPORT.md"
    pdf = IR + "/30_REPORT/INTERNAL_RESIDUAL_AUDIT_REPORT.pdf"
    o["internal_report"] = {
        "md_present": os.path.isfile(md), "pdf_present": os.path.isfile(pdf),
        "md_sha256": h(md) if os.path.isfile(md) else None,
        "md_declared": REPORT_MD,
        "md_match": os.path.isfile(md) and h(md) == REPORT_MD,
        "pdf_sha256": h(pdf) if os.path.isfile(pdf) else None,
        "pdf_declared": REPORT_PDF,
        "pdf_match": os.path.isfile(pdf) and h(pdf) == REPORT_PDF}
    # R0..R6 presence and their summaries
    gates = {}
    ev = IR + "/20_EVIDENCE"
    if os.path.isdir(ev):
        for g in sorted(os.listdir(ev)):
            d = os.path.join(ev, g)
            if not os.path.isdir(d):
                continue
            rec = {"files": []}
            for dp, dn, fn in os.walk(d):
                for f in sorted(fn):
                    rec["files"].append(os.path.relpath(os.path.join(dp, f), d)
                                        .replace("\\", "/"))
            s = os.path.join(d, "results", "summary.json")
            if os.path.isfile(s):
                try:
                    rec["summary"] = json.load(open(s, encoding="utf-8"))
                except Exception as e:
                    rec["summary_error"] = str(e)
            gates[g] = rec
    o["gates"] = gates

    # R4: the copied external logs must be byte-consistent with MY logs
    r4 = os.path.join(ev, "R4_FORMAL_REUSE", "results")
    mine = PREV_EXT + "/20_EVIDENCE/H_LEAN_REPRODUCTION/results"
    comp = []
    if os.path.isdir(r4):
        for f in sorted(os.listdir(r4)):
            p = os.path.join(r4, f)
            if not os.path.isfile(p):
                continue
            row = {"file": f, "sha256": h(p)}
            # try to find a same-content file among my own external logs
            match = None
            if os.path.isdir(mine):
                for g in os.listdir(mine):
                    q = os.path.join(mine, g)
                    if os.path.isfile(q) and h(q) == row["sha256"]:
                        match = g
                        break
            row["byte_identical_to_external_log"] = match
            comp.append(row)
    o["R4_copied_log_consistency"] = comp

    # the three substantive R4 claims
    def read(p):
        return open(p, encoding="utf-8", errors="replace").read() if os.path.isfile(p) else ""
    blog = os.path.join(r4, "BUILD_LOG.txt")
    bexit = os.path.join(r4, "BUILD_EXIT.txt")
    axr = os.path.join(r4, "AXIOMS_REPORT.txt")
    bt = read(blog)
    o["R4_substantive"] = {
        "build_exit_text": read(bexit).strip(),
        "build_exit_zero": "0" in read(bexit),
        "reports_8063_jobs": "8063 jobs" in bt,
        "build_completed_line": next((l for l in bt.splitlines()
                                      if "Build completed" in l), None),
        "axiom_surfaces": sum(1 for l in read(axr).splitlines()
                              if "depends on axioms" in l),
        "axiom_surfaces_expected": 16,
        "nonstandard_axiom_lines": [l for l in read(axr).splitlines()
                                    if "depends on axioms" in l
                                    and "propext" in l
                                    and "sorryAx" in l]}

    # R6: ZIP members and sidecar
    zp = IR + "/40_PACKAGE/INTERNAL_RESIDUAL_AUDIT_PACKAGE.zip"
    zr = {"present": os.path.isfile(zp)}
    if zr["present"]:
        zr["sha256"] = h(zp)
        sc = zp + ".sha256"
        if os.path.isfile(sc):
            zr["sidecar_declared"] = open(sc, encoding="utf-8").read().split()[0].lower()
            zr["sidecar_matches"] = zr["sidecar_declared"] == zr["sha256"]
        bad = []
        with zipfile.ZipFile(zp) as z:
            names = [n for n in z.namelist() if not n.endswith("/")]
            for n in names:
                cand = os.path.join(IR, n.replace("/", os.sep))
                if os.path.isfile(cand) and \
                   hashlib.sha256(z.read(n)).hexdigest() != h(cand):
                    bad.append(n)
        zr["members"] = len(names)
        zr["member_mismatches"] = bad[:5]
        zr["members_consistent"] = not bad
    o["R6_zip"] = zr
    return o


def control_C(files):
    o = {}
    rel = [r for _, r in files]
    o["hygiene"] = {
        "tmp_dirs": sorted({os.path.dirname(r) for r in rel
                            if any(s == "tmp" for s in r.split("/"))}),
        "scratch_files": [r for r in rel
                          if any(r.lower().endswith(e) for e in SCRATCH)],
        "zero_byte": [r for p, r in files if os.path.getsize(p) == 0],
        "dollar_names": [r for r in rel if "$" in os.path.basename(r)],
        "unexpected_hidden": [r for r in rel
                              if os.path.basename(r).startswith(".")
                              and os.path.basename(r) not in (".gitattributes",
                                                              ".gitignore")]}
    # authorized delta
    if os.path.isfile(PREV_INV):
        prev = {i["path"]: i["sha256"]
                for i in json.load(open(PREV_INV))["files"]}
        now = {r: h(p) for p, r in files}
        added = sorted(set(now) - set(prev))
        removed = sorted(set(prev) - set(now))
        changed = sorted(k for k in set(now) & set(prev) if now[k] != prev[k])
        unauth_added = [r for r in added
                        if r not in AUTH_ADDED_FILES
                        and not r.startswith(AUTH_ADDED_PREFIX)]
        unauth_changed = [r for r in changed if r not in AUTH_CHANGED]
        o["delta"] = {"previous_files": len(prev), "current_files": len(now),
                      "added": len(added), "removed": len(removed),
                      "changed": len(changed),
                      "changed_list": changed,
                      "removed_list": removed,
                      "unauthorized_additions": unauth_added,
                      "unauthorized_changes": unauth_changed,
                      "deletions_present": removed,
                      "clean": not unauth_added and not unauth_changed and not removed}
    # stale v1.0.1 and manuscript self-containment
    stale = []
    for p, r in files:
        if os.path.splitext(r)[1].lower() not in (".md", ".tex", ".txt", ".json",
                                                  ".yml", ".yaml"):
            continue
        t = open(p, encoding="utf-8", errors="replace").read()
        for term in ("v1.0.1", "lean_v1.0.1_freeze", "PAPER_II_LEAN_v1.0.1"):
            if term in t:
                stale.append({"file": r, "term": term})
    o["stale_v101_references"] = stale
    sc = {}
    for lang, path in (("EN", "01_manuscript/PAPER_II_preprint_draft_v1.2.md"),
                       ("ES", "01_manuscript/PAPER_II_preprint_draft_v1.2_es.md")):
        t = open(os.path.join(ROOT, path), encoding="utf-8").read()
        sc[lang] = [x for x in ("v1.0.1", "supersede", "CORRECTION_MATRIX",
                                "EXTERNAL_AUDIT", "RESIDUAL_MATRIX", "EXT-PII-",
                                "EXT-P2-", "residual audit")
                    if x.lower() in t.lower()]
    o["manuscript_self_containment"] = sc
    # status consistency
    stat = {}
    for f in ("README.md", "DRAFT_METADATA.yml", "DRAFT_NOTES.md"):
        p = os.path.join(ROOT, f)
        if os.path.isfile(p):
            t = open(p, encoding="utf-8", errors="replace").read()
            stat[f] = {"mentions_internal_residual_pass":
                       any(k in t for k in ("INTERNAL_RESIDUAL_PASS",
                                            "internal residual PASS",
                                            "residual PASS", "RESIDUAL_PASS")),
                       "mentions_external_pending":
                       any(k in t.lower() for k in ("external residual pending",
                                                    "external audit pending",
                                                    "pending external"))}
    o["status_consistency"] = stat
    return o


def main():
    files = targets()
    print(json.dumps({"spec": "FINAL_RESIDUAL_AUDIT_REQUEST_SPEC.md",
                      "control_B": control_B(),
                      "control_C": control_C(files)}, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
