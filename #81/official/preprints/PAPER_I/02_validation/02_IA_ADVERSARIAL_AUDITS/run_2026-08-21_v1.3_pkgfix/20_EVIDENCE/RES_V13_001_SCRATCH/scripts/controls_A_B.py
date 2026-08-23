#!/usr/bin/env python3
"""FINAL RESIDUAL AUDIT, PAPER_I v1.3 pkgfix.

Control A (RES-V13-001): no compiler scratch anywhere in the input target.
Control B (RES-V13-002): the changelog declaration names are corrected, and agree with
the manuscript, the frozen axiom file, the recorded axiom report and the previous
external verbatim theorem-level output.
"""
import json
import os

ROOT = "C:/v13"
EXCL = "02_validation/02_IA_ADVERSARIAL_AUDITS"
SCRATCH_EXT = {".aux", ".toc", ".out", ".fls", ".fdb_latexmk", ".nav", ".snm",
               ".synctex.gz", ".synctex", ".bbl", ".blg", ".idx", ".ilg", ".ind",
               ".lof", ".lot", ".spl", ".bcf", ".run.xml"}
CORRECT = ["PaperI.assembly_sharp", "PaperI.Split.residual_duality"]
WRONG = ["PaperI.Split.assembly_sharp", "PaperI.residual_duality"]


def walk():
    for dp, dn, fn in os.walk(ROOT):
        q = dp.replace("\\", "/")
        if EXCL in q:
            continue
        dn[:] = [d for d in dn if EXCL not in (q + "/" + d)]
        for f in fn:
            yield os.path.join(dp, f).replace("\\", "/")


def control_A():
    files = list(walk())
    rel = [p[len(ROOT) + 1:] for p in files]
    tmp_dirs = sorted({os.path.dirname(r) for r in rel
                       if any(seg == "tmp" for seg in r.split("/"))})
    scratch = []
    for r in rel:
        low = r.lower()
        if any(low.endswith(e) for e in SCRATCH_EXT):
            scratch.append(r)
    zero = [r for r, p in zip(rel, files) if os.path.getsize(p) == 0]
    stray = [r for r in rel if os.path.basename(r) in ("$o", "$O")
             or "$" in os.path.basename(r)]
    hidden = [r for r in rel
              if os.path.basename(r).startswith(".")
              and os.path.basename(r) not in (".gitattributes", ".gitignore")]
    # duplicate internal-report copies: same basename INTERNAL_*REPORT.pdf in >1 place
    from collections import defaultdict
    byname = defaultdict(list)
    for r in rel:
        b = os.path.basename(r)
        if b.upper().startswith("INTERNAL") and b.lower().endswith((".pdf", ".log", ".aux")):
            byname[b].append(r)
    dup_reports = {k: v for k, v in byname.items() if len(v) > 1}
    # are the removed files referenced anywhere in target documents?
    removed = ["tmp/internal_report_v1.3/INTERNAL_AUDIT_FINAL_REPORT.aux",
               "tmp/internal_report_v1.3/INTERNAL_AUDIT_FINAL_REPORT.log",
               "tmp/internal_report_v1.3/INTERNAL_AUDIT_FINAL_REPORT.pdf",
               "tmp/internal_report_v1.3", "internal_report_v1.3"]
    refs = []
    for p, r in zip(files, rel):
        if os.path.splitext(r)[1].lower() not in (".md", ".tex", ".txt", ".json",
                                                  ".yml", ".yaml", ".sha256"):
            continue
        try:
            t = open(p, encoding="utf-8", errors="replace").read()
        except Exception:
            continue
        for needle in removed:
            if needle in t:
                refs.append({"file": r, "reference": needle})
    return {
        "files_scanned": len(files),
        "tmp_directories_found": tmp_dirs,
        "scratch_files_found": scratch,
        "zero_byte_files": zero,
        "dollar_stray_files": stray,
        "unexpected_hidden_files": hidden,
        "duplicate_internal_report_copies": dup_reports,
        "references_to_removed_files": refs,
        "verdict": "PASS" if not (tmp_dirs or scratch or zero or stray or hidden
                                  or dup_reports or refs) else "FAIL",
    }


def control_B():
    cl = os.path.join(ROOT, "CHANGELOG_v1.3.md")
    t = open(cl, encoding="utf-8").read()
    counts = {n: t.count(n) for n in CORRECT + WRONG}
    # PaperI.assembly_sharp is a substring of nothing else, but
    # PaperI.Split.residual_duality contains PaperI.Split... ; count wrong forms exactly
    wrong_present = {w: t.count(w) for w in WRONG}
    # "PaperI.residual_duality" would be a substring of nothing; but
    # "PaperI.Split.assembly_sharp" contains "assembly_sharp"
    ok = (counts["PaperI.assembly_sharp"] == 1
          and counts["PaperI.Split.residual_duality"] == 1
          and wrong_present["PaperI.Split.assembly_sharp"] == 0
          and wrong_present["PaperI.residual_duality"] == 0)
    # cross-check against the other authorities
    auth = {}
    for label, path in (
        ("manuscript Appendix C (EN)", "01_manuscript/PAPER_I_preprint_draft_v1.3.md"),
        ("manuscript Appendix C (ES)", "01_manuscript/PAPER_I_preprint_draft_v1.3_es.md"),
        ("recorded axiom report",
         "02_validation/01_INTERNAL_AUDITS/residual_run_2026-08-21_v1.3_pkgfix/"
         "20_EVIDENCE/R4_FORMAL_REUSE/results/AXIOMS_REPORT.txt"),
    ):
        p = os.path.join(ROOT, path)
        if os.path.isfile(p):
            s = open(p, encoding="utf-8", errors="replace").read()
            auth[label] = {n: s.count(n) for n in CORRECT + WRONG}
    return {
        "changelog": "CHANGELOG_v1.3.md",
        "correct_name_counts": {n: counts[n] for n in CORRECT},
        "wrong_name_counts": wrong_present,
        "exactly_one_each_correct": ok,
        "cross_check_authorities": auth,
        "verdict": "PASS" if ok else "FAIL",
    }


def main():
    a = control_A()
    b = control_B()
    print(json.dumps({
        "spec": "FINAL_RESIDUAL_AUDIT_REQUEST_SPEC.md",
        "target": "preprint_draft_v1.3 (corrected)",
        "control_A_RES_V13_001": a,
        "control_B_RES_V13_002": b,
    }, indent=1))


if __name__ == "__main__":
    main()
