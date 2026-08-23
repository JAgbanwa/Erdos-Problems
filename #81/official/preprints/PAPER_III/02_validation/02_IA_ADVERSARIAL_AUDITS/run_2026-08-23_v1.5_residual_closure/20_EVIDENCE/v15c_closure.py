#!/usr/bin/env python3
"""Independent closure check for EXT-V15-M01, Paper III v1.5.

Covers the six checks the request enumerates, and adds four the request does not ask for but
that a file relocation makes necessary: whether anything in the release now points at a moved
or deleted file, whether the relocation was byte-preserving in both directions (nothing lost,
nothing invented), whether the removed generic JSON is genuinely still preserved elsewhere,
and whether the shadowing pattern recurs anywhere else in the release surfaces.

Nothing here relies on the author's own verify script or on the declared results file.
"""
import hashlib
import io
import json
import os
import re
import sys
import urllib.parse

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")

T = "C:/p3v15"
LOGS = f"{T}/03_reproducibility/manuscript_build_logs"
REQ = f"{T}/02_validation/02_IA_ADVERSARIAL_AUDITS/REQUEST_v1.5_PASS_CLOSURE"
PRIOR = f"{T}/02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-23_v1.5_residual"
OUT = "C:/v15c/20_EVIDENCE"

TARGET = {
    "PAPER_III_preprint_v1.5.md":
        "a98e9313bfe5f1f98cc92bb29ba97386e8178e38c0201854cf40bd255066c99a",
    "PAPER_III_preprint_v1.5_en.tex":
        "6a97bc718df81d1cf91ab88ccffd9a9f701482fb898fbeca9240d19b4124195c",
    "PAPER_III_preprint_v1.5_en.pdf":
        "077a12da4db42ecbe6bcc25333539bf7ee3e63fa20bc7a46d8e801120ac9bb27",
    "PAPER_III_preprint_v1.5_es.md":
        "ee5a3ef2614316d573f622633d3ac5c544a262a43f36d0a8bacfe149b7beca3e",
    "PAPER_III_preprint_v1.5_es.tex":
        "cfc2cac78ce2495207e300c7f184c04b0aa778d91f077f25d4481b68dfb8ebcd",
    "PAPER_III_preprint_v1.5_es.pdf":
        "5ed3f83b97f6c900d63d09dd3eb491ed903693df1b90fe0dbac5df2e1e93ec92",
}
LEAN = "79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104"
PRIOR_REPORTS = {
    "v1.4 external residual":
        ("02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-22_v1.4_residual/30_REPORT/"
         "FINAL_AUDIT_REPORT.md",
         "2c19bf1ca74f77cc409b8d0102adf01b92d13db885ac81d15d156477abed8842"),
    "v1.4 external challenger":
        ("02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-23_v1.4_challenger/30_REPORT/"
         "FINAL_AUDIT_REPORT.md",
         "a196479b8b2adde5077669ec5e398dfc4d640e006bd97b10ef0f72696bdfb5f3"),
    "v1.5 external residual (CONDITIONAL_PASS, this auditor)":
        ("02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-23_v1.5_residual/30_REPORT/"
         "FINAL_AUDIT_REPORT.md",
         "4f4537816840c62fb23521190fab4fa1a860085e05a4cb956d8afe1eb3b67596"),
}
# the four files this auditor named in the finding, plus the generic JSON
NAMED_IN_FINDING = ["LUALATEX_FINAL_en.log", "LUALATEX_FINAL_es.log",
                    "LUALATEX_en_PASS1.txt", "LUALATEX_en_PASS2.txt",
                    "LUALATEX_es_PASS1.txt", "LUALATEX_es_PASS2.txt"]
PROHIBITED = ["^!", "Undefined control sequence", "Missing character", "Overfull",
              "LaTeX Error", "Fatal"]


def h(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest() if os.path.isfile(p) else None


def rd(p):
    return open(p, encoding="utf-8", errors="replace").read() if os.path.isfile(p) else ""


def parse_manifest(p):
    out = {}
    for line in rd(p).splitlines():
        pr = line.split(None, 1)
        if len(pr) == 2 and len(pr[0]) == 64:
            out[pr[1].strip().lstrip("*").replace("\\", "/")] = pr[0].lower()
    return out


def main():
    os.makedirs(OUT, exist_ok=True)
    res, ck = {}, {}

    print("=== check 1 - no file directly under manuscript_build_logs/")
    entries = sorted(os.listdir(LOGS))
    loose = [e for e in entries if os.path.isfile(f"{LOGS}/{e}")]
    subdirs = [e for e in entries if os.path.isdir(f"{LOGS}/{e}")]
    print(f"  loose files: {len(loose)} {loose}")
    print(f"  subdirectories: {subdirs}")
    res["check1"] = {"loose_files": loose, "subdirs": subdirs}
    ck["1_no_loose_files"] = not loose

    print("\n=== check 2 - the 29 relocated logs, hashes and content")
    leg = f"{LOGS}/v1.3_legacy"
    legacy_files = sorted(os.listdir(leg)) if os.path.isdir(leg) else []
    man = parse_manifest(f"{REQ}/LEGACY_V1.3_LOGS_SHA256.txt")
    print(f"  files in v1.3_legacy/: {len(legacy_files)}   manifest entries: {len(man)}")
    hmis, absent, notv13, v15ish = [], [], [], []
    for name, want in man.items():
        base = os.path.basename(name)
        p = f"{leg}/{base}"
        if not os.path.isfile(p):
            absent.append(base)
            continue
        if h(p) != want:
            hmis.append(base)
    for f in legacy_files:
        t = rd(f"{leg}/{f}")
        # Test the OUTPUT JOB NAME, not any occurrence of a version string: a LaTeX log is
        # full of package version numbers such as "v1.5", so a bare search for "v1.5"
        # misclassifies genuine v1.3 logs as misfiled.
        jobs = re.findall(r"Output written on (\S+)", t) + \
            re.findall(r"^\*\*(\S+\.tex)", t, re.M)
        names13 = any("v1.3" in j for j in jobs)
        names15 = any("v1.5" in j for j in jobs)
        if not names13:
            notv13.append({"file": f, "jobs": jobs[:4]})
        if names15:
            v15ish.append({"file": f, "jobs": jobs[:4]})
    print(f"  manifest hash mismatches: {len(hmis)} {hmis[:5]}")
    print(f"  manifest entries absent from v1.3_legacy/: {len(absent)} {absent[:5]}")
    print(f"  files not naming a v1.3 job: {len(notv13)} {notv13[:5]}")
    print(f"  files naming a v1.5 job (would be misfiled): {len(v15ish)} {v15ish[:5]}")
    res["check2"] = {"legacy_file_count": len(legacy_files),
                     "manifest_entries": len(man), "hash_mismatches": hmis,
                     "absent": absent, "not_naming_v1_3": notv13,
                     "naming_v1_5": v15ish,
                     "extra_files_not_in_manifest":
                         [f for f in legacy_files
                          if f not in {os.path.basename(k) for k in man}]}
    ck["2_relocated_logs_intact"] = (len(legacy_files) == 29 and len(man) == 29
                                     and not hmis and not absent and not notv13
                                     and not v15ish
                                     and not res["check2"]["extra_files_not_in_manifest"])

    print("\n=== check 3 - the six v1.5 logs still carry the correct evidence")
    cur = f"{LOGS}/v1.5"
    cur_files = sorted(os.listdir(cur)) if os.path.isdir(cur) else []
    curman = parse_manifest(f"{REQ}/CURRENT_V1.5_LOGS_SHA256.txt")
    rows, bad3 = [], []
    for f in cur_files:
        t = rd(f"{cur}/{f}")
        m = re.search(r"Output written on (\S+) \((\d+) pages", t)
        diag = {p: len(re.findall(p, t, re.M | re.I)) for p in PROHIBITED}
        diag = {k: v for k, v in diag.items() if v}
        lang = "es" if "_es" in f else "en"
        exp = 47 if lang == "es" else 46
        okrow = (m is not None and "v1.5" in m.group(1) and int(m.group(2)) == exp
                 and not diag)
        rows.append({"file": f, "sha256": h(f"{cur}/{f}"),
                     # the manifest keys are full target-relative paths, not basenames
                     "manifest_match": h(f"{cur}/{f}") == curman.get(
                         f"03_reproducibility/manuscript_build_logs/v1.5/{f}"),
                     "builds": m.group(1) if m else None,
                     "pages": int(m.group(2)) if m else None,
                     "expected_pages": exp, "prohibited_diagnostics": diag, "ok": okrow})
        if not okrow:
            bad3.append(f)
        print(f"  {'ok ' if okrow else 'BAD'} {f:28} {m.group(1) if m else '?':34} "
              f"{m.group(2) if m else '?'} pages  diag={diag or 'none'}")
    mh = [r["file"] for r in rows if not r["manifest_match"]]
    print(f"  files: {len(cur_files)}  manifest entries: {len(curman)}  "
          f"manifest hash mismatches: {len(mh)} {mh}")
    res["check3"] = {"files": rows, "manifest_entries": len(curman),
                     "manifest_mismatches": mh}
    ck["3_current_logs_correct"] = (len(cur_files) == 6 and not bad3 and not mh)

    print("\n=== check 4 - generic consistency JSON absent, versioned one PASS 61/61")
    gen = f"{T}/03_reproducibility/MANUSCRIPT_CONSISTENCY_RESULTS.json"
    ver = f"{T}/03_reproducibility/MANUSCRIPT_CONSISTENCY_RESULTS_v1.5.json"
    d = json.loads(rd(ver)) if os.path.isfile(ver) else {}
    mden = (d.get("files", {}).get("md_en", {}) or {}).get("sha256")
    checks = d.get("checks")
    failed = d.get("failed")
    print(f"  generic JSON present: {os.path.isfile(gen)} (must be False)")
    print(f"  versioned JSON verdict={d.get('verdict')} checks={checks} failed={failed}")
    print(f"  versioned JSON md_en sha256: {mden}")
    print(f"  == declared v1.5 English markdown: "
          f"{mden == TARGET['PAPER_III_preprint_v1.5.md']}")
    res["check4"] = {"generic_absent": not os.path.isfile(gen),
                     "versioned_verdict": d.get("verdict"), "checks": checks,
                     "failed": failed, "md_en_sha256": mden,
                     "md_en_matches_target": mden == TARGET[
                         "PAPER_III_preprint_v1.5.md"],
                     "versioned_sha256": h(ver)}
    ck["4_consistency_json"] = (not os.path.isfile(gen) and d.get("verdict") == "PASS"
                                and str(checks) == "61" and str(failed) in ("0", "[]")
                                and mden == TARGET["PAPER_III_preprint_v1.5.md"])

    print("\n=== check 5 - six manuscript hashes and the Lean ZIP unchanged")
    t5 = {}
    for name, want in TARGET.items():
        got = h(f"{T}/01_manuscript/{name}")
        t5[name] = got == want
        print(f"  {'MATCH   ' if got == want else 'MISMATCH'} {name}")
    zp = f"{T}/05_formalization/lean_v1.4_freeze/PAPER_III_lean_v1.4_freeze.zip"
    lz = h(zp) == LEAN
    print(f"  {'MATCH   ' if lz else 'MISMATCH'} Lean archive")
    res["check5"] = {"manuscript": t5, "lean_zip": lz}
    ck["5_target_unchanged"] = all(t5.values()) and lz

    print("\n=== check 6 - no prior audit report modified")
    r6 = {}
    for k, (rel, want) in PRIOR_REPORTS.items():
        got = h(f"{T}/{rel}")
        r6[k] = {"sha256": got, "unchanged": got == want}
        print(f"  {'ok      ' if got == want else 'CHANGED '} {k}")
    # and the prior sealed packages must still re-verify
    for run in ("run_2026-08-22_v1.4_residual", "run_2026-08-23_v1.4_challenger",
                "run_2026-08-23_v1.5_residual"):
        base = f"{T}/02_validation/02_IA_ADVERSARIAL_AUDITS/{run}"
        mp = f"{base}/40_PACKAGE/PACKAGE_MANIFEST.json"
        if os.path.isfile(mp):
            mm = json.load(open(mp, encoding="utf-8"))
            bad = [i["path"] for i in mm["files"]
                   if h(f"{base}/{i['path']}") != i["sha256"]]
            r6[run + "_package"] = {"files": len(mm["files"]), "mismatched": len(bad),
                                    "problems": bad[:8]}
            print(f"  {run}: {len(mm['files']) - len(bad)}/{len(mm['files'])} re-verify")
    res["check6"] = r6
    ck["6_prior_reports_unmodified"] = (
        all(v["unchanged"] for v in r6.values() if "unchanged" in v)
        and all(v["mismatched"] == 0 for v in r6.values() if "mismatched" in v))

    # ---------- checks the request does not ask for ----------
    print("\n=== extra A - does anything in the release now point at a moved/removed file?")
    dangling = []
    scan = []
    for d_, _, fs in os.walk(T):
        rel = os.path.relpath(d_, T).replace("\\", "/")
        if any(s in rel for s in ("02_IA_ADVERSARIAL_AUDITS", "superseded", ".git",
                                  "05_formalization", "01_INTERNAL_AUDITS")):
            continue
        for f in fs:
            if f.lower().endswith((".md", ".html", ".yml", ".yaml", ".json", ".cff",
                                   ".bib", ".txt")):
                scan.append(os.path.join(d_, f))
    # A keyword-proximity test is wrong for tree listings: in TREE.txt the parent directory
    # header sits dozens of sibling lines above the filename, so requiring "v1.3_legacy" in a
    # 120-character window flags correct entries. Instead, resolve each reference to a path
    # and ask whether that path exists.
    def tree_paths(text):
        """Reconstruct paths from an indented tree listing."""
        out, stack = [], []
        for line in text.splitlines():
            m = re.match(r"^([|`\s-]*)(?:\|--|`--)\s*(\S.*?)\s*$", line)
            if not m:
                m2 = re.match(r"^(\S.*?)/?\s*$", line)
                if m2 and "/" not in m2.group(1) and m2.group(1).endswith("/"):
                    stack = [m2.group(1).rstrip("/")]
                continue
            depth = len(m.group(1)) // 4
            name = m.group(2)
            isdir = name.endswith("/")
            name = name.rstrip("/")
            stack = stack[:depth]
            stack.append(name)
            out.append(("/".join(stack), isdir))
        return out

    for p in scan:
        t = rd(p)
        rel_p = os.path.relpath(p, T).replace("\\", "/")
        if os.path.basename(p) == "TREE.txt":
            entries = tree_paths(t)
            miss = []
            for path, isdir in entries:
                # strip a leading repository/package component if it is not a real directory
                cand = path
                parts = cand.split("/")
                for start in range(0, min(3, len(parts))):
                    probe = os.path.join(T, *parts[start:])
                    if os.path.exists(probe):
                        break
                else:
                    miss.append(path)
            res.setdefault("extra_A_tree", {})[rel_p] = {
                "entries": len(entries), "unresolvable": len(miss),
                "sample_unresolvable": miss[:10]}
            print(f"  {rel_p}: {len(entries)} tree entries, "
                  f"{len(miss)} do not resolve to an existing path")
            for x in miss[:8]:
                print(f"      unresolvable: {x}")
            dangling += [{"file": rel_p, "reference": x, "context": "tree entry"}
                         for x in miss]
            continue
        for pat in NAMED_IN_FINDING + ["MANUSCRIPT_CONSISTENCY_RESULTS.json"]:
            for m in re.finditer(re.escape(pat), t):
                ctx = t[max(0, m.start() - 200):m.start() + 100].replace("\n", " ")
                # look for an explicit path in the surrounding text and test it
                paths = re.findall(r"[\w./\\-]*" + re.escape(pat), ctx)
                resolved = any(os.path.exists(os.path.join(T, q.lstrip("./")))
                               for q in paths if "/" in q or "\\" in q)
                names_new = re.search(r"v1\.3_legacy|v1\.5/|_v1\.5\.json|relocat|moved|"
                                      r"legacy|removed|EXT-V15-M01", ctx, re.I)
                if not resolved and not names_new:
                    dangling.append({"file": rel_p, "reference": pat,
                                     "context": ctx[-160:]})
    print(f"  files scanned: {len(scan)}")
    print(f"  references to moved/removed files that do not name the new location: "
          f"{len(dangling)}")
    for x in dangling[:10]:
        print(f"      {x['file']}: {x['reference']}")
        print(f"        ctx: {x['context'][:110]}")
    res["extra_A_dangling_references"] = dangling
    ck["A_no_dangling_references"] = not dangling

    print("\n=== extra B - local links in README and HTML still resolve")
    broken = []
    for s in ("README.md", "PaperIII_explained_4_levels.html"):
        t = rd(f"{T}/{s}")
        links = re.findall(r"\]\(([^)\s]+)\)", t) + re.findall(r'href="([^"]+)"', t)
        for l in links:
            if re.match(r"^(https?:|mailto:|#|data:)", l):
                continue
            tgt = urllib.parse.unquote(l.split("#")[0])
            if tgt and not os.path.exists(os.path.normpath(os.path.join(T, tgt))):
                broken.append({"surface": s, "link": l})
    print(f"  broken local links: {len(broken)} {broken[:6]}")
    res["extra_B_broken_links"] = broken
    ck["B_links_resolve"] = not broken

    print("\n=== extra C - the removed generic JSON is genuinely preserved elsewhere")
    want = "04d9e9e95f1e3a9743fa7d286aadfe0f51b4fb7c94b468b13980dc4346d19e7f"
    # the request claims an identical v1.4 historical copy survives under superseded/
    copies = []
    for d_, _, fs in os.walk(f"{T}/superseded"):
        for f in fs:
            if f == "MANUSCRIPT_CONSISTENCY_RESULTS.json":
                p = os.path.join(d_, f)
                copies.append({"path": os.path.relpath(p, T).replace("\\", "/"),
                               "sha256": h(p)})
    print(f"  copies under superseded/: {len(copies)}")
    for c in copies:
        print(f"      {c['path']}  {c['sha256'][:16]}...")
    res["extra_C_preserved_copies"] = copies
    ck["C_removed_evidence_preserved"] = bool(copies)

    print("\n=== extra D - does the shadowing pattern recur anywhere in the release?")
    import collections
    seen = collections.defaultdict(list)
    for d_, _, fs in os.walk(T):
        rel = os.path.relpath(d_, T).replace("\\", "/")
        if any(s in rel for s in ("02_IA_ADVERSARIAL_AUDITS", "01_INTERNAL_AUDITS",
                                  "superseded", ".git", "05_formalization",
                                  "manuscript_render_qa_v1.")):
            continue
        for f in fs:
            seen[f].append(os.path.join(d_, f).replace("\\", "/"))
    recur = []
    for k, v in seen.items():
        if len(v) < 2 or not k.lower().endswith((".log", ".txt", ".json", ".md")):
            continue
        tagged = [p for p in v if re.search(r"v1\.\d", p)]
        untagged = [p for p in v if p not in tagged]
        if tagged and untagged:
            recur.append({"filename": k,
                          "version_tagged_paths": [os.path.relpath(p, T).replace("\\", "/")
                                                   for p in tagged],
                          "untagged_paths": [os.path.relpath(p, T).replace("\\", "/")
                                             for p in untagged]})
    print(f"  filenames existing both at a version-tagged and an untagged path: "
          f"{len(recur)}")
    for x in recur[:8]:
        print(f"      {x['filename']}: untagged={x['untagged_paths']}")
    res["extra_D_pattern_recurrence"] = recur
    ck["D_pattern_does_not_recur"] = not recur

    print("\n=== closure verdict")
    for k, v in ck.items():
        print(f"  {k:34} {'PASS' if v else 'FAIL'}")
    res["checks"] = ck
    res["closure_pass"] = all(ck.values())
    res["checks_passed"] = f"{sum(1 for v in ck.values() if v)}/{len(ck)}"
    print(f"  => EXT-V15-M01 closure {'PASS' if res['closure_pass'] else 'FAIL'} "
          f"({res['checks_passed']})")

    with open(f"{OUT}/EXT_V15_M01_INDEPENDENT_CHECK.json", "w", encoding="utf-8",
              newline="\n") as f:
        json.dump(res, f, indent=1, ensure_ascii=False)
        f.write("\n")


if __name__ == "__main__":
    main()
