#!/usr/bin/env python3
"""Sweep the release surfaces for the shadowing pattern found in manuscript_build_logs:
a current-version artifact and a stale artifact of an older version carrying the same
filename, where the stale one sits at the path a reader is more likely to open.
"""
import collections
import io
import json
import os
import re
import sys

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")

T = "C:/p3v15"
# manuscript_render_qa_v1.4/ and _v1.5/ are correctly version-labelled directories, so their
# identically-named page-NN.png contact sheets are expected duplicates, not shadowing. They are
# excluded so the sweep reports only generically-named copies of version-specific evidence.
SKIP = ("02_IA_ADVERSARIAL_AUDITS", "01_INTERNAL_AUDITS", "superseded", ".git",
        "05_formalization", "manuscript_render_qa_v1.")
OUT = "C:/v15r/20_EVIDENCE/E7_RELEASE"


def main():
    seen = collections.defaultdict(list)
    for d, dirs, fs in os.walk(T):
        rel = os.path.relpath(d, T).replace("\\", "/")
        if any(s in rel for s in SKIP):
            continue
        for f in fs:
            seen[f].append(os.path.join(d, f).replace("\\", "/"))
    dup = {k: v for k, v in seen.items() if len(v) > 1}
    print(f"filenames appearing at more than one path (release surfaces only): {len(dup)}")
    findings = []
    for k, v in sorted(dup.items()):
        print(f"\n  {k}")
        rows = []
        for p in v:
            t = ""
            try:
                t = open(p, encoding="utf-8", errors="replace").read(400000)
            except OSError:
                pass
            vers = sorted(set(re.findall(r"v?1\.\d", t)))
            m = re.search(r"Output written on (\S+)", t)
            rows.append({"path": os.path.relpath(p, T).replace("\\", "/"),
                         "versions_mentioned": vers[:6],
                         "builds": m.group(1) if m else None,
                         "bytes": os.path.getsize(p)})
            print(f"      {rows[-1]['path']}")
            print(f"        versions={rows[-1]['versions_mentioned']} "
                  f"builds={rows[-1]['builds']}")
        # shadowing = a copy that never mentions 1.5 while a sibling does
        mentions15 = [r for r in rows if any("1.5" in x for x in r["versions_mentioned"])
                      or (r["builds"] or "").find("v1.5") >= 0]
        stale = [r for r in rows if r not in mentions15]
        if mentions15 and stale:
            findings.append({"filename": k, "current": mentions15, "stale": stale})
            print(f"        --> SHADOWING: {len(stale)} stale copy/copies alongside "
                  f"{len(mentions15)} current")

    # the non-versioned consistency results file, checked directly
    print("\n=== non-versioned MANUSCRIPT_CONSISTENCY_RESULTS.json")
    p = f"{T}/03_reproducibility/MANUSCRIPT_CONSISTENCY_RESULTS.json"
    if os.path.isfile(p):
        s = open(p, encoding="utf-8", errors="replace").read()
        vers = sorted(set(re.findall(r"v?1\.\d", s)))
        print(f"  versions mentioned: {vers}")
        p5 = f"{T}/03_reproducibility/MANUSCRIPT_CONSISTENCY_RESULTS_v1.5.json"
        s5 = open(p5, encoding="utf-8", errors="replace").read()
        vers5 = sorted(set(re.findall(r"v?1\.\d", s5)))
        print(f"  v1.5 file versions mentioned: {vers5}")
        try:
            d, d5 = json.loads(s), json.loads(s5)
            print(f"  non-versioned keys: {list(d)[:8]}")
            print(f"  v1.5 keys         : {list(d5)[:8]}")
            for tag, dd in (("non-versioned", d), ("v1.5", d5)):
                for key in ("target", "version", "manuscript", "files", "checks_total",
                            "total_checks"):
                    if key in dd:
                        val = dd[key]
                        print(f"    {tag}.{key} = "
                              f"{str(val)[:120] if not isinstance(val, list) else f'[{len(val)} items]'}")
        except json.JSONDecodeError as e:
            print(f"  JSON parse issue: {e}")
        stale_nv = not any("1.5" in x for x in vers)
        print(f"  --> non-versioned file is stale relative to v1.5: {stale_nv}")
        findings.append({"filename": "MANUSCRIPT_CONSISTENCY_RESULTS.json",
                         "non_versioned_is_stale": stale_nv,
                         "versions_mentioned": vers})

    print(f"\nshadowing findings: {len(findings)}")
    with open(f"{OUT}/stale_shadowing_sweep.json", "w", encoding="utf-8",
              newline="\n") as f:
        json.dump({"duplicate_filenames": len(dup), "findings": findings}, f,
                  indent=1, ensure_ascii=False)
        f.write("\n")


if __name__ == "__main__":
    main()
