#!/usr/bin/env python3
"""E6 - prior-art/novelty regression, and E7 - release package and public surfaces.

E6 is a regression check, not a fresh literature sweep: the obligation is to show that v1.5
changed no citation, bibliography entry or novelty proposition relative to the audited v1.4,
and that the bounded negative statement is retained rather than promoted to an absolute
priority claim.

E7 checks that the seven release surfaces agree with each other and with the manuscript,
that every local link resolves, that the HTML states the split-graph scope and leaves the full
chordal problem open, and that v1.5 is represented as a first public preprint rather than as
superseding a prior official release.
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
OLD = f"{T}/superseded/unpublished_audited_draft_v1.4/01_manuscript"
EN_OLD = f"{OLD}/PAPER_III_preprint_draft_v1.4.md"
EN_NEW = f"{T}/01_manuscript/PAPER_III_preprint_v1.5.md"
ES_NEW = f"{T}/01_manuscript/PAPER_III_preprint_v1.5_es.md"
OUT6 = "C:/v15r/20_EVIDENCE/E6_PRIORART"
OUT7 = "C:/v15r/20_EVIDENCE/E7_RELEASE"

SURFACES = ["README.md", "CHANGELOG_v1.5.md", "RELEASE_METADATA.yml", "RELEASE_NOTES.md",
            "CITATION.cff", "CITATION.bib", "PaperIII_explained_4_levels.html"]


def rd(p):
    return open(p, encoding="utf-8", errors="replace").read() if os.path.isfile(p) else ""


def h(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest() if os.path.isfile(p) else None


def bibliography(t):
    """Ordered bibliography entries [n] ... from the references section."""
    m = re.search(r"^#+\s*(?:References|Referencias|Bibliography)\s*$", t, re.M)
    tail = t[m.end():] if m else t
    return [re.sub(r"\s+", " ", x).strip()
            for x in re.findall(r"^\[(\d+)\][^\n]*", tail, re.M)]


def bib_entries(t):
    m = re.search(r"^#+\s*(?:References|Referencias|Bibliography)\s*$", t, re.M)
    tail = t[m.end():] if m else t
    return [re.sub(r"\s+", " ", x).strip() for x in re.findall(r"^\[\d+\][^\n]*", tail, re.M)]


def main():
    os.makedirs(OUT6, exist_ok=True)
    os.makedirs(OUT7, exist_ok=True)
    a, b, es = rd(EN_OLD), rd(EN_NEW), rd(ES_NEW)

    # ================= E6 =================
    print("=== E6.1 citation and bibliography regression, audited v1.4 -> v1.5 (EN)")
    r6 = {}
    ba, bb = bib_entries(a), bib_entries(b)
    r6["bibliography"] = {"v1_4_entries": len(ba), "v1_5_entries": len(bb),
                          "identical": ba == bb,
                          "only_v1_4": [x[:110] for x in ba if x not in bb][:6],
                          "only_v1_5": [x[:110] for x in bb if x not in ba][:6]}
    print(f"  bibliography entries {len(ba)} -> {len(bb)}  identical: {ba == bb}")
    for x in r6["bibliography"]["only_v1_4"]:
        print(f"      only v1.4: {x}")
    for x in r6["bibliography"]["only_v1_5"]:
        print(f"      only v1.5: {x}")

    ca = re.findall(r"\[(\d+(?:\s*,\s*\d+)*)\]", a)
    cb = re.findall(r"\[(\d+(?:\s*,\s*\d+)*)\]", b)
    r6["citation_sequence_identical"] = ca == cb
    print(f"  in-text citation sequence identical: {ca == cb} "
          f"({len(ca)} -> {len(cb)} references)")

    print("\n=== E6.2 the bounded negative statement is retained, and not promoted")
    bounded = {
        "EN_bounded_phrase_present": bool(re.search(
            r"corpus-bounded negative search|On the reviewed corpus", b)),
        "ES_bounded_phrase_present": bool(re.search(
            r"b[uú]squeda negativa acotada al corpus|corpus revisado|"
            r"acotad. al corpus", es, re.I)),
        "EN_full_chordal_open": bool(re.search(
            r"full chordal problem remains open|remains open", b)),
        "ES_full_chordal_open": bool(re.search(
            r"problema cordal completo (sigue|permanece) abierto|sigue abierto", es, re.I)),
        "EN_peer_review_disclaimed": bool(re.search(
            r"not a substitute for human peer review|not human peer-reviewed", b)),
        # the Spanish says "revision humana por pares"; an earlier revision of this pattern
        # required "revision por pares" with nothing between the noun and "por pares"
        "ES_peer_review_disclaimed": bool(re.search(
            r"no sustituye una revisi[oó]n (humana )?por pares|"
            r"sin revisi[oó]n (humana )?por pares|"
            r"no (es|son) (un |)sustitut\w*[^.]{0,60}revisi[oó]n (humana )?por pares",
            es, re.I)),
    }
    # an absolute priority claim would be a regression
    absolute = re.findall(
        r"[^.]*\b(?:no published result (?:exists|gives)|there is no published|"
        r"exists no published|first ever|establishes priority|proves priority)[^.]*\.",
        b, re.I)
    bounded["no_absolute_priority_claim"] = not absolute
    r6["bounded_statement"] = bounded
    r6["absolute_claims_found"] = [x.strip()[:200] for x in absolute]
    for k, v in bounded.items():
        print(f"  {'yes' if v else 'NO '} {k}")
    for x in r6["absolute_claims_found"]:
        print(f"      ABSOLUTE CLAIM: {x}")

    r6["E6_pass"] = (ba == bb and ca == cb and all(bounded.values()))
    print(f"\n  => E6 {'PASS' if r6['E6_pass'] else 'FAIL'}")
    with open(f"{OUT6}/E6_priorart.json", "w", encoding="utf-8", newline="\n") as f:
        json.dump(r6, f, indent=1, ensure_ascii=False)
        f.write("\n")

    # ================= E7 =================
    print("\n=== E7.1 the seven release surfaces are present")
    r7 = {"surfaces": {}}
    for s in SURFACES:
        p = f"{T}/{s}"
        r7["surfaces"][s] = {"present": os.path.isfile(p), "sha256": h(p),
                             "bytes": os.path.getsize(p) if os.path.isfile(p) else 0}
        print(f"  {'ok ' if os.path.isfile(p) else 'MISSING'} {s}")
    r7["all_surfaces_present"] = all(v["present"] for v in r7["surfaces"].values())

    print("\n=== E7.2 mutual consistency of version, date, title, author, DOI-less status")
    txt = {s: rd(f"{T}/{s}") for s in SURFACES}
    cons = {}
    for s, t in txt.items():
        # "\b1\.5\b" never matches inside "v1.5": v and 1 are both word characters, so there
        # is no word boundary between them. Match the optional v explicitly.
        cons[s] = {"mentions_1_5": bool(re.search(r"(?<![\d.])v?1\.5(?![\d])", t)),
                   "mentions_v1_4_as_superseded": bool(
                       re.search(r"superseded|unpublished audited draft|sustitu", t, re.I)),
                   "author_present": "Traverso" in t,
                   "mentions_2026_08_23": bool(re.search(r"2026-08-23|August 23, 2026|"
                                                         r"23 de agosto de 2026", t))}
        print(f"  {s:34} 1.5={'y' if cons[s]['mentions_1_5'] else 'N'} "
              f"author={'y' if cons[s]['author_present'] else 'N'} "
              f"date={'y' if cons[s]['mentions_2026_08_23'] else 'N'}")
    r7["consistency"] = cons
    r7["all_mention_1_5"] = all(v["mentions_1_5"] for v in cons.values())

    print("\n=== E7.3 hash agreement between the surfaces and the actual artifacts")
    real = {os.path.basename(k): v for k, v in
            [(f, h(f"{T}/01_manuscript/{f}"))
             for f in os.listdir(f"{T}/01_manuscript")
             if os.path.isfile(f"{T}/01_manuscript/{f}")]}
    quoted, wrong = 0, []
    for s, t in txt.items():
        for m in re.finditer(r"\b([0-9a-f]{64})\b", t):
            hv = m.group(1)
            quoted += 1
            # a quoted hash must correspond to some real file in the package
            if hv not in set(real.values()):
                ctx = t[max(0, m.start() - 90):m.start() + 70].replace("\n", " ")
                wrong.append({"surface": s, "hash": hv, "context": ctx[-140:]})
    # cross-check against the whole-target inventory before calling any of them wrong
    inv = set()
    for d, _, fs in os.walk(T):
        for f in fs:
            try:
                inv.add(h(os.path.join(d, f)))
            except OSError:
                pass
    unmatched = [w for w in wrong if w["hash"] not in inv]
    print(f"  64-hex hashes quoted across release surfaces: {quoted}")
    print(f"  quoted hashes not matching any file in the package: {len(unmatched)}")
    for w in unmatched[:8]:
        print(f"      {w['surface']}: {w['hash'][:20]}...  ctx: {w['context'][:90]}")
    r7["quoted_hashes"] = {"count": quoted, "unmatched": unmatched[:20]}
    r7["all_quoted_hashes_resolve"] = not unmatched

    print("\n=== E7.4 local link resolution in README and HTML")
    broken = []
    for s in ("README.md", "PaperIII_explained_4_levels.html"):
        t = txt[s]
        links = re.findall(r"\]\(([^)\s]+)\)", t) + re.findall(r'href="([^"]+)"', t)
        for l in links:
            if re.match(r"^(https?:|mailto:|#|data:)", l):
                continue
            tgt = urllib.parse.unquote(l.split("#")[0])
            if not tgt:
                continue
            p = os.path.normpath(os.path.join(T, tgt))
            if not os.path.exists(p):
                broken.append({"surface": s, "link": l})
        print(f"  {s}: {len(links)} links")
    print(f"  broken local links: {len(broken)}")
    for x in broken[:12]:
        print(f"      {x['surface']}: {x['link']}")
    r7["broken_local_links"] = broken
    r7["links_resolve"] = not broken

    print("\n=== E7.5 the HTML states scope, openness and the actual Lean/audit status")
    ht = txt["PaperIII_explained_4_levels.html"]
    plain = re.sub(r"<[^>]+>", " ", ht)
    plain = re.sub(r"\s+", " ", plain)
    html = {
        "states_split_scope": bool(re.search(r"split graph", plain, re.I)),
        "leaves_full_chordal_open": bool(re.search(
            r"chordal[^.]{0,120}(open|unresolved|not (yet )?(settled|proved))|"
            r"(open|unresolved)[^.]{0,80}chordal", plain, re.I)),
        "does_not_claim_full_chordal_solved": not bool(re.search(
            r"(solves|settles|resolves|proves)[^.]{0,60}chordal (problem|conjecture)",
            plain, re.I)),
        "reports_lean_status": bool(re.search(r"Lean", plain)),
        "reports_audit_status": bool(re.search(r"audit", plain, re.I)),
        "discloses_no_human_peer_review": bool(re.search(
            r"not .{0,40}peer[- ]review|no human peer review|peer review[^.]{0,60}not",
            plain, re.I)),
        "no_absolute_priority_claim": not bool(re.search(
            r"first (ever|in the world)|no one has|nobody has|proves priority", plain, re.I)),
    }
    r7["html"] = html
    for k, v in html.items():
        print(f"  {'yes' if v else 'NO '} {k}")

    print("\n=== E7.6 v1.5 framed as first public preprint, not superseding a public release")
    frame = {}
    for s in ("README.md", "CHANGELOG_v1.5.md", "RELEASE_NOTES.md", "RELEASE_METADATA.yml"):
        t = txt[s]
        frame[s] = {
            "says_first_public": bool(re.search(
                r"first (formal )?public (preprint|release)|primer preprint p[uú]blico|"
                r"first_formal_public_release:\s*true", t, re.I)),
            "declares_no_superseded_public_version": bool(re.search(
                r"supersedes_public_version:\s*null", t)) or None,
            "v1_4_called_unpublished": bool(re.search(
                r"unpublished", t, re.I)),
            "claims_superseding_public_release": bool(re.search(
                r"supersedes (the )?(public|official|published) release", t, re.I)),
        }
        print(f"  {s:26} first_public={'y' if frame[s]['says_first_public'] else 'N'} "
              f"v1.4_unpublished={'y' if frame[s]['v1_4_called_unpublished'] else 'N'} "
              f"claims_superseding_public="
              f"{'Y!' if frame[s]['claims_superseding_public_release'] else 'n'}")
    r7["framing"] = frame
    r7["framing_ok"] = (any(v["says_first_public"] for v in frame.values())
                        and not any(v["claims_superseding_public_release"]
                                    for v in frame.values()))

    print("\n=== E7.7 v1.4 evidence preserved and not rewritten")
    prior = {
        "v1_4_residual_report":
            f"{T}/02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-22_v1.4_residual/"
            f"30_REPORT/FINAL_AUDIT_REPORT.md",
        "v1_4_challenger_report":
            f"{T}/02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-23_v1.4_challenger/"
            f"30_REPORT/FINAL_AUDIT_REPORT.md",
    }
    expect = {"v1_4_residual_report":
                  "2c19bf1ca74f77cc409b8d0102adf01b92d13db885ac81d15d156477abed8842",
              "v1_4_challenger_report":
                  "a196479b8b2adde5077669ec5e398dfc4d640e006bd97b10ef0f72696bdfb5f3"}
    pres = {}
    for k, p in prior.items():
        got = h(p)
        pres[k] = {"present": os.path.isfile(p), "sha256": got,
                   "unchanged": got == expect[k]}
        print(f"  {'ok ' if pres[k]['unchanged'] else 'CHANGED'} {k}")
    # both prior sealed packages must still re-verify
    for k, run in (("v1_4_residual", "run_2026-08-22_v1.4_residual"),
                   ("v1_4_challenger", "run_2026-08-23_v1.4_challenger")):
        base = f"{T}/02_validation/02_IA_ADVERSARIAL_AUDITS/{run}"
        mp = (f"{base}/40_PACKAGE/PACKAGE_MANIFEST.json")
        if os.path.isfile(mp):
            man = json.load(open(mp, encoding="utf-8"))
            bad = [i["path"] for i in man["files"] if h(f"{base}/{i['path']}") != i["sha256"]]
            pres[k + "_package"] = {"files": len(man["files"]), "mismatched": len(bad),
                                    "problems": bad[:10]}
            print(f"  {k} package: {len(man['files']) - len(bad)}/{len(man['files'])} "
                  f"files re-verify")
    r7["preserved"] = pres
    r7["preserved_ok"] = all(v.get("unchanged", True) for v in pres.values()) and \
        all(v.get("mismatched", 0) == 0 for v in pres.values() if "mismatched" in v)

    checks7 = {"surfaces_present": r7["all_surfaces_present"],
               "all_mention_1_5": r7["all_mention_1_5"],
               "quoted_hashes_resolve": r7["all_quoted_hashes_resolve"],
               "links_resolve": r7["links_resolve"],
               "html_ok": all(html.values()),
               "framing_ok": r7["framing_ok"],
               "preserved_ok": r7["preserved_ok"]}
    r7["checks"] = checks7
    r7["E7_pass"] = all(checks7.values())
    print("\n=== E7 verdict")
    for k, v in checks7.items():
        print(f"  {k:26} {'PASS' if v else 'FAIL'}")
    print(f"  => E7 {'PASS' if r7['E7_pass'] else 'FAIL'}")
    with open(f"{OUT7}/E7_release.json", "w", encoding="utf-8", newline="\n") as f:
        json.dump(r7, f, indent=1, ensure_ascii=False)
        f.write("\n")


if __name__ == "__main__":
    main()
