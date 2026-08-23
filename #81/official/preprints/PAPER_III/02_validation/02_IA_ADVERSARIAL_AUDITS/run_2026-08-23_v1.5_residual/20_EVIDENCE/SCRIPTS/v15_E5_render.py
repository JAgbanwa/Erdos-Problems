#!/usr/bin/env python3
"""E5 (part 2) - rendered-artifact review for both v1.5 PDFs.

Establishes the derivation chain by reproduction rather than by assertion: the auditor
rebuilds each PDF from the delivered .tex with the same LuaTeX that produced it and compares
page text. Then checks page counts, font embedding, figures, author block, clipping, glyph
loss, escape corruption, and the diagnostics in both the author's final log and the auditor's
own log.
"""
import glob
import hashlib
import io
import json
import os
import re
import subprocess
import sys

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")

M = "C:/p3v15/01_manuscript"
LOGS = "C:/p3v15/03_reproducibility/manuscript_build_logs"
MINE = "C:/erdos_audit/v15/render"
OUT = "C:/v15r/20_EVIDENCE/E5_RENDER"

EXPECT_PAGES = {"en": 46, "es": 47}
DIAG = ["^!", "Undefined control sequence", "Missing character", "Overfull",
        "LaTeX Error", "Package .* Error", "Fatal", "File .* not found",
        "Font .* not (found|loadable)"]
# escape artifacts that must not reach rendered text
ESCAPE_ARTIFACTS = [r"\\_", r"\{\[\}", r"\{\]\}", r"\\allowbreak", r"\\textbackslash",
                    r"\\%", r"\\&", r"\\\$", r"\\#"]


def h(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def run(cmd):
    return subprocess.run(cmd, capture_output=True)


def pagetext(p, i):
    return run(["pdftotext", "-f", str(i), "-l", str(i), "-enc", "UTF-8", p, "-"]).stdout


def readpgm(p):
    d = open(p, "rb").read()
    parts, i = [], 0
    while len(parts) < 4:
        while d[i:i + 1].isspace():
            i += 1
        if d[i:i + 1] == b"#":
            while d[i:i + 1] != b"\n":
                i += 1
            continue
        j = i
        while not d[j:j + 1].isspace():
            j += 1
        parts.append(d[i:j])
        i = j
    i += 1
    w, hh = int(parts[1]), int(parts[2])
    return w, hh, d[i:i + w * hh]


def main():
    os.makedirs(OUT, exist_ok=True)
    res, allok = {}, True

    for lang in ("en", "es"):
        pdf = f"{M}/PAPER_III_preprint_v1.5_{lang}.pdf"
        print(f"\n{'=' * 66}\n=== {lang.upper()} : {os.path.basename(pdf)}")
        r = {"sha256": h(pdf)}
        ck = {}

        info = run(["pdfinfo", pdf]).stdout.decode("utf-8", "replace")
        pages = int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1))
        author = (re.search(r"^Author:\s+(.*)$", info, re.M) or [None, ""])
        author = author.group(1).strip() if hasattr(author, "group") else ""
        title = re.search(r"^Title:\s+(.*)$", info, re.M)
        r.update({"pages": pages, "author_metadata": author,
                  "title_metadata": title.group(1).strip() if title else ""})
        ck["page_count"] = pages == EXPECT_PAGES[lang]
        ck["author_metadata_correct"] = author == "Juan Pablo Traverso Gianini"
        ck["author_metadata_not_placeholder"] = "AUTHORBLOCK" not in author.upper()
        print(f"  pages {pages} (expected {EXPECT_PAGES[lang]}) -> "
              f"{'OK' if ck['page_count'] else 'MISMATCH'}")
        print(f"  Author metadata: {author!r} -> "
              f"{'OK' if ck['author_metadata_correct'] else 'WRONG'}")

        fonts = run(["pdffonts", pdf]).stdout.decode("utf-8", "replace").splitlines()[2:]
        fonts = [l for l in fonts if l.strip()]
        nonemb = [l for l in fonts if re.search(r"\bno\b\s+\w+\s+\w+\s+\d+\s+\d+\s*$", l)]
        r["fonts"] = {"count": len(fonts), "non_embedded": len(nonemb)}
        ck["fonts_embedded"] = len(fonts) > 0 and not nonemb
        print(f"  fonts {len(fonts)}, non-embedded {len(nonemb)} -> "
              f"{'OK' if ck['fonts_embedded'] else 'FAIL'}")

        full = run(["pdftotext", "-enc", "UTF-8", pdf, "-"]).stdout.decode("utf-8", "replace")
        r["author_name_occurrences"] = full.count("Juan Pablo Traverso")
        r["orcid_occurrences"] = full.count("0009-0003-6068-4096")
        r["authorblock_token_occurrences"] = len(re.findall(r"AUTHORBLOCK", full, re.I))
        ck["exactly_one_author_block"] = (r["author_name_occurrences"] == 1
                                          and r["orcid_occurrences"] == 1)
        ck["no_authorblock_token"] = r["authorblock_token_occurrences"] == 0
        print(f"  author name in text: {r['author_name_occurrences']}, "
              f"ORCID: {r['orcid_occurrences']}, AUTHORBLOCK token: "
              f"{r['authorblock_token_occurrences']} -> "
              f"{'OK' if ck['exactly_one_author_block'] and ck['no_authorblock_token'] else 'FAIL'}")

        # the single author block must be on page 1
        p1 = pagetext(pdf, 1).decode("utf-8", "replace")
        r["author_block_on_page_1"] = "Juan Pablo Traverso" in p1
        ck["author_block_on_page_1"] = r["author_block_on_page_1"]
        print(f"  author block on page 1: {r['author_block_on_page_1']}")

        esc = {p: len(re.findall(p, full)) for p in ESCAPE_ARTIFACTS}
        esc = {k: v for k, v in esc.items() if v}
        r["escape_artifacts_in_rendered_text"] = esc
        ck["no_escape_corruption"] = not esc
        print(f"  escape artifacts in rendered text: {esc or 'none'}")

        # figures
        figs = run(["pdfimages", "-list", pdf]).stdout.decode("utf-8", "replace")
        nimg = max(0, len([l for l in figs.splitlines() if re.match(r"\s*\d+", l)]))
        r["embedded_images"] = nimg
        ck["figures_present"] = nimg >= 2
        print(f"  embedded images: {nimg} (2 figures expected) -> "
              f"{'OK' if ck['figures_present'] else 'CHECK'}")

        # Author's final log. NOTE: LOGS/LUALATEX_FINAL_{lang}.log at the top level is a
        # stale v1.3 artifact (it builds PAPER_III_preprint_draft_v1.3_*.tex, 45/46 pages,
        # 2 overfull boxes) that shadows the real v1.5 log one directory below. The v1.5 log
        # is authoritative; the shadowing is reported as a finding, not worked around
        # silently.
        stale = f"{LOGS}/LUALATEX_FINAL_{lang}.log"
        alog = f"{LOGS}/v1.5/LUALATEX_FINAL_{lang}.log"
        if os.path.isfile(stale):
            st = open(stale, encoding="utf-8", errors="replace").read()
            m = re.search(r"Output written on (\S+) \((\d+) pages", st)
            r["shadowing_stale_log"] = {
                "path": os.path.relpath(stale, "C:/p3v15"), "sha256": h(stale),
                "builds": m.group(1) if m else None,
                "pages": int(m.group(2)) if m else None,
                "overfull": len(re.findall(r"Overfull", st)),
                "describes_delivered_v1_5_pdf": bool(m) and "v1.5" in m.group(1)}
            print(f"  [!] same-named stale log at the parent level builds "
                  f"{r['shadowing_stale_log']['builds']} "
                  f"({r['shadowing_stale_log']['pages']} pages, "
                  f"{r['shadowing_stale_log']['overfull']} overfull)")
        adiag = {}
        if os.path.isfile(alog):
            t = open(alog, encoding="utf-8", errors="replace").read()
            for p in DIAG:
                adiag[p] = len(re.findall(p, t, re.M | re.I))
            m = re.findall(r"Output written on .*?\((\d+) pages", t)
            r["author_log"] = {"path": os.path.basename(alog), "sha256": h(alog),
                              "diagnostics": adiag,
                              "pages_written": int(m[-1]) if m else None}
            fatal = sum(v for k, v in adiag.items() if k != "Overfull")
            ck["author_log_clean"] = fatal == 0
            print(f"  author final log: pages={r['author_log']['pages_written']}, "
                  f"diagnostics={ {k: v for k, v in adiag.items() if v} or 'none'} -> "
                  f"{'OK' if ck['author_log_clean'] else 'FAIL'}")
        else:
            ck["author_log_clean"] = False
            print(f"  author final log MISSING at {alog}")

        # auditor's own rebuild
        mine_pdf, mine_log = f"{MINE}/{lang}.pdf", f"{MINE}/{lang}.log"
        if os.path.isfile(mine_pdf) and os.path.isfile(mine_log):
            t = open(mine_log, encoding="utf-8", errors="replace").read()
            mdiag = {p: len(re.findall(p, t, re.M | re.I)) for p in DIAG}
            mpages = int(re.search(r"^Pages:\s+(\d+)", run(["pdfinfo", mine_pdf]).stdout
                                   .decode("utf-8", "replace"), re.M).group(1))
            diff = [i for i in range(1, pages + 1)
                    if pagetext(pdf, i) != pagetext(mine_pdf, i)]
            r["auditor_rebuild"] = {
                "log_sha256": h(mine_log), "pages": mpages,
                "diagnostics": {k: v for k, v in mdiag.items() if v},
                "pages_text_identical": pages - len(diff), "differing_pages": diff}
            mfatal = sum(v for k, v in mdiag.items() if k != "Overfull")
            ck["auditor_rebuild_clean"] = mfatal == 0
            ck["auditor_rebuild_matches"] = mpages == pages and not diff
            print(f"  auditor rebuild: pages={mpages}, diagnostics="
                  f"{ {k: v for k, v in mdiag.items() if v} or 'none'}")
            print(f"  auditor rebuild text-identical pages: {pages - len(diff)}/{pages}, "
                  f"differing: {diff or 'none'} -> "
                  f"{'OK' if ck['auditor_rebuild_matches'] else 'FAIL'}")
        else:
            ck["auditor_rebuild_clean"] = ck["auditor_rebuild_matches"] = False
            print(f"  auditor rebuild MISSING")

        # clipping: raster all pages, look for ink in the margin bands
        for f in glob.glob(f"{MINE}/{lang}-pg-*.pgm"):
            os.remove(f)
        run(["pdftoppm", "-r", "72", "-gray", pdf, f"{MINE}/{lang}-pg"])
        band = []
        for p in sorted(glob.glob(f"{MINE}/{lang}-pg-*.pgm")):
            w, hh, px = readpgm(p)
            L = R = T = B = 0
            for y in range(hh):
                row = px[y * w:(y + 1) * w]
                for x in range(w):
                    if row[x] < 200:
                        if x < 60:
                            L += 1
                        if x > w - 60:
                            R += 1
                        if y < 50:
                            T += 1
                        if y > hh - 40:
                            B += 1
            if L or R or T or B:
                band.append({"page": os.path.basename(p), "left": L, "right": R,
                             "top": T, "bottom": B})
        r["margin_scan"] = {"pages_rastered": len(glob.glob(f"{MINE}/{lang}-pg-*.pgm")),
                            "pages_with_margin_ink": len(band), "detail": band[:10]}
        ck["no_clipping"] = not band
        print(f"  raster margin scan: {r['margin_scan']['pages_rastered']} pages, "
              f"pages with ink in margin bands: {len(band)} -> "
              f"{'OK' if not band else 'CHECK'}")

        r["checks"] = ck
        r["pass"] = all(ck.values())
        allok &= r["pass"]
        print(f"  ===> {lang.upper()}: {'PASS' if r['pass'] else 'FAIL'}  "
              f"failing: {[k for k, v in ck.items() if not v] or 'none'}")
        res[lang] = r

    res["E5_render_pass"] = allok
    print(f"\nE5 (render) {'PASS' if allok else 'FAIL'}")
    with open(f"{OUT}/E5_render.json", "w", encoding="utf-8", newline="\n") as f:
        json.dump(res, f, indent=1, ensure_ascii=False)
        f.write("\n")


if __name__ == "__main__":
    main()
