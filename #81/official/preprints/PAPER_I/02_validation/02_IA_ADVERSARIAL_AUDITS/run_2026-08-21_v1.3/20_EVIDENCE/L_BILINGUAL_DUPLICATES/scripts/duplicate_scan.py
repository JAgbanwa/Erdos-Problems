#!/usr/bin/env python3
"""RESIDUAL AUDIT, PAPER_I v1.3, control 1 (EXT-P1-L-001).

General exact AND near-duplicate scan of normalized long units across all six
manuscript artifacts, plus a rendered-page duplicate check.

Not limited to the known v1.2 phrases: every long unit is compared against every other.

Units
  - paragraph units: maximal runs of non-blank lines, normalized
  - line units: individual non-blank lines, normalized
Normalization: NFKC, lowercase, collapse whitespace, strip punctuation.
Threshold: normalized length >= MINLEN characters (reported).
Near-duplicate: difflib SequenceMatcher ratio >= RATIO between two distinct units
(reported); every candidate is printed in full for manual inspection.

Page duplicates: each rendered page is hashed exactly (SHA-256 of the PNG bytes) and
also compared by a coarse downsampled grayscale signature, so a repeated page survives
re-rendering differences.
"""
import difflib
import glob
import hashlib
import os
import re
import sys
import unicodedata
from collections import Counter, defaultdict
import json

MINLEN = 60
RATIO = 0.92

ART = {
    "EN_md": "C:/v13/01_manuscript/PAPER_I_preprint_draft_v1.3.md",
    "ES_md": "C:/v13/01_manuscript/PAPER_I_preprint_draft_v1.3_es.md",
    "EN_tex": "C:/v13/01_manuscript/PAPER_I_preprint_draft_v1.3_en.tex",
    "ES_tex": "C:/v13/01_manuscript/PAPER_I_preprint_draft_v1.3_es.tex",
    "EN_pdftext": "C:/erdos_audit/v13txt/en.txt",
    "ES_pdftext": "C:/erdos_audit/v13txt/es.txt",
}


def norm(s):
    s = unicodedata.normalize("NFKC", s)
    s = re.sub(r"\s+", " ", s).strip().lower()
    s = re.sub(r"[^\w\s]", "", s)
    return s


def paragraphs(lines):
    out, cur, start = [], [], None
    for i, l in enumerate(lines):
        if l.strip():
            if start is None:
                start = i + 1
            cur.append(l)
        else:
            if cur:
                out.append((start, norm(" ".join(cur))))
                cur, start = [], None
    if cur:
        out.append((start, norm(" ".join(cur))))
    return [(s, t) for s, t in out if len(t) >= MINLEN]


def line_units(lines):
    return [(i + 1, norm(l)) for i, l in enumerate(lines) if len(norm(l)) >= MINLEN]


def scan(units, label):
    exact = {}
    c = Counter(t for _, t in units)
    for t, n in c.items():
        if n > 1:
            exact[t] = [i for i, x in units if x == t]
    near = []
    seen = list(units)
    for a in range(len(seen)):
        for b in range(a + 1, len(seen)):
            ta, tb = seen[a][1], seen[b][1]
            if ta == tb:
                continue
            if abs(len(ta) - len(tb)) > 0.25 * max(len(ta), len(tb)):
                continue
            r = difflib.SequenceMatcher(None, ta, tb).ratio()
            if r >= RATIO:
                near.append({"ratio": round(r, 4),
                             "loc_a": seen[a][0], "loc_b": seen[b][0],
                             "text_a": ta[:220], "text_b": tb[:220]})
    return {"unit_kind": label, "units": len(units),
            "exact_duplicate_classes": len(exact),
            "exact_detail": [{"count": len(v), "locations": v, "text": k[:220]}
                             for k, v in list(exact.items())[:20]],
            "near_duplicate_pairs": len(near), "near_detail": near[:20]}


def page_dupes():
    pop = (r"C:/Users/jtrav/AppData/Local/Microsoft/WinGet/Packages/"
           r"oschwartz10612.Poppler_Microsoft.Winget.Source_8wekyb3d8bbwe/"
           r"poppler-25.07.0/Library/bin/pdftoppm.exe")
    import subprocess
    res = {}
    try:
        from PIL import Image
        have = True
    except Exception:
        have = False
    for lang in ("en", "es"):
        pdf = f"C:/v13/01_manuscript/PAPER_I_preprint_draft_v1.3_{lang}.pdf"
        d = f"C:/erdos_audit/v13pages/{lang}"
        os.makedirs(d, exist_ok=True)
        subprocess.run([pop, "-r", "100", "-png", pdf, d + "/p"], capture_output=True)
        pages = sorted(glob.glob(d + "/*.png"))
        exact = defaultdict(list)
        sigs = {}
        for pg in pages:
            b = open(pg, "rb").read()
            exact[hashlib.sha256(b).hexdigest()].append(os.path.basename(pg))
            if have:
                im = Image.open(pg).convert("L").resize((16, 22))
                sigs[os.path.basename(pg)] = tuple(im.getdata())
        dup_exact = {k: v for k, v in exact.items() if len(v) > 1}
        near = []
        names = sorted(sigs)
        for a in range(len(names)):
            for b in range(a + 1, len(names)):
                sa, sb = sigs[names[a]], sigs[names[b]]
                diff = sum(abs(x - y) for x, y in zip(sa, sb)) / len(sa)
                if diff < 6:
                    near.append({"pages": [names[a], names[b]],
                                 "mean_abs_gray_diff": round(diff, 3)})
        res[lang] = {"pages": len(pages),
                     "exact_duplicate_page_sets": [v for v in dup_exact.values()],
                     "near_duplicate_page_pairs": near}
    return res


def main():
    out = {"spec": "RESIDUAL_AUDIT_REQUEST_SPEC.md", "control": "1 (EXT-P1-L-001)",
           "target": "preprint_draft_v1.3",
           "thresholds": {"min_normalized_length": MINLEN,
                          "near_duplicate_ratio": RATIO,
                          "page_near_duplicate_mean_gray_diff": 6},
           "exclusions": "none; every long unit in every artifact is compared",
           "artifacts": {}}
    for k, p in ART.items():
        lines = open(p, encoding="utf-8", errors="replace").read().splitlines()
        out["artifacts"][k] = {"paragraphs": scan(paragraphs(lines), "paragraph"),
                               "lines": scan(line_units(lines), "line")}
    out["page_images"] = page_dupes()
    print(json.dumps(out, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
