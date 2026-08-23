#!/usr/bin/env python3
"""RESIDUAL AUDIT, PAPER_I v1.3.

(a) Confirm the Spanish manuscript carries the same eight corrections as the English.
(b) Spec Section 6: confirm the manuscript contains no internal version-history
    narrative and no dependency on audit documents.
Plain substring tests, so no regex escaping hazards.
"""
import json

EN = "C:/v13/01_manuscript/PAPER_I_preprint_draft_v1.3.md"
ES = "C:/v13/01_manuscript/PAPER_I_preprint_draft_v1.3_es.md"

MIRROR = [
    ("control 3a  z_e=x_e substitution stated", "z_e=x_e"),
    ("control 3a  capped-dual polytope named", "capped-dual"),
    ("control 3b  H-slack sum present", "\\sum_{e\\in H}"),
    ("control 4   A.2 restricted", "\\ge3"),
    ("control 4   o=0,1,2 routed to A.3", "o=0,1,2"),
    ("control 6   author-hosted CEO scan", "ordman.net"),
    ("control 7   Schrijver at chapter level", "Chapter 7"),
    ("control 8   repository citation removed", "github.com/jtraverso"),
]
MIRROR_ES = [
    ("control 3a  z_e=x_e substitution stated", "z_e=x_e"),
    ("control 3a  capped-dual polytope named", "dual acotado"),
    ("control 3b  H-slack sum present", "\\sum_{e\\in H}"),
    ("control 4   A.2 restricted", "\\ge3"),
    ("control 4   o=0,1,2 routed to A.3", "o=0,1,2"),
    ("control 6   author-hosted CEO scan", "ordman.net"),
    ("control 7   Schrijver at chapter level", "Cap"),
    ("control 8   repository citation removed", "github.com/jtraverso"),
]
FORBIDDEN = ["v1.1.4", "v1.1.5", "supersede", "CORRECTION_MATRIX",
             "EXTERNAL_AUDIT", "INTERNAL_AUDIT_FINAL", "CHANGELOG",
             "EXT-P1-", "residual audit"]


def count(path, needle):
    lines = open(path, encoding="utf-8").read().splitlines()
    return [i + 1 for i, l in enumerate(lines) if needle in l]


def main():
    out = {"spec": "RESIDUAL_AUDIT_REQUEST_SPEC.md",
           "target": "preprint_draft_v1.3", "mirror": {}, "self_containment": {}}
    for tag, items, path in (("EN", MIRROR, EN), ("ES", MIRROR_ES, ES)):
        rows = []
        for name, needle in items:
            locs = count(path, needle)
            expect_absent = "removed" in name
            ok = (not locs) if expect_absent else bool(locs)
            rows.append({"check": name, "needle": needle, "lines": locs[:6],
                         "expected": "absent" if expect_absent else "present",
                         "pass": ok})
        out["mirror"][tag] = rows
    for tag, path in (("EN", EN), ("ES", ES)):
        hits = []
        lines = open(path, encoding="utf-8").read().splitlines()
        for i, l in enumerate(lines):
            for f in FORBIDDEN:
                if f.lower() in l.lower():
                    hits.append({"line": i + 1, "term": f, "text": l.strip()[:160]})
        out["self_containment"][tag] = {"violations": len(hits), "detail": hits[:10]}
    print(json.dumps(out, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
