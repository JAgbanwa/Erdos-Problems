#!/usr/bin/env python3
"""EXTERNAL ADVERSARIAL AUDIT, protocol v1.1, Gate L.

EN/ES protected-content comparison, reusable across papers.

Display-math blocks are extracted and all \\text{...}, \\mathrm{...} and
\\operatorname{...} prose is BLANKED, so idiomatic translation of embedded words is
ignored and only mathematical structure is compared, as a multiset (immune to ordering
and to count drift cascading into spurious mismatches).

Also compares: equation tags, code/Lean identifiers, citation keys, heading hierarchy,
and duplicated non-trivial lines (the Paper I v1.2 defect class).

Usage: python gate_L_check.py EN.md ES.md
"""
import collections
import json
import re
import sys

OPEN = "\\" + "["
CLOSE = "\\" + "]"
TEXT_RE = re.compile(re.escape("\\text") + r"\{[^{}]*\}")
MATHRM_RE = re.compile(re.escape("\\mathrm") + r"\{[^{}]*\}")
OPNAME_RE = re.compile(re.escape("\\operatorname") + r"\{[^{}]*\}")
TAG_RE = re.compile(re.escape("\\tag") + r"\{([^}]*)\}")
WS_RE = re.compile(r"\s+")


def read(path):
    return open(path, encoding="utf-8").read()


def display_blocks(text):
    out, cur = [], None
    for line in text.splitlines():
        s = line.strip()
        if s == OPEN:
            cur = []
            continue
        if s == CLOSE and cur is not None:
            out.append(" ".join(cur))
            cur = None
            continue
        if cur is not None:
            cur.append(s)
    norm = []
    for b in out:
        b = TEXT_RE.sub("<T>", b)
        b = MATHRM_RE.sub("<M>", b)
        b = OPNAME_RE.sub("<O>", b)
        norm.append(WS_RE.sub("", b))
    return norm


def idents(text):
    return collections.Counter(re.findall(r"`([A-Za-z_][A-Za-z0-9_.']*)`", text))


def cites(text):
    return sorted(set(re.findall(r"\[(\d+(?:\s*,\s*\d+)*)\]", text)))


def heads(text):
    return [m.group(1) for m in re.finditer(r"^(#+)\s", text, re.M)]


def dupes(text, minlen=30):
    L = text.splitlines()
    c = collections.Counter(l.strip() for l in L if len(l.strip()) >= minlen)
    out = {}
    for k, v in c.items():
        if v > 1:
            out[k] = {"count": v,
                      "lines": [i + 1 for i, l in enumerate(L) if l.strip() == k]}
    return out


def main():
    en_t, es_t = read(sys.argv[1]), read(sys.argv[2])
    en_b, es_b = display_blocks(en_t), display_blocks(es_t)
    ce, cs = collections.Counter(en_b), collections.Counter(es_b)
    only_en, only_es = ce - cs, cs - ce

    ie, is_ = idents(en_t), idents(es_t)
    de, ds = dupes(en_t), dupes(es_t)
    # duplications present in ES but not in EN, and vice versa
    dup_es_only = {k: v for k, v in ds.items() if k not in de}
    dup_en_only = {k: v for k, v in de.items() if k not in ds}

    res = {
        "protocol": "EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1",
        "gate": "L",
        "en_file": sys.argv[1], "es_file": sys.argv[2],
        "display_math": {
            "en_blocks": len(en_b), "es_blocks": len(es_b),
            "structurally_identical": (not only_en and not only_es),
            "only_en_count": sum(only_en.values()),
            "only_es_count": sum(only_es.values()),
            "only_en": [k[:240] for k in only_en],
            "only_es": [k[:240] for k in only_es],
        },
        "equation_tags": {
            "en": sorted(TAG_RE.findall(en_t)), "es": sorted(TAG_RE.findall(es_t)),
            "identical": sorted(TAG_RE.findall(en_t)) == sorted(TAG_RE.findall(es_t)),
        },
        "identifiers": {
            "en_unique": len(ie), "es_unique": len(is_),
            "only_en": sorted(set(ie) - set(is_)),
            "only_es": sorted(set(is_) - set(ie)),
        },
        "citations": {"en": cites(en_t), "es": cites(es_t),
                      "identical": cites(en_t) == cites(es_t)},
        "headings": {"en": len(heads(en_t)), "es": len(heads(es_t)),
                     "level_sequence_identical": heads(en_t) == heads(es_t)},
        "duplicated_lines": {
            "en_total": len(de), "es_total": len(ds),
            "duplicated_only_in_es": dup_es_only,
            "duplicated_only_in_en": dup_en_only,
        },
    }
    print(json.dumps(res, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
