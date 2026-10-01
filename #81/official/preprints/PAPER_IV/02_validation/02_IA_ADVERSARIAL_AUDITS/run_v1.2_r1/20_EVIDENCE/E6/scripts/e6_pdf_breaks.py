"""E6: find line breaks inside monospace identifiers in PDFs; classify with/without continuation arrow."""
import pymupdf, json, re
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.2_full_rebuild_candidate/"
E = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1/20_EVIDENCE/E6/"
res = {}
for l in ("en", "es"):
    doc = pymupdf.open(D + f"PAPER_IV_preprint_v1.2_{l}.pdf")
    rows = []
    for p in doc:
        d = p.get_text("dict")
        lines = []
        for b in d["blocks"]:
            for ln in b.get("lines", []):
                sp = [s for s in ln["spans"] if s["text"].strip()]
                if sp:
                    lines.append(sp)
        for i, sp in enumerate(lines):
            last = sp[-1]
            # detect arrow marker: CMSY glyph sequence ",→" or "↪" or "→" at line end
            tail = "".join(s["text"] for s in sp[-3:])
            is_mono_last = "Mono" in last["font"]
            prev_mono = len(sp) >= 2 and "Mono" in sp[-2]["font"]
            has_arrow = bool(re.search(r"(,→|↪|→)\s*$", tail)) and (is_mono_last or prev_mono or "CMSY" in last["font"])
            nxt = lines[i + 1][0] if i + 1 < len(lines) else None
            nxt_mono = nxt is not None and "Mono" in nxt["font"]
            if has_arrow and (prev_mono or is_mono_last):
                rows.append(dict(page=p.number + 1, kind="arrow_break", end=tail[-45:], next=(nxt["text"][:40] if nxt else None)))
            elif is_mono_last and nxt_mono:
                t = last["text"].rstrip()
                # break between two mono spans across lines w/o arrow
                rows.append(dict(page=p.number + 1, kind="mono_to_mono_no_arrow", end=t[-45:], next=nxt["text"][:45]))
            elif is_mono_last and re.search(r"[._/\-]$", last["text"].rstrip()):
                rows.append(dict(page=p.number + 1, kind="mono_end_with_separator", end=last["text"][-45:], next=(nxt["text"][:40] if nxt else None)))
    res[l] = rows
    kinds = {}
    for r in rows:
        kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
    print(l, kinds)
    for r in rows:
        if r["kind"] != "arrow_break":
            print("  ", r)
json.dump(res, open(E + "results/pdf_mono_breaks.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
