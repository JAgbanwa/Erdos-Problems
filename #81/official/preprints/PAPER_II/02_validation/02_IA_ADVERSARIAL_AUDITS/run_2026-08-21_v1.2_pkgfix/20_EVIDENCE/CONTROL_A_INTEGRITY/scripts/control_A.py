#!/usr/bin/env python3
"""PAPER_II v1.2 pkgfix — Control A: independently close EXT-PII-M-001.

Every bullet of specification Section 5 Control A is checked, plus the six corrected
integrity-document anchors, plus a content verification of every sidecar in the target.
"""
import hashlib
import json
import os

ROOT = "C:/p2t"
EXCL = "02_validation/02_IA_ADVERSARIAL_AUDITS"

ANCHORS = {
    "04_integrity/INITIAL_SOURCE_SHA256.txt":
        "1d5f8d91cb5d459eb0678e0a9ed2299a5b10b8ad69ae1a0640fa39fe4e220323",
    "04_integrity/INITIALIZATION_DIFF.md":
        "4b88e30639bc91cb71ab3ea88adad758604c2c96bae3722e40e2d14a92550c2c",
    "04_integrity/README.md":
        "d7ed1d33556de1f0ec2b79ba769b9ed255d4df8101d51fa3aa425f6ccb011e85",
    "04_integrity/CURRENT_TARGET_SHA256.txt":
        "79fd65426d03a77867f6591b7580651c98d3ce14580aed3d1e68e69b477a315d",
    "04_integrity/SEMANTIC_INTEGRITY_REPORT_v1.2.md":
        "5c9d6dc4694987fdc4f070b19eb1c3362083834ada009fd6227bb402526d817e",
    "04_integrity/EXTERNAL_AUDIT_V1.2_RESIDUAL_MATRIX.md":
        "a004b4fec8520c14ba55b812d4231c8863088bbc988b2c3fb8a3dd04f4350857",
}


def h(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def endings(p):
    raw = open(p, "rb").read()
    crlf = raw.count(b"\r\n")
    lf = raw.count(b"\n") - crlf
    return "MIXED" if (crlf and lf) else ("CRLF" if crlf else "LF")


def verify_sidecar(rel, bases):
    p = os.path.join(ROOT, rel)
    raw = open(p, "rb").read()
    entries = []
    for line in raw.decode("utf-8", "replace").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split(None, 1)
        if len(parts) == 2:
            entries.append((parts[0].lower(),
                            parts[1].lstrip("*").strip().replace(chr(92), "/")))
    best = None
    for base in bases:
        ok = bad = miss = 0
        det = []
        for hh, fn in entries:
            fp = os.path.join(base, fn)
            if not os.path.isfile(fp):
                miss += 1
                det.append("MISSING " + fn)
            elif h(fp) == hh:
                ok += 1
            else:
                bad += 1
                det.append("MISMATCH " + fn)
        cand = (miss + bad, ok, bad, miss, base, det)
        if best is None or cand[0] < best[0]:
            best = cand
    _, ok, bad, miss, base, det = best
    return {"sidecar": rel, "line_endings": endings(p), "entries": len(entries),
            "ok": ok, "mismatch": bad, "missing": miss,
            "resolved_from": os.path.relpath(base, ROOT).replace("\\", "/"),
            "verifies": bad == 0 and miss == 0, "detail": det[:4],
            "paths": [fn for _, fn in entries]}


def main():
    out = {"spec": "FINAL_RESIDUAL_AUDIT_REQUEST_SPEC.md",
           "control": "A (EXT-PII-M-001)", "checks": {}}

    # the six corrected integrity-document anchors
    rows = []
    for rel, want in ANCHORS.items():
        p = os.path.join(ROOT, rel)
        if not os.path.isfile(p):
            rows.append({"file": rel, "status": "MISSING"})
            continue
        got = h(p)
        rows.append({"file": rel, "declared": want, "computed": got,
                     "match": got == want, "line_endings": endings(p)})
    out["checks"]["corrected_integrity_anchors"] = {
        "rows": rows, "all_match": all(r.get("match") for r in rows)}

    # INITIAL_SOURCE_SHA256.txt: LF-only, three entries, resolve from package root
    isc = verify_sidecar("04_integrity/INITIAL_SOURCE_SHA256.txt", [ROOT])
    isc["three_entries"] = isc["entries"] == 3
    isc["no_v11_manuscript_path"] = not any(
        "preprint_draft_v1.1" in x for x in isc["paths"])
    isc["lf_only"] = isc["line_endings"] == "LF"
    out["checks"]["INITIAL_SOURCE_SHA256"] = isc

    # CURRENT_TARGET_SHA256.txt: LF-only, nine entries, resolve
    cts = verify_sidecar("04_integrity/CURRENT_TARGET_SHA256.txt", [ROOT])
    cts["nine_entries"] = cts["entries"] == 9
    cts["lf_only"] = cts["line_endings"] == "LF"
    out["checks"]["CURRENT_TARGET_SHA256"] = cts

    # README.md describes v1.2, not a pending v1.1 workspace
    rp = os.path.join(ROOT, "04_integrity/README.md")
    rt = open(rp, encoding="utf-8").read()
    out["checks"]["integrity_README"] = {
        "mentions_v1_2": "v1.2" in rt,
        "still_says_pending_for_v1_1": "Pending for v1.1" in rt,
        "mentions_superseded_dir": "superseded" in rt.lower(),
        "text": rt.strip()[:700]}

    # INITIALIZATION_DIFF.md documents v1.1 -> v1.2, claims no protected math change
    dp = os.path.join(ROOT, "04_integrity/INITIALIZATION_DIFF.md")
    dt = open(dp, encoding="utf-8").read()
    out["checks"]["INITIALIZATION_DIFF"] = {
        "documents_v11_to_v12": ("v1.1" in dt and "v1.2" in dt),
        "asserts_no_protected_change": any(
            k in dt.lower() for k in ("no theorem", "sin cambio", "no protected",
                                      "unchanged", "no mathematical")),
        "text": dt.strip()[:900]}

    # every sidecar in the target verifies by content
    all_sc = []
    for dp2, dn, fn in os.walk(ROOT):
        q = dp2.replace("\\", "/")
        if EXCL in q:
            continue
        dn[:] = [d for d in dn if EXCL not in (q + "/" + d)]
        for f in fn:
            low = f.lower()
            if low.endswith(".sha256") or ("sha256" in low and low.endswith(".txt")) \
               or ("manifest" in low and low.endswith((".txt", ".sha256"))):
                rel = os.path.relpath(os.path.join(dp2, f), ROOT).replace("\\", "/")
                d = os.path.dirname(os.path.join(dp2, f))
                bases = [d]
                cur = d
                for _ in range(7):
                    cur = os.path.dirname(cur)
                    bases.append(cur)
                bases.append(ROOT)
                r = verify_sidecar(rel, bases)
                r.pop("paths", None)
                all_sc.append(r)
    out["checks"]["all_sidecars"] = {
        "checked": len(all_sc),
        "verifying": sum(1 for x in all_sc if x["verifies"]),
        "failing": [x for x in all_sc if not x["verifies"]],
        "line_ending_summary": {e: sum(1 for x in all_sc if x["line_endings"] == e)
                                for e in ("LF", "CRLF", "MIXED")}}
    print(json.dumps(out, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
