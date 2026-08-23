#!/usr/bin/env python3
"""FINAL RESIDUAL AUDIT, PAPER_I v1.3 pkgfix, target verification.

The spec declares an aggregate path/hash-list SHA-256 that this auditor could not
reproduce under twelve plausible conventions, while the declared file count and total
byte size matched exactly. This script settles whether that is a target defect or a
convention difference, by comparing the owner's own target manifest against the
auditor's independently computed inventory entry by entry.
"""
import hashlib
import json
import os

OWNER = ("C:/v13/02_validation/01_INTERNAL_AUDITS/residual_run_2026-08-21_v1.3_pkgfix/"
         "20_EVIDENCE/R0_PACKAGE_FIX/results/TARGET_FREEZE_MANIFEST.sha256")
MINE = "C:/c1/00_REQUEST/INPUT_TARGET_INVENTORY.json"
DECLARED = "f12e1060c0e8693a5702ae9a5c0d143a3025feadcf6a7289e90c061769c748b6"
BACKSLASH = chr(92)


def main():
    raw = open(OWNER, "rb").read()
    crlf = raw.count(b"\r\n")
    lf = raw.count(b"\n") - crlf
    endings = "CRLF" if crlf and not lf else ("LF" if lf and not crlf else "MIXED")

    theirs = {}
    for line in raw.decode("utf-8", "replace").splitlines():
        line = line.strip()
        if not line:
            continue
        parts = line.split(None, 1)
        if len(parts) == 2:
            path = parts[1].lstrip("*").strip().replace(BACKSLASH, "/")
            theirs[path] = parts[0].lower()

    inv = json.load(open(MINE))
    mine = {i["path"]: i["sha256"] for i in inv["files"]}

    only_theirs = sorted(set(theirs) - set(mine))
    only_mine = sorted(set(mine) - set(theirs))
    disagree = sorted(k for k in set(theirs) & set(mine) if theirs[k] != mine[k])
    agree = not only_theirs and not only_mine and not disagree

    out = {
        "spec": "FINAL_RESIDUAL_AUDIT_REQUEST_SPEC.md",
        "question": ("is the unreproducible aggregate a target defect, or a difference "
                     "in aggregation convention?"),
        "owner_manifest": OWNER,
        "owner_manifest_bytes": len(raw),
        "owner_manifest_line_endings": endings,
        "owner_entries": len(theirs),
        "auditor_entries": len(mine),
        "only_in_owner_manifest": only_theirs,
        "only_in_auditor_inventory": only_mine,
        "hash_disagreements": disagree,
        "manifests_agree_entry_for_entry": agree,
        "auditor_file_count": inv["file_count"],
        "declared_file_count": inv["file_count_expected"],
        "file_count_match": inv["file_count"] == inv["file_count_expected"],
        "auditor_total_bytes": inv["total_bytes"],
        "declared_total_bytes": inv["total_bytes_expected"],
        "total_bytes_match": inv["total_bytes"] == inv["total_bytes_expected"],
    }

    # can the declared aggregate be reproduced from the owner's own artifacts?
    tried = {"sha256_of_owner_manifest_file": hashlib.sha256(raw).hexdigest()}
    inv_json = OWNER.replace("TARGET_FREEZE_MANIFEST.sha256", "INPUT_INVENTORY.json")
    if os.path.isfile(inv_json):
        b = open(inv_json, "rb").read()
        tried["sha256_of_owner_inventory_json"] = hashlib.sha256(b).hexdigest()
        try:
            d = json.loads(b.decode("utf-8"))
            for k, v in d.items():
                if isinstance(v, str) and len(v) == 64:
                    tried[f"owner_inventory_field:{k}"] = v.lower()
        except Exception:
            pass
    out["declared_aggregate"] = DECLARED
    out["reproduction_attempts_from_owner_artifacts"] = {
        k: {"value": v, "matches_declared": v == DECLARED} for k, v in tried.items()}
    out["aggregate_reproduced"] = any(v == DECLARED for v in tried.values())

    if agree and out["file_count_match"] and out["total_bytes_match"]:
        out["conclusion"] = (
            "TARGET CONTENT VERIFIED. The owner's manifest and the auditor's independent "
            "inventory agree on every path and every hash, and the declared file count and "
            "total byte size both match. The declared aggregate is therefore an aggregation "
            "convention this auditor could not reproduce, not evidence of a content "
            "difference. Reported as a NOTE, not a BLOCKER.")
    else:
        out["conclusion"] = ("TARGET CONTENT MISMATCH - this is a genuine discrepancy and "
                            "must be treated as a BLOCKER.")
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
