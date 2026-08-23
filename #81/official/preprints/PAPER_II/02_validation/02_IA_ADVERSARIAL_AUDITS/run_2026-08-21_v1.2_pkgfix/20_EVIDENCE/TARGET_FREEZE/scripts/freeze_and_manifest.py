#!/usr/bin/env python3
"""PAPER_II v1.2 pkgfix residual re-audit — target freeze and canonical manifest.

The specification publishes the manifest algorithm explicitly, so it is reproducible:

  UTF-8, LF-only lines of the form
      <file_sha256><two spaces><target-relative POSIX path>\\n
  sorted CASE-INSENSITIVELY by target-relative POSIX path,
  then SHA-256 over the exact manifest bytes.

Declared: 245 files, 3,940,779 bytes, manifest SHA-256
4b41f7e2e9415ca55514c6997dc6bff4e952b830282f46012c5214b04f688c1e.

A file-entry mismatch is a blocker. A manifest-summary mismatch is reported separately.
"""
import hashlib
import json
import os

ROOT = "C:/p2t"
EXCL = "02_validation/02_IA_ADVERSARIAL_AUDITS"
DECL_FILES = 245
DECL_BYTES = 3940779
DECL_MANIFEST = "4b41f7e2e9415ca55514c6997dc6bff4e952b830282f46012c5214b04f688c1e"


def main():
    items = []
    for dp, dn, fn in os.walk(ROOT):
        q = dp.replace("\\", "/")
        if EXCL in q:
            continue
        dn[:] = [d for d in dn if EXCL not in (q + "/" + d)]
        for f in fn:
            p = os.path.join(dp, f)
            b = open(p, "rb").read()
            items.append({"path": os.path.relpath(p, ROOT).replace("\\", "/"),
                          "bytes": len(b),
                          "sha256": hashlib.sha256(b).hexdigest()})
    # canonical order: case-insensitive by POSIX path
    items.sort(key=lambda x: x["path"].lower())
    manifest_bytes = "".join(f"{i['sha256']}  {i['path']}\n"
                             for i in items).encode("utf-8")
    man_hash = hashlib.sha256(manifest_bytes).hexdigest()
    nfiles = len(items)
    nbytes = sum(i["bytes"] for i in items)

    with open("C:/p2o/00_REQUEST/INPUT_TARGET_MANIFEST.sha256", "wb") as fh:
        fh.write(manifest_bytes)

    out = {
        "spec": "FINAL_RESIDUAL_AUDIT_REQUEST_SPEC.md",
        "spec_sha256": "2eadd655d6dd9f1d96127c979ba43a0b2d251da7478cd84ba4bb1868e38cb683",
        "paper": "PAPER_II", "target": "preprint_draft_v1.2 (corrected in place)",
        "run": "run_2026-08-21_v1.2_pkgfix",
        "manifest_algorithm": ("UTF-8, LF-only, '<sha256><two spaces><posix path>\\n', "
                              "sorted case-insensitively by path, then SHA-256 of the "
                              "exact manifest bytes"),
        "file_count": nfiles, "file_count_declared": DECL_FILES,
        "file_count_match": nfiles == DECL_FILES,
        "total_bytes": nbytes, "total_bytes_declared": DECL_BYTES,
        "total_bytes_match": nbytes == DECL_BYTES,
        "manifest_sha256": man_hash, "manifest_sha256_declared": DECL_MANIFEST,
        "manifest_sha256_match": man_hash == DECL_MANIFEST,
        "excluded_subtree": EXCL,
        "files": items,
    }
    json.dump(out, open("C:/p2o/00_REQUEST/INPUT_TARGET_INVENTORY.json", "w"), indent=1)

    print(f"file count      : {nfiles:>10}  declared {DECL_FILES:>10}  "
          f"{'MATCH' if out['file_count_match'] else 'MISMATCH'}")
    print(f"total bytes     : {nbytes:>10}  declared {DECL_BYTES:>10}  "
          f"{'MATCH' if out['total_bytes_match'] else 'MISMATCH'}")
    print(f"manifest sha256 : {man_hash}")
    print(f"        declared: {DECL_MANIFEST}")
    print(f"                  {'MATCH' if out['manifest_sha256_match'] else 'MISMATCH'}")


if __name__ == "__main__":
    main()
