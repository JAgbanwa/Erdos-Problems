#!/usr/bin/env python3
"""Identify the two package-manifest entries whose hash did not match the archive member my
suffix matcher paired them with. Distinguish a real discrepancy from a mis-pairing."""
import hashlib
import io
import sys
import zipfile

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")

F = "C:/p3v15/05_formalization/lean_v1.4_freeze"

pkg = {}
for line in open(f"{F}/PACKAGE_MANIFEST.sha256", encoding="utf-8", errors="replace"):
    p = line.split(None, 1)
    if len(p) == 2 and len(p[0]) == 64:
        pkg[p[1].strip().lstrip("*").replace("\\", "/")] = p[0].lower()

z = zipfile.ZipFile(f"{F}/PAPER_III_lean_v1.4_freeze.zip")
inside = {n.replace("\\", "/"): hashlib.sha256(z.read(n)).hexdigest()
          for n in z.namelist() if not n.endswith("/")}

print(f"manifest entries: {len(pkg)}   archive files: {len(inside)}")
print(f"manifest key sample: {list(pkg)[:3]}")
print(f"archive  key sample: {list(inside)[:3]}\n")

# exact-key comparison first: the honest test
exact_ok = exact_bad = absent = 0
bad = []
for rel, want in pkg.items():
    if rel in inside:
        if inside[rel] == want:
            exact_ok += 1
        else:
            exact_bad += 1
            bad.append((rel, want, inside[rel]))
    else:
        absent += 1
print("--- exact-key comparison (no suffix heuristics)")
print(f"  match: {exact_ok}   mismatch: {exact_bad}   key absent from archive: {absent}")
for rel, w, g in bad:
    print(f"    MISMATCH {rel}\n      manifest {w}\n      archive  {g}")

# now show what the suffix matcher did, to expose mis-pairings
print("\n--- suffix-heuristic comparison, for contrast")
for rel, want in pkg.items():
    cands = [k for k in inside if k == rel or k.endswith("/" + rel) or rel.endswith(k)]
    if cands and inside[cands[0]] != want:
        print(f"    entry {rel}")
        print(f"      candidates: {cands}")
        print(f"      manifest {want}")
        print(f"      first candidate {cands[0]} -> {inside[cands[0]]}")
        exact = inside.get(rel)
        print(f"      exact-key hash: {exact}  (matches manifest: {exact == want})")

# any archive member not covered by the manifest?
extra = [k for k in inside if k not in pkg]
print(f"\narchive members absent from the manifest: {len(extra)} {extra[:10]}")
