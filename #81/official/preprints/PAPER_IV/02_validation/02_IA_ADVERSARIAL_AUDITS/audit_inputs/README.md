# Historical inputs — not public manuscript editions

This directory preserves the exact intermediate inputs needed to understand
and reproduce the audit chain. They are **not alternative releases**.
Read the current manuscript at ../../../01_manuscript/ (relative to the
Paper IV package root, the current location is 01_manuscript/).

Original manuscript filenames and sealed ZIPs are retained. Original audit
targets are not rewritten: their paths describe the workspace used at the
time. The [relocation map](../../../04_integrity/RELOCATION_MAP_v1.22.json)
identifies original and current relative paths and hashes for every copied
artifact. The exact published v1.22 package is also retained in
[published_v1.22](published_v1.22/). The current v1.23 manuscript is an
editorial revision, not a byte-identical copy of the audited v1.22 input.
The relocation delta in `../../../04_integrity/RELOCATION_DELTA_v1.23.json`
resolves the former active v1.22 paths without changing the historical map.

For portable replay, the release verification tool can restore mapped
artifacts to their original relative paths in a new, separate directory.
This does not execute Lean or restore dependencies. The actual prior build
cache is not a publication artifact.
