# E0 — identity

**Obligation.** Recompute input hashes, ZIP CRC and member hashes; traversal, hidden payloads, freeze/config
consistency, source immutability at the end; distinguish main ZIP, annex and historical v0.8.

**Method.** (1) The mandated read-only `verify_audit_target.py` (output `verify_audit_target_output.json`:
`INTAKE_IDENTITY_OK`, 178 checks, exit 0). (2) Auditor-written `e0_identity.py` (independent of (1)) run at
intake (10:59) and final (11:26): SHA-256 + size of all 22 AUDIT_TARGET files; cross-check of the nine hashes
quoted in the request table against both AUDIT_TARGET.json and the bytes; for the four ZIPs: `testzip`, member
list, duplicate names, absolute/`..`/drive/backslash paths, symlink bits, encryption flags, comments, extra
fields, local-header signatures and any byte ranges not covered by local records or the central directory;
candidate `MANIFEST.json` (156 files) vs disk. (3) `E0_sources_vs_zip.json`: the 504 `.lean` members equal the
504 `SOURCES.json` entries byte for byte (module names unique). (4) Annex internal `SOURCE_MANIFEST.sha256`:
39/39 OK (CRLF-normalised).

**Results.** All target hashes and sizes match (intake and final, identical); request table = AUDIT_TARGET.json
= bytes for all nine; CRC OK for all four ZIPs; members 508 / 40 / 2 480 / 158; no traversal, duplicates,
symlinks, encryption, comments or hidden bytes; manifest 0 mismatches (two unlisted `.aux` files — F-08).
Toolchain file `leanprover/lean4:v4.28.0`; lakefile requires Mathlib `v4.28.0`; manifest pins equal the installed
HEADs (`00_CONTROL/ENVIRONMENT.md`). Main ZIP ≠ annex (annex = 38 `BoundedCliqueGap` modules + README +
manifest, no overlap with the 504 main modules); the public v0.8 draft was not used. The read-only extracted copy
was unchanged at the end and contains no `.lake`. **Negative control (`E0_negative_control.txt`):** an in-memory one-byte modification of the EN md is detected as a mismatch (False), the original matches (True). **E0 = PASS.**
