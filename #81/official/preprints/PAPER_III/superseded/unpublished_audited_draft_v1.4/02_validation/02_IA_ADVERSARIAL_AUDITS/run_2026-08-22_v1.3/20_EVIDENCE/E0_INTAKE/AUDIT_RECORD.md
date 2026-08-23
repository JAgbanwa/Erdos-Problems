# E0 -- intake, provenance and sealing

**Verdict: `PASS`.**

Every declared hash and manifest entry was recomputed before any substantive work, as the
request requires. A mismatch would have been a blocking intake failure.

| Chain | Entries | Result |
|---|---|---|
| `04_integrity/CURRENT_TARGET_SHA256.txt` | 12 | **12/12**, LF-only |
| manuscript sidecar | 6 | **6/6**, LF-only |
| freeze-archive sidecar | 1 | **1/1**, LF-only |
| `SOURCE_MANIFEST.sha256` | 707 | **707/707** |
| `PACKAGE_MANIFEST.sha256` | 742 | **742/742** |

The freeze ZIP hashes to `2eb0ff20a9dae6610a46026355374570d5afdfea89837ea7f9dd29da10b9d300`,
matching the value the request declares. `testzip` reports the CRC of all 743 members intact.

Archive hygiene, all zero: path traversal, absolute paths, backslash names, symlink or reparse
entries, compiled artifacts (`.olean`, `.ilean`, `.o`, `.c`, `.dll`, ...), `.lake` directories,
duplicate entries.

Auditor manifest: **875 files, 16,502,156 bytes**, at `00_CONTROL/TARGET_SHA256.txt`, computed
with UTF-8 LF-only lines `<sha256><two spaces><target-relative posix path>` sorted by path.
`05_formalization/lean_v1.3_candidate/` is excluded because the request states it is not part
of the frozen target and must not be copied, trusted or used.

Version labelling: thirteen stale-version strings occur in the tree. Twelve are legitimate
baseline or provenance references in validation documents. The two remaining, in
`FREEZE_REPORT.md` and `CHANGELOG_v1.3.md`, are explicit statements of what v1.3 descends from
("The source provenance is the preserved Paper III v1.2 formal snapshot...", "Baseline:
unpublished Paper III v1.2 draft package"). The publication artifacts carry none.

Evidence: `scripts/v13_E0_intake.py`, `results/E0_intake.json`.
