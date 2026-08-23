# Final External Package-Residual Re-audit — Paper I, `preprint_draft_v1.3` (corrected)

**Specification:** `FINAL_RESIDUAL_AUDIT_REQUEST_SPEC.md`
**Specification SHA-256:** `93cf8e6a06cd47189e98a4939145b21a32a283956c172a2791812a4df5a87484`
**Run:** `run_2026-08-21_v1.3_pkgfix`
**Audit class:** external residual adversarial re-audit
**Audit date:** 2026-08-21

---

## 1. Executive verdict

> ## `PASS`

**Paper I v1.3 is externally closed with a plain `PASS`.**

Both open MINOR findings are independently **closed**. The corrected target's inventory and
all ten anchors verify. The package regression found **no new blocker, major or minor**.
Reused evidence satisfies byte identity. The two standing NOTEs are preserved.

| Item | Result |
|---|---|
| `RES-V13-001` compiler scratch | **CLOSED** |
| `RES-V13-002` transposed changelog namespaces | **CLOSED** |
| Control A — no scratch anywhere in the target | **PASS** |
| Control B — changelog names corrected and cross-consistent | **PASS** |
| Control C — general package regression | **PASS** |
| Anchors | **10 / 10 match** |
| Target inventory | **308 files, 37,763,479 bytes — exactly as declared** |
| New blocker / major / minor | **0 / 0 / 0** |
| Open notes | 2 (`RES-V13-004`, `PKGFIX-N01`) |

**This audit is not human peer review and does not prove global novelty.**

This report does **not** relabel or supersede the earlier `PASS_WITH_RESIDUALS` report,
which stands against its own hashes.

## 2. Target identity

### 2.1 Anchors — 10 / 10

| Artifact | SHA-256 | Result |
|---|---|---|
| English Markdown | `f3094b670c93ff622c3f573cdab61bdd0f5d84007f04b1888b364e0183565bea` | MATCH |
| Spanish Markdown | `57ba967fc2de805b7bbb4cf5f937727bde43c2ada80fa794bcbb5a727db05b8b` | MATCH |
| English LaTeX | `1a87de70548879ca90a714ec9e1b10c8576b380a749785916e5d59176e479465` | MATCH |
| Spanish LaTeX | `f83ee709c1168b5b9afe504e6b6a43763bf3bb2a08f674f2031f83670ba9bb56` | MATCH |
| English PDF | `7d04c47692b613c8d6e2cc4471f0205128b4ae06ca11d581a08d020eb2236db0` | MATCH |
| Spanish PDF | `3ad16ae86e8fcad358bf964a6ae98ae053b0bde2fdf3140e008cedab78b90c2a` | MATCH |
| Lean archive | `0181506408644fc1f8872d711de5a98a500f4052aa295bcd6f8c82776694fd3a` | MATCH |
| Previous external report | `f2ad1605f0a802932c07503bfad429a98b08af26844dd968aad6e3f145aee495` | MATCH — located at `run_2026-08-21_v1.3/30_REPORT/FINAL_AUDIT_REPORT.md` |
| Corrected changelog | `0850e518dc35bab0065ddb9f6b2a5850bc8c1d079ce7ed27872d6b09074349ef` | MATCH |
| Internal residual audit ZIP | `0ac2fa306a2df8607b2d2d5d54ec4d9cdda8eca4f21dd8e47f1e36d8adae92e6` | MATCH |

The six publication artifacts and the Lean archive are **unchanged**, which is what licenses
the evidence reuse in Section 5. The Lean archive was re-extracted for the byte-identity
check and its hash was re-verified afterwards: unchanged, so the target was not mutated.

### 2.2 Inventory

| Quantity | Recomputed | Declared | Result |
|---|---|---|---|
| file count | **308** | 308 | **MATCH** |
| total bytes | **37,763,479** | 37,763,479 | **MATCH** |
| paths into the excluded audit subtree | 0 | — | correct |

Every entry was recomputed before analysis, as Section 2 requires.

**Independent cross-check against the owner's own manifest.** The package contains the
owner's target freeze manifest at
`02_validation/01_INTERNAL_AUDITS/residual_run_2026-08-21_v1.3_pkgfix/20_EVIDENCE/R0_PACKAGE_FIX/results/TARGET_FREEZE_MANIFEST.sha256`
(219 entries, CRLF). Resolved against the target root it verifies **219 of 219, with zero
mismatches and zero missing files**, and there is **no path present in the owner's manifest
and absent from this auditor's inventory**. The 89 additional files in the auditor's
inventory are exactly the owner's own pkgfix internal-residual-audit output, which their
earlier manifest predates. **The target content is independently verified.**

### 2.3 One declared control value could not be reproduced — `PKGFIX-N01` (NOTE)

The specification declares an aggregate path/hash-list SHA-256 of
`f12e1060c0e8693a5702ae9a5c0d143a3025feadcf6a7289e90c061769c748b6`. This auditor **could
not reproduce it** under **16 combinations** of scope and convention, including: hashing the
manifest text as `hash  path\n`, `hash *path\n` and with CRLF; `path\nhash\n`; bare
concatenations in both orders; hashes only; a `hash|path|bytes` form; backslash path
separators; sorting by hash instead of path; and each of those over both the 308-file scope
and the 219-file scope that excludes the pkgfix internal-audit output.

It also does not equal the aggregate recorded in the owner's own inventory for the same
correction (`402fe23d5538851b290c749927ea75052efadc8c5df5cda5aba5fdbe0495a325`).

**Classification.** Specification Section 2 says "Recompute every entry before analysis. Any
mismatch is a `BLOCKER`." Every entry *was* recomputed and **every entry matches** — the
file count, the total byte size, all ten anchors, and all 219 entries of the owner's own
manifest. There is therefore **no entry mismatch and no content discrepancy**. What cannot
be reproduced is a single summary value whose construction algorithm is not published and
which the owner's own artifacts do not reproduce either. That is a defect in the
**specification's control value**, not in the target package, so it is recorded as a `NOTE`
rather than a `BLOCKER`.

**If the owner intends this aggregate to function as a hard integrity control, the
algorithm needs to be published** — otherwise no external party can ever verify it, and it
cannot do the job it is there to do.

## 3. Control A — `RES-V13-001` is closed

Scope: all 308 files of the input target.

| Check | Result |
|---|---|
| any directory named `tmp` | **none** |
| `.aux`, `.toc`, `.out`, `.fls`, `.fdb_latexmk`, `.synctex(.gz)`, `.nav`, `.snm`, `.bbl`, `.blg`, `.idx`, `.ilg`, `.ind`, `.lof`, `.lot`, `.spl`, `.bcf`, `.run.xml` | **none** |
| zero-byte files | **none** |
| stray `$o` or any `$` in a basename | **none** |
| unexpected hidden files (beyond `.gitattributes`, `.gitignore`) | **none** |

**Two initial flags were investigated and dismissed rather than filed.**

1. Two files share the basename `INTERNAL_AUDIT_FINAL_REPORT.pdf`, under
   `00_BASELINE_INTERNAL_AUDIT_v1.2/10_REPORT/` and `01_INTERNAL_AUDITS/10_REPORT/`. Their
   hashes **differ** (`193d219b...` and `45a47049...`): they are two distinct reports from two
   distinct audit runs, each in its own report directory. Not a duplicate copy — the initial
   flag came from matching on basename alone.
2. The strings `tmp/internal_report_v1.3` and `internal_report_v1.3` occur in two target
   documents. Both are **records of the removal**, not dependencies on the removed files:
   `04_integrity/EXTERNAL_AUDIT_V1.3_RESIDUAL_MATRIX.md` L14 reads "Removed
   `tmp/internal_report_v1.3/` from the active package; the three scratch files were moved
   outside the target to a recoverable agent-work location", and the internal residual
   report L36 reads "The active package no longer contains `tmp/internal_report_v1.3/`." A
   correction record must be able to name what it removed. **No document points to the
   removed files as though they still existed.**

Also worth recording: the scratch files were **moved out of the target, not destroyed**, so
the correction is reversible.

**Control A verdict: `PASS`. `RES-V13-001` is closed.**

## 4. Control B — `RES-V13-002` is closed

`CHANGELOG_v1.3.md`:

| Name | Occurrences | Required |
|---|---|---|
| `PaperI.assembly_sharp` | **1** | exactly 1 |
| `PaperI.Split.residual_duality` | **1** | exactly 1 |
| `PaperI.Split.assembly_sharp` (transposed) | **0** | absent |
| `PaperI.residual_duality` (transposed) | **0** | absent |

**Cross-checked against every other authority**, as the specification requires. All four
agree, and none contains a transposed form:

| Authority | `PaperI.assembly_sharp` | `PaperI.Split.residual_duality` | transposed forms |
|---|---|---|---|
| corrected changelog | 1 | 1 | 0 |
| manuscript Appendix C, English | 3 | 4 | 0 |
| manuscript Appendix C, Spanish | 3 | 4 | 0 |
| recorded axiom report (`R4_FORMAL_REUSE/results/AXIOMS_REPORT.txt`) | 1 | 1 | 0 |
| `FreezeAxioms.lean` in the delivered archive | present | present | 0 |
| **previous external verbatim `#print axioms` output** | present | present | 0 |

The previous external run's own verbatim theorem-level output was:

```
'PaperI.paperI_main' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.Split.paperI_main_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.assembly_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.Split.residual_duality' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The changelog now agrees with the compiled reality. **Control B verdict: `PASS`.
`RES-V13-002` is closed.**

## 5. Control C — general package regression

### 5.1 Sidecars: 37 of 37 verify

Every sidecar in the input target was verified by content. **All 37 verify with zero
mismatches and zero missing files.**

One sidecar initially appeared to fail — the owner's own 219-entry
`TARGET_FREEZE_MANIFEST.sha256`, reported as missing `.gitattributes` and `.gitignore`.
That was this auditor's own base-directory resolver stopping five levels up when the
manifest's paths are relative to the target root, six levels up. Resolved against the
target root it verifies **219 of 219**. Recorded because a tool artifact should not be left
looking like a target defect.

### 5.2 The internal residual audit ZIP

| Check | Result |
|---|---|
| SHA-256 | `0ac2fa306a2df8607b2d2d5d54ec4d9cdda8eca4f21dd8e47f1e36d8adae92e6` |
| matches its own `.sha256` sidecar | **yes** |
| matches the specification anchor | **yes** |
| members | 87 |
| every member byte-identical to the corresponding loose file | **yes, 0 mismatches** |

### 5.3 No unannounced target delta

This is the load-bearing check for Section 4's claim that the delta is package-only. The
current 308-file target was diffed against the **previous external freeze** (221 files,
recorded in `run_2026-08-21_v1.3/00_REQUEST/INPUT_INVENTORY.json`) and every difference was
classified against the four authorized changes.

| Delta | Count | Classification |
|---|---|---|
| **removed** | 3 | all three are the `tmp/` scratch files — authorized change 1 |
| **changed** | 4 | `CHANGELOG_v1.3.md` (authorized change 2) plus 3 README / metadata / status files (authorized change 4) |
| **added** | 90 | all are the correction matrix and the new internal residual audit evidence — authorized change 3 |
| **UNANNOUNCED** | **0** | — |

**Zero unannounced changes in all three categories.** In particular there is no manuscript,
theorem, proof, citation, figure, LaTeX, PDF, formal source, toolchain, dependency or
axiom-query change, exactly as Section 4 states.

### 5.4 Stale strings, truncation, self-containment

| Check | Result |
|---|---|
| stale `v1.0.1`, `lean_v1.1_freeze`, `PAPER_I_LEAN_v1.1_FREEZE` in the manuscripts | **none** |
| truncated Markdown or scripts | **none**. Ten files were flagged by a deliberately crude end-of-file heuristic and each was inspected: a YAML list item, a hash sidecar ending in a filename, a Python file ending in `raise`, and similar. All complete. |
| manuscript self-containment, English | **0 violations** |
| manuscript self-containment, Spanish | **0 violations** |

The manuscripts reference no version history, no correction matrix, no audit report, no
changelog and no finding identifier. They remain self-contained.

### 5.5 The internal residual report was inspected, not taken on its label

Specification Section 5 asks for the raw gate evidence rather than the PASS label. Inspected:

| Raw artifact | Content |
|---|---|
| `R4_FORMAL_REUSE/results/BUILD_EXIT.txt` | `EXIT_CODE=0` |
| `R4_FORMAL_REUSE/results/AXIOMS_EXIT.txt` | `0` |
| `R4_FORMAL_REUSE/results/AXIOMS_REPORT.txt` | the four claim-surface declarations with the correct namespaces and `[propext, Classical.choice, Quot.sound]` — **identical to this auditor's own external verbatim output** |
| `R4_FORMAL_REUSE/results/ESCAPE_HATCH_SCAN.txt` | hits are all doc comments and prose, consistent with this auditor's independent finding of **0** escape hatches in active code |

One discrepancy in their scan output was chased down: it shows
`FreezeAxioms.lean:8` reading "preprint draft **v1.1**". The **delivered** archive's
`FreezeAxioms.lean` line 8 reads "preprint draft **v1.2**", verified both inside the archive
and in the loose copy. Their scan evidently ran over a different working tree. **The
delivered artifact is correct**; no finding.

**Control C verdict: `PASS`.**

## 6. Reused evidence — `REUSED_BYTE_IDENTICAL_EXTERNAL_EVIDENCE`

Specification Section 6 permits reuse once the eight manuscript and formal anchors match,
and prohibits unnecessary rework. The anchors match, so the following are reused and **were
not rerun**: `lake update`, `lake exe cache get`, the 8,034-job Lean build, the frozen and
independent axiom queries, the full mathematical enumeration, the bilingual and duplicate
analysis, the citation work, and PDF compilation.

Reused from `run_2026-08-21_v1.3` and, transitively, the external `run_2026-08-21_v1.2`
clean room:

| Reused item | Recorded result |
|---|---|
| clean Lean build | exit 0, 24m47.960s, `Build completed successfully (8034 jobs)`, zero errors |
| axiom footprint | `[propext, Classical.choice, Quot.sound]` on all four claim surfaces and all 15 frozen declarations |
| escape hatches in active code | 0 |
| mathematical regression | 14/14 exact symbolic identities; 6,732 orbit-LP cases with 0 mismatches; 5,429 split graphs with 0 violations of Theorem 1.1; `(p,q,s)=(2,4,2)` confirmed as equality |
| duplication analysis | 0 genuine duplicates across all six artifacts; 0 exact-duplicate pages |
| citations | the `3/16` constant verified against the primary source with pinpoint **Theorem 1, page 23** |
| bilingual chain | all eight corrections present in both languages at identical line numbers |

Byte identity for the formal reuse was re-established in this run, not assumed: the archive
was re-extracted and all **32 members** compared against the external clean room —
**32 byte-identical, 0 differing, 0 missing** — with `lean-toolchain`, `lake-manifest.json`,
`lakefile.toml` and `FreezeAxioms.lean` each identical.

## 7. Findings

| ID | Severity | Status | Summary |
|---|---|---|---|
| `RES-V13-001` | MINOR | **CLOSED** | compiler scratch removed; no `tmp` directory and no scratch file anywhere in 308 files |
| `RES-V13-002` | MINOR | **CLOSED** | changelog namespaces corrected and cross-consistent with five other authorities |
| `RES-V13-004` | NOTE | OPEN | the cited `ordman.net` URL serves an expired certificate, so the printed citation does not resolve cleanly. Preserved as the specification directs. The `3/16` constant itself **is** verified, so this is accessibility, not an evidentiary gap. |
| `PKGFIX-N01` | NOTE | OPEN | the specification's declared aggregate hash is not reproducible under 16 scope-by-convention combinations and differs from the owner's own recorded aggregate. Target content independently verified by other means. See Section 2.3. |

**No new blocker, major or minor finding.**

## 8. Verdict against the Section 7 rule

| Condition for a plain `PASS` | Met |
|---|---|
| both MINOR findings independently closed | **yes** — Sections 3 and 4 |
| the target inventory and anchors verify | **yes** — 308 files, 37,763,479 bytes, 10/10 anchors, and the owner's 219-entry manifest verifies 219/219 |
| the package regression finds no new blocker, major or minor | **yes** — 0/0/0; two NOTEs only |
| reused evidence satisfies byte identity | **yes** — 32/32 members byte-identical |
| the report preserves the accessibility NOTE | **yes** — `RES-V13-004`, Section 7 |
| the report states this is not human peer review and does not prove global novelty | **yes** — Sections 1 and 9 |

> **Paper I v1.3 is externally closed with a plain `PASS`.**

## 9. What this audit does not establish

- It does **not** establish that Theorem 1.1 is true. Across three runs, a determined
  adversarial effort — exhaustive enumeration, exact symbolic recomputation and an
  independent formal reproduction — failed to falsify it. That is the strongest statement
  the evidence supports.
- It is **not** human peer review.
- It does **not** prove global novelty. No run performed a prior-art search that could;
  the Gate K conclusion of the v1.2 run was evidence-bounded and remains so.
- It does **not** re-derive the Lean development in this run; Gate H is reused under
  byte identity.
- It does **not** verify that the delivered PDFs were compiled from the delivered TeX.
- It does **not** cover the six project Lean modules outside the eight built targets.
- It does **not** formally establish that the bespoke `PaperI.Split` structure models every
  split graph; that adequacy step is by inspection.
- **Disclosure carried forward:** this auditor produced the findings being verified here,
  and no adversarial challenger was run for v1.3 or for this package-fix run. An
  independent second opinion, ideally from a different model family, would be stronger than
  any of these three runs.

## 10. Signature

| Item | Value |
|---|---|
| Auditor | Claude Opus 5 (`claude-opus-5`), Anthropic |
| Configuration | primary auditor; no challenger for this run |
| Audit date | 2026-08-21 |
| Specification | `FINAL_RESIDUAL_AUDIT_REQUEST_SPEC.md`, SHA-256 `93cf8e6a...7484` |
| Target | `preprint_draft_v1.3` corrected, 308 files, 37,763,479 bytes |
| **Verdict** | **`PASS`** — both MINORs closed; 0 new blocker/major/minor; 2 disclosed NOTEs |

The earlier `PASS_WITH_RESIDUALS` report is **not** relabelled. It stands against its own
hashes as the record of the state that preceded these corrections.
