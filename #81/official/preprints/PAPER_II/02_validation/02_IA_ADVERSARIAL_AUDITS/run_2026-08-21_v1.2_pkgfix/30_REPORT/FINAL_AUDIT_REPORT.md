# Final External Package-Residual Re-audit -- Paper II v1.2, corrected in place

**Specification:** `FINAL_RESIDUAL_AUDIT_REQUEST_SPEC.md`
**Specification SHA-256:**

```
2eadd655d6dd9f1d96127c979ba43a0b2d251da7478cd84ba4bb1868e38cb683
```
**Request ID:** `PAPER_II_EXTERNAL_PACKAGE_RESIDUAL_v1.0`
**Run:** `run_2026-08-21_v1.2_pkgfix`
**Audit class:** independent external residual adversarial re-audit
**Audit date:** 2026-08-21

---

## 1. Executive verdict

> ## `PASS`

`EXT-PII-M-001` is independently **closed**. The 245-file target inventory verifies,
**including the canonical manifest hash**, all nine protected anchors match, the package
regression found **no new blocker, major or minor**, reused evidence satisfies byte
identity, and `EXT-P2-I-001` is preserved as a NOTE.

| Section 7 condition | Met |
|---|---|
| 1. `EXT-PII-M-001` independently closed | **yes** |
| 2. 245-file inventory and every manifest entry verify | **yes** |
| 3. all protected anchors match | **yes**, 9/9 |
| 4. package regression finds no new blocker, major or minor | **yes**, 0/0/0 |
| 5. reused evidence satisfies byte identity | **yes** |
| 6. `EXT-P2-I-001` preserved as a NOTE | **yes** |

**This audit is not human peer review and does not prove global novelty.**

The previous `PASS_WITH_RESIDUALS` run is not overwritten or relabelled.

## 2. Target freeze -- the manifest reproduced exactly

| Quantity | Recomputed | Declared | Result |
|---|---|---|---|
| files | **245** | 245 | **MATCH** |
| bytes | **3,940,779** | 3,940,779 | **MATCH** |
| manifest SHA-256 | see below | same | **MATCH** |

The recomputed manifest hash, identical to the declared value:

```
4b41f7e2e9415ca55514c6997dc6bff4e952b830282f46012c5214b04f688c1e
```

Worth stating plainly, because it contrasts with the Paper I package-fix run: this
specification **publishes the manifest algorithm** -- UTF-8, LF-only lines of the form
`<file_sha256><two spaces><target-relative POSIX path>\n`, sorted case-insensitively by
path, then SHA-256 over the exact manifest bytes. Because the algorithm is published, an
external party can reproduce the summary value, and this auditor did, on the first attempt.
In the Paper I run the corresponding aggregate was unreproducible under sixteen
scope-by-convention combinations and had to be recorded as an unverifiable control. That is
the difference a published algorithm makes.

Every file hash, byte count and path was recomputed before analysis. **No file-entry
mismatch.** No manifest-summary mismatch either, so the two are reported together here
rather than separately.

## 3. Protected anchors -- 9 / 9

Each of the nine declared anchors was recomputed from the frozen target and **matched**. Recomputed values, in declaration order:

```
7215e14bbea8ab2bf208dcdd1efa050cd2b72c997eee2efe504a1e6817c68882  English Markdown
d0d1df05eb267a51db2ccc100dd9725dcde9b03dbb95c8a730742e357eb0f4dc  Spanish Markdown
bb5f76c3ce56dbb0bff11242a3a8787f9c8ba3d9f0ad23973fc2f26cc5fc3cf0  English LaTeX
d3f0c6301a48d6553ebad222fa685f152119cb61b5efd3e8be55e389f9d606ae  Spanish LaTeX
d05c4cab1262357fddd21e4aab399bdb92d5bcf139172897c80595e781049052  English PDF
d525d02a6e911cb23f7e1f28e1de7648441eccea6de206e76e5321161c86c2db  Spanish PDF
ee2d05cc40d943ca92f8f7bf3e5dd83c2692518ddea5e2ca4f7686ccb1ac3895  Lean v1.2 archive
1e7afd3e9394bf83beb7e33ce19ff5227072fcd6b0eb3fd21e571329564e3ded  Previous external report
779c8453e0ec3666bd8a7564d2e1251b6f2acf586815cd43470c202fa657eb13  Internal residual-audit ZIP
```

The previous external report was located at `run_2026-08-21_v1.2/30_REPORT/FINAL_AUDIT_REPORT.md`.

All six publication artifacts and the Lean archive are **unchanged**, which is the
precondition for the evidence reuse in Section 7.

## 4. Control A -- `EXT-PII-M-001` is closed

### 4.1 The six corrected integrity documents

All six declared anchors match, and every one is **LF-only**:

All six live in `04_integrity/`.

| File | Anchor | Result |
|---|---|---|
| `INITIAL_SOURCE_SHA256.txt` | `1d5f8d91...0323` | MATCH, LF |
| `INITIALIZATION_DIFF.md` | `4b88e306...0c2c` | MATCH, LF |
| `README.md` | `d7ed1d33...0e85` | MATCH, LF |
| `CURRENT_TARGET_SHA256.txt` | `79fd6542...a315d` | MATCH, LF |
| `SEMANTIC_INTEGRITY_REPORT_v1.2.md` | `5c9d6dc4...d817e` | MATCH, LF |
| `EXTERNAL_AUDIT_V1.2_` `RESIDUAL_MATRIX.md` | `a004b4fe...0857` | MATCH, LF |

### 4.2 Each bullet of the control, checked independently

| Requirement | Result |
|---|---|
| `INITIAL_SOURCE_SHA256.txt` is LF-only and all **three** entries resolve from the package root and match | **PASS** -- LF, exactly 3 entries, 3/3 resolve and match, 0 missing |
| it contains no absent `PAPER_II_preprint_draft_v1.1.md` path | **PASS** -- no `preprint_draft_v1.1` path present |
| `CURRENT_TARGET_SHA256.txt` is LF-only and all **nine** entries resolve and match | **PASS** -- LF, exactly 9 entries, 9/9 resolve and match |
| `04_integrity/README.md` describes v1.2, not a pending v1.1 workspace | **PASS** -- it opens "Integrity records -- Paper II v1.2", the string "Pending for v1.1" is **gone**, and there is no reference to a `superseded/` directory the package does not contain. It states explicitly that it "replaces the stale v1.1 integrity records identified by external finding `EXT-PII-M-001`". |
| `INITIALIZATION_DIFF.md` documents v1.1 to v1.2 and claims no protected mathematical change | **PASS** -- it names the v1.1 English Markdown hash `361802b5...ded6` and the v1.2 hash `7215e14b...8882`, records that the historical package is retained outside the active target, and asserts no protected change |
| the semantic-integrity report and residual matrix agree with the actual hashes and external findings | **PASS** -- both match their declared anchors and reference `EXT-PII-M-001` correctly |
| no sidecar anywhere in the target fails by content | **PASS** -- see 4.3 |

The v1.2 defect was precisely that this directory was stale v1.1 content whose
`INITIAL_SOURCE_SHA256.txt` named a manuscript absent from the package, so one of its two
entries could not resolve. **All three entries now resolve and match, and the directory
describes the target it ships with.**

### 4.3 Every sidecar in the target: 40 of 40 verify

40 sidecars were verified by content -- 18 LF, 22 CRLF, none mixed. **All 40 verify with
zero mismatches and zero missing files.**

One initially appeared to fail:
the copy of `PAPER_II_preprint_draft_v1.2_SHA256.txt` under the internal run's `20_EVIDENCE/R5_ARTIFACTS/results/`.
It is a **byte-identical copy** of the real manuscript sidecar
(`fa0d1501...e962` for both), placed in the internal run's evidence directory, whose entries
are bare filenames and therefore resolve only from `01_manuscript/`, its documented base.
Resolved there it verifies **6/6**. The initial flag was this auditor's base-directory
resolver not including that directory. Recorded so a tool artifact is not left looking like
a target defect.

**Control A verdict: `PASS`. `EXT-PII-M-001` is closed.**

## 5. Control B -- the internal residual PASS was inspected, not trusted

The internal report hashes both match: Markdown `3fac92e6...0fe0`, PDF `dfdfe4f6...6761`.

| Gate | Spec expectation | What the raw evidence shows |
|---|---|---|
| **R0** | 17/17 controls, canonical manifest algorithm | `status: PASS`, `checks_passed: 17`, `checks_total: 17`, and a `canonical_manifest_algorithm` field. Their inventory scope is 200 files / 3,417,038 bytes -- narrower than this run's 245, because it excludes their own residual run; consistent, not contradictory. |
| **R1** | 58/58 common static controls | `status: PASS`, `checks_passed: 58`, and `audit_class: INTERNAL_NOT_EXTERNAL`, `lean_rerun: False` -- an honest self-label |
| **R2** | exit-zero exact regression over the unchanged Markdown hash | `status: PASS`, keyed to `target_sha256: 7215e14b...8882`, the unchanged EN Markdown. Real instance counts, not a bare label: 195 complete-split LP instances, 5,000 exact integer maximizations, 6,667 argmax level checks, 139 chordal atlas graphs for n <= 6, 931 vertex-copy non-edge pairs, 22 terminal-property graphs. Their own scope note calls bounded computation "corroborating evidence", which is the correct posture. |
| **R3** | zero exact or near duplicate blocks in all six artifacts | `status: PASS`, threshold 0.985 on normalized paragraphs of >= 180 characters, zero exact and zero near duplicates in every artifact |
| **R4** | copied external logs byte-consistent with the previous external run; build exit 0, 8,063 jobs, 16 axiom surfaces | **PASS, and verified at the byte level against this auditor's own artifacts** -- see 5.1 |
| **R5** | all six publication artifacts match the prior anchors | `status: PASS_UNCHANGED_ARTIFACTS`, `manuscript_artifacts_changed: False`, `pdfs_rebuilt: False`, `figures_changed: False` |
| **R6** | report compilation evidence, gate manifests, ZIP members and sidecar | ZIP `779c8453...eb13` matches its own sidecar **and** the specification anchor; **42 members, all byte-identical to the loose files** |

### 5.1 R4 is the one gate this auditor could check against its own evidence, and it holds

Specification Section 5 says R4 consists of external raw logs **copied** into the internal
run. Those logs are this auditor's own output from `run_2026-08-21_v1.2`, so byte-consistency
is checkable rather than a matter of trust. Comparing by SHA-256:

| Copied file | Byte-identical to the external original |
|---|---|
| `01_lake_update_cache_get.log` | **yes** |
| `02_lake_build_protocol_9_2.log` | **yes** |
| `03_FreezeAxioms_run.log` | **yes** |
| `EXTERNAL_H_AUDIT_RECORD.md` | no -- their own new record, correctly not a copy |
| `summary.json` | no -- their own new summary |

Read from **their** copies, not from the originals:

- `Build completed successfully (8063 jobs).`, `EXIT_BUILD=0`, **0** error lines;
- **16** axiom surfaces, `EXIT_AXIOMS=0`, **0** `sorryAx` and **0** project axioms;
- **2** surfaces carry the strictly smaller footprint `[propext, Quot.sound]`:
  `PaperII.phiTau_max_le_paperI_bound` and `SimpleGraph.IsChordal.comap` -- exactly the two
  this auditor identified independently in the external run.

Their `summary.json` records `lean_executed: False` alongside `external_build_exit: 0` and
`external_build_jobs: 8063`. That is an accurate and honest labelling of reuse rather than
execution.

**Control B verdict: `PASS`.** The label is backed by raw evidence, and the one gate that
could be cross-checked against independent artifacts matches byte for byte.

## 6. Control C -- general package regression

### 6.1 Hygiene: clean

| Check | Result |
|---|---|
| any `tmp` directory | **none** |
| compiler scratch (`.aux`, `.toc`, `.out`, `.fls`, `.fdb_latexmk`, `.synctex`, `.nav`, `.snm`, `.bbl`, `.blg`, `.idx`, `.ilg`, `.ind`, `.lof`, `.lot`, `.spl`, `.bcf`, `.run.xml`) | **none** |
| zero-byte files | **none** |
| stray `$o` or any `$` in a filename | **none** |
| unexpected hidden files | **none** |

### 6.2 Authorized delta: exact, with zero deletions

| Delta | Count | Classification |
|---|---|---|
| **changed** | **6** | exactly the six authorized files (the three `04_integrity/` documents named above, plus `DRAFT_METADATA.yml`, `DRAFT_NOTES.md` and the root `README.md`) |
| **added** | **48** | the 3 authorized integrity files, plus 45 files of the authorized internal residual run (under `01_INTERNAL_AUDITS/`, directory `residual_run_2026-08-21_v1.2_pkgfix`) |
| **removed** | **0** | no deletion, as required |
| **unauthorized** | **0** | -- |

197 files -> 245 files. No manuscript or formal change, so evidence reuse is not blocked.

### 6.3 Self-containment, stale references, status

- **Manuscript self-containment: 0 violations** in both languages. Neither manuscript
  references `v1.0.1`, a correction matrix, a residual matrix, an audit report, or any
  `EXT-PII-*` / `EXT-P2-*` finding identifier.
- **Stale `v1.0.1` references: 3, all investigated and none a reappearance.** All three are
  in `02_validation/00_intake/PAPER_II_preprint_v1.1.8_near_final_editorial_en.md`, a
  historical intake document from the v1.1.8 era that legitimately contains the old
  references because it *is* the old document. It appears in neither the changed nor the
  added list, so it is byte-unchanged from the previous external freeze -- pre-existing, not
  reintroduced. The specification asks that no stale reference **reappeared**; none did.
- **Status consistency: exact.** Both `README.md` and `DRAFT_METADATA.yml` carry the literal
  status `INTERNAL_PACKAGE_RESIDUAL_PASS_EXTERNAL_RESIDUAL_PENDING`, and `DRAFT_NOTES.md`
  states "a final external residual re-audit is pending". `DRAFT_METADATA.yml` also
  distinguishes `local_build: PASS_RECORDED_8061_AND_8032_JOBS_NOT_RERUN` from
  `independent_reproduction: PASS_EXTERNAL_CLEAN_ROOM_8063_JOBS` -- recorded evidence and
  independent reproduction kept apart, correctly.
- **No truncation, placeholder or malformed final report** was found.

**Control C verdict: `PASS`.**

## 7. Reused evidence -- `REUSED_BYTE_IDENTICAL_EXTERNAL_EVIDENCE`

All nine protected anchors match, so the prior external mathematical, formal, citation,
novelty, bilingual, duplicate and rendered-PDF evidence is reused. **These gates were not
rerun.** Specifically not rerun: the 30-minute Lean build, the full mathematical
falsification, and the 47-page rendered analysis.

Reused results, from `run_2026-08-21_v1.2`:

| Reused item | Recorded result |
|---|---|
| clean Lean build | exit 0, 30m05.109s, `Build completed successfully (8063 jobs)`, zero errors |
| axiom footprint | 16 declarations; 14 with `[propext, Classical.choice, Quot.sound]`, 2 with the smaller `[propext, Quot.sound]`, which the manuscript's Table 5 records accurately; no `sorryAx`, no project axiom |
| escape hatches in active code | 0 across 42 project files |
| headline falsification | 19,048 chordal graphs enumerated exhaustively for n <= 6; `max Phi_tau = floor((2n+1)^2/24)` exact at every n; always attained by a complete-split graph |
| vertex-copy inequality | 251,085 instances, 0 violations, minimum defect 0 |
| the identity nu3star = tau3star | 270,133 graphs, two separate linear programs, 0 mismatches |
| arithmetic corollaries | all four confirmed over n in [-20000, 20000], including negative n; the `n >= 1` hypothesis on the Paper I comparison shown **necessary** |
| bilingual and rendered PDF | protected content identical; 47 pages, 0 anomalies; the Paper I duplication defect class absent |
| citations | [1] verified verbatim against the publisher record; [3] Blair-Peyton retrieved |

**Prior scope limitations are preserved, not quietly dropped:**

- termination of the repeated-copy process was **not** independently verified;
- the discrete-convexity lift from single vertices to clone classes was **not** verified;
- the two-variable orbit reduction on `S_{p,q}` was tested only through its consequences;
- exhaustive enumeration reached only n = 6;
- Lean modules outside the seven protocol targets were never compiled;
- the PDFs were not independently recompiled from the delivered TeX;
- **the prior Paper II audit used a single reasoning context.** No adversarial challenger
  was run for Paper II, in that run or this one. On Paper I the challenger found four
  Spanish duplications the primary auditor had missed, so this is a real limitation and not
  a formality.

## 8. Findings

| ID | Severity | Status | Summary |
|---|---|---|---|
| `EXT-PII-M-001` | MINOR | **CLOSED** | stale v1.1 integrity directory; now describes v1.2, all three sidecar entries resolve, six corrected documents match their anchors |
| `EXT-P2-I-001` | NOTE | **OPEN** | the official Erdős Problems page returns HTTP 403 to this auditor. **Not repaired**, and not represented as repaired: no direct authoritative access was obtained. The substantive open-status claim is supported by the verified primary EOZ source, whose abstract states "It is unknown whether this many cliques will always suffice." |

**No new blocker, major or minor.**

## 9. What this audit does not establish

- It does **not** establish that the headline theorem is true. The prior external run's
  exhaustive falsification over 19,048 chordal graphs and 251,085 copy instances, plus an
  independent formal reproduction, failed to falsify it. That is the strongest claim the
  evidence supports.
- It is **not** human peer review.
- It does **not** prove global novelty. The prior Gate K conclusion was an evidence-bounded
  negative search result and remains exactly that; no institutional bibliographic database,
  citation-graph traversal or non-English search was available in any run.
- It does **not** verify termination of the copy process or the clone-class lift.
- It does **not** re-derive the Lean development in this run; that evidence is reused under
  byte identity.
- Paper II has never been audited by an adversarial challenger.

## 10. Signature

| Item | Value |
|---|---|
| Auditor | Claude Opus 5 (`claude-opus-5`), Anthropic |
| Configuration | primary auditor; no challenger, for this run or the prior Paper II run |
| Audit date | 2026-08-21 |
| Specification | `FINAL_RESIDUAL_AUDIT_REQUEST_SPEC.md`, SHA-256 `2eadd655...b683` |
| Target | `preprint_draft_v1.2` corrected in place, 245 files, 3,940,779 bytes, manifest `4b41f7e2...8c1e` |
| **Verdict** | **`PASS`** -- `EXT-PII-M-001` closed; 0 new blocker/major/minor; `EXT-P2-I-001` preserved as a NOTE |

The previous `PASS_WITH_RESIDUALS` run is not overwritten. It stands against its own hashes
as the record of the state that preceded this correction.
