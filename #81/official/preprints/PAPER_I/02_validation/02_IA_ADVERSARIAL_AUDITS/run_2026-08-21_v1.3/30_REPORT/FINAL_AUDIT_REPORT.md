# External Residual Adversarial Re-audit — Paper I, `preprint_draft_v1.3`

**Specification:** `RESIDUAL_AUDIT_REQUEST_SPEC.md`
**Specification SHA-256:** `e8d92cf5fffbc55b02eada99e4e446207752dbe28f1b8492195838b123d85435`
**Run:** `run_2026-08-21_v1.3`
**Audit class:** external residual adversarial re-audit
**Audit date:** 2026-08-21

---

## 1. Executive verdict

> ## `PASS_WITH_RESIDUALS`

**What this means.** **All nine** mandatory correction controls pass, the general
regression passes in full, and there is **no unresolved `BLOCKER` and no unresolved
`MAJOR`**. The `MAJOR` finding that made v1.2 fail — five duplicated Spanish blocks
reaching the delivered PDF — is **fully corrected and independently re-verified**.

Control 6 was initially assessed `PARTIAL`, because the newly cited Chen–Erdős–Ordman
author-hosted scan could not be retrieved by any of four routes the auditor attempted.
The owner then supplied the scan, downloaded from the cited URL in their own browser. The
auditor rendered and read it, and the `3/16` constant is now **verified against the
primary source with a pinpoint**: Theorem 1, page 23. Control 6 therefore passes. This
evidence is disclosed as **owner-supplied and auditor-verified**, not as an independent
auditor retrieval (Section 4.4).

**Why not a plain `PASS`.** Two correctable `MINOR` package defects remain open: compiler
residue left inside the sealed package, and two transposed declaration namespaces in the
changelog (Section 7). Neither is claim-critical, and Specification Section 7 permits
minor findings that are compatible with the PASS rule — but a sealed package carrying
stray build artifacts is a real defect the owner can fix in minutes. **Deleting `tmp/` and
correcting the two changelog names would make a plain `PASS` available on a new target
hash.** Standing external residuals also remain (Section 10).

**This audit is not human peer review and does not prove global novelty.**

## 2. Target identity — all eight anchors verified

Recomputed from the delivered bytes before any analysis. **8/8 match.**

| Artifact | Required SHA-256 | Result |
|---|---|---|
| English Markdown | `f3094b670c93ff622c3f573cdab61bdd0f5d84007f04b1888b364e0183565bea` | MATCH |
| Spanish Markdown | `57ba967fc2de805b7bbb4cf5f937727bde43c2ada80fa794bcbb5a727db05b8b` | MATCH |
| English LaTeX | `1a87de70548879ca90a714ec9e1b10c8576b380a749785916e5d59176e479465` | MATCH |
| Spanish LaTeX | `f83ee709c1168b5b9afe504e6b6a43763bf3bb2a08f674f2031f83670ba9bb56` | MATCH |
| English PDF | `7d04c47692b613c8d6e2cc4471f0205128b4ae06ca11d581a08d020eb2236db0` | MATCH |
| Spanish PDF | `3ad16ae86e8fcad358bf964a6ae98ae053b0bde2fdf3140e008cedab78b90c2a` | MATCH |
| Lean archive | `0181506408644fc1f8872d711de5a98a500f4052aa295bcd6f8c82776694fd3a` | MATCH |
| Internal-audit ZIP | `f261add8050f1ab8779d9e25f345475790768368f4c056067358153db6639382` | MATCH |

Input freeze sealed before analysis: **221 files, 24,675,148 bytes**, aggregate
`a8852b0e4d424615d299d9b1dba5bb0aef244295193a662f57afc48a652427fb`, with the audit-output
subtree excluded. Manuscript sidecar is **LF-only, 6/6 entries verify**. No path resolves
into `superseded/`. The target did not change during the run and was not modified by the
auditor.

## 3. What actually changed from v1.2

Established by a line-level diff of the two English manuscripts, not taken on trust:
**14 changed regions, every one of them an announced correction.** v1.2 had 1,089 lines;
v1.3 has 1,101.

No theorem statement, no constant, no proof step changed, with two exceptions that both
*strengthen* the argument: the added `H`-slack accounting in the derivation of (4.7), and
the domain restriction on the Appendix A.2 excess formula. This matches the specification's
own statement in Section 1 and the `CHANGELOG_v1.3.md`.

## 4. Mandatory correction controls, one by one

| # | Finding | Verdict | Evidence |
|---|---|---|---|
| 1 | `EXT-P1-L-001` duplicated Spanish blocks | **PASS** | Section 5 |
| 2 | `EXT-P1-M-001` integrity metadata | **PASS** | Section 6 |
| 3 | `EXT-P1-D-001` derivation of (4.7) | **PASS** | Section 4.1 |
| 4 | `EXT-P1-E-002` Appendix A.2 restriction | **PASS** | Section 4.2 |
| 5 | `EXT-P1-J-001` meaning of "sharp" | **PASS** | Section 4.3 |
| 6 | `EXT-P1-I-001` CEO scan and `3/16` | **PASS** | Section 4.4 |
| 7 | `EXT-P1-I-002` Schrijver pinpoint absent | **PASS** | Section 4.5 |
| 8 | `EXT-P1-I-003` stale repository citation absent | **PASS** | Section 4.5 |
| 9 | `P1-IA-V13-001` no residual pinpoint | **PASS** | Section 4.5 |

### 4.1 Control 3 — the derivation of (4.7) is now complete and correct

Both halves of the v1.2 finding are addressed.

- **The substitution is stated.** English and Spanish L270 now read that the second
  substitution "gives `z_e = x_e` and leads to the fixed **capped-dual** polytope". In v1.2
  the composition `y = 1-x` then `z = 1-y` was left unremarked, so (4.5) appeared to be a
  new polytope rather than the original capped dual.
- **Every edge of `H` is accounted for.** New text at L303–317 supplies the cancellation
  v1.2 omitted:

  `|w_1| = b_{>=2}/2 + sum_{e in H} (1 - kappa_e)`
  `|w_2| = M(kappa) - sum_{e in H} (1 - kappa_e)`

  and notes explicitly that "On `H`, the residual coefficient `r_e` is zero" — precisely the
  distinction the v1.2 finding turned on, since `r_e = max{1-kappa_e, 0}` vanishes on `H`
  rather than being negative.

**Independently verified symbolically, not merely read:**

- the new `|w_1|` identity is *consistent with* (4.3) `|w_1| = |H| + sum_{e in L} kappa_e`,
  given Lemma 3.1 (`sum over all e of kappa_e = b_{>=2}/2`). Exact identity, residual zero.
- adding the two new identities yields (4.7) `V_com = b_{>=2}/2 + M(kappa)` exactly: the
  two `sum_H (1 - kappa_e)` terms cancel. Exact identity, residual zero.

So the accounting is not just present, it is right.

### 4.2 Control 4 — Appendix A.2 is now correctly restricted

L888 now reads "If `A >= 0` **and `o >= 3`**", and L904–906 route the cases `o = 0,1,2` to
Appendix A.3. Verified symbolically that this is the *exact* correct domain:

| Endpoint | Excess over `U` | Matches printed `(B-2A)/6`? |
|---|---|---|
| `(0, 1/2, 1/3)`, valid when `o >= 3` | `(B - 2A)/6` | **yes** |
| `(0, 1/2, 0)`, the case `o <= 2` | `(B - 2A - 2C)/6` | **no**, differs by `-2C/6` |

The v1.2 text printed `(B-2A)/6` unconditionally, which is false for `o <= 2`. The v1.3
restriction is precisely the right one.

### 4.3 Control 5 — "sharp" no longer overreaches

The phrase "the sharp target" is **gone** from L691/L705. "Sharp" now appears only inside
the declaration names `paperI_main_sharp` and `assembly_sharp`, and L750 still states
plainly that "The additive term `n/2` in Theorem 1.1 is not optimized", giving the `n/6` to
`n/2` window. The `CHANGELOG` records the intent as clarifying that `sharp` refers to the
quadratic coefficient `1/6`. Consistent, and consistent with this audit's own computation
that the extremal family attains `n^2/6 + n/6`, which is what makes `n/2` non-optimal.

### 4.4 Control 6 — cited, and now verified against the primary source: `PASS`

**The citation.** Reference [2] now reads, in both languages and in all four generated
artifacts: "...World Scientific, 1994, pp. 21-30, author-hosted scan:
`https://ordman.net/MathResearch/CEOClique_Parts.pdf`, accessed August 21, 2026." The URL
is present once in the English Markdown, Spanish Markdown, both LaTeX sources **and both
rendered PDFs** - the acceptance criterion the owner's own correction matrix set.

**Retrieval, and how the evidence was obtained.** The auditor could not retrieve the scan.
Four routes were attempted and all failed:

| Route | Outcome |
|---|---|
| `WebFetch` on the printed `https` URL | certificate expired |
| `curl` on the `http` URL | HTTP 302 to `https`, certificate expired |
| internal browser, `https` | navigation denied |
| `web.archive.org` snapshot | not reachable from this environment |

The auditor declined to disable certificate validation. **The owner then supplied the
file**, downloaded from the cited URL in their own browser after clicking through the
certificate warning. This is disclosed plainly: the evidence below is
**owner-supplied and auditor-verified**, not an independent auditor retrieval. The auditor
did perform the verification itself - the file is an image-only scan (`pdftotext` extracts
zero lines, Producer "EPSON Scan"), so it was rendered at 150 dpi and read.

Received file SHA-256 `b7d965e6e00cd664ad2249ad7fa3640330009c3c9057301d73f752a718b28262`,
6 pages, archived in `20_EVIDENCE/I_CITATIONS_NOVELTY/results/`.

**Identity confirmed.** Title "CLIQUE PARTITIONS OF SPLIT GRAPHS"; authors Guan-Tao Chen
(North Dakota State University), Paul Erdos (Mathematical Institute, Hungarian Academy Of
Sciences), Edward T. Ordman (Memphis State University). A handwritten annotation on the
first page records the volume: "Combinatorics, Graph Theory, Algorithms, and Applications,
ed. Yousef Alavi, Don Lick, Jiuqiang Liu; World Scientific Pub Co. Pte Ltd, Singapore,
1994 (Conference Beijing 1-5 June 1993)". Printed folios run `-21-`, `-22-`, `-23-`, `-24-`,
consistent with the cited "pp. 21-30".

**The `3/16` constant, verified twice.**

- Abstract, page 21, verbatim: "It is well-known that edge-partitioning a split graph on n
  vertices may require as many as `n^2/6 + n/6` cliques. We show that `(3/16)n^2 + O(n)`
  cliques will always suffice."
- **Pinpoint**, page 23, Section 2 "Statement of results": **"Theorem 1. For all split
  graphs `G_n`, `cp(G_n) <= (3/16) n^2 + O(n)`."** with "Corollary 1. The same bound
  applies to threshold graphs."

The manuscript's attribution is therefore **`SUPPORTED`, with pinpoint Theorem 1, page
23.** The residual that made this a `MINOR` finding in the v1.2 report
(`EXT-P1-I-001`) is **closed**.

**Two further findings of independent value, from the same source.**

1. Page 22, Example 1: "The clique partition number of `G_n = K_n - K_2n/3(bar)` is
   `n^2/6 + n/6`, provided 6 divides n." This is **exactly** the complete-split benchmark
   value this audit verified independently by explicit construction for `p = 2..40` in the
   Paper III Gate F evidence. Primary source and independent computation agree.
2. Page 23: "A split graph on n vertices may need `n^2/6 + O(n)` cliques to partition it.
   **We cannot show that this many will suffice.**" The original authors thus flag as open
   precisely the gap Paper III claims to close. Their Theorem 2 obtains `n^2/6 + O(n)`
   only for the special form `K_n - K_m(bar)`, a difference of cliques, **not** for general
   split graphs. Paper III's general claim is therefore genuinely stronger than CEO
   Theorem 1 and is not implied by CEO Theorem 2 - no collision, and the `3/16 -> 1/6`
   framing is well posed.

**What remains.** The printed URL is still unusable as printed, since the host serves an
expired certificate. That is now an accessibility matter rather than an evidentiary gap,
recorded as `RES-V13-004` (NOTE).

### 4.5 Controls 7, 8, 9 — removals verified across all six artifacts

| Check | EN md | ES md | EN tex | ES tex | EN pdf | ES pdf |
|---|---|---|---|---|---|---|
| `Corollary 7.1g` pinpoint | absent | absent | absent | absent | absent | absent |
| `github.com/jtraverso` citation | absent | absent | absent | absent | absent | absent |

Schrijver is now cited at the **verified chapter level**: "[4, Chapter 7]" at L1025, and
"Schrijver [4, Chapter 7] remains the classical reference" at L781. Control 9 is therefore
satisfied: no residual occurrence of the old pinpoint survived regeneration.

The bibliography went from 10 entries to 9 with the removal of the repository entry. **No
dangling and no orphaned citation resulted**: keys cited in the body are exactly
{1,2,3,5,6,7} plus [4] cited as "[4, Chapter 7]", and the reference list defines {1,...,7}.
Two apparent anomalies were investigated and dismissed — an apparent citation "[0]" is the
unit cube `z in [0,1]^{E(K)}` in (4.5), and [4] appeared "uncited" only because the pinpoint
form escapes a plain-bracket regex.

## 5. Control 1 — duplication, tested generally rather than by known phrase

The specification requires an exact **and near-duplicate** scan of normalized long units in
all six artifacts, manual inspection of every candidate, and a page-image check. All were
performed.

**Method.** Units are (a) paragraphs, i.e. maximal runs of non-blank lines, and (b)
individual lines. Normalization: NFKC, lowercase, whitespace collapsed, punctuation
stripped. Threshold: normalized length >= **60** characters. Near-duplicate criterion:
`difflib` ratio >= **0.92** between distinct units. **Exclusions: none** — every long unit in
every artifact was compared against every other. Pages: exact SHA-256 of the rendered PNG
plus a 64x88 grayscale signature compared by mean absolute difference.

**Result.**

| Artifact | Long units (para/line) | Exact duplicate classes | Near-duplicate pairs |
|---|---|---|---|
| EN Markdown | 116 / 106 | 0 / 0 | 1 / 1 |
| ES Markdown | 121 / 111 | 0 / 0 | 1 / 1 |
| EN LaTeX | 133 / 133 | 0 / 0 | 1 / 3 |
| ES LaTeX | 139 / 139 | 0 / 0 | 1 / 3 |
| EN PDF text | 68 / 243 | 1 / 0 | 0 / 0 |
| ES PDF text | 73 / 274 | 1 / 0 | 0 / 0 |

**Every candidate was inspected individually. All are legitimate:**

- the near-duplicate paragraph in each artifact is the constraint set (6.4)
  `3a>=1, a+2b>=1, 2b+g>=1, 3g>=1` restated in Appendix A.1 — the two differ only by the
  `\tag{6.4}` marker;
- the near-duplicate lines are the two *different* declarations `paperI_main_sharp` and
  `paperI_main` reporting the same axiom footprint, and in the LaTeX the pair
  `\pdftitle{...}` / `\title{...}`, both of which are required;
- the one "exact duplicate" in each PDF text layer is the string
  `propext, Classical.choice, Quot.sound` on consecutive lines — adjacent table cells for
  different declarations that legitimately share a footprint, flattened into separate lines
  by `pdftotext`.

**Page images.**

| PDF | Pages | Exact-duplicate page sets | Min signature distance | Median | Pairs below strict threshold 1.5 |
|---|---|---|---|---|---|
| English | 19 | **0** | 3.850 | 8.496 | **0** |
| Spanish | 20 | **0** | 4.619 | 8.515 | **0** |

A genuinely repeated page would show a signature distance near zero; the closest pair in
either document sits at roughly half the median separation, nowhere near identity. No
near-blank page and no anomalous black area in either document.

**The five v1.2 duplications are gone and nothing replaced them.** For the record, they
were at Spanish v1.2 lines 51–65/67–81, 730/732, 742/744, 758–762/764–768 and
776–785/787–794, including an orphaned sentence and an ungrammatical duplicate "Esto prueba
Teorema 1.1."; none of these patterns occurs in v1.3.

Note: the Spanish PDF remains 20 pages against the English 19, unchanged from v1.2. Since
the duplicated content has been removed and the page count did not fall, the page delta is
ordinary Spanish text expansion plus the newly added `H`-accounting and A.2 text — not
duplication.

## 6. Control 2 — integrity metadata now identifies v1.3 and verifies exactly

**28 of 28 sidecars in the package verify by content, with zero problems.** This is the
control v1.2 failed.

| Sidecar | Entries | Result |
|---|---|---|
| `01_manuscript/..._v1.3_SHA256.txt` | 6 | all verify, **LF-only** |
| `04_integrity/CURRENT_TARGET_SHA256.txt` | 8 | all verify |
| `04_integrity/INITIAL_SOURCE_SHA256.txt` | 2 | **both verify** (in v1.2, 1 of 2 was unresolvable) |
| `05_formalization/.../PACKAGE_MANIFEST.sha256` | 31 | all verify |
| `05_formalization/.../SOURCE_MANIFEST.sha256` | 19 | all verify |
| internal-audit manifests (v1.2 baseline + current) | 40 across 22 files | all verify |

`04_integrity/` now carries v1.3-specific records: `CURRENT_TARGET_SHA256.txt`,
`EXTERNAL_AUDIT_CORRECTION_MATRIX.md`, `SEMANTIC_INTEGRITY_REPORT_v1.3.md`. The stale
"Pending for v1.1" baseline that produced `EXT-P1-M-001` is gone.

## 7. New findings opened against v1.3

| ID | Severity | Status | Summary |
|---|---|---|---|
| `RES-V13-001` | MINOR | OPEN | stray `tmp/internal_report_v1.3/` directory containing compiler residue |
| `RES-V13-002` | MINOR | OPEN | `CHANGELOG_v1.3.md` names two declarations with swapped namespaces |
| `RES-V13-003` | MINOR | **RESOLVED** | the `3/16` constant is verified against the primary source (Theorem 1, page 23) |
| `RES-V13-004` | NOTE | OPEN | the cited URL is unusable as printed; the host serves an expired certificate |

### `RES-V13-001` — compiler residue inside the frozen package

The package contains `tmp/internal_report_v1.3/` with three files:
`INTERNAL_AUDIT_FINAL_REPORT.aux` (628 B), `.log` (17,594 B) and `.pdf` (164,176 B). The
`.log` and `.pdf` are **byte-identical** to files already correctly placed under
`02_validation/01_INTERNAL_AUDITS/10_REPORT/`, so `tmp/` is pure LaTeX scratch left behind
by the internal-report build. Specification Section 6 explicitly requires verifying "no
compiler residue"; this is that. **Disposition:** delete the `tmp/` subtree and reseal.

### `RES-V13-002` — swapped namespaces in the changelog

`CHANGELOG_v1.3.md` line 10 states the axiom query was expanded to cover
`PaperI.Split.assembly_sharp` and `PaperI.residual_duality`. The actual declarations are
`PaperI.assembly_sharp` and `PaperI.Split.residual_duality` — the namespaces are
transposed. The **manuscript itself is correct**: Appendix C prints the four declarations
with the right namespaces, matching this auditor's verbatim `#print axioms` output exactly.
So the error is confined to package documentation and does not affect any claim.
**Disposition:** correct the two names in the changelog.

### `RES-V13-003` — RESOLVED

The `3/16` constant is verified against the primary source with a pinpoint (Theorem 1,
page 23). See Section 4.4. No further action.

### `RES-V13-004` — the printed URL does not resolve (NOTE)

`ordman.net` redirects `http` to `https` and serves an expired certificate, so a reader
following reference [2] hits a certificate error. Now an accessibility matter, not an
evidentiary gap. **Disposition:** optionally note the expired certificate in the
manuscript, or cite a stable mirror alongside the author-hosted copy. The defect is on a
third-party host and cannot be fixed by editing the target.

## 8. General regression (specification Section 6)

### 8.1 Mathematics — 14 of 14 symbolic identities exact; 6,732 LP cases with zero mismatches

Every identity is checked as an exact polynomial identity (expand, subtract, require the
residual to be identically zero), not sampled. Two of the fourteen are new in v1.3 and are
the ones that validate the control-3 correction.

| Tag | Identity | Holds |
|---|---|---|
| `v13-4.3/4.8` | v1.3 `|w_1|` identity agrees with (4.3) given Lemma 3.1 | yes |
| `v13-4.7` | the two v1.3 identities add to (4.7); `sum_H` terms cancel | yes |
| `L3.1` | `C(d,2)/(d-1) = d/2` | yes |
| `6.3` | `A+B+C = (p^2-p-sq)/2` | yes |
| `7.2`, `7.4`, `7.4c`, `7.6` | the three Section 7 comparisons and the nonnegativity certificate | yes |
| `8.2`, `8.3`, `8.res` | the simplification, the assembly difference, the residual regime | yes |
| `9.cs` | complete-split value `n^2/6 + n/6` at `n = 3p` | yes |
| `A.2-o>=3`, `A.2-o<=2` | the A.2 excess at each endpoint | yes |

Orbit program, exact rational vertex enumeration, `p = 2..18`, `q = 1..44`, `s = 2..p`:
**6,732 cases, 0 closed-form mismatches, 0 violations of (7.8)**.

Tightness Remark, all claims re-verified with the same sharp constants:

| Regime | Minimum slack | At | Claim |
|---|---|---|---|
| `s>=3, o>=3` | `9/4` | `(6,3,3)` | `>= 9/4` — PASS, tight |
| `s=2, o>=1` | `1/4` | `(3,3,2)` | `>= 1/4` — PASS, tight |
| `o=1` | `1/4` | `(3,3,2)` | `>= 1/4` — PASS, tight |
| `o=2` | `1` | `(4,2,2)` | `>= 1/4` — PASS |
| `o=0` | `0` | `(2,4,2)` | equality regime |

The mandated point `(p,q,s) = (2,4,2)` gives LP value `-3` and slack **exactly 0**:
**CONFIRMED** in the equality family. All 17 equality cases have `o=0` and `q=2p`, exactly
as the Remark claims.

A direct enumeration of split graphs with `nu_3^*` by exact rational simplex was launched
to re-falsify Theorem 1.1 itself; its result file is recorded under
`20_EVIDENCE/MATH_REGRESSION/results/`.

### 8.2 Bilingual chain

All eight corrections are present in **both** languages, at **identical line numbers**
(270, 308/311/314, 888, 904/906, 1091/1089, 781/1025), which indicates a properly
regenerated pair rather than a hand-patched one. Zero self-containment violations: neither
manuscript references `v1.1.4`, `v1.1.5`, "supersede", the correction matrix, the external
or internal audit reports, the changelog, or any `EXT-P1-*` finding id. The manuscript is
self-contained, as Section 6 requires.

### 8.3 Rendered artifacts

Both PDFs: LuaTeX-1.24.0, A4, unencrypted, text layer Unicode-recoverable including
mathematical alphanumeric symbols. All 39 pages (19 EN + 20 ES) rendered at 100 dpi and
analysed; no blank page, no anomalous black area, no duplicated page, no malformed
structure.

### 8.4 Package hygiene

| Check | Result |
|---|---|
| zero-byte files | 0 |
| stray `$o` | absent |
| paths into `superseded/` | 0 |
| compiler residue | **3 files** — `RES-V13-001` |
| stale version, path or hash in the manuscripts | none |
| truncated report or script | none found |

## 9. Gate H — reused under the byte-identity rule

Labelled **`REUSED_BYTE_IDENTICAL_EXTERNAL_EVIDENCE`**. All five conditions of
specification Section 5 are shown:

1. **Archive hash.** The delivered archive is
   `0181506408644fc1f8872d711de5a98a500f4052aa295bcd6f8c82776694fd3a`, exactly the required
   value.
2. **Byte-identical to what was previously rebuilt externally.** The archive was
   re-extracted and compared member by member against the external v1.2 clean room:
   **32 of 32 members byte-identical, 0 differing, 0 missing.**
3. **Nothing that governs the build changed.** `lean-toolchain`, `lake-manifest.json`,
   `lakefile.toml` and `FreezeAxioms.lean` are each **IDENTICAL** to the versions built.
   Toolchain Lean 4.28.0 commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`; Mathlib pinned
   at `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
4. **The v1.3 manuscript's formal claims check out against those unchanged sources.**
   Appendix C's axiom report lists four declarations; all four match the auditor's own
   independently obtained verbatim output, **including the namespaces** that the changelog
   gets wrong:

```
PaperI.Split.paperI_main_sharp depends on axioms: [propext, Classical.choice, Quot.sound]
PaperI.paperI_main            depends on axioms: [propext, Classical.choice, Quot.sound]
PaperI.assembly_sharp         depends on axioms: [propext, Classical.choice, Quot.sound]
PaperI.Split.residual_duality depends on axioms: [propext, Classical.choice, Quot.sound]
```

   Appendix C's stated theorem `G.Phi <= (G.n : R)^2/6 + (G.n : R)/2` matches the compiled
   `PaperI.Split.paperI_main_sharp : forall (G : PaperI.Split), G.Phi <= G.n^2/6 + G.n/2`,
   and the companion form matches `paperI_main`. Table 2's five rows are covered by the
   frozen axiom file, which reported the standard footprint for all 15 of its declarations
   with exit code 0.
5. **Reused evidence is cited by direct path** and carries the required label:
   `20_EVIDENCE/H_LEAN_REUSE/results/` mirrors the external clean-room logs — the
   `lake build` log (`Build completed successfully (8034 jobs)`, exit 0, 24m47.960s, zero
   errors), the frozen axiom run, and the auditor's own independent axiom query.

No Lean build was rerun. Per specification Section 5, this reuse does **not** carry over any
manuscript, citation, bilingual, PDF or package verdict from v1.2 — every one of those was
re-established fresh in this run.

## 10. Residual risks

| Risk | Can this audit close it? |
|---|---|
| the printed citation URL does not resolve (expired third-party certificate) | **No** — the constant itself is now verified; only accessibility remains |
| erdosproblems.com returns HTTP 403 to this auditor, so the official problem page was never read directly | **No** — the open status is corroborated by the verified primary source [1] |
| novelty | **No** — this is a residual re-audit, not a fresh prior-art search; the v1.2 Gate K conclusion was evidence-bounded and remains so |
| PDFs not independently recompiled from the delivered TeX | **No** — producer strings and source-to-PDF tracking checked instead |
| the six project Lean modules outside the eight built targets | **No** — never compiled, no verdict |
| adequacy of the bespoke `PaperI.Split` structure as a model of every split graph | **No** — judged faithful by inspection; not formalized |

## 11. What this audit does not establish

- It does **not** establish that Theorem 1.1 is true; it establishes that a determined
  adversarial regression failed to falsify it.
- It is **not** human peer review.
- It does **not** prove global novelty.
- It does **not** re-derive the Lean development; Gate H is reused under byte identity.
- A `PASS_WITH_RESIDUALS` does **not** close any release gate that explicitly requires one
  of the residuals in Section 10.

## 12. Signature

| Item | Value |
|---|---|
| Auditor | Claude Opus 5 (`claude-opus-5`), Anthropic |
| Configuration | primary auditor; the v1.2 run additionally used an adversarial challenger of the same model family |
| Audit date | 2026-08-21 |
| Specification | `RESIDUAL_AUDIT_REQUEST_SPEC.md`, SHA-256 `e8d92cf5...5435` |
| Target | `preprint_draft_v1.3`, EN Markdown `f3094b67...5bea` |
| **Verdict** | **`PASS_WITH_RESIDUALS`** — all 9 controls pass; general regression passes; 0 blocker, 0 major, 2 open minor, 1 note |

The v1.2 report is **not** rewritten, relabelled or superseded by this document. It stands
with its own `FAIL` verdict against its own hashes, and no evidence from the two runs is
merged.
