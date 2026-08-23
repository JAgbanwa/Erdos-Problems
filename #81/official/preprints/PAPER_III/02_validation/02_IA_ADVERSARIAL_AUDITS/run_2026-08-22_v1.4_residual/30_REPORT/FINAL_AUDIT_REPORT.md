# External Residual Adversarial Audit -- Paper III preprint draft v1.4

**Request:** `EXTERNAL_RESIDUAL_AUDIT_REQUEST_v1.4.md`, delivered in
`PAPER_III_v1.4_EXTERNAL_RESIDUAL_AUDIT_INSTRUCTIONS.zip`

**Instructions ZIP SHA-256:**

```
0dd44c49c43bff8cb6d7880b4d2825c83c1a88cf30d2be2111772b5e418854c0
```

**Target:** `preprints/PAPER_III/active/preprint_draft_v1.4/`
**Run:** `run_2026-08-22_v1.4_residual` **Dates:** 2026-08-22/23
**Auditor:** Claude (Anthropic), `claude-opus-5`. **No adversarial challenger.**

---

## 1. Overall verdict

### CONDITIONAL_PASS

Every blocking gate passes. **No mathematical or formal defect was found**, the three MAJOR
findings of the v1.3 baseline are independently confirmed corrected, and the uninterrupted Lean
reproduction the request demands was achieved -- something the author's own package could not
supply, and says so.

The verdict is `CONDITIONAL_PASS` rather than `PASS` for one reason, stated plainly: **this
package has never been audited by an adversarial challenger.** Every finding across four audits
of Paper III comes from a single reasoning context. On Paper I a challenger found four Spanish
duplications this auditor's own diff had missed, which upgraded a MINOR to a MAJOR and moved
that paper's verdict to FAIL. The request makes overall `PASS` contingent on every blocking gate
passing with no open blocker or major; that condition is met. Independence of review is the one
thing this audit cannot supply about itself.

| Gate | Verdict | Basis |
|---|---|---|
| 1 intake, manifests, provenance | **`PASS`** | 22/22, 6/6, 1/1, 707/707, 751/751; ZIP hash matches the request; archive clean |
| 2 headline claims and regression | **`PASS`** | Sections 1-10 and 12 byte-identical to v1.3; scope clauses intact |
| 3 EN/ES and MD/TeX/PDF chains | **`PASS`** | block-aligned comparison; one MINOR remark divergence |
| 4 rendered PDFs | **`PASS`** | 46 and 47 pages, no clipping, no lost glyph, 66/66 tags |
| 5 independent Lean reproduction | **`PASS`** | **uninterrupted**, 8,455 jobs, exit 0, from an absent project build |
| 6 aggregate root and axiom boundary | **`PASS`** | root closure 429 modules, reaches both canonical roots; axiom modules unreachable |
| 7 canonical bridges and AX1/AX2 semantics | **`PASS`** | validated against an auditor-built bridge, AX1 as an `iff` |
| 8 citations, openness, novelty | **`PASS`** | six load-bearing references verified at source; no collision found |
| 9 regression of the v1.3 findings | **`PASS`** | 3 MAJOR and 4 MINOR all dispositioned; 5 closed, 1 withdrawn, 1 recurring as a NOTE |

Findings: **0 blocking, 0 critical, 0 major, 2 minor, 1 note.**

---

## 2. The v1.3 findings, regressed

This is the heart of the audit, so it comes first. Each disposition rests on work done in this
run, not on the author's changelog.

### `EXT-V13-001` (was MAJOR) -- **CLOSED, with hard proof**

v1.3's defect: `PaperIII.lean`, the library root and `defaultTargets`, imported neither
`Theorem_1_1_Final` nor `PublicAPI`. `lake build PaperIII` therefore reported
`Build completed successfully (8203 jobs)` **without compiling Theorem 1.1**, and seven of the
eight axiom queries then failed for want of that object.

v1.4 adds both imports (lines 46-47). The auditor did not accept the lines at face value; it
built:

```
lake build PaperIII
Build completed successfully (8455 jobs).
real 70m10.765s
EXIT_BUILD=0
errors: 0
```

and then checked what the build produced:

| Object | Present after `lake build PaperIII` |
|---|---|
| `PaperIII/Theorem_1_1_Final.olean` | **yes** |
| `PaperIII/PublicAPI.olean` | **yes** |
| `PaperIII/CanonicalTrianglePacking.olean` | **yes** |
| total project `.olean` created | **429** |

Three independent measurements agree, which is why this is closed rather than merely reported:

- the job count is **8,455**, matching the author's declared `public_root_jobs` exactly, and
  **252 more than v1.3's 8,203**;
- the aggregate root's transitive import closure is **429 modules**, up from **177** in v1.3,
  and it now exceeds both `PublicAPI` (402) and `Theorem_1_1_Final` (393) -- which is what an
  aggregate root should look like;
- the closure count **equals** the number of `.olean` files built, 429 = 429.

The build topology inverted, as it should: in v1.3 the aggregate root was smaller than the query
roots (8,203 against 8,444) because the canonical path had to be requested separately; in v1.4
the public root subsumes them and the query-root build takes **8m37s** against v1.3's **105
minutes**, adding only 42 objects.

The root's docstring was rewritten to state the reason, which also closes `EXT-V13-006`: "The
explicit final imports at the end of this file are release gates: they prevent a successful
default build from omitting the paper's headline theorem."

### `EXT-V13-002` (was MAJOR) -- **CLOSED**

v1.3's defect: Spanish Proposition 7.4 dropped the hypothesis `h_i >= max{rho, q_J - r_b}` and
the entire displayed inequality, replacing the conclusion with a pointer to Section 7 where the
formula does not appear.

The auditor read both statements in v1.4. The Spanish now carries the hypothesis in full and the
complete inequality, term for term identical to the English:

```
nu_3(G) >= C(b,2) + C(rho,2) - ((2b-1)A_J - A_2J)/(2 q_J)
           + (1 - theta_R)(q_J - r_b)B_J/q_J
```

with `A_J = sum t_i`, `A_2J = sum t_i^2`, `B_J = sum g_i` defined in both. `A_{2J}` occurrence
counts moved from **4 EN / 2 ES** to **4 / 4**, in Markdown and in TeX alike, and the variant
`A_{2,J}` appears zero times anywhere.

### `EXT-V13-003` (was MAJOR) -- **CLOSED, and the design fixed rather than the field**

v1.3's defect: `FREEZE_METADATA.json` declared `"internal_audit": "NOT_STARTED"` while the
package shipped a completed internal audit with verdict `PASS`.

v1.4 does not merely edit the field; it fixes the category error. The metadata now declares

```
"audit_lifecycle": "AUDIT_RESULTS_ARE_EXTERNAL_TO_THIS_IMMUTABLE_FORMAL_SNAPSHOT"
"external_reproduction": "PENDING"
```

so audit state is explicitly outside the immutable snapshot, and the snapshot's own fields are
freeze-time facts. That is the right resolution: an immutable archive cannot truthfully carry a
mutable audit status.

`BUILD_INPUT_METADATA.json` still reads `"internal_audit": "PENDING_FOR_VERSION_1.4"` while a
v1.4 internal audit with verdict `PASS` exists in the target. Under the declared lifecycle
policy that is a freeze-time statement, not a live claim, so it is recorded as **`EXT-V14-N01`
(NOTE)** rather than a recurrence of the MAJOR. The policy declaration is what makes the
freeze-time reading defensible; without it this would be the same finding again.

### `EXT-V13-004` (was MINOR) -- **CLOSED by disclosure**

v1.3's defect: the recorded build was an incremental replay presented through a job count that
looked like a clean build.

v1.4 discloses the limitation in three places, voluntarily and in the auditor's own terms.
`FREEZE_METADATA.json` carries `"uninterrupted": false` and
`"classification": "PASS_CLEAN_ORIGIN_RESUMED"`. Section 13 of the manuscript states: "The
desktop application restarted during the first public-root process; the unchanged project was
then resumed incrementally." Section 11's Table 2 records the public-root build as 8,455 jobs
with the note that it imports the final theorem and public API.

**This audit supplies what that disclosure says is missing.** The 70-minute public-root build
above ran to completion without interruption, from a project build directory proved absent, so
the uninterrupted reproduction the request demands now exists as external evidence.

### `EXT-V13-005` -- **remains WITHDRAWN**

Withdrawn in the v1.3 addendum after retrieving the Cavers survey and finding it has no chordal
or split-graph clique-partition content. Nothing in v1.4 changes that; the withdrawal stands.

### `EXT-V13-006` (was MINOR) -- **CLOSED**

The scaffold docstring is gone, replaced by the release-gate explanation quoted above.

### `EXT-V13-007` (was MINOR) -- **CLOSED**

v1.3's defect: the reproduction protocol's step 8 prescribed a build that did not cover step
9's queries, so following both in order produced seven failures. In v1.4 the sequence works as
written: the public root builds, and all eight queries then run with exit 0. The request's own
mandated command sequence was followed verbatim and completed.

### `EXT-V13-008` (was MINOR) -- **remains CLOSED**

The `3/16` Chen-Erdős-Ordman baseline was confirmed from the Erdős Problems record for #81 in
the v1.3 addendum and re-confirmed in this run's refresh.

---

## 3. Gate 1 -- intake, manifests and provenance: `PASS`

| Chain | Entries | Result |
|---|---|---|
| `04_integrity/CURRENT_TARGET_SHA256.txt` | 22 | **22/22**, LF-only |
| manuscript sidecar | 6 | **6/6**, LF-only |
| freeze-archive sidecar | 1 | **1/1**, LF-only |
| `SOURCE_MANIFEST.sha256` | 707 | **707/707** |
| `PACKAGE_MANIFEST.sha256` | 751 | **751/751** |

Freeze ZIP: `79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104`, **matching the
value the request declares**; CRC of all 751 members intact. Archive hygiene, every category
zero: path traversal, absolute paths, backslash names, symlink or reparse entries, compiled
artifacts, `.lake` directories, duplicate entries. v1.4 also carries no local build workspace,
unlike v1.3.

Auditor's own manifest of the received target: **1,194 files, 49,760,012 bytes**, at
`00_CONTROL/TARGET_SHA256.txt`.

One provenance claim was tested because it concerns this auditor's own work.
`BUILD_INPUT_METADATA.json` declares `external_audit_report_sha256`
`4b0c6d895155974e7fface2b773d64b8ae0bee796f9da405981a3c79dcdae2c8` for the v1.3 report. That is
**exactly** the SHA-256 of the v1.3 report as preserved inside the v1.4 target: the report is
carried byte-identical, and the claim is true.

Twenty-three stale-version strings occur in the tree; all are in baseline, regression or
preserved prior-run documents that legitimately reference earlier versions, including this
auditor's own v1.3 run directory. The publication artifacts carry none.

---

## 4. Gates 2 and 9 -- claims and general regression: `PASS`

The mathematics did not change. Section by section against v1.3:

| Sections | Text | Displayed-formula sequence |
|---|---|---|
| 1-10, 12 | **byte-identical** | identical |
| 11, 13 | changed | **identical formula sets** |

Sections 11 and 13 are the formalization-status and release-record sections, which is exactly
where the corrections belong: the new ZIP hash, the split public-root/query-root build sequence,
the interruption disclosure, and Table 2's updated `PaperIII` row.

Headline claims re-parsed from v1.4's own text: Theorem 1.1 and Corollary 1.2 assert
`exists C` with `|E(G)| - 2 nu3(G) <= n^2/6 + C n` and `cp(G) <= n^2/6 + C n` for split graphs.
The constant is existential. The sharp quadratic coefficient `1/6` is claimed and the least
uniform linear coefficient is explicitly left undetermined; the general chordal problem is
declared open three times in each language. **Zero** occurrences, either language, of wording
claiming to resolve the split case or Erdős #81.

---

## 5. Gate 3 -- EN/ES and MD/TeX/PDF: `PASS`, one MINOR

Counting totals cannot catch content lost in one place and duplicated in another, so the two
manuscripts were aligned **block by block** on their heading structure -- 144 blocks each,
identical level sequence -- and compared inside each block for display formulas, inline
formulas, table rows, citations, Lean identifiers, equation tags and paragraph counts.

**Zero duplicated paragraphs** in either language. Equation-tag order identical, 66/66.
MD -> TeX -> PDF: 66/66 tags, 20/20 theorem numbers, 17/17 references, 42/42 formal identifiers
present in both TeX files and both PDF texts. `[3,8]` and `[11,17]` symmetric.

Four blocks differed on inline-formula counts by one or two; each was read and each is phrasing,
not lost content -- including block 69, a Proof, where both languages carry the same reasoning
and the same values `2 <= 3/2 + 3C` and `C >= 1/6`.

**`EXT-V14-M01` (MINOR).** In Section 2.4 the English reads "Sections 5--7 **and Proposition
10.5** use no asymptotic input, though they use standard facts such as the edge coloring of
complete graphs", while the Spanish rephrases as "las Secciones 5–7 son efectivas y no dependen
de una hipótesis externa de coloreo", dropping the Proposition 10.5 mention. Both languages do
state Proposition 10.5's independence from Theorems 2.1 and 2.3 in Section 11.3, so no
information is unavailable to a Spanish reader. This is a divergence in a remark, not in a
statement, hypothesis or formula. Suggested correction: align the two sentences.

---

## 6. Gate 4 -- rendered PDFs: `PASS`

| | EN | ES |
|---|---|---|
| pages | 46 | 47 |
| right-margin overflow | **none** | **none** |
| bottom-margin overflow | **none** | **none** |
| producer | LuaTeX-1.24.0 | LuaTeX-1.24.0 |
| ink range | 0.32% - 9.40% | 1.43% - 9.01% |

Every page of both documents was rendered and inspected. The English page 46 was flagged by the
auditor's low-ink threshold and read: it is the closing bibliography page carrying reference
[17] and the folio, not a blank page. The Spanish, being longer, fills it.

---

## 7. Gate 5 -- independent Lean reproduction: `PASS`

Warm-dependency clean room, per the request's own procedure.

| Requirement | Evidence |
|---|---|
| fresh extraction, no project `.lake/build` | ZIP hash verified **before** extraction; `.lake/build` absent; **0** project `.olean`/`.ilean` |
| origin of reused dependencies recorded | `C:\erdos_audit\PIII\.lake\packages`, the auditor's own checkout from the v1.2 audit |
| nine dependency `HEAD` revisions verified, clean `git status` | **9/9 exact, 9/9 clean** |
| Mathlib commit verified before use | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` |
| no author-built Paper III objects reused | 0 present before the build; **429 created by this run** |
| complete project-root build | `Build completed successfully (8455 jobs)`, exit 0, **70m10s, uninterrupted** |
| query roots | `Build completed successfully (8444 jobs)`, exit 0, 8m38s |
| all eight axiom files | **8/8 exit 0** |

Configuration files byte-identical to the freeze; Lean 4.28.0 (`7e01a1bf…a79b`) and Lake
5.0.0-src+7e01a1b recorded. Zero errors across both builds; output is linter advice only.

**One deviation, disclosed.** `lake exe cache get` hung on network -- 3.7 seconds of CPU across
roughly 40 minutes of wall clock, no output, no download process. The dependency cache was
already complete and pin-verified: 7,655 Mathlib `.olean` files totalling 1.76 GB with
`Mathlib.olean` present, plus batteries 175, aesop 135, Qq 14, proofwidgets 12, importGraph 10,
LeanSearchClient 4, plausible 11. In the v1.3 audit the same command reported "No files to
download / Already decompressed 8010 file(s)", so it had no work to do. The request asks for it
"when available"; it was terminated, the state that made it unnecessary was recorded, and the
build proceeded. Full note in `20_EVIDENCE/G5_LEAN/results/01_cache_get.log`.

### Axiom surfaces

**42 surfaces across the eight files, 0 `sorryAx`, 0 non-standard footprints, 0 project
axioms.**

| File | Surfaces |
|---|---|
| `FreezeAxioms` | 12 |
| `FreezeAxiomsAuditClosure` | 13 |
| `FreezeAxiomsCanonical` | 7 |
| `FreezeAxiomsAX1Closure` | 4 |
| `FreezeAxiomsByproducts` | 2 |
| `FreezeAxiomsObstructions` | 2 |
| `FreezeAxiomsAX1` | 1 |
| `FreezeAxiomsAX2` | 1 |

`PaperIII.Theorem_1_1` shows no project-local axiom and no `sorryAx`, as the request requires.

---

## 8. Gate 6 -- aggregate root and axiom boundary: `PASS`

The aggregate root reaches both canonical roots: `PaperIII`'s transitive closure is **429
modules** and contains `Theorem_1_1_Final` and `PublicAPI`, confirmed both by the import graph
and by the objects the build produced.

The archived project-axiom modules are excluded, verified by transitive import graph over all
**704** project modules rather than by grep:

| Module | Direct importers | Reachable from any canonical root |
|---|---|---|
| `Ax2.PartB.Axioms` (`bklo_kthree_transfer`) | **none** | **no** |
| `Ax2.PartA.Wlog` (`dross_fractional_flow_noHDT`) | **none** | **no** |

`Theorem_1_1_Final` does import `Ax2.PartB.BKLO.Bridge` and reaches thirteen other `Ax2`
modules; none of them is axiom-bearing. Neither axiom appears in any of the 42 footprints.

---

## 9. Gate 7 -- canonical bridges and AX1/AX2 semantics: `PASS`

Settled against an auditor-constructed bridge, not by compiling the target's lemmas.
`AuditorE3.lean` restates the manuscript forms from the manuscript text, proves them with the
auditor's own arguments, and only then asserts the target's statements and discharges them with
those proofs. Exit 0; every declaration `[propext, Classical.choice, Quot.sound]`.

| Auditor theorem | What it settles |
|---|---|
| `auditor_fracPacking_iff` | the two fractional-packing predicates define the same feasible set; the Nibble side's extra capacities on **non-edges** are vacuous, because a 3-clique containing both ends of a pair forces adjacency |
| `auditor_nu3Star_eq` | the two fractional optima are equal |
| `auditor_tau3Star_eq_nu3Star` | cover-side and packing-side optima coincide at PaperIII's own names |
| `auditor_AX1_iff_manuscript` | **an `iff`, both directions**: `AX1Assumption` is equivalent to manuscript Theorem 2.1 at `H = K3`, packing side |
| `auditor_manuscriptAX1_holds` | that form holds unconditionally in the development |
| `auditor_AX2_implies_manuscript` | AX2 gives Theorem 2.3, with `0.9` checked against `9/10` and `3 divides card` against `card % 3 = 0` |
| `auditor_decomposition_unfolds` | `HasTriangleDecomposition` is an exact edge decomposition into 3-cliques, by `Iff.rfl` |

The `iff` is what rules out a one-directional weakening. No inequality direction or feasibility
condition is lost at any interface, and `nu3` and `nu3Star` refer to the intended objects
throughout. The target's own four canonical lemmas -- `isFracPacking_iff_yuster`,
`nu3Star_eq_yuster`, `tau3Star_eq_nu3Star`, `AX1Assumption_iff_packing_form` -- were asserted
verbatim and discharged by the auditor's constructions, so agreement is a theorem rather than a
comparison of prose.

---

## 10. E2 -- independent mathematical rederivation: `PASS`

The request states that carry-forward is not sufficient, so the independent work is described
here rather than cited.

**What is inherited, and why that is legitimate:** nothing. The mathematics was re-derived. What
*is* established is that v1.4's Sections 4-9 are **byte-identical** to v1.3's, with identical
displayed-formula sequences, so the derivation applies to the bytes actually delivered here.
That identity is itself a verified result, not an assumption.

**23 items rederived from the manuscript's definitions in exact symbolic algebra: 22 `PASS`, 1
scope `NOTE`, zero failures.** Plus 15 items on Section 9: 14 `PASS`, 1 partial.

`K-CORRIDOR`, Lemmas 5.1 to 7.1: the averaging identity holds because the `r_p` factors
partition `E(K_p)`; (5.2) is exact, with the step `((2p-1)M - S2)/q - M = ((s-1)M - S2)/q`
turning on `2p - 1 - q = s - 1`; (5.3) is exact, the parabola peaking at `y = (s-1)/2` so that
`-s^2/6 + (s-1)^2/4 = (s^2-6s+3)/12` identically; Lemma 5.2's mixture identity is exact, with
the factor 2 forced by `Phi = |E| - 2 nu3`; Lemma 6.1's count reproduces
`C(a,2) + a(p-|S_j|-a)` identically and the hypothesis `2p - 3m - 1 >= 0` is what keeps the
extracted factor nonnegative; (6.1) is a bijection of counted triples. **Lemma 7.1's full (7.6)
assembly closes with difference identically zero**, carried by two cancellations:
`(2b-1)A_R/q = ((s-2rho-1)A_R)/q + A_R` kills the `-A_R` from `sum d_i`, and `1 - u/q = r_b/q`
turns `(1 - u/q)/r_b` into exactly `1/q`.

`K-SPARSE`, Section 8: the Dirac hypothesis holds with its rounding carried explicitly; the
parity construction works at **both endpoints** precisely because `|O|` is even by handshaking;
Turán's threshold is right, since a `K_5`-free graph has at most `3p^2/8` edges and
`delta > 3p/4` forces more; the mod-3 correction covers all three residues exactly, since
`|E(C_4)| = 4 = 1` and `|E(C_5)| = 5 = 2` mod 3, and removing a cycle changes each degree by 0
or 2. The `0.91p` threshold: loss is at most `2 + 2 = 4`, so `delta(H) >= 0.95p - 5 >= 0.91p`
once `p >= 125`, and **`|V(H)| = p`** -- the correction removes edges only, never a vertex, so
the threshold is measured on the original clique set. (8.10)-(8.11) are exact:
`(1/3)C(p,2) + pq/3 = (p+q)^2/6 - (p+q^2)/6` identically.

`K-GLOBAL`: `Phi(G) <= Phi(G-v) + d(v)` because `|E(G)| = |E(G-v)| + d(v)` and
`nu3(G) >= nu3(G-v)`; minimality then gives `d(v) > (2n-1)/6 + k`, which is (9.2) exactly.
`n_k -> infinity` because `Phi <= C(n,2) < n^2/6 + kn` once `k > n/2`. The `q = 0` case is
covered by Section 8, which matters because (9.2) needs `I` nonempty.

`K-EPS`: the margin constant is explicit. On `eps <= alpha <= 2 - eps`, `mu` is the pointwise
minimum of `alpha^2/12` and `(2-alpha)^2/48`, minimized at an endpoint, so `c_eps = eps^2/48`.
Theorem 4.2 gives margin at least `eps^2 p^2/48 - p/4`; Theorem 2.1 costs `o(n^2)`, and
`alpha < 2` forces `n < 3p`, so that loss is `o(p^2)`. Taking `c = eps^2/96` leaves
`eps^2 p^2/96 - p/4`, positive once `p > 24/eps^2`.

`K-COVER`, already closed in the v1.3 report and re-run here: the split is exhaustive and
non-overlapping at four levels, including the subsequence trichotomy by Bolzano-Weierstrass on
`[0,2]`.

**Scope `NOTE`.** This is the manuscript's ledger. The manuscript depends on Theorem 2.1 as a
cited external theorem, verified at source in gate 8. The Lean development separately proves an
AX1 statement through an internal nibble chain whose own parameter ledger is a different object
and was not audited; the manuscript-level claim does not rest on it.

**One residual, stated plainly.** Theorem 2.2, the list-edge-colouring input to Lemma 7.1, is
proved self-contained in Appendix D, and **Appendix D was not audited**. This leaves nothing
unproven: the statement is the maximum-degree case of Galvin's theorem, published and classical,
and the auditor verified that the hypothesis the manuscript needs (`|L(e)| >= Delta(B)`) is
exactly Galvin's. What is unverified is only the claim of self-containedness.

---

## 11. Gate 8 -- citations, openness and novelty: `PASS`

Citation integrity: 17 references; every bracketed citation resolves to a listed reference and
every listed reference is cited.

**The six load-bearing references, each verified at source and against the claim it supports:**

| Reference | Verified |
|---|---|
| [3] Erdős-Ordman-Zalcstein | *CPC* **2**(4), Dec 1993, 409-415, abstract verbatim: `n^2/6` is a **lower** bound from a construction "which is also a threshold graph and a split graph", the proved chordal **upper** bound is `(1-c)n^2/4`, and sufficiency is **open** |
| [5] Chen-Erdős-Ordman | Beijing 1993, 21-30, World Scientific 1994; `3/16 n^2 + O(n)` for split graphs, per the Erdős Problems record for #81 |
| [11] Haxell-Rödl | *Combinatorica* **21** (2001), 13-38, from Haxell's own CV |
| [17] Yuster | *Random Structures & Algorithms* **26** (2005), 110-118; main result is exactly that the fractional-integral packing difference is `o(|V(G)|^2)` |
| [2] Barber-Kühn-Lo-Osthus | *Adv. Math.* **288** (2016), 337-385; with Dross implies every large `K_3`-divisible graph of min degree `>= 9n/10 + o(n)` has a `K_3`-decomposition -- literally Theorem 2.3 |
| [7] Dross | confirmed through that consequence statement |

**The precise claim tested, and the result: no collision found.** No published integral upper
bound for split graphs at or below `n^2/6 + O(n)` exists. The state of the art is a **gap**:
lower bound `n^2/6 + O(n)`, best known split-graph upper bound `3/16 n^2 + O(n)`, problem open.
Paper III closes exactly that gap for split graphs.

The four distinctions the request asks for, each tested separately:

| Distinguish from | Result |
|---|---|
| **fractional** results | Papers I and II bound `\|E\| - 2 nu3*`; EOZ, CEO and Theorem 1.1 bound `\|E\| - 2 nu3` and `cp`. Different objects; Paper III's claim is the integral one |
| **`o(n^2)`** statements | Haxell-Rödl and Yuster bound the fractional-integral **gap**. An input, not a partition bound, and no quadratic coefficient follows from it alone |
| **general chordal** | open; published upper bound `(1-c)n^2/4`. Paper III claims only the split case and says so repeatedly |
| **optimal linear coefficient** | undetermined; Paper III asserts sharpness of the **quadratic** coefficient only |

Most recent adjacent work, retrieved and read: **arXiv:2608.11536, Bo Ning, 30 July 2026**, on
`f(n)`, the maximum difference between clique partition and covering numbers, proving
`floor(n^2/4) - C_1 n^{4/3} <= f(n) <= floor(n^2/4) - C_2 n^{4/3}`. It cites EOZ only as prior
work. **No collision.** The Cavers survey was retrieved in full and contains zero occurrences of
"chordal", `3/16`, `n^2/6` or "Zalcstein"; it does not bear on the claim.

**Limitations, stated.** `erdosproblems.com/81` returns HTTP 403 to direct fetching, so its
status text was read through the search index. The 1994 World Scientific volume holding [5] is
not openly accessible, so the `3/16` coefficient rests on the Erdős Problems record rather than
the volume. No subscription index (MathSciNet, zbMATH) was reachable from this environment.

---

## 12. Findings

| ID | Severity | Artifact | Substance | Required correction |
|---|---|---|---|---|
| `EXT-V14-M01` | MINOR | Section 2.4, EN and ES manuscripts | the English names Proposition 10.5 as asymptotic-input-free; the Spanish rephrasing drops that mention. Both languages state it in Section 11.3, so no information is lost | align the two sentences |
| `EXT-V14-M02` | MINOR | Appendix D | the self-containedness of the list-edge-colouring proof was not audited; the statement is classical (Galvin, maximum-degree case) and its hypothesis matches what Lemma 7.1 needs | none required for correctness; a reviewer should check Appendix D before release if self-containedness is to be claimed |
| `EXT-V14-N01` | NOTE | `BUILD_INPUT_METADATA.json` | reads `"internal_audit": "PENDING_FOR_VERSION_1.4"` while a v1.4 internal audit with verdict `PASS` exists in the target. Defensible as a freeze-time statement under the declared `audit_lifecycle` policy | optionally note in the archive README that its status fields are freeze-time facts |

**No mathematical or formal defect at any severity.**

### Auditor tool artifacts, recorded rather than filed as findings

Five of them in this audit, each resolved by going to the raw bytes. Naive substring matching
against generated LaTeX and extracted PDF text produces false positives, and the pattern is
worth stating because three of the five looked at first like real defects:

1. 16,368 "replacement characters" in each PDF text -- poppler emits **CESU-8** for
   astral-plane characters; decoded correctly, zero remain and the recovered glyphs are the
   intended mathematical italics.
2. A missing table row for `PaperIII.CanonicalTrianglePackingGate` -- pandoc inserts
   `\allowbreak{}` inside long verbatim tokens, so the identifier is present in the TeX and
   three times in each PDF, exactly as in the Markdown.
3. Seventeen "missing" formal identifiers -- present with escaped underscores.
4. A "blank" page 46 in the English PDF -- the closing bibliography page with reference [17].
5. A phantom module named `tree` in an import closure -- the phrase "import tree stays lean"
   inside a docstring; the parser now honours nested comments.

---

## 13. What this audit does and does not establish

**Establishes.** The delivered bytes are exactly what the package declares. Paper III rebuilds
**cleanly and uninterrupted** from its frozen sources against the exact pinned dependency
revisions -- not a rebuild of Mathlib from source. `lake build PaperIII` alone now compiles the
headline theorem, which is the defect that made v1.3 fail. All 42 named surfaces have
foundational footprints with no `sorryAx` and no project axiom, and the two archived axioms are
unreachable from every canonical root. The AX1 and AX2 interfaces say what the manuscript says,
proved against the auditor's own construction with AX1 settled in both directions. Sections 4
through 9 are rederived from definitions with every identity exact, and are byte-identical to
the version in which they were first rederived. Both PDFs render without clipping or a lost
glyph. No published result gives an integral split-graph bound at or below `n^2/6 + O(n)`.

**Does not establish.** The **truth** of Theorem 1.1 -- no audit establishes that, and failed
falsification is not proof. Appendix D's self-containedness. The Lean nibble chain's internal
parameter ledger. Novelty beyond the corpus actually searched. **Human peer review.** And,
decisively for the verdict, **adversarial challenge**: four audits of this paper have all come
from one reasoning context.

## 14. Signature

Claude (Anthropic), `claude-opus-5`, external residual adversarial auditor under
`EXTERNAL_RESIDUAL_AUDIT_REQUEST_v1.4.md`. 2026-08-22/23.

**Overall verdict: `CONDITIONAL_PASS`** -- every blocking gate passes, 0 blocking, 0 critical, 0
major, 2 minor, 1 note; no mathematical or formal defect; the three v1.3 MAJOR findings closed
with independent evidence. The single condition is an adversarial challenger review, which this
auditor cannot supply about its own work.
