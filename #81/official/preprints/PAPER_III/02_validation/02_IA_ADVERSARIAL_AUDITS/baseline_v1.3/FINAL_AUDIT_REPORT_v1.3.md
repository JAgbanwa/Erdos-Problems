# External Adversarial Audit -- Paper III preprint draft v1.3

**Request:** `EXTERNAL_ADVERSARIAL_AUDIT_REQUEST.md`

**Request SHA-256:**

```
a0569fa455d70ee3e8af8ddb4362c52863de69d830bc76975bb6f9d22d9e12c0
```

**Target:** `preprints/PAPER_III/active/preprint_draft_v1.3/`
**Run:** `run_2026-08-22_v1.3` **Dates:** 2026-08-22
**Auditor:** Claude (Anthropic), `claude-opus-5`. **No adversarial challenger.**

Only v1.3 was evaluated. No verdict, PASS, or conclusion from any earlier run was inherited.

---

## 1. Overall verdict

### FAIL

Three gates fail. E2 and E6, inconclusive in the first pass, were closed to `PASS` by
the addendum `ADDENDUM_E2_E6_REGRESSION_DIAGNOSIS.md` of the same date; that addendum also
delivers the v1.4 conclusion **EXPECTED_PASS_ON_V1.4_IF_CORRECTIONS_VERIFY**. **No mathematical or formal defect was found**, and
that distinction carries the whole weight of this report: the theorem compiles, its axiom
footprint is clean, and every inequality this auditor rederived held exactly. The failures are
in the **build configuration** and in **bilingual fidelity** -- release-readiness defects in a
release candidate.

| Gate | Verdict | Basis |
|---|---|---|
| E0 intake, provenance, sealing | **`PASS`** | every declared hash and manifest verifies; archive structurally clean |
| E1 mathematical claims and scope | **`PASS`** | claims, quantifiers and scope separation all confirmed |
| E2 independent rederivation | **`PASS`** (addendum) | Sections 4-9 rederived exactly; all five kill switches closed |
| E3 formal statement conformance | **`PASS`** | validated against an auditor-constructed bridge, not by compilation |
| E4 Lean reproduction and axioms | **`FAIL`** | the public aggregate root does not import the canonical theorem path |
| E5 bilingual, format, render | **`FAIL`** | EN/ES divergence in the content of a numbered proposition |
| E6 citations, prior art, novelty | **`PASS`** (addendum) | load-bearing references retrieved at source; **no published integral split-graph bound at or below `n^2/6+O(n)`** |
| E7 release-package integrity | **`FAIL`** | freeze metadata contradicts its own package |

Findings: **0 blocking, 0 critical, 3 major, 4 minor** (one earlier minor was
withdrawn after retrieving the source, and one was added).

---

## 2. E0 -- intake, provenance and sealing: `PASS`

Every integrity chain verifies against the bytes received.

| Check | Result |
|---|---|
| `04_integrity/CURRENT_TARGET_SHA256.txt` | **12/12**, LF-only |
| manuscript sidecar | **6/6**, LF-only |
| freeze-archive sidecar | **1/1**, LF-only |
| `SOURCE_MANIFEST.sha256` | **707/707** |
| `PACKAGE_MANIFEST.sha256` | **742/742** |
| freeze ZIP SHA-256 vs the value declared in the request | `2eb0ff20...d300`, **match** |
| CRC of all 743 archive members | **intact** |

Archive hygiene, every category zero: path traversal, absolute paths, backslash names,
symlink/reparse entries, compiled project artifacts (`.olean`, `.ilean`, `.o`, `.c`, ...),
`.lake` directories, duplicate entries.

Auditor's own manifest of the received target: **875 files, 16,502,156 bytes**, recorded at
`00_CONTROL/TARGET_SHA256.txt`. `05_formalization/lean_v1.3_candidate/` is excluded, as the
request directs.

Thirteen stale-version strings appear in the tree; twelve are legitimate provenance or
baseline references, and the two in `FREEZE_REPORT.md` and `CHANGELOG_v1.3.md` are explicit
statements of what v1.3 descends from. The publication artifacts themselves carry **no** stale
label.

---

## 3. E1 -- claims and scope: `PASS`

Theorem 1.1 and Corollary 1.2 assert, with an **existential** absolute constant:

```
exists C, for every split graph G on n vertices:  |E(G)| - 2 nu3(G) <= n^2/6 + C n
exists C, for every split graph G on n vertices:  cp(G)             <= n^2/6 + C n
```

The paper claims exactly what the request says it should, and not more. It states that
Corollary 1.2 "improves the quadratic coefficient from `3/16` to the sharp value `1/6`",
that this matches the lower bound at quadratic order, and -- three times in English and three
times in Spanish -- that the corresponding statement for general chordal graphs **remains
open**. It separates the sharp quadratic coefficient from the "still-undetermined least
uniform linear coefficient", which is the two-sharpness-roles distinction the request asks
about.

**Zero** occurrences, in either language, of wording claiming to resolve or settle the split
case or Erdős Problem #81. The previously recorded overbroad-scope finding is closed.

---

## 4. E2 -- independent rederivation: `INCONCLUSIVE`

### 4.1 What was rederived, exactly

Section 9, the proof of the main theorem, was rederived in exact symbolic algebra from the
manuscript's own displayed inequalities. **14 of 15 items PASS, one PARTIAL, none fails.**

`K-COVER` is closed. The case split is exhaustive and non-overlapping:

- `q >= 2p-1` versus `q < 2p-1` is complementary over the integers, and the second gives
  `alpha = q/p < 2 - 1/p < 2`, so `alpha` lies in `[0,2)`.
- Every sequence `alpha_k` in `[0,2)` has, by Bolzano-Weierstrass on the compact `[0,2]`, a
  convergent subsequence. Interior limit gives the bulk regime with
  `eps = min(L, 2-L)/2 > 0`; limit `0` gives Section 9.2; limit `2` gives Section 9.3. The three are
  mutually exclusive and exhaust the possibilities, which is exactly what a
  contradiction-over-subsequences argument requires.
- Inside Section 9.3, `s = O(sqrt p)` and `s/sqrt p -> infinity` are complementary by construction,
  and `s = Theta(p)` cannot occur since `alpha -> 2` forces `s = o(p)`.
- The dispersion dichotomy `D >= q s^2/12` or `D < q s^2/12` is trichotomy of the reals.

The numbered inequalities, each verified exactly:

| Item | Result |
|---|---|
| (9.4) `p >= 2304` | **forced, not chosen**: the window `6 sqrt p <= s <= p/8` is non-empty exactly when `48 <= sqrt p`, i.e. `p >= 2304` |
| (9.5) `3m <= s-3` | valid: `k >= 1` gives `3m < s - 5/2`, and integrality rounds to `s-3` |
| (9.10) `delta >= 7/8` | both parities; the odd case `(p-s)/p` is binding and attains equality exactly at `s = p/8` |
| (9.11) parabola bound | exact: the maximum over the admissible range is at `x=(s-3)/3` and equals `2s(s-3)/9` identically |
| (9.12) high-dispersion contradiction | exact: `5*36/288 = 5/8` and `1/2 - 5/8 = -1/8`, so the sign flip holds at the boundary and strictly beyond |
| `theta_R <= 8s/(23p)` | exact at the two extreme substitutions `rho = s/3`, `s = p/8` |
| (9.16) `kappa_R <= 5s/(4p)` | holds, at about `1.229 s/p` against the allowed `1.25 s/p` -- valid but **not generous** |
| (9.18) | reduces exactly to `s <= p/8`, consuming the whole hypothesis budget |
| (9.19) completion of the square | **exact identity**, so the bound `s^2/24` is attained at `rho = s/4` and loses nothing |
| (9.20) low-dispersion contradiction | exact: `36/64 = 9/16` and `1/2 - 9/16 = -1/16` |

Section 4 was rederived in the same way in the immediately preceding audit of the unchanged
mathematics and is not re-reported here; Section 9 is the new work.

The one PARTIAL: the Lemma 7.1 hypothesis chain in the low-dispersion branch. The arithmetic
checks exactly (`q >= 15p/8` from `s <= p/8`; `b = p - rho > p - s/3`; `b >= 2` with enormous
room since `p >= 2304`), but the chain `2 rho + t_i + 1 <= 3m + 1 <= s - 2` needs the
definitional facts `rho <= m` and `t_i <= m` from Section 7, which the auditor did not
rederive.

### 4.2 What was not attempted, named individually

- **`K-EPS`**: the AX1/nibble epsilon ledger -- parameter ranges, real/natural conversions,
  exceptional-set and rounding terms, and the accumulation of all losses inside `eps n^2`.
- **`K-CORRIDOR`**: Sections 5-7 themselves. Section 9 *uses* Lemmas 5.1, 5.2, 6.1 and 7.1 as
  inputs; this audit verified how Section 9 combines them, not that those lemmas are true.
- **`K-SPARSE`**: Section 8, which discharges the `alpha -> 0` endpoint and supplies `C_0`.
  Section 9.2 is one sentence and defers entirely to it, so Case C of the cover is closed only
  modulo Section 8.
- **`K-GLOBAL`**: PARTIAL. The minimal-counterexample frame was read and its structure
  checked, including the step from minimality to (9.2), and the formal counterpart
  `global_bound_from_eventual_high_degree` was inspected -- it converts an eventual bound with
  constant 2 into `Phi <= n^2/6 + max(2,N) n` for **all** split graphs. But the auditor did
  not verify `Phi(G) <= Phi(G-v) + d(v)` for every vertex of every split graph, nor the small
  orders.

One `INCONCLUSIVE` mandatory gate is enough to bar overall `PASS` independently of E4, E5 and
E7.

---

## 5. E3 -- formal conformance: `PASS`

The request demands the four canonical bridges be *independently validated, not just compiled*,
and compared against an auditor-constructed bridge. So the auditor did not cite them: it
restated the manuscript forms from the manuscript text, proved them with its own arguments,
and only then asserted the target's statements and discharged them with those proofs.

Auditor file `AuditorE3.lean`, exit 0, every declaration reporting
`[propext, Classical.choice, Quot.sound]`:

| Auditor theorem | What it settles |
|---|---|
| `auditor_fracPacking_iff` | the two fractional-packing predicates define the same feasible set; the Nibble side's extra capacities on **non-edges** are vacuous because a 3-clique containing both ends of a pair forces adjacency |
| `auditor_nu3Star_eq` | the two fractional optima are equal |
| `auditor_tau3Star_eq_nu3Star` | cover-side and packing-side optima coincide, at PaperIII's own names |
| `auditor_AX1_iff_manuscript` | **an `iff`, both directions**: `AX1Assumption` is equivalent to manuscript Theorem 2.1 at `H = K3`, packing side |
| `auditor_manuscriptAX1_holds` | that manuscript form holds unconditionally in the development |
| `auditor_AX2_implies_manuscript` | `AX2Assumption` gives manuscript Theorem 2.3, with `0.9` checked against `9/10` and `3 divides card` against `card % 3 = 0` |
| `auditor_decomposition_unfolds` | `HasTriangleDecomposition` is an exact edge decomposition into 3-cliques, by `Iff.rfl` |

The target's own four lemmas -- `isFracPacking_iff_yuster`, `nu3Star_eq_yuster`,
`tau3Star_eq_nu3Star`, `AX1Assumption_iff_packing_form` -- were then asserted verbatim and
discharged **by the auditor's constructions**, so agreement is a theorem, not a comparison of
prose. This is the bridge that was missing from the previous version and had to be supplied by
the auditor then; in v1.3 it is in the package, and it is correct.

No inequality direction or feasibility condition is lost at any interface: `nu3` and `nu3Star`
refer to the intended objects, and the `iff` in `auditor_AX1_iff_manuscript` rules out a
one-directional weakening.

**Claim map**, compiled statements verbatim:

```
Theorem_1_1                : exists C, for all G : SplitGraph, Phi <= n^2/6 + C n
Corollary_1_2              : exists C, for all G : SplitGraph, cp  <= n^2/6 + C n
Theorem_1_1_of_AX1_AX2     : AX1Assumption -> AX2Assumption -> (the above)
AX1_holds                  : AX1Assumption
AX2_holds                  : AX2Assumption
eventual_bound_of_..._AX1_AX2 : AX1 -> AX2 -> exists N, (eventual high-degree bound with 2n)
global_bound_from_eventual_high_degree :
    (eventual bound) -> for all G, Phi <= n^2/6 + max 2 N * n
```

The manuscript's Theorem 1.1 therefore traces: AX1/AX2 interfaces (conformance proved above)
-> `Theorem_1_1_of_AX1_AX2` -> discharged by `AX1_holds` and `AX2_holds` -> `Theorem_1_1`, with
the eventual-to-global step isolated in `global_bound_from_eventual_high_degree`.

---

## 6. E4 -- Lean reproduction and axiom boundary: `FAIL`

### 6.1 The clean build was achieved

Protocol followed as written: ZIP hash verified before extraction, extracted into a short path,
`lake-manifest.json` / `lakefile.toml` / `lean-toolchain` confirmed byte-identical to the
freeze, Lean 4.28.0 and Lake 5.0.0 recorded.

**All nine pinned dependencies at their exact declared revisions, every working tree clean**,
including mathlib at `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. `lake exe cache get` exited 0
with nothing to download. Project `.lake/build` **absent** before and after, with zero project
`.olean`/`.ilean` anywhere -- recorded as a listing, not asserted.

| Build | Jobs | Exit | Duration | Errors |
|---|---|---|---|---|
| `lake build PaperIII`, as the protocol prescribes | 8,203 | 0 | 90 min | 0 |
| the seven roots the axiom queries actually need | 8,444 | 0 | 105 min | 0 |

The eight axiom queries, all exit 0: **42 surfaces, 0 `sorryAx`, 0 non-standard footprints, 0
project axioms.** Includes `Theorem_1_1`, `Corollary_1_2`, `AX1_holds`, `AX2_holds`,
`Theorem_1_1_of_AX1_AX2`, both `PublicAPI` surfaces, `global_bound_from_eventual_high_degree`,
`Nibble.AX1.ax1Statement_holds`, `BKLO.triangle_decomposition_dense`, the two obstruction
certificates and the seven canonical bridges. One surface,
`isTrianglePacking_iff_yuster`, carries the **smaller** footprint `[propext, Quot.sound]`.

The archived comparison axioms are genuinely outside the closure, and this was checked properly
rather than by grep. The auditor first flagged that `Theorem_1_1_Final.lean` imports an `Ax2`
module -- it imports `Ax2.PartB.BKLO.Bridge`, not an axiom-bearing one. Building the transitive
import graph over all **704** project modules:
`Ax2.PartB.Axioms` and `Ax2.PartA.Wlog` are imported by **nobody**, and no canonical root's
closure reaches either. The `ESCAPE_HATCH_ASSESSMENT.md` claim survives scrutiny.

### 6.2 Why the gate nonetheless fails

`PaperIII.lean` is the library root and the project's `defaultTargets`. It imports 36 modules
and **imports neither `PaperIII.Theorem_1_1_Final` nor `PaperIII.PublicAPI`**.

The request's E4 requires: *"confirm that the public aggregate root and `PublicAPI` import the
intended canonical theorem path."* That confirmation **fails**.

The consequence is not theoretical. `lake build PaperIII` -- the command
`MATHLIB_REPRODUCTION_PROTOCOL.md` prescribes at step 8 -- reported
`Build completed successfully (8203 jobs)` with exit 0 **without compiling Theorem 1.1**. Run
immediately afterwards, as step 9 directs, **seven of the eight** axiom queries failed with
`object file 'PaperIII/Theorem_1_1_Final.olean' does not exist`. Only
`FreezeAxiomsCanonical` succeeded.

The aggregate root's closure is **177 of 704** modules; `Theorem_1_1_Final` needs **393**. An
auditor who follows the protocol literally and does not read the query logs would report a
successful clean build of a build that omits the paper's central result.

This also reconciles the three job counts, which are not a discrepancy: 8,203 for the
aggregate target, 8,444 for the canonical roots, and the author's recorded 8,719 for a still
larger set including aggregates no query imports.

**`EXT-V13-001` (MAJOR).** Required correction: have `PaperIII.lean` import
`PaperIII.Theorem_1_1_Final` and `PaperIII.PublicAPI`, or change the protocol's prescribed
command to build the canonical roots explicitly. Either fixes it; the first is better, because
it makes the default target mean what a reader assumes.

### 6.3 The author's build record is a replay, not a build

`FREEZE_METADATA.json` records `Build completed successfully (8719 jobs)`, exit 0, in **403
seconds**, from `gate_logs/BUILD_LOG_FINAL_INCREMENTAL.txt`. The log's own lines read
`Replayed Nibble.LPDuality` from job 8021 onward; roughly 180 jobs actually executed. The
figure is a replay summary.

The request already says this record is not a substitute for the external build, so nothing is
overclaimed. But the consequence should be stated: **the author-side package contains no
clean-build evidence at all.** This audit's two builds supply it.

**`EXT-V13-004` (MINOR).**

---

## 7. E5 -- bilingual, format and render: `FAIL`

### 7.1 What passes, and it is most of it

Both PDFs, every page rendered and inspected at 60 dpi:

| | EN | ES |
|---|---|---|
| pages | 45 | 46 |
| blank or near-blank pages | **none** | **none** |
| right-margin overflow (clipping) | **none** | **none** |
| bottom-margin overflow | **none** | **none** |
| ink coverage range | 1.22% - 9.20% | 1.43% - 8.58% |
| producer | LuaTeX-1.24.0 | LuaTeX-1.24.0 |

MD -> TeX and MD -> PDF are faithful in both languages: **66/66 equation tags, 20/20 theorem
numbers, 17/17 references, 42/42 formal identifiers** present in the generated TeX and in the
extracted PDF text.

Structural EN/ES agreement: 144 headings with **identical level sequence**, 66 identical
equation tags, 17 identical numbered references, identical theorem numbering, identical formal
identifiers.

The named regressions are closed. `A_{2J}` is now uniform -- **zero** occurrences of the
variant `A_{2,J}` in either language, in Markdown and in TeX. `[3,8]` appears 2/2 and
`[11,17]` 2/2, identical across languages, so the combined-citation divergence is gone. No
stale version label appears in any publication artifact.

Two auditor artifacts, recorded so they are not mistaken for defects. First, a naive extraction
reported 16,368 replacement characters in the English PDF text; the extracted bytes are
**CESU-8**, poppler's non-standard encoding for astral-plane characters, and decoding them
correctly leaves **zero** replacements and recovers exactly the intended mathematical italics
(`G`, `p`, `q`, `nu`, `alpha`). The PDF text layer is correct. Second, 17 formal identifiers
appeared "missing" from the TeX; all 17 are present with escaped underscores.

### 7.2 The divergence

**Proposition 7.4** differs in content between languages.

The English states the full hypotheses, including `h_i >= max{rho, q_J - r_b}` for every
`i in J`, and then the explicit inequality

```
nu3(G) >= C(b,2) + C(rho,2) - ((2b-1)A_J - A_{2J})/(2 q_J)
          + (1 - theta_R)(q_J - r_b)B_J/q_J
```

with `A_J = sum t_i`, `A_{2J} = sum t_i^2`, `B_J = sum g_i`.

The Spanish replaces the hypothesis with "las hipótesis de factibilidad de la Sección 7" and
replaces **the entire conclusion** with "vale la cota exacta `reserved_gain_packing_bound_subset`
mostrada allí" -- no formula at all. And the pointer is misdirected: Section 7 in Spanish
contains no such formula. The formula does appear in the Spanish Appendix E.1.3, which is
**identical** to the English one.

So no mathematics differs and nothing is unrecoverable. But a Spanish-only reader cannot read
the hypotheses or the conclusion of a numbered proposition that an English reader can, and is
sent to the wrong place. The divergence propagates to the TeX, so it is EN<->ES, not MD<->TeX.

Section 3 of the request permits minor editorial findings to coexist with `PASS` "only if they
do not create semantic ambiguity, provenance failure, or divergence among MD/TeX/PDF or
EN/ES". This is such a divergence, so the gate cannot pass.

**`EXT-V13-002` (MAJOR).** Required correction: translate the English statement of Proposition
7.4 in full, or in both languages replace it with a pointer to Appendix E.1.3 -- where the
statement actually lives -- so the two versions say the same thing.

---

## 8. E6 -- citations, prior art, novelty: `INCONCLUSIVE`

**A correction the auditor owes the record.** A first draft of this gate declared
`INCONCLUSIVE` on the grounds that no bibliographic database was reachable, and reported zero
search strings -- **without having attempted a single search in this run.** That claim was
carried over from earlier audits of earlier versions, which is precisely what this request
forbids. The searches were then run. They worked. What follows replaces that draft.

### Structural integrity: passes

17 references listed; **every bracketed citation resolves to a listed reference and every
listed reference is cited.** An apparent citation `[0]` was the auditor's regex reading the
interval `[0,2]`. Every source the request names is present and cited.

### The specialist search, and its negative result

Three searches were run on 2026-08-22, across the Erdős Problems record for #81, arXiv
listings through August 2026, Cambridge Core, ScienceDirect, Springer, the Rényi Institute's
Erdős archive, Ordman's academic page and the Waterloo C&O repository. Strings are recorded in
`results/novelty_search.json`.

**The decisive question -- does a published result already give the split-graph `1/6` quadratic
coefficient, a stronger statement, or an equivalent method? No such result was found.** The
state of the art the search establishes:

| Quantity | Value found in the literature |
|---|---|
| chordal **lower** bound | `n^2/6`, from the Erdős-Ordman-Zalcstein construction, which is itself a split and threshold graph |
| chordal **upper** bound | `(1-c) n^2/4` for some `c > 0` |
| split-graph upper bound | `3/16 n^2 + O(n)`, Chen-Erdős-Ordman |
| status of Erdős #81 | **open**; unknown whether `n^2/6` always suffices |

That is consistent with the manuscript's framing and with its claim to improve the split-graph
coefficient from `3/16` to `1/6`.

The most recent relevant paper found was retrieved and read: **arXiv:2608.11536, Bo Ning, 30
July 2026, "On the difference between clique partition and clique covering numbers."** Its
Theorem 1.2 bounds `f(n)`, the maximum difference between the clique partition and clique
covering numbers, as `floor(n^2/4) - C_1 n^{4/3} <= f(n) <= floor(n^2/4) - C_2 n^{4/3}`. It
cites Erdős-Ordman-Zalcstein only as prior work and makes no claim about split-graph clique
partition asymptotics. **No collision.**

Bibliographic details of the baseline were confirmed: Chen, Guan-Tao; Erdős, Paul; Ordman,
Edward T., "Clique partitions of split graphs", in *Combinatorics, graph theory, algorithms and
applications* (Beijing, 1993), pp. 21-30, World Scientific, 1994. The manuscript's attribution
is correct.

### The Cavers survey: a finding withdrawn

A first draft raised the survey's absence from the bibliography as `EXT-V13-005`. The survey
was then retrieved and read in full: **Michael S. Cavers, "Clique partitions and coverings of
graphs", Masters essay, University of Waterloo, 20 December 2005**, 87,916 characters extracted.

It contains **zero** occurrences of "chordal", **zero** of `3/16`, **zero** of `n^2/6` and
**zero** of "Zalcstein"; its three occurrences of "split" are the verb, splitting trees. The
essay is about trees, forests and their complements.

**It does not bear on the split-graph claim, so its absence is not a defect. `EXT-V13-005` is
WITHDRAWN.**

### Why the gate is still inconclusive

The request's first E6 bullet is mandatory: "Retrieve and check every cited source against the
claim it supports." That was not completed. `erdosproblems.com/81` returns HTTP 403 to direct
fetching, so its status text came from a search snippet rather than the record itself. More
importantly, **the `3/16` coefficient was not confirmed at a primary source**: the 1994 World
Scientific volume is not openly accessible and the copy at `ordman.net` could not be fetched
because the host's TLS certificate has expired. The remaining references were not retrieved
individually.

So the harder half of this gate -- novelty against the searched corpus -- is positively
verified, and the easier half is not done.

**`EXT-V13-008` (MINOR), new.** The `3/16` baseline is the comparison point for the paper's
headline improvement and could not be verified at a primary source. Cite a page or theorem
number, or quote the bound, so a reader can check it without the 1994 volume.

## 9. E7 -- release-package integrity: `FAIL`

**Self-containment passes.** The manuscript does not require an earlier internal draft. Its
three mentions of the internal audit are status disclosures that say the opposite of a
dependency: "the author-side internal audit passes. Independent reproduction remains open; the
candidate is a local formal freeze, not yet a public release", and "They do not replace
independent reproduction or external adversarial review." Paper III is described consistently
as a candidate for its first formal public release, symmetrically in both languages.

**The final hash re-verification passes: 12/12, the target did not change during the audit.**

**What fails** is the mandated agreement among "filenames, hashes, build records, formal names,
changelog, metadata and reproducibility documents".
`05_formalization/lean_v1.3_freeze/FREEZE_METADATA.json` declares

```
"status": "LOCAL_FREEZE_PREPARED_PENDING_INTERNAL_AUDIT"
"internal_audit": "NOT_STARTED"
```

while the same package ships `02_validation/01_INTERNAL_AUDITS/10_REPORT/INTERNAL_AUDIT_FINAL_REPORT.md`
with **overall verdict `PASS`**, and the manuscript itself says the internal audit passes. The
metadata contradicts both its own package and the manuscript. This is a provenance
misstatement in a release artifact, which Section 3 excludes from `PASS`.

**`EXT-V13-003` (MAJOR).** Required correction: update `status` and `internal_audit` to the
package's actual state, and add the external reproduction result once this run is accepted.

**`EXT-V13-006` (MINOR).** `PaperIII.lean`'s docstring still reads "Scaffold only for now:
this file imports Mathlib so `lake build` confirms the toolchain ... before any node is
formalized", inaccurate for a root that now imports 36 modules -- and misleading in exactly the
area of `EXT-V13-001`.

**`EXT-V13-007` (MINOR).** `MATHLIB_REPRODUCTION_PROTOCOL.md` step 8 prescribes a build command
that does not cover the modules step 9's queries require. The two steps are mutually
inconsistent as written.

---

## 10. Mandatory regression matrix

| Item | Disposition | Evidence |
|---|---|---|
| stale integrity or axiom labels | **partly closed**: publication artifacts clean; `FREEZE_METADATA.json` stale, `EXT-V13-003`; root docstring stale, `EXT-V13-006` | E0, E7 |
| overbroad "resolves the split case" wording | **CLOSED**: zero occurrences in either language | E1 |
| `A_{2,J}` / `A_{2J}` and combined-citation divergence | **CLOSED**: notation uniform in MD and TeX; `[3,8]` 2/2 and `[11,17]` 2/2 identical EN/ES | E5 |
| incomplete citation retrieval and bounded novelty search | **partly closed**: an independent specialist search was run and found **no collision**; per-reference retrieval still incomplete, and the `3/16` baseline is unverified at source (`EXT-V13-008`) | E6 |
| the two archived comparison-route axioms and dependency closure | **CLOSED**: imported by nobody among 704 modules; absent from all canonical closures and all 42 footprints | E4 |
| missing graph/Yuster model bridge | **CLOSED**: present in v1.3 and independently validated against an auditor-built bridge | E3 |
| `K-EPS` | **NOT ATTEMPTED** | E2 |
| `K-CORRIDOR` | **NOT ATTEMPTED** | E2 |
| `K-SPARSE` | **NOT ATTEMPTED** | E2 |
| `K-COVER` | **CLOSED**: split exhaustive and non-overlapping, four levels checked | E2 |
| `K-GLOBAL` | **PARTIAL**: frame and formal counterpart checked; deletion step and small orders not verified | E2 |
| manuscript AX1/AX2 vs `AX1Assumption`/`AX2Assumption` | **CLOSED**: AX1 by an `iff`, AX2 by implication with both coercions checked | E3 |
| quantitative tolerances and the hypergraph-to-graph bridge | **bridge CLOSED; tolerances NOT ATTEMPTED** | E3, E2 |
| independent rederivation of Sections 4-9 | **Section 4 and Section 9 rederived; Section 5-8 not** | E2 |

As the request demands, these are stated separately and not conflated: **semantic
correspondence** (E3, proved), **successful compilation** (E4, 8,444 jobs exit 0), **axiom
footprint** (E4, 42 surfaces clean), and **independent mathematical rederivation** (E2,
partial). No mathematical item is marked closed merely because a Lean declaration compiles.

---

## 11. Findings ledger

| ID | Severity | Gate | Substance |
|---|---|---|---|
| `EXT-V13-001` | MAJOR | E4 | the public aggregate root imports neither `Theorem_1_1_Final` nor `PublicAPI`; the protocol's prescribed build omits the main theorem and breaks 7 of 8 axiom queries |
| `EXT-V13-002` | MAJOR | E5 | Proposition 7.4 diverges EN<->ES: the Spanish drops a hypothesis and the entire conclusion, and misdirects the reader to Section 7 |
| `EXT-V13-003` | MAJOR | E7 | `FREEZE_METADATA.json` says the internal audit has not started; the package ships one with verdict `PASS` |
| `EXT-V13-004` | MINOR | E4 | the author's recorded build is an incremental replay (403 s, ~180 jobs), so the package carries no clean-build evidence |
| `EXT-V13-005` | *withdrawn* | E6 | raised for the Cavers survey's absence; **withdrawn** after retrieving the survey and finding it has no chordal or split-graph clique-partition content |
| `EXT-V13-008` | MINOR | E6 | the `3/16` Chen-Erdős-Ordman baseline could not be verified at a primary source |
| `EXT-V13-006` | MINOR | E7 | `PaperIII.lean`'s docstring still describes the root as a scaffold |
| `EXT-V13-007` | MINOR | E7 | `MATHLIB_REPRODUCTION_PROTOCOL.md` steps 8 and 9 are mutually inconsistent |

---

## 12. What this audit does and does not establish

**Establishes.** The delivered bytes are exactly what the package declares, and did not move
during the audit. The archive is structurally clean and contains no compiled artifact. Paper
III rebuilds cleanly from its frozen sources against the exact pinned dependency revisions --
not a rebuild of Mathlib from source, as the protocol's claim boundary requires. All 42 named
surfaces have foundational axiom footprints with no `sorryAx` and no project axiom, and the two
archived axioms are unreachable from every canonical root. The AX1 and AX2 interfaces say what
the manuscript says, proved against the auditor's own construction with AX1 settled in both
directions. Section 9's case split is exhaustive and its ten numbered inequalities are exact,
with three of them tight at their boundaries. Both PDFs render without a blank page, a clipped
margin or a lost glyph.

**Does not establish.** The truth of Theorem 1.1. The AX1 epsilon budget. Sections 5 through 8.
Novelty, or that no published result already gives the `1/6` coefficient. Human peer review.
And Paper III has never been audited by an adversarial challenger -- on Paper I a challenger
found four Spanish duplications this auditor's own diff had missed, so the absence is material.

**The failures are release-readiness defects, not mathematics.** Three of them are mechanical
to fix: two import lines, one translated proposition, and two metadata fields. Once fixed, the
gates that fail here would be re-auditable cheaply, since the target hashes and the clean-build
evidence in this package remain valid for everything else.

## 13. Signature

Claude (Anthropic), `claude-opus-5`, external adversarial auditor under
`EXTERNAL_ADVERSARIAL_AUDIT_REQUEST.md`. 2026-08-22. Only v1.3 was evaluated; no earlier
verdict was inherited.

**Overall verdict: `FAIL`** -- E4, E5 and E7 fail on release defects; 0 blocking, 0 critical,
3 major, 3 minor open, 1 withdrawn and 1 closed; no mathematical or formal defect found. E2 and
E6 are `PASS` after the addendum, whose conclusion is
**EXPECTED_PASS_ON_V1.4_IF_CORRECTIONS_VERIFY**.
