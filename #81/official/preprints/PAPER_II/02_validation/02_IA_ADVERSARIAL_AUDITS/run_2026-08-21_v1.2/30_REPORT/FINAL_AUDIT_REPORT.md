# External AI Adversarial Audit — Paper II, `preprint_draft_v1.2`

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
**Protocol SHA-256:** `8ba029f443297927c9a5101b0a349bd33e3772587e56d32cbb70145de24ae505`
**Run:** `run_2026-08-21_v1.2`
**Audit class:** `EXTERNAL_AI_ADVERSARIAL`
**Paper:** *Complete-Split Extremizers for a Fractional Triangle-Cover Functional on Chordal Graphs*

---

## 1. Target identity and controlling hashes

| Item | SHA-256 |
|---|---|
| This protocol | `8ba029f443297927c9a5101b0a349bd33e3772587e56d32cbb70145de24ae505` (verified against its sidecar) |
| English Markdown (semantic source) | `7215e14bbea8ab2bf208dcdd1efa050cd2b72c997eee2efe504a1e6817c68882` |
| Frozen Lean archive | `ee2d05cc40d943ca92f8f7bf3e5dd83c2692518ddea5e2ca4f7686ccb1ac3895` |
| Sealed internal-audit ZIP | `e6f625486db867582da72fff9e71fa0f600dcce40e43ef885ce01756282b24e2` |

All three protocol anchors match the delivered bytes exactly. Input freeze sealed before
analysis: **197 files, 3,411,262 bytes**, with the audit-output subtree excluded per
protocol Section 2. The target did not change during the run.

## 2. Audit class, independence and limitations

Primary auditor. The adversarial challenger required by protocol Section 3.1 was run
against **Paper I only**; Paper II's findings therefore come from a single reasoning
context. That is a real weakening relative to Paper I, and it matters concretely: on Paper I
the challenger found four Spanish duplications the primary auditor's diff had missed. To
compensate, Paper II's duplication and bilingual checks were made **general and mechanical**
rather than targeted at known phrases.

Both contexts used in this series are the same model family (Claude Opus 5) and the same
operator launched them. "External" means separation from the authoring workflow, **not**
independent human peer review. Full disclosure: `00_REQUEST/AUDITOR_DECLARATION.md`.

## 3. Executive verdict

> ## `PASS_WITH_RESIDUALS`

**Meaning.** Under protocol Section 6.2, `PASS_WITH_RESIDUALS` means no known
mathematical or formal defect and no unresolved `BLOCKER` or `MAJOR`, but a non-claim-critical
residual remains. **No mathematical or formal defect was found in Paper II.** The headline
theorem survived exhaustive falsification, the Lean development clean-builds with the
expected axiom footprint, and the one open finding is a stale integrity directory.

Counts: **`BLOCKER` 0, `MAJOR` 0, `MINOR` 1, `NOTE` 1.**

This verdict does **not** close any release gate that explicitly requires one of the
residuals in Section 11.

## 4. Gate-by-gate verdicts

| Gate | Verdict |
|---|---|
| G0 — target, identity, independence | `PASS` |
| A — definitions and claims | `PASS` |
| B — definitions, conventions, the functional | `PASS` |
| C — vertex-copy inequality and symmetrization | `PASS` |
| D — monotonicity, ties, level sets | `PASS` (termination not independently verified) |
| E — complete-split value | `PASS` |
| F — integer maximization and corollaries | `PASS` |
| G — exhaustive falsification | `PASS` |
| H — Lean reproduction and conformance | `PASS` |
| I — citations and problem status | `PASS_WITH_RESIDUALS` |
| J — scope and overclaim | `PASS` |
| K — prior art and novelty | `PASS_WITH_RESIDUALS` |
| L — bilingual and artifact consistency | `PASS_WITH_RESIDUALS` |
| M — package integrity | `PASS_WITH_RESIDUALS` |

**Overall: `PASS_WITH_RESIDUALS`**, no stronger than the weakest mandatory gate.

## 5. Claim map

**`P2-MAIN-V1_2`** — the exact chordal maximum. For every integer *n* >= 1,
max over chordal *G* with |V(G)| = *n* of Phi_tau(G) = floor((2n+1)^2/24), with
Phi_tau(G) = |E(G)| - 2*tau3star(G), together with attainment by a complete-split graph.
Formal: `PaperII.theorem_1_2`. Role: **final theorem**. **Survived.**

**`P2-EXTREMIZER`** — maximizers, level sets, copy defects. Formal:
`Fsat_argmax_unique`, `Fsat_argmax_tie`, `level_set_iff`, `copyDefect_nonneg`,
`copyGamma_ge_half_copyDefect`. Role: **structural bridges**. **Survived** on the
single-step inequality; termination and the clone-class lift not independently verified.

**`P2-ASYM-COR`** — asymptotic, modular and Paper I comparison corollaries. Formal:
`phiTau_max_sandwich`, `odd_sq_emod_24`, `phiTau_max_closed`,
`phiTau_max_le_paperI_bound`. Role: **byproducts**. **Survived**, all four in exact
arithmetic including the negative range.

**`P2-FORMAL-CONFORMANCE`** — the v1.2 surface and reusable components. Formal: `PaperII`,
`Contrib.Submission.Chordal`, `Contrib.Submission.GeodesicChordless`. Role: **byproduct**.
Built as explicit targets with the expected footprints.

Full map with hypotheses and falsification strategies: `10_CONTROL/CLAIM_MAP.md`.

## 6. The Section 4.1 regression controls — including the one Paper II previously failed

| Control | Result |
|---|---|
| no path resolves into `superseded/` | **PASS** — 0 of 197 |
| no unexpected zero-byte file | **PASS** — 0 |
| no stray `$o` | **PASS** — absent |
| manuscript sidecar verifies, LF-safe | **PASS** — LF-only, 6/6 entries verify |
| every archive name and SHA-256 printed in the manuscript exists and matches | **PASS** — the single printed hash resolves to the delivered archive, in both languages |
| **no stale `v1.0.1`, nonexistent freeze filename or hash, nonexistent gate-log path, or mislabeled formalization table** | **PASS** — 0 hits for `v1.0.1` or `lean_v1.1_freeze`; Table 4 is captioned "Lean v1.2"; no gate-log path is referenced |

The last row is the control Paper II failed at v1.1, where the manuscript documented a
v1.0.1 freeze that was absent from the package, along with a nonexistent hash and a
nonexistent build-log path. **The defect is corrected**, and it was re-established from
scratch on the v1.2 bytes rather than carried forward.

## 7. Analytic and computational falsification

Every number below comes from code written for this audit, in exact arithmetic, over a
stated domain, with **no random seeds**. Two failure routes were sought for the headline
claim — a chordal graph exceeding the formula, and the formula being unattainable.

### 7.1 The headline claim, exhaustively

| *n* | labeled graphs | chordal graphs | max Phi_tau found | floor((2n+1)^2/24) | match | complete-split argmax |
|---|---|---|---|---|---|---|
| 1 | 1 | 1 | 0 | 0 | yes | (0,1), (1,0) |
| 2 | 2 | 2 | 1 | 1 | yes | (1,1), (2,0) |
| 3 | 8 | 8 | 2 | 2 | yes | (1,2) |
| 4 | 64 | 61 | 3 | 3 | yes | (1,3), (2,2) |
| 5 | 1,024 | 822 | 5 | 5 | yes | (2,3) |
| 6 | 32,768 | 18,154 | 7 | 7 | yes | (2,4) |
| **total** | **33,867** | **19,048** | — | — | **exact at every n** | **always attained** |

**Zero counterexamples.** The maximum is attained by a complete-split graph at every *n*,
which is the attainment half of the claim established by computation rather than assumed.
The left endpoint *n* = 1 — where closed forms of this shape usually fail — holds.

### 7.2 The vertex-copy inequality, the structural core

Phi_tau(G_{v->u}) + Phi_tau(G_{u->v}) >= 2*Phi_tau(G) for nonadjacent *u*, *v*
(`copyDefect_nonneg`), tested over **all** labeled graphs on 2..6 vertices and **all**
nonadjacent pairs:

| Domain | Instances | Violations | Min defect |
|---|---|---|---|
| *n* = 2..6, all nonadjacent pairs | **251,085** | **0** | 0 |

An observation that supports the manuscript: among the 148,919 chordal instances, **6,090**
have **both** copy directions destroying chordality. The manuscript claims preservation only
for copying toward a *simplicial clone class*. Those 6,090 cases show that restriction is
**necessary**, not decorative.

### 7.3 The packing/cover identity, not assumed

The abstract asserts nu3star = tau3star. Rather than assume it, both optima were computed by
**separate linear programs** on every graph tested: **270,133 graphs across Gates C and G,
zero mismatches.**

### 7.4 The arithmetic corollaries

Exact integer and rational arithmetic over *n* in [-20000, 20000], deliberately including
negatives because `phiTau_max_sandwich` is stated for *n* : Z with no lower bound.

| Claim | Result |
|---|---|
| `phiTau_max_sandwich`: 4n^2+4n-23 < 24*floor((2n+1)^2/24) <= 4n^2+4n+1 for all *n*  in  Z | **HOLDS**, all 40,001 values including negatives |
| bounded remainder: M(n) = n^2/6 + n/6 + theta_n with theta_n  in  (-1, 1/24] | **HOLDS**; observed range [-1/3, 0] |
| `odd_sq_emod_24`: (2n+1)^2 == 1 or 9 (mod 24) | **CONFIRMED**; residue set is exactly {1, 9} |
| `phiTau_max_le_paperI_bound`: floor((2n+1)^2/24) <= n^2/6 + n/2 for *n* >= 1 | **HOLDS**, margin 8n - 1 |

**The `n >= 1` hypothesis is necessary.** Tested for *n* <= 0: the Paper I comparison
**fails** there. The manuscript states the hypothesis; an adversarial check that came out in
the paper's favour.

**Cross-paper (protocol Section 10):** the comparison uses Paper I's **corrected `+n/2`
surface**, not the superseded `+n` form. Requirement satisfied.

## 8. Lean reproduction

Detail: `20_EVIDENCE/H_LEAN_REPRODUCTION/AUDIT_RECORD.md`.

- Archive hash verified **before** extraction; clean room provably free of `.lake` and
  `.olean`; 42 project `.lean` files, matching the freeze metadata.
- Lean 4.28.0 commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`, Mathlib
  `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. `lake update` did not mutate the pin.
- Protocol Section 9.2 command run verbatim: **exit 0**, **30m05.109s**,
  `Build completed successfully (8063 jobs)`, **zero errors**.
- **Job-count note, reported rather than glossed:** the manuscript records 8,061 for the
  main build and 8,032 for the supplement; this run produced 8,063 in one invocation over
  all seven targets. Different target set, not a discrepancy.
- **Explicit targets versus aggregate root.** The protocol warns that the aggregate
  `PaperII` target does not by itself prove `Extremizer` and `CopyDefect` are imported. Both
  are **explicit build targets**, and `FreezeAxioms.lean` imports them **directly**, so the
  axiom queries do not rely on aggregate-root closure. **No first axiom attempt failed**, so
  there is no collision log to preserve for this paper.
- **Axiom footprint.** 16 declarations queried, exit 0. Fourteen report
  `[propext, Classical.choice, Quot.sound]`. Two report the strictly smaller
  `[propext, Quot.sound]`: `PaperII.phiTau_max_le_paperI_bound` and
  `SimpleGraph.IsChordal.comap`. **The manuscript's Table 5 records exactly that reduced
  footprint** for the former — accurate reporting at a level of detail that is easy to get
  wrong. **No `sorryAx`, no project-level axiom.**
- **Escape hatches in active code: 0** across all 42 files (2 hits, both prose).

## 9. Citations and open status

Detail: `20_EVIDENCE/I_CITATIONS_STATUS/AUDIT_RECORD.md`.

`SUPPORTED`: [1] Erdős–Ordman–Zalcstein 1993 — publisher record retrieved, abstract obtained
**verbatim**, both constants (n^2/6 and (1-c)n^2/4) matching. [3] Blair–Peyton 1993 — record
retrieved and content confirmed. [2] Golumbic, [5] Lean, [6] mathlib — standard citations as
printed. [7] the project repository — retrieved, and its statement of **Paper II's** result
agrees with this manuscript.

`UNVERIFIED` by direct access: [8] erdosproblems.com returns HTTP 403 to this auditor. The
substantive status claim is corroborated by the verified [1] abstract ("It is unknown whether
this many cliques will always suffice").

**Distinctions maintained correctly.** Paper II works over chordal graphs and determines an
**exact fractional** extremum; [1] concerns the **integral** clique-partition number and
leaves it open. The abstract states plainly that the paper "does not prove an integral
clique-partition theorem" and that its cover-first proof "does not use strong LP duality or
an asymptotic packing theorem" — and the reference list contains no asymptotic packing
result, consistent with that claim.

## 10. Prior art, scope, and bilingual QA

**Novelty (Gate K).** No prior result with the same statement was found in the corpus
searched to 2026-08-21. No retrieved work states an exact maximum of |E| - 2*tau3star over
chordal graphs, identifies complete-split extremizers, or uses vertex-copy symmetrization.
The most recent relevant preprint located (Ning, arXiv:2608.11536, 30 July 2026) concerns a
different object and still cites [1] as the chordal state of the art. **This is an
evidence-bounded negative result, not proof of novelty.**

**Scope (Gate J).** No resolution claim: a targeted search for "settles/resolves/solves" plus
a problem object returned only false positives ("**Solv**ing its two branches"). Status is
`EDITORIAL_DRAFT_WITH_OPEN_GATES`, unpublished, with independent reproduction, external
adversarial audit and peer review named as **open** gates. Novelty is explicitly labelled an
internal editorial assessment. Table 4 is correctly captioned "Lean v1.2" and states
"independent reproduction remains pending". The uniqueness claim is bounded to the clique
size within the complete-split family — and the enumeration confirms that the weaker claim
is the right one, since ties do occur at *n* = 2 and *n* = 4.

**Bilingual (Gate L).** Protected content is **identical**: display mathematics 96/96 with
zero one-sided blocks after blanking translated prose, equation tags 7/7, citation keys
identical, headings 52/52 with identical level sequence. The one asymmetry is the Lean tactic
name `simp` appearing once in Spanish prose — not a declaration, no mathematical content.

**The Paper I defect class is absent.** Paper II was screened explicitly for duplicated
blocks, since Paper I v1.2 carried five. The duplicated-line classes here are **symmetric**
between languages: the headline floor formula appears 9 times in each, and the table header
twice in each because there are **two** distinct tables (Table 4 and Table 5) — verified by
reading both regions. An initial flag on the Spanish header was an artifact of a
40-character threshold (the English header is 38) and was **dismissed rather than filed**.

**Rendered pages.** 47 pages (23 EN + 24 ES) rendered and analysed; LuaTeX-1.24.0, A4,
unencrypted; no blank page, no anomalous black area, no malformed structure. The one-page
difference is ordinary Spanish text expansion, which the duplication screen is what
establishes.

## 11. Unresolved findings and residual risks

| ID | Gate | Severity | Summary |
|---|---|---|---|
| `EXT-PII-M-001` | M | MINOR | `04_integrity/` is stale v1.1 content; 1 of 2 sidecar entries unresolvable; no documented v1.1->v1.2 initialization diff |
| `EXT-P2-I-001` | I | NOTE | the official Erdős Problems page could not be retrieved (HTTP 403) |

**Coverage limits — declared, not assumed to pass:** termination of the repeated-copy
process; the discrete-convexity lift to clone classes; the two-variable orbit reduction on
S_{p,q}; exhaustive enumeration beyond *n* = 6; modules outside the seven build targets;
independent PDF recompilation; institutional bibliographic databases and non-English search.

## 12. What this audit does not establish

- It does **not** establish that the headline theorem is true. It establishes that a
  determined adversarial search over 19,048 chordal graphs and 251,085 copy instances, plus
  an independent formal reproduction, failed to falsify it.
- It is **not** human peer review.
- It does **not** prove global novelty.
- It does **not** verify termination of the copy process or the clone-class lift — the two
  structural steps beyond the single-step inequality.
- It does **not** verify that the delivered PDFs were compiled from the delivered TeX.
- It does **not** cover Lean modules outside the seven protocol targets.
- Paper II's findings rest on a **single reasoning context**; no challenger was run.

## 13. Package and reproduction

`40_PACKAGE/SHA256_MANIFEST.txt`, `PACKAGE_MANIFEST.json` and `TREE.txt` record final
contents. Every referenced log exists as a directly visible file under
`20_EVIDENCE/*/results/`, not only inside the archive. Scripts are Python 3.14 needing only
the standard library plus `Pillow`; the Lean reproduction needs the pinned toolchain and, on
Windows, `core.longpaths` plus a short clean-room root.

## 14. Signature

| Item | Value |
|---|---|
| Auditor | Claude Opus 5 (`claude-opus-5`), Anthropic |
| Configuration | primary auditor only; no challenger for this paper |
| Audit date | 2026-08-21 |
| Protocol | `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`, SHA-256 `8ba029f4...e505` |
| Target | `preprint_draft_v1.2`, EN Markdown `7215e14b...8882` |
| **Verdict** | **`PASS_WITH_RESIDUALS`** — no mathematical or formal defect; 0 blocker, 0 major, 1 minor, 1 note |
