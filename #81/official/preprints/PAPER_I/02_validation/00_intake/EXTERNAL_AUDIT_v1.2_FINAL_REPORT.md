# External AI Adversarial Audit — Paper I, `preprint_draft_v1.2`

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
**Run:** `run_2026-08-21_v1.2`
**Audit class:** `EXTERNAL_AI_ADVERSARIAL`
**Paper:** *Affine Profile Reduction for Fractional Triangle Packings in Split Graphs*

---

## 1. Target identity and controlling hashes

| Item | SHA-256 |
|---|---|
| This protocol | `8ba029f443297927c9a5101b0a349bd33e3772587e56d32cbb70145de24ae505` (verified against its supplied sidecar) |
| English Markdown (semantic source) | `da7e48196a03a8698a9c5a503976b43780cb9e5309558f1b7d3e06b4af35ee9e` |
| Frozen Lean archive | `0181506408644fc1f8872d711de5a98a500f4052aa295bcd6f8c82776694fd3a` |
| Sealed internal-audit ZIP | `34d41bb9fec6fdc1adb6e544d7f5974438c7453ef7f7eb217f857489987d32e6` |
| Aggregate target hash (auditor construction over 155 frozen files, 2,746,928 bytes) | `9b6a07804601326b8a7d977940322e98c29c7f91e108865915737f6a19477e77` |

All three protocol anchors for Paper I match the delivered bytes exactly, as do the six
anchors for Papers II and III. The audit-output subtree
`02_validation/02_IA_ADVERSARIAL_AUDITS/**` is excluded from the target hash, per
protocol Section 2. The target did not change during the run.

## 2. Audit class, independence and limitations

Two isolated reasoning contexts were used, as protocol Section 3.1 requires: a primary
auditor and an adversarial challenger which received only the frozen target and the
protocol and produced its own attack plan, kill switches, claim map and findings before
any reconciliation. Neither context read the internal-audit directories during its
independent pass.

**Disclosed limitations, stated plainly:**

- Both contexts are the **same model family** (Claude Opus 5). A different provider would
  be stronger. This is disclosed as protocol Section 3.1 requires.
- The **same operator** launched both contexts. "External" therefore means separation
  from the authoring workflow, **not** independent human peer review.
- This audit is **not** human peer review and does **not** establish global novelty.

Full disclosure: `00_REQUEST/AUDITOR_DECLARATION.md`.

## 3. Executive verdict

> ## `FAIL`

**and its exact meaning.** Under protocol Section 6.2, `FAIL` means "at least one
claim-critical defect or failed mandatory gate". Here the failed gate is **Gate L
(bilingual and artifact consistency)**, on account of one `MAJOR` finding: the delivered
Spanish manuscript, Spanish TeX and Spanish PDF contain **five duplicated blocks**, one of
them an orphaned sentence fragment and one an ungrammatical duplicate. Protocol
Section 6.2 states that `PASS` requires no unresolved `MAJOR`, and the overall verdict is
"no stronger than the weakest mandatory gate".

**What this verdict does NOT mean.** It is **not** a mathematical finding. The
mathematics of Paper I survived every attack mounted against it by both contexts:

- Theorem 1.1 was **not** falsified in any of 5,429 exhaustively enumerated split graphs
  (primary auditor) or 8,646 (challenger), with `nu3*` computed by exact rational simplex.
- All 11 proof-critical identities of Sections 3, 6, 7, 8 and 9 verify as **exact
  symbolic polynomial identities**.
- The reduced pure-profile LP closed form (6.5) reproduced with **zero mismatches** in
  30,450 exact-rational instances (primary) and 70,200 (challenger).
- The Lean development **clean-builds** with the protocol's own command and carries
  exactly the expected foundational axiom footprint on every headline surface.

The blocking defect is editorial and confined to the Spanish artifact chain. It is
straightforward to fix, and fixing it necessarily produces a new target hash and requires
a new audit run.

## 4. Protocol compliance statement and deviations

Gates G0 and A–M were all attempted. Deviations, each declared rather than concealed:

- **Gate L page-image QA** — performed: all 39 pages (19 EN, 20 ES) rendered at 110 dpi
  and analysed; two pages inspected visually in detail.
- **Gate L recompilation** — the PDFs were **not** independently recompiled from the
  delivered TeX. Producer strings and source-to-PDF text tracking were verified instead.
- **Gate I / K sources** — erdosproblems.com returned HTTP 403 on every path; the
  Chen–Erdős–Ordman 1994 volume and Schrijver 1986 were unobtainable; no institutional
  bibliographic database was available.
- **Concurrency** — Papers II and III were built in separate clean rooms concurrently
  with report preparation. Evidence independence is preserved (separate roots, separate
  build directories, separate logs); only compute was shared.
- **Shared dependency cache** — the Mathlib dependency cache was used, as protocol
  Section 3.3 permits when disclosed. It holds no compiled project module.

## 5. Claim map

**`P1-FRAC-THM-V1_2`** — Theorem 1.1 (L67–75): for every split graph *G* on *n*
vertices, |*E*(*G*)| - 2*nu3star(*G*) <= *n*^2/6 + *n*/2.
Formal: `PaperI.Split.paperI_main_sharp`. Role: **final theorem**.
Attacked by exhaustive enumeration with exact nu3star and by symbolic rederivation of
every step. **Survived.**

**Companion** — L77 describes `paperI_main` as a weaker form with additive term *n*.
Formal: `PaperI.paperI_main`. Role: **byproduct / traceability**.
Checked that it is never substituted for the headline. **No `+n` leakage found anywhere.**

**`P1-ASSEMBLY-V1_2`** — Section 8 assembly, with the case split "if *b*_1 >= 1 then
*p* >= 1". Formal: `PaperI.assembly_sharp`. Role: **bridge**.
Attacked by symbolic identity check and by the boundary regime *p*=1, *q*=0. **Survived.**

**`P1-DUALITY`** — Proposition B.1, finite covering/packing duality, and residual
duality. Formal: `FiniteLPDuality.covering_packing_duality`,
`PaperI.Split.residual_duality`, `Contrib.Submission.covering_packing_duality`.
Role: **premise** (duality) and **bridge** (residual).
Orientation, feasibility, boundedness and normalization checked, plus independent LP
computation. **Survived**, and it is derived from a finite Farkas lemma rather than
postulated.

**`P1-INTERFACES`** — Remark after Section 5; Section 10. Formal:
`Contrib.lpVal_concave`, `lpVal_ge_min`, `lpVal_lipschitz`,
`Contrib.tuza_split_centered_scalar`. Role: **byproduct**.
Verified present, built, and correctly labelled a byproduct. **Survived.**

The distinctions protocol Section 5.2 requires are recorded explicitly: source present
(yes, 16 files); target compiled (yes, the 8 protocol targets); aggregate root imports
target (**no** — see Section 8); public API re-exports declaration (n/a for Paper I);
headline theorem has the claimed axiom footprint (**yes**, independently queried).

## 6. Gate-by-gate verdicts

| Gate | Verdict |
|---|---|
| G0 — target, identity, independence | `PASS` |
| A — definitions and claims | `PASS` |
| B — definitions, normalizations, factors | `PASS` |
| C — affine reduction and concavity | `PASS` |
| D — LP/Farkas duality and transfer | `PASS` with 1 `MINOR` |
| E — reduced pure-profile LP | `PASS` with 1 `MINOR` |
| F — final assembly and `+n` leakage | `PASS` |
| G — enumeration and falsification | `PASS` |
| H — Lean reproduction and conformance | `PASS` |
| I — citations and problem status | `PASS_WITH_RESIDUALS` |
| J — scope and overclaim | `PASS` with 1 `MINOR` |
| K — prior art and novelty | `PASS_WITH_RESIDUALS` |
| **L — bilingual and artifact consistency** | **`FAIL`** |
| M — package integrity | `PASS_WITH_RESIDUALS` |

Basis, gate by gate:

- **G0** — 9/9 anchors match; freeze sealed; clean room provably free of inherited build
  state; all Section 4.1 intake controls pass.
- **A** — independent claim map built; definitions, hypotheses and quantifier domains
  coherent.
- **B** — definitions and normalizations rederived. The 1/(*d*_v-1) normalization is
  exactly what produces the factor 1/2 in Lemma 3.1.
- **C** — affine dependence and concavity verified; the profile weights summing to 1 is
  precisely what makes the objective a convex combination; the polytope is nonempty and
  compact.
- **D** — duality orientation, feasibility, boundedness and normalization all correct.
  `EXT-P1-D-001` is an expository gap in deriving (4.7), which is itself true.
- **E** — (6.5) reproduced with 0 mismatches in 30,450 exact instances.
  `EXT-P1-E-002` is an unqualified formula in Appendix A.2.
- **F** — assembly rederived symbolically; **no `+n` leakage** in prose, equations,
  either translation, either TeX, either PDF, or the declaration names.
- **G** — 5,429 split graphs enumerated with exact nu3star; no counterexample; the
  complete-split family value confirmed.
- **H** — clean build, exit 0, 8,034 jobs reproducing the recorded count; footprint
  exactly `[propext, Classical.choice, Quot.sound]`; 0 escape hatches in active code.
- **I** — [1] and [5] verified against primary sources; three residuals remain.
- **J** — status language well scoped; `EXT-P1-J-001` concerns the word "sharp".
- **K** — no collision in the searched corpus; bounded negative result; specialist
  residuals remain.
- **L** — `EXT-P1-L-001` (`MAJOR`): five duplicated blocks reaching the delivered
  Spanish PDF.
- **M** — 79 of 82 sidecars verify; `EXT-P1-M-001` is a stale v1.1 integrity baseline.

**Overall: `FAIL`**, no stronger than the weakest mandatory gate.

## 7. Analytic rederivation and computational falsification

### 7.1 Symbolic identities — 11 of 11 exact

Each was checked as an exact polynomial identity (expand, subtract, require identically
zero), not sampled. Evidence: `20_EVIDENCE/F_PROOF_CHAIN/results/symbolic_identities.json`.

Lemma 3.1's per-vertex contribution `C(d,2)/(d-1) = d/2`; `A+B+C = (p^2-p-sq)/2`;
(7.2) `12(U-R) = q(2o+q)-2p`; (7.4) `12(D-R) = 12o^2-6o(2p-q)+(2p-q)^2-6p`; the
nonnegativity certificate `12u^2-6uv+v^2 = 12(u-v/4)^2+v^2/4`;
(7.6) `12(H-R) = (2s-q)^2+2q(p-s)-2p-4s`; (8.2) `C(p,2)-2R+p = (p+q)^2/6+p/2`; the Section 8
assembly difference; its residual regime `p=1,q=0`; the complete-split value
`n^2/6+n/6` at `n=3p`; and the Paper II comparison margin `8n-1`.

### 7.2 Exact-rational computation

| Test | Domain | Result |
|---|---|---|
| Closed form (6.5) | `p=2..18, q=1..44, s=2..p` (6,732) and `p=2..30, q=1..70` (30,450) | **0 mismatches** |
| Uniform bound (7.8) | same | **0 violations** |
| Mandated point `(2,4,2)` | — | LP value `0`, `R-p/2 = 0`, slack `0`; `s=2, o=0, q=2p` — **CONFIRMED** in the equality family |
| Tightness Remark, all four regimes | exhaustive | **all confirmed**; minima exactly `9/4` (`s>=3,o>=3`), `1/4` (`s=2,o>=1`), `1/4` (`o=1`), `1` (`o=2`) — three of four are attained, so the stated constants are sharp |
| Equality characterisation | exhaustive | 17 equality cases, **all** with `o=0` and `q=2p`, exactly as claimed |
| Theorem 1.1 direct | 5,429 split graphs, `nu3*` by exact simplex | **0 violations** |
| Complete-split family | `p=2..8` | `nu3* = C(p,2)` exactly; `\|E\|-2nu3* = n^2/6+n/6` exactly |

The only deviations from (6.5) anywhere in the unrestricted sweep occur at `q=0, p=2`,
outside the formula's stated domain, where the manuscript proves `M(0)=0` separately.
Not a defect; recorded so the domain restriction is explicit.

## 8. Lean reproduction

Detail: `20_EVIDENCE/H_LEAN_REPRODUCTION/AUDIT_RECORD.md`.

- Archive hash verified **before** extraction; clean room provably free of `.lake` and
  `.olean`.
- Lean 4.28.0 commit `7e01a1bf...` and Mathlib `8f9d9cff...`, both matching the protocol.
  `lake update` did not mutate the pin.
- Protocol Section 9.1 command run verbatim: **exit 0**, `24m47.960s`,
  `Build completed successfully (8034 jobs)`, **zero errors**. The job count
  independently reproduces the manuscript's recorded 8,034.
- **Aggregate root versus explicit targets:** `defaultTargets = ["AristotleLean"]` and
  `AristotleLean.lean` imports only `AristotleLean.Basic`, so **no aggregate root imports
  `PaperI`, `FiniteLPDuality` or `Contrib`**. Coverage is by explicit target enumeration.
  The lakefile documents the `Contrib` isolation deliberately, which positively supports
  the manuscript's byproduct claim.
- **Verbatim axiom output**, auditor's own independent query:

```
'PaperI.paperI_main' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.Split.paperI_main_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.assembly_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperI.Split.residual_duality' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contrib.Submission.covering_packing_duality' depends on axioms: [propext, Classical.choice, Quot.sound]
```

  The supplied `FreezeAxioms.lean` reported the same footprint for all 15 declarations it
  queries, exit 0. **No `sorryAx`, no project-level axiom.**
- Verbatim statements conform to the manuscript, including
  `paperI_main_sharp : forall  G, G.Phi <= G.n^2/6 + G.n/2` and `assembly_sharp` carrying the
  side hypothesis `(1 <= b -> 1 <= p)` that mirrors the manuscript's own case split.
- **Escape hatches in active code: 0** (9 hits, all comment/prose).

## 9. Citation ledger and open-status assessment

Detail: `20_EVIDENCE/I_CITATIONS_STATUS/AUDIT_RECORD.md`.

`SUPPORTED`: [1] Erdős–Ordman–Zalcstein 1993 — publisher record and abstract retrieved;
`n^2/6` and `(1-c)n^2/4` match **verbatim**. [5] Cavers 2005 — full text retrieved; supports
the "broader background" use for which it is cited, and contains no chordal- or
split-specific claim, so it must not be read as supporting one. [6], [7] standard.

`UNVERIFIED`: [2]'s constant `3/16` (bibliographic record exact; 1994 volume
unobtainable). [3] erdosproblems.com (HTTP 403 on every path).

`PARTIAL`: [4] Schrijver — monograph correct, pinpoint `Corollary 7.1g` unverified.

`MISSTATED`: [8] — the cited public repository advertises the obsolete `n^2/6 + n` bound.

**Erdős Problem #81 status: open.** Supported by the verified [1] abstract ("It is unknown
whether this many cliques will always suffice") and corroborated by the most recent
relevant preprint located. The manuscript correctly maintains the chordal-versus-split and
integral-versus-fractional distinctions throughout.

## 10. Prior art and novelty

Detail: `20_EVIDENCE/K_PRIOR_ART_NOVELTY/` (Paper III's record carries the shared corpus).

**No prior result with the same statement was found in the searched corpus as of
2026-08-21.** The most recent relevant preprint located, Ning, arXiv:2608.11536
(30 July 2026), concerns the clique partition/covering difference for general graphs and
does **not** collide; it still cites Erdős–Ordman–Zalcstein as the chordal state of the
art. The Barbados 2025 open-problem collection contains no colliding problem.

This is a **bounded negative search result**, not proof that no such result exists, and it
does not substitute for specialist confirmation.

## 11. Bilingual and artifact QA

Detail: `20_EVIDENCE/L_BILINGUAL_ARTIFACTS/AUDIT_RECORD.md`.

**Protected content is identical** between English and Spanish: display mathematics
(after blanking translated prose, **zero** English-only blocks), equation tags, Lean
identifiers (21/21), citation keys, heading hierarchy (33/33) and protected constants.

**All 39 pages rendered** at 110 dpi. No blank page (minimum ink 0.875%), no anomalous
black area (maximum very-dark 1.135%), no malformed PDF structure. Both PDFs are A4,
unencrypted, produced by LuaTeX-1.24.0, consistent with the recorded LuaLaTeX chain. The
text layer is properly Unicode-encoded, including mathematical alphanumeric symbols such
as `U+1D43A`.

**The failing finding.** `EXT-P1-L-001` (`MAJOR`): the Spanish Markdown duplicates five
blocks that appear once in English — lines 51–65/67–81, 730/732, 742/744, 758–762/764–768
and 776–785/787–794. Two details make it worse than a simple repetition: at 730/732 the
**first** occurrence is orphaned, introducing an equation that does not follow it; and at
742/744 the second copy is **ungrammatical** ("Esto prueba Teorema 1.1." missing the
article). The defect propagates into `_es.tex` and is **visible on the rendered Spanish
pages** — page 3 shows the proof-shape paragraph and its display twice, page 14 shows the
six-item ledger list and the internal-audit paragraph twice. The Spanish PDF is 20 pages
against the English 19, and this accounts for the difference.

The author-side consistency report records `Status: PASS` and "Full-page visual
inspection: PASS". **That internal PASS is unearned on this point.**

## 12. Unresolved findings and residual risks

| ID | Gate | Severity | Summary |
|---|---|---|---|
| `EXT-P1-L-001` | L | **MAJOR** | five duplicated blocks in the Spanish chain, visible in the delivered PDF |
| `EXT-P1-M-001` | M | MINOR | `04_integrity/` is stale v1.1 content; 1 sidecar entry unresolvable; no v1.1->v1.2 diff |
| `EXT-P1-D-001` | D | MINOR | expository gap in the derivation of (4.7); `z = x` substitution unremarked |
| `EXT-P1-E-002` | E | MINOR | Appendix A.2 excess formula unqualified; correct only for `o >= 3` |
| `EXT-P1-J-001` | J | MINOR | "sharp" applied to a bound whose linear term is explicitly not optimized |
| `EXT-P1-I-001` | I | MINOR | `3/16` constant unverifiable from primary sources |
| `EXT-P1-I-002` | I | MINOR | Schrijver pinpoint unverified |
| `EXT-P1-I-003` | I | MINOR | cited public repository advertises the obsolete `n^2/6 + n` |

Counts: `BLOCKER 0`, `MAJOR 1`, `MINOR 7`, `NOTE 0`.

**One challenger finding was tested and rejected.** The challenger reported that the PDF
mathematical text layer was not Unicode-recoverable (~16% replacement characters). The
primary auditor could not reproduce this: `pdftotext -enc UTF-8` to a file yields **zero**
U+FFFD in both languages, and the extracted text contains genuine mathematical Unicode
glyphs. The challenger's figure is attributable to a console-encoding artifact, not to the
artifact under audit. It is therefore **not** recorded as a finding.

## 13. What this audit does NOT establish

- It does **not** establish that Theorem 1.1 is true. It establishes that a determined
  adversarial search over finite domains, a symbolic recheck of every displayed identity,
  and an independent formal reproduction all failed to falsify it.
- It does **not** constitute human peer review.
- It does **not** prove global novelty. The Gate K conclusion is bounded by the corpus
  actually searched and by the auditor's lack of access to institutional databases,
  non-English literature, and two key primary sources.
- It does **not** verify the `3/16` historical constant.
- It does **not** verify that the delivered PDFs were compiled from the delivered TeX;
  they were not recompiled.
- It does **not** cover the six project modules outside the eight protocol build targets.
- It does **not** formally establish that the bespoke `PaperI.Split` structure models
  every split graph; that adequacy step is by inspection and is not formalized in the
  artifact.
- A `PASS` from this audit, had one been reachable, would **not** have closed any release
  gate that explicitly requires an unavailable residual.

## 14. Package manifest and reproduction

`40_PACKAGE/SHA256_MANIFEST.txt`, `40_PACKAGE/PACKAGE_MANIFEST.json` and
`40_PACKAGE/TREE.txt` record final contents. All scripts run from the commands documented
in their gate records and depend only on Python 3.14 with `sympy` and `Pillow`; the Lean
reproduction requires the pinned toolchain. Every referenced log exists as a directly
visible file under `20_EVIDENCE/*/results/`, not only inside the archive.

## 15. Signature, dates and disposition

| Item | Value |
|---|---|
| Auditor | Claude Opus 5 (`claude-opus-5`), Anthropic, operating under this protocol |
| Configuration | primary auditor + adversarial challenger, same model family (disclosed) |
| Audit date | 2026-08-21 |
| Protocol | `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`, SHA-256 `8ba029f4...e505` |
| Target | `preprint_draft_v1.2`, EN Markdown `da7e4819...ee9e` |
| **Verdict** | **`FAIL`** — Gate L, on one `MAJOR` editorial finding; no mathematical or formal defect found |

**Disposition.** Correcting `EXT-P1-L-001` requires editing the Spanish Markdown and then
regenerating `_es.tex`, `_es.pdf`, the page QA and the manuscript sidecar in that order.
Per protocol Section 5.8 that invalidates the downstream artifacts and their hashes, and
therefore produces a **new immutable audit target**. Per Section 6.2 this run must be
closed with its actual verdict; the corrected target requires a **new audit run with new
hashes**, and evidence from the two runs must never be merged into one `PASS`.
