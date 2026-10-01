# External AI adversarial audit of Paper IV v1.2

**Run:** `run_v1.2_r1`. **Handoff revision:** v1.2-r1. **Manuscript version:** 1.2
(`piv-v12-manuscripts-2451d43bface`). **Lean source cut:** `piv-v12-fb459343d234`.
**Dates:** 2026-09-30, 12:21–22:10 UTC, started at the owner's request in chat. **Auditor:** Claude Opus 5.5
(`claude-opus-5-5`, Anthropic), a fresh Claude Code session on the owner's machine. Some bounded sub-tasks
were delegated to same-family subagents (§7).

**Overall verdict: INCONCLUSIVE.** No mathematical error, identity defect, attribution blocker or
formal-reproduction failure was found. The isolated rebuild compiled all 607 modules and the 50-module annex
with only the standard axioms. Its 607 `.olean` files are byte-identical to the author's. The overall
verdict is still not PASS, because gate E2 is INCONCLUSIVE. Four summarized derivations of Appendix A.2 are
judged **REQUIRES_EXPANSION** (A2-3, A2-4, A2-5, A2-6). For A2-3, the manuscript's own description of the
cleaned rounding system does not give the per-edge feasibility it asserts. These are gaps in the
human-readable proof, not counterexamples; the formal proofs cover them.

This is an AI audit. It is not human peer review, not a proof of universal novelty, and not permission to
publish. It is sent to the owner for the release decision.

## 1. Target and identity (E0 = PASS)

All bound hashes, byte counts, ZIP CRCs and member identities match `AUDIT_TARGET_v1.2.json` (sha256
`d1eb542d…fdc29`); the recheck at 22:04 UTC is identical. The source ZIP, the source directory and the
manifest agree: 615 = 615 = 615 entries, of which 607 are `.lean` modules. The toolchain is v4.28.0 and
Mathlib is at `8f9d9cff…`. The nine shared packages are at their frozen pins, with no tracked edits. The
19 targets equal FREEZE_SCOPE, and their closure is all 607 modules. The manuscript manifest (105 files)
and ZIP (106 members) match, and the six MD/TeX/PDF files match, with 68 (EN) and 69 (ES) PDF pages. The
author evidence (1238 files) matches its seal. The annex (38 files plus manifest) and the v1.0 base
configuration match. The source identity, the two-segment author-build evidence and the manuscript identity
were kept separate.

## 2. Gate verdicts

| Gate | Verdict | Basis (under `20_EVIDENCE/`) |
|---|---|---|
| E0 Identity | **PASS** | `E0/` intake and final records identical |
| E1 Claims | **PASS** | `E1/E1_RECORD.md`: A, B, C, C′, 6.1–6.6, 6.3a, F.3a, G.1 mapped to literal Lean types; all-order / eventual / fixed-defect / uniform / sublinear / unrestricted / actual-vs-resized root kept distinct |
| E2 Mathematics | **INCONCLUSIVE** | `E2/E2_RECORD.md`: 56-component ledger; no error; A2-3/4/5/6 REQUIRES_EXPANSION |
| E3 Conformance | **PASS** with finding X-27 | `E3/E3_STATIC_RECORD.md` (static + dynamic) |
| E4 Formal reproduction | **PASS** | `E4/E4_RECORD.md`: 607/607 + 50/50, 19 targets, own axiom/cone checks, negative control |
| E5 Falsification | **PASS** (finite scope) | `E5/`: 24 predeclared exact tests PASS; all negative controls rejected; Certo certificate audited (E8) |
| E6 Bilingual artifacts | **PASS** with findings | `E6/`: all 137 pages viewed; math, numbers and qualifiers agree; 1 MODERATE, 4 MINOR |
| E7 Attribution | **PASS** with MINOR findings | `E7/`: r2 blocker resolved; [15], [22], [5] checked against cited versions (no later versions on 2026-09-30) |
| E8 Internal evidence | **PASS** with findings | `E8/`: two-segment evidence consistent and corroborated by E4; disagreement with the internal A.2 verdicts |

## 3. Main findings (full list: `FINDINGS.csv`)

**MODERATE**
- **X-01 (E2, A2-3):** Theorem 3.1, App. C.2 l.1606–1615. Per-edge feasibility (load ≤ 1) of the cleaned
  mixed system. Following the prose (weights ψ_H/b_H with b_H ≥ a₃t³, ψ_H ≤ t², at most t copies per edge)
  gives a load bound of 1/a₃, not 1. The Lean proof removes roots whose copy count deviates two-sidedly from a
  reference value, using a Chebyshev second-moment bound (`RC01DeviationCleanup`, `RC01CleanFiber`), and then
  uses the resulting upper spread bound. The manuscript never states this step.
- **X-02 (E2, A2-5):** App. E.1 / E.4. The normalization estimates that carry the fixed-defect constructor
  (Theorem C for s > 0, i.e. the order-four strengthening relative to [15], and Theorem C′) are asserted, not
  derived.
- **X-03 (E2, A2-6):** (E.2d), the joint use of rooted defect on up to 2s+2 exceptions, is only outlined.
- **X-04 (E6):** the Spanish edition uses "holgura" for the margin Δ(G) (ES l.150, the §3 title at l.269,
  l.303). Its own l.159 reserves "holgura del selector" for a different notion and warns against confusing
  the two.
- **X-27 (E3/E4):** Table 9 cites `E32.cp_classification_of_theoremCPrimeC` for the unrestricted equality
  classification (6.18). That declaration, and `E32.ref15Theorem11_of_theoremCPrimeC`, depend through
  `E32.theoremC_at` on the historical Alon–Shapira chain (`AlonShapira.lemma_4_2`, `AFKS.strong_regularity`,
  `EditRoute.fixedL4Localization_unconditional`, …). §7, E.2 and [23] present that chain as historical and not
  selected. There is no correctness impact: the chain is fully proved with standard axioms. The provenance
  statement is incomplete.

**MINOR** — X-05 A2-4 (Table C.1 schedule functions undefined in the text; affects only the explicit
threshold values). X-06 Table 4/l.1257 misdescribe [15]'s use of K₃…K_L. X-07 l.1259 calls the c₄
hypothesis "stronger" when it is the weaker one. X-08 l.1261 "order-four version of (1.5)" (the proof in
[15] already uses L = 4). X-09 the abstract and Theorem A omit [15, Cor. 1.2] as a source of the all-orders
chordal bound (it is credited in §1). X-10 provenance note for [5] / Jacobian [14]. X-11 l.314 "reduced from
10^32" (whose value?). X-12–X-15 typesetting and translation (Lean identifiers without the arrow; Spanish
subscripts in EN; A.1 "literal" excerpt printed `{{v : V}}`; English words left in ES). X-16 A.2 cites a
non-existent "§3.2". X-28 both build runners' sorry-detection pattern does not match Lean 4.28 output
(mitigated: no sorry anywhere).

**Observations** X-17…X-25, X-29 (e.g. Prop 6.3a is existential in Lean; the Lean τ is any real; lakefile
residue; 461 records = 314 `#print axioms` + 147 custom lists; byte-identical oleans).

## 4. What was verified, stated separately

- **Mathematical rederivation (E2).** Rederived by the auditor: the loss budget; Lemmas 3.3 and 3.4;
  Corollary 3.5; Lemma 4.1 (transport, twin potential, Dirac step, chordality); Lemma 4.2 and the descent,
  including the 4·10¹² calibration; Prop 4.3; Lemma 5.1; Prop 5.2 with (5.3), (5.4), (5.7); both phases
  with (5.5)–(5.14); Lemma 5.3; (5.16); Theorem B/A assembly; §§6.1–6.4; Theorem 6.1 and Cor 6.1a/6.2;
  Theorem C′ deletion/reinsertion and the window invariant; the E.4 account combination (the terminal
  constant 40000(s+1)³); CoreCliqueAlternative; TemplateDistance; Cor 6.3 with the parabola;
  Prop 6.3a; the low-star branch of Prop 6.4; Lemma F.3a and Cor F.3b; (F.6); E.1 (E.2)–(E.2e) and the
  three-case arithmetic given (E.2d); E.2–E.3; the F.5 case assembly; D.1–D.3; Prop G.1. Imported with
  attribution: the Paper III nibble; LP duality (Paper I); [15, Lemma 3.1]; [22]'s set-colouring, section and
  gluing lemmas; STS existence; Behrend; Haxell–Rödl context. Formally inspected only: the (5.1a) middle and
  third packings, the C.3 schedule, the normalization estimates, (E.2d), list hosting, (F.7)–(F.10), and
  the E35 tower comparisons.
- **Conformance (E3).** All headline statements match their literal Lean types, statically and
  dynamically. The 224 exports compile through `import PaperIV`. There are exactly 19 targets.
- **Isolated build with shared dependencies (E4).** A fresh project with no author objects, compiled by the
  auditor's own runner. 607/607 modules plus 50/50 in the annex. The shared cache was verified unchanged
  (113 821 files).
- **Axiom footprint.** The auditor's own cone traversal over 50 public declarations found only {propext,
  Classical.choice, Quot.sound}, no `sorryAx` and no `Erdos81` root. The named Alon–Shapira removal lemmas
  are absent from the public Theorem C / C′ / 6.5 cones, but present in the cp-classification cone (X-27).
- **Falsification (E5).** 24 predeclared exact tests with exact LP certificates. They include exhaustive
  small-graph checks of F.3a, Prop 6.4, (F.7), (F.9), D.2, D.3 and Prop 6.3a. The Certo certificate was
  audited by its specification: it is an exact clique partition of K₃∨I₃ into 6 cliques, and it certifies
  feasibility only; optimality follows from (6.1).
- **Bilingual QA (E6).** EN/ES MD and TeX were compared (1988 math segments identical up to 4 translated
  `\text{}` words), and all 137 PDF pages were viewed.
- **Attribution (E7).** [15] v1, [22] v1 and [5] at `cbde8a0a` were read literally; erdosproblems #81 is
  still OPEN. The r2 finding F-01 is resolved in v1.2. No claim of universal b = 0, a universal linear
  mixed gap, unqualified superiority or a practical threshold was found.
- **Independence limitations.** See §7.

## 5. A.2 exposition verdicts (separate from formal correctness)

| Item | Verdict | Reason |
|---|---|---|
| A2-1 regularization (5.4), (5.7) | ACCEPTABLE_SUMMARY | rederived with wide margins; the source of 113a/64 deserves one sentence |
| A2-2 discard counts (3.10) | ACCEPTABLE_SUMMARY | standard regularity bookkeeping; the charging argument is given |
| A2-3 fibres and normalization | **REQUIRES_EXPANSION** | the per-edge load bound needs the unstated two-sided deviation cleanup (X-01) |
| A2-4 Table C.1 / tower | **REQUIRES_EXPANSION** (minor impact) | schedule functions undefined in the text; only explicit values affected |
| A2-5 normalization before the terminal | **REQUIRES_EXPANSION** | estimates asserted; they carry Theorem C (s>0) and Theorem C′ |
| A2-6 (E.2b), (E.2d), three cases | **REQUIRES_EXPANSION** | (E.2d) only outlined |
| A2-7 Bose/Skolem frames | ACCEPTABLE_SUMMARY | classical designs; supplement not used by Theorems A–C |

The internal audit rated all seven items ACCEPTABLE_SUMMARY "for the paper accompanied by its sources".
This audit disagrees for four items. The mandate asks about adequacy for a human referee, and neither the
disclosure in A.2 nor a successful build settles that.

## 6. Attribution (E7) — summary

v1.2 credits [15, Theorem 1.1] with the rooted-defect class, Q_s, the eventual unrestricted maximum and the
equality family, and presents Theorem C's contribution as the order-four upper bound. It also credits
[15, Lemma 3.1] (signed star), [22] (removal, with its adaptations listed) and [5] (eventual chordal bound).
The literal text of [15] v1 confirms the manuscript's account of the cutoff L (chosen from ε in
Theorem 3.3; L = 4 only for (1.5)), of Corollary 5.5 and of the question in §7. Only v1 of [15] and [22]
exists, and [5]'s HEAD and PDF are unchanged since the cited commit. The remaining issues are MINOR
(X-06…X-11). The provenance item X-27 is a conformance issue, not a missing citation: [23] is cited.

## 7. Independence and limitations

- **No cross-family independence.** The auditor model is Claude, the family the manuscript says was used
  to explore and check arguments and prepare the manuscript. It is also the same model as the r2 auditor.
  The delegated subagents (E5 implementation, E6 page inspection, E7 retrieval) were the same model. The
  lead auditor wrote the E5 predeclaration, reproduced the scalar and integer E5 runs, and spot-checked the
  E6 and E7 findings against the literal sources.
- **Same machine and shared pinned third-party oleans.** This is not separate-machine or clean-room Mathlib
  reproduction, and no `leanchecker` kernel replay was performed.
- The reading restriction was operational. Access is logged in `00_CONTROL/INPUT_ACCESS_LOG.csv`.
  Incidental exposures (directory file names, and another session's process command line naming an `ar_*`
  path) are recorded; no excluded file was opened. Author PASS statements seen at intake are disclosed
  exposure, not evidence.
- Literature coverage: arXiv, Crossref, the GitHub API, erdosproblems.com and one web search; no
  MathSciNet/zbMATH/Scholar. This is not a complete novelty search.
- Auditor corrections C-01…C-07 and process deviation AUD-P1 (a lost supplementary first-run output in E5)
  are preserved in `00_CONTROL/CORRECTIONS.md`.

## 8. Recommendation (authority boundary: recommendation only)

1. Before release, expand the written proof for A2-3 (state the two-sided deviation cleanup and the
   per-edge load computation), A2-5 (state the normalization lemmas and their estimates) and A2-6 (prove
   (E.2d)). Either define the C.3 schedule functions or label Table C.1 as formally verified numerics only
   (A2-4).
2. Fix X-27: route `E32.theoremC_at` through the explicit E34 theorem, or disclose that the cp-part of
   (6.18) and the formal [15, Thm 1.1] derivation use the historical Alon–Shapira chain.
3. Correct X-04 (Spanish "holgura") and the MINOR wording, attribution and typesetting items.
4. Any corrected text or source needs a new target binding and revision ID. After that, rerun E0, E2 for
   the expanded items, E3/E4 if sources change, and E6/E7 for changed text.
5. Human expert review of the RC01 cleanup and the fixed-defect normalization remains advisable in any case.
