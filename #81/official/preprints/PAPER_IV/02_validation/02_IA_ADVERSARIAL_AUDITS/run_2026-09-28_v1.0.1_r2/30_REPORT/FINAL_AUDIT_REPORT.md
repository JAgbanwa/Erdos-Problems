# External AI adversarial audit — Paper IV v1.0.1 editorial candidate

**Run:** `run_2026-09-28_v1.0.1_r2` · **Handoff revision:** r2 · **Audit date:** 28 September 2026
(10:55–11:30 −03:00) · **Auditor:** Claude Opus 5.5 (`claude-opus-5-5`, Anthropic), fresh Claude Code session,
operated by the author's account on the author's machine.

**Overall verdict: FAIL.** One confirmed, release-blocking attribution defect (F-01, gate E7). The full Lean
rebuild (E4) was therefore **not** run (pre-build checkpoint decision STOP), so formal conformance, the axiom
footprint and the build are **not** certified by this audit. No mathematical error was found in the parts the
auditor could rederive.

This is an AI audit. It is not human peer review, not a proof of universal novelty, and not an authorization to
release.

## 1. Target and identity

Lean source cut `piv-v1.0-f1769273dd2c` (`LEAN_SOURCE_SNAPSHOT_v1.0.zip`
`0a13c01cc4cf0198d5d138082d45b25df4c5ac0684c0ed85e7cc758575f8a7dd`), annex `2847a422…837d`, EN md/tex/pdf
`71417794…` / `0b4b116d…` / `0c17c730…`, ES md/tex/pdf `8448d14e…` / `1b4c8be4…` / `84c49df8…`, internal-audit
ZIP `1911f29e…`. All hashes, sizes, CRCs and member hashes matched at intake and at the final recheck; no
traversal, hidden payload or manifest mismatch (E0 = PASS). The mandated `verify_audit_target.py` reported
`INTAKE_IDENTITY_OK` (178 checks).

## 2. Gate verdicts

| Gate | Verdict | Basis (evidence under `20_EVIDENCE/`) |
|---|---|---|
| E0 identity | **PASS** | `E0/E0_RECORD.md`; intake and final hash sets identical |
| E1 claim semantics | **PASS** | `E1/E1_RECORD.md`, 36-claim map; no semantic defect in the statements |
| E2 independent mathematics | **INCONCLUSIVE** | `E2/E2_RECORD.md`; no defect found; seven proof-critical components only sketched in prose (F-02) |
| E3 formal conformance | **INCONCLUSIVE** | `E3/E3_STATIC_RECORD.md`; static match of all headline types; dynamic part not run |
| E4 Lean / trust boundary | **INCONCLUSIVE (not run)** | `E4/E4_RECORD.md`; stopped by F-01 |
| E5 independent falsification | **INCONCLUSIVE** | `E5/E5_RECORD.md`; 87 checks, 0 failures, all 9 negative controls fail as required; Certo item not done |
| E6 bilingual artifacts | **INCONCLUSIVE** | `E6/E6_RECORD.md`; automated checks pass; full visual QA not done |
| E7 citations and priority | **FAIL** | `E7/E7_RECORD.md`; F-01 confirmed from the literal source |
| E8 audit of the audit | **INCONCLUSIVE (not run)** | `E8/E8_RECORD.md`; reading-order rule and blocker stop |

## 3. Blocking finding F-01 (MAJOR, E7)

**Theorem C's eventual maximum coincides in statement with Okechukwu [15, Theorem 1.1], and the manuscript never
cites that theorem.**

[15] = arXiv:2609.20871**v1** (15 Sep 2026; on 28 Sep 2026 the submission history lists only v1). Its
Theorem 1.1 (p. 2) states: for each s ≥ 0 there are K_s, N_s such that every graph with rsd(G) ≤ s satisfies
cp(G) ≤ Q_s(n) + K_s; for n ≥ N_s the maximum is exactly Q_s(n); equality holds exactly for
(K_{k−s} ⊔ K̄_s) ∨ K̄_{n−k}, with Q_s(n) = ⌊(n+s)(n+s+1)/6⌋ − C(s+1,2).

Against Paper IV's Theorem C (EN §1, l. 81–94; Lean `DefectSharpPublication.rooted_defect_eventual`,
`rooted_defect_maximum`):

* the class is the same (the manuscript's rooted-defect definition and Lean's `RootedDefectAt` are literally
  equivalent to [15]'s rsd(G) ≤ s, empty root included);
* the target is the same, under the same symbol Q_s;
* the quantifier structure (∀s ∃N_s ∀n ≥ N_s) is the same;
* the maximum statement — "the eventual maximum is Q_s(n), also when cliques of arbitrary order are allowed"
  — is [15]'s "the maximum is exactly Q_s(n)" (cp is the unrestricted parameter);
* the lower witness is the same graph family (E.3 = [15, Lemma 2.5]);
* the only statement-level difference is that Paper IV bounds c₄ (pieces of order ≤ 4) instead of cp, a genuine
  formal strengthening of the upper bound (AUDITOR_INFERENCE: [15]'s localization uses a cutoff L = L(ε), so
  [15] does not state the c₄ form). [15] is stronger in classifying equality graphs and in its all-orders bound.

The manuscript cites [15] only for Cor 1.2 (chordal case), Thm 1.3 and Cor 5.5 (stability), and for mechanisms
(Thm 3.3, Lemma 3.4, Lemma 4.1). The abstract (l. 28) and the statement of Theorem C carry no citation of [15];
§8.1 says only that "[15] studies rooted simplicial defect", that Theorem C "uses that class", and that
"comparing mechanisms is not a priority claim for the extremal formula". It does not tell the reader that
[15, Theorem 1.1] already proves the Q_s(n) maximum. The Spanish edition has the same text. By contrast, the
manuscript does state that [5] proves Theorem B's eventual maximum.

Under request §5 the auditor had to determine whether Theorem C coincides in statement with a result of [15] and
whether §8.1 matches that finding. The coincidence is confirmed and §8.1 does not match it. Because Theorem C is
a headline theorem, this is treated as a material attribution defect. Under request §4.1–4.2 such a defect is a
blocker.

*Minimal repair (proposal only, not applied):* at Theorem C, in the abstract/§1 and in §8.1, credit
[15, Theorem 1.1] with the fixed-s eventual maximum Q_s(n) (with classification and an all-orders cp bound); credit
[15] with the rooted-defect definition and the notation Q_s; present Paper IV's contribution for s > 0 as the
order-≤4 (c₄) upper bound and the independent formal proof. A corrected target needs a new revision ID and
hashes, and the resumed run must redo E7 and E6 before E4.

## 4. Other findings

| ID | Sev. | Summary |
|---|---|---|
| F-02 | MODERATE | Seven proof-critical components appear in the prose only as sketches: (5.4)/(5.7) regularization bounds; C.2 discard counts and fibre lower bounds; C.3 Table C.1; E.1 normalization, (E.2b), (E.2d); D.1 frame constructions. Their correctness rests on Lean, which this audit did not run. |
| F-03 | MINOR | Cipollini's partial result n²/6 + o(n²) (Erdős-problems claim 2026-08-10; cited by [5]) is not cited. |
| F-06 | MINOR | Lean identifiers in both PDFs are broken across lines without any marker and set in roman type. |
| F-07 | MINOR | The EN Markdown contains a stray `\Needspace{20\baselineskip}` that the ES Markdown does not. |
| F-04, F-05, F-08–F-12 | OBS. | #81 is listed as OPEN on erdosproblems.com; [15, §7] asks for exactly the quantitative stability that Thm 6.1 gives for s = 0; `.aux` files are missing from the manifest; the Prop 6.3 Lean wording is weaker than the prose (the claim follows by combining it with another declaration); Lean's Cor 6.1a is stronger (any τ ∈ ℚ); 16 and 48 are tight for account (6.7); the path of [5]'s FORMALIZATION_STATUS.md is `lean/`. |
| F-13 | INFO | Model-family overlap (see §7). |
| F-14 | CORR. | Auditor self-corrections: one timestamp and one false-positive font check. |

Full list: `FINDINGS.csv`.

## 5. What was verified, stated separately

* **Mathematical rederivation (E2).** Rederived by the auditor: the gain/loss identity; Lemmas 3.3–3.4 (two
  quotas, pairing, marks); Corollary 3.5; Lemma 4.1 (mixed transport, twin potential, existence of steps,
  chordality); Lemma 4.2 and the descent (no circularity); Prop 4.3; Lemma 5.1 and Prop 5.2 (except (5.4)/(5.7));
  Table 2 and both phases; Lemma 5.3 and (5.16); Cor 5.4; §§6.1–6.7; Theorem A with the tower propagation;
  Theorem 6.1 (γ = η₀/4, 16δ); Corollary 6.1a ((6.7b), 48δ, root fixed before Q); Cor 6.2; E.2–E.3; §8.3.
  **No defect found.** Components known only through Lean or imported papers: the Paper III nibble; the
  regularity and cleaning counts in RC01; Table C.1; the regularization constants (5.7); E.1's budget; the
  design frames of D.1.
* **Manuscript/Lean semantic match (E3, static only).** The literal Lean headers and definitions match the
  manuscript for Theorems A, B and C; the maximum; Theorems 3.1 and 5.0; Cor 3.5; the dichotomy; Cor 5.4;
  Thm 6.1; Cor 6.1a; Cor 6.2; the optimality of 1/6; the tower; Prop D.2; and the annex (8.1a). Edge partitions
  are exact; chordality is the standard chord condition; M(n) is ℕ division; the root precedes every partition;
  Q is unrestricted in Cor 6.1a; γ > 0 is an explicit constant. The textual sweep found no code-level escape
  hatches. The elaborated types are **not** kernel-confirmed.
* **Isolated project build against a shared dependency cache (E4).** **Not performed.** Only the environment
  was checked: toolchain present, all nine dependency HEADs equal to the frozen pins, no tracked changes.
* **Axiom footprint.** **Not verified** by this audit.
* **Bilingual PDF QA (E6).** Hashes and page counts match (50/51); fonts are embedded; no replacement glyphs or
  unresolved references; all 158 display-math blocks are identical in EN and ES; key constants agree across
  md/tex and EN/ES; the status language is current. Page-by-page visual inspection was **not** completed.
* **Source/provenance review.** The freeze contains no `Erdos81.*` names (static reading only). Provenance of
  Paper II/III code, Mathlib regularity and Behrend, and the use of Aristotle, Claude, ChatGPT/Codex, Certo and
  Jacobian is disclosed in the manuscript. Jacobian belongs to the group behind [5].
* **Literature scope (E7).** [15] v1 (only version), [5] at `cbde8a0a…` (= current `main` HEAD), the
  erdosproblems page and forum threads, the lean-pool PRs, the Zenodo DOIs, [16], five arXiv API queries and one
  web search. No MathSciNet/zbMATH access; [1] was not retrieved in primary form.

## 6. Stop reason and deferred checks

The run stopped at the pre-build checkpoint on F-01 (`00_CONTROL/PREBUILD_CHECKPOINT.json`, decision STOP). The
dynamic checks deferred to E4 are listed there: rebuild of 504 modules in an isolated directory without author
oleans, 13 target exits, `#print axioms`, elaborated `#check`, 195 exports, the author's audit-target logs, and
the annex overlay. The Certo re-examination (E5), full visual PDF QA (E6) and E8 are also pending.

## 7. Independence and limitations

* The auditor model belongs to the family (Claude) that the manuscript says was used "to explore and check
  arguments and to prepare the manuscript". This was disclosed at intake as probable and confirmed during
  reading. This is a same-family, fresh-session review, not a different-model review.
* The audit ran on the same machine and user account, with the same dependency cache. The reading restriction
  is operational, not OS-enforced; compliance is evidenced by `00_CONTROL/INPUT_ACCESS_LOG.csv`. No excluded tree
  (`ar_*`, `handoff_*`, Aristotle trees, Paper V, editorial history, credentials) was accessed. No internal or
  editorial verdict, derivation or test conclusion was read.
* The only author script used was `verify_audit_target.py`, as mandated.
* No TeX engine is installed. The PDF of this report was rendered from its Markdown source with PyMuPDF, not
  compiled from the TeX file (installing a TeX engine would need owner approval). The TeX source is provided.

## 8. Recommendation (authority boundary: recommendation only)

Hold release of v1.0.1. Correct the attribution of Theorem C (F-01). Consider F-02 (either expand the prose or
label those steps as checked only in Lean) and F-03. Issue a new revision ID, then resume with E0 → E7/E6 → E8 →
pre-build checkpoint → E4. Human expert review of the LEAN_ONLY components remains necessary in any case.
