# External Adversarial Audit Report — Paper III (v0.9.5)

*Linear-Error Clique Partitions of Split Graphs* (Erdős #81, Paper III), review
version v0.9.5. Engagement per `MANIFESTO/AUDIT_MANDATE.md`: adversarial stance,
Lean 4 formalization **out of scope**, verdicts earned by reproducible evidence only.

Auditor: external adversarial audit agent (Claude, Anthropic model `claude-fable-5`),
2026-07-21. Package audited: SHA-256 record in `received_inputs.sha256` (56 files;
all 54 entries of the package's own manifest verified bit-identical on receipt).

---

## 1. Executive verdict

# **PASS_WITH_OBSERVATIONS**

No counterexample, no overstated axiom, no circular or missing dependency, no
statement↔claim mismatch, and no arithmetic error in a load-bearing step was found —
under adversarial testing that exceeded the internal audit's ranges by one to seven
orders of magnitude and used independent methods throughout. The observations are:
one minor overstatement of "self-containment" (classical Dirac/Turán/χ'(K_t) inputs
are also load-bearing but unproved in the paper), three minor presentational issues,
and three minor script defects in the internal audit (none verdict-affecting).

**Scope reminder:** Theorem 1.1 and Corollary 1.2 are *conditional on AX1 and AX2*
(verified faithful to the published literature, not stronger). Their unconditional
content — Proposition 10.1, Theorems 3.1/4.2, Lemmas 4.1–7.1, Appendices B/D — is
what a finite audit can attack, and all of it survived. A computational audit cannot
*prove* the ∀-statements; it can only fail to break them while verifying every
finite/closed-form component exactly. Qualified human expert review of the two
asymptotic inputs' journal texts and of the global assembly remains advisable before
publication (see §5).

## 2. Per-claim verdict table

| Claim | Statement | Verdict | Evidence |
|---|---|---|---|
| C-1 · Theorem 1.1 | Φ(G) ≤ n²/6 + Cn (relative to AX1, AX2) | **VERIFIED_WITHIN_SCOPE (conditional)** — assembly reconstructed, acyclic, every finite ingredient verified; asymptotic inputs faithful | Blocks A2, B, C, D |
| C-2 · Corollary 1.2 | cp(G) ≤ n²/6 + Cn | **VERIFIED_WITHIN_SCOPE (conditional)** — follows from (1.1), which is immediate | Block A1 |
| C-3 · Prop 10.1 (i) | p≥36, 0≤s≤6√p ⟹ Φ ≤ n²/6+2n | **VERIFIED_WITHIN_SCOPE** — analytic chain machine-verified exhaustively for 36≤p≤600 (D20) + instance certificates at p≤100 (C4) | D20, C4 |
| C-3 · Prop 10.1 (ii) | p≥2304, 6√p≤s≤p/8, deg cond ⟹ Φ ≤ n²/6 | **VERIFIED_WITH_RESIDUAL_RISK** — every inequality of the §9.3 chain re-derived and grid-verified (D11–D18); true-scale instance certificates at p=2304, s=288 (2.44M-triangle packings, exact counters); residual: instance testing is existential, the ∀-claim rests on the (verified) analytic chain | D11–D18, C4 |
| C-4 · Theorem 3.1 | ν₃*(H(p,q,d)) = F(p,q,d) | **VERIFIED_WITHIN_SCOPE** — exact rational sandwich certificates (primal orbit LP + feasible dual covers) on 49,079 instances incl. p up to 10⁴, q up to 4p; independent raw exact rational simplex (no orbit reduction) on 266 small instances: all match. 0 failures / 49,345 total | C1, D02/D03 |
| C-5 · Lemma 4.1 | ν₃*(G) ≥ (1/q)ΣF(p,q,dᵢ) | **VERIFIED_WITHIN_SCOPE** — exact simplex on 153 arbitrary-profile graphs, 0 violations (78 tight) | C7 |
| C-6 · Theorem 4.2 | ν₃* ≥ T + μ(α)p² − p/4; core (4.5) | **VERIFIED_WITHIN_SCOPE** — 2,497,464 exact-integer checks (exhaustive p≤150; random p≤10⁹), all three branches; residuals re-derived symbolically incl. exact square completions (D04–D07) | C2, D |
| C-7 · Lemma 5.1 + Cor 5.3 | ν₃ ≥ (1/q)ΣC(dᵢ,2); Φ ≤ n²/6+p/2+(s²−6s+3)/12 | **VERIFIED_WITHIN_SCOPE** — 443 applicable instances confirmed by packing certificates + 40-instance exact-ν₃ sample; (5.2)/(5.3) algebra proved as identities (D09/D10) | C3, D |
| C-8 · Lemma 5.2 | double-factor inequality (5.4) | **VERIFIED_WITHIN_SCOPE** — 443 applicable instances (certificates + exact sample); V computed exactly per instance | C3 |
| C-9 · Lemma 6.1 | polarization V ≥ ((2p−3m−1)/4)Σ\|SᵢΔSⱼ\| | **VERIFIED_WITHIN_SCOPE** — counting identity exhaustive at p=7; V-identity + inequality on 400 random exact instances | D21 |
| C-10 · Lemma 7.1 | reserved-gain shifted-center (7.6) | **VERIFIED_WITHIN_SCOPE** — 525 applicable (R, instance) pairs confirmed (hypotheses (7.1)–(7.2) checked per instance); assembly identity (7.6) reconstructed and machine-verified (D23 — the paper does not display it) | C3, D23 |
| C-11 · Appendix B | Odd(J)=O, \|E(J)\|≤p−1, Δ(J)≤2 | **VERIFIED_WITHIN_SCOPE** — exhaustive 65,534 cases (p≤16, all even O) | C6 |
| C-12 · Appendix D | self-contained list edge coloring | **VERIFIED_WITHIN_SCOPE (logical audit)** — D.1–D.3 read line-by-line: kernel lemma, Gale–Shapley, inline König (bipartite odd-path parity correct), out-degree ≤ Δ−1, kernels=stable matchings; hypothesis check \|L\|=b−tᵢ≥max{ρ,u}≥Δ correct. No computational test performed (coverage note §5) | A3 |
| C-13 · Sharpness §10.2 | K_p∨K̄₂ₚ attains n²/6+n/6 | **VERIFIED_WITHIN_SCOPE** — ν₃=C(p,2) certified both directions, p≤24; closed form is a polynomial identity (D22); no audited instance beat 1/6 | C3/C5, D22 |
| C-14/15/16 · Addenda | Cor 10.4 / 10.4b / 12.2 | **VERIFIED_WITHIN_SCOPE** — restatements/specializations of C-4/C-1/C-3; no new mathematical content; Cor 10.4's extended range (q≥0, all d) explicitly covered by C1's grid | C1, A1 |
| AX1 · Theorem 2.1 | ν₃*−ν₃ = o(\|V\|²) uniform | **VERIFIED_WITHIN_SCOPE (faithfulness)** — verbatim in Yuster arXiv:math/0305350 (families ⊇ fixed K₃, attributed to Haxell–Rödl); not stronger than literature; used only in bulk | B1, B3 |
| AX2 · Theorem 2.3 | triangle-divisible, δ≥(0.9+ε)\|V\| ⟹ decomposition | **VERIFIED_WITHIN_SCOPE (faithfulness)** — verbatim in Dross arXiv:1503.08191 abstract; divisibility stated in full (degrees even + \|E\|≡0 mod 3); used only in sparse | B2, B3 |

## 3. Findings

Severities per `DELIVERABLE_SPEC.md`. Full machine-readable list: `findings/FINDINGS.csv`.

**Blocking: none. Major: none. Minor: 6.**

1. **A-04 (minor).** §2.4's "Sections 5–7 and Proposition 10.1 depend on no external
   theorem" and §11.3's "no external theorem whatsoever" overstate: the classical
   1-factorization χ'(K_t) (eq. 2.2, stated without proof) is load-bearing for
   Lemmas 5.1/5.2/7.1 and hence Prop 10.1; §8 additionally uses Dirac and Turán.
   These are classical, constructive facts (this audit constructs the factorizations
   explicitly), and LEDGER.md lists them openly — but the wording should say
   "no external theorem beyond classical finite facts (χ'(K_t), Dirac, Turán)".
2. **A-05 (minor, presentational).** Figure links in the review md point to a
   directory not shipped at that relative path.
3. **A-06 (minor, reproducibility).** §11.6's "46,390 + 91 checks" and Appendix C's
   script names are not reproducible from this package (different audit generation
   shipped). No logical weight (the paper states no computation is a premise).
4. **E-02 (minor).** Internal block02's docstring advertises an "(EXACT)" second
   verification that is not implemented.
5. **E-03 (minor).** Internal block02 is float-with-tolerance (1e-7) by design —
   masking-capable; did not bite (this audit's exact certificates agree).
6. **E-04 (minor).** Internal block04 ignores the CBC solver status; fail-safe
   direction only (cannot create a false PASS). Status-checked re-runs agree 40/40
   with this audit's independent branch-and-bound.

**Corrections against the auditor (recorded symmetrically):** two initial defects in
this audit's own Block D script (wrong guessed square-completion center; malformed
D16 check) were found and fixed during development; one Block C4 certificate
construction (mixed two-center) was initially too weak and produced a spurious FAIL
that was diagnosed as an auditor-side construction deficit, not a paper defect, and
repaired following the paper's own mechanism (after which it PASSED with slack 1,397).

## 4. What was attacked and how (summary)

- **Block A:** both documents read in full; 18 ledger nodes compared statement-by-
  statement; DAG rebuilt from the proofs; 35 mechanical anchors; external-theorem
  census with line numbers. No mismatch; no circularity (§8's degree bound is
  hypothesis-passing, not circular).
- **Block B:** AX1/AX2 checked against primary arXiv statements (verbatim sentences
  located); citation metadata verified; usage localization confirmed mechanically.
- **Block C:** ~2.61 million adversarial instances, zero violations:
  C1 49,345 certified equalities ν₃*=F (two independent exact methods: 49,079
  sandwich certificates + 266 raw exact simplex);
  C2 2,497,464 margin checks (p≤150 exhaustive, p≤10⁹ random, all-integer);
  C3 821 instances / 1,854 bound checks with verified packing certificates + forced
  exact-ν₃ refutation sample; C4 true-scale corridor certificates incl. p=2304
  (window degeneracy [288,288] at threshold confirmed); C5 sharpness both directions;
  C6 Appendix B exhaustive; C7 Lemma 4.1 exact simplex.
- **Block D:** 38/38 algebra checks with a self-written exact polynomial engine
  (no CAS), including certificates the paper leaves implicit (branch-3 square
  completion with boundary case; Lemma 7.1 assembly identity D23).
- **Block E:** internal audit reproduced bit-identically (4/4 blocks); its scripts
  read adversarially (3 minor defects); its shared formulas stress-tested at
  boundaries (0 mismatches on 20k+ cases).

## 5. Coverage statement (honest boundary)

**Tested:**
- Every finite/closed-form claim (C-4…C-13) with exact arithmetic, at ranges
  exceeding the internal audit's: p≤150 exhaustive for (4.5) (internal: p≤48);
  p≤40 full grid + p≤10⁴ sampled for ν₃*=F with q up to 4p (internal: p≤8, q≤8,
  float); instance families with 9 adversarial profile classes (internal: 3).
- The §9.3/§10.5 corridor chains: every inequality re-derived independently and
  machine-verified, including exact grids at p=2304…2339 and up to 10⁵ (D15).
- Prop 10.1 at true scale: explicit packings at p=2304 (n=6624, up to 12.2M edges),
  edge-disjointness verified by exact counters.
- AX1/AX2 faithfulness at the primary-abstract level; usage localization.
- The internal audit: full re-run + code review + boundary stress.

**NOT tested / limitations:**
- The Lean 4 formalization — **excluded by mandate**; nothing here relies on it.
- The truth of AX1/AX2 themselves — axioms by engagement design; only faithfulness
  to the literature was audited, and for Haxell–Rödl (Combinatorica) and BKLO
  (Adv. Math.) the paywalled journal texts were verified at abstract/secondary level
  only (the two decisive sentences appear verbatim in the Yuster and Dross arXiv
  abstracts, which are primary).
- ∀-claims over infinite families (Thm 1.1, Prop 10.1, lemmas at all orders) cannot
  be established by computation. For these, what was verified is: (a) the complete
  analytic chains, step-by-step, in exact arithmetic; (b) adversarial instances,
  which all confirmed. The global Theorem 1.1 additionally rests on the two
  asymptotic inputs and on the regime-assembly logic (verified by reading, A2).
- Appendix D was audited logically (line-by-line), not computationally.
- Part (ii) instance certificates used common/two-center profiles; fully generic
  profiles at p=2304 (requiring the IRQ list-coloring family) were not instantiated —
  the analytic chain covering them is verified (D15–D18, C3's Lemma 7.1 tests at
  small scale exercise IRQ hypotheses (7.1)–(7.2) directly).
- No independent literature/novelty search was performed (out of the mandate's scope).

**Residual risks:** LOW overall. The single locus of non-elementary trust is the two
asymptotic inputs (paywalled full texts; abstract-level verification) — flagged
`VERIFIED_WITH_RESIDUAL_RISK` at the source-inspection level, standard for these
well-known results.

## 6. Recommendation

Maintain the paper's claims as stated, with the wording fix of Finding A-04 (list the
classical inputs explicitly), the presentational fixes A-05/A-06, and the internal-
audit script repairs E-02/E-03/E-04. A qualified human review of the two paywalled
journal statements (Combinatorica 21:13–38; Adv. Math. 288:337–385) before the v1.0
preprint would close the last source-verification gap. This report does not modify
any authoritative gate record.

## 7. Reproduction appendix

Environment: `ENVIRONMENT.md`. All scripts are deterministic (fixed seeds), write
full logs to their block's `results/`, and exit nonzero on any failure.

```
python blockA_faithfulness/check_census.py
python blockC_counterexample_search/c1_nu3star_certificates.py    # ~1-2 h
python blockC_counterexample_search/c2_margin_grid.py             # ~5 s
python blockC_counterexample_search/c3_lemmas_packing.py          # ~30 s
python blockC_counterexample_search/c4_corridor.py                # ~1 min
python blockC_counterexample_search/c6_appendixB.py               # ~1 s
python blockC_counterexample_search/c7_cloning_lemma41.py         # ~10 s
python blockD_algebra_rederivation/rederive_algebra.py            # ~30 s
python blockE_audit_the_audit/e3_boundary_stress.py               # ~30 s
python build_deliverable.py                                       # certificates+zips+manifest
```
Internal-audit re-run (Block E1): copy `OUR_INTERNAL_AUDIT/`, move each block's
`results/` aside, run the four `verify_*.py`, diff outputs (no timestamps inside).
