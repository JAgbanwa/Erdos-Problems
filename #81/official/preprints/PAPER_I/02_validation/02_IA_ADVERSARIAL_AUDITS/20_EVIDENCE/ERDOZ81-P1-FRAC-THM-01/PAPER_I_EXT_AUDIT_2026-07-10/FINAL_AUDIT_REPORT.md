# External Adversarial Audit — Paper I (Split-Graph Fractional Triangle-Packing Theorem)

**Audit ID:** PAPER_I_EXT_AUDIT_2026-07-10
**Date:** 2026-07-10
**Auditor:** independent external AI adversarial auditor (adversarial-math-audit protocol)
**Request spec:** `PAPER_I_EXTERNAL_FULL_AUDIT_REQUEST_SPEC.md`
**Target (only):** Theorem 1.1 of *Affine Profile Reduction for Fractional Triangle
Packings in Split Graphs* —

> For every split graph `G` on `n` vertices, `|E(G)| − 2·ν₃*(G) ≤ n²/6 + n`,
> where `ν₃*(G)` is the maximum fractional triangle-packing value.

**Ground truth:** `01_manuscript/PAPER_I_preprint_v1.0.{md,pdf,tex}` (Theorem 1.1,
Appendix C); calculation ledger `02_validation/CALCULATION_LEDGER_…v1.0.md` (L1–L63);
Lean sources `05_formalization/lean/`.
**Prior internal status:** ledger `FINAL_PASS / FROZEN / CLEAN`; manuscript claims the
theorem is machine-verified in Lean, sorry-free, axioms `[propext, Classical.choice,
Quot.sound]`.

---

## 1. Executive verdict

### Verdict: **PASS** (intermediate AI-assurance tier — not human peer review)

The finite fractional split-graph theorem `|E(G)| − 2ν₃*(G) ≤ n²/6 + n` is **sound and
correctly established** at every step the auditor could check independently, and the
manuscript's scope is stated honestly (no over-claim into integral packing, clique
partitions, chordal graphs, or Erdős #81). Specifically:

- **Analytic proof (Gates A–G):** the two-phase packing, the exact deficit identity, the
  affine/concavity reduction to pure profiles, the orbit symmetrization, the three-orbit
  LP, the quadratic benchmark `R(p,q)`, and the conversion to `n` all reproduce exactly.
  Every closed-form algebraic identity of the ledger was re-derived **symbolically and
  found exact** (Script 01, 9/9). The residual-cover LP optimum equals the closed form
  `min{U,D,H}` and the full `C(p,2)`-variable LP equals the 3-orbit LP (orbit
  symmetrization lossless), and the affine reduction with uniform bound `R(p,q) − p/2`
  holds on 400 random mixed profiles with **no counterexample** (Script 02).
- **Falsification (Gate F / kill-switch):** on 622 split graphs (structured + random +
  adversarial) the theorem was **never violated**; the extremal family `K_p ∨ K̄_{2p}`
  attains `n²/6 + n/6` exactly, confirming the leading constant `1/6` is tight and the
  `+n` term is a non-optimized slack (Script 03).
- **Formal certificate (Gate H): PASS.** An **independent rebuild** in a fresh source
  tree (no inherited `.lake` cache; community Mathlib cache) reports `Build completed
  successfully (8027 jobs)`, exit 0, with `PaperI.paperI_main` **and** the LP-duality node
  `PaperI.Split.residual_duality` each depending on axioms `[propext, Classical.choice,
  Quot.sound]` — no `sorryAx`, no `native_decide`, no project-specific axiom. The released
  Lean sources match the recorded integrity manifest by SHA-256 (8/8), the Lean statement
  `paperI_main : Phi ≤ n²/6 + n` (`Phi = edgeCount − 2·nu3star`) is exactly Theorem 1.1,
  and a static scan finds no `sorry`/`admit`/`native_decide`/added `axiom` in the sources.
  This independently reproduces the recorded gate log.
- **Citations (Gate I):** the single proof-critical import — finite-dimensional LP strong
  duality — is standard, and the Lean development derives it from Mathlib's finite Farkas
  (`residual_duality`), so the result does not depend on the exact Schrijver reference.

No counterexample, circularity, unmet hypothesis, or scope over-claim was found. This is
an independent AI adversarial audit: an intermediate assurance tier, stronger than
self-audit but **not** external human peer review; it confers no publication status.

---

## 2. Scope, method, independence

**In scope:** Theorem 1.1 (finite fractional bound for split graphs) and its full proof
chain, plus the Lean certificate for `paperI_main`.
**Out of scope (confirmed absent from the claim):** integral triangle packing, clique
partitions/`cp`, chordal graphs, `Φτ`, asymptotic Erdős #81, any fractional-to-integral
transfer. Paper II and the asymptotic #81 route were not consulted.

**Method:** clean-context decomposition into claim IDs mapped to gates A–J; predeclared
kill-switches for every computation; independent re-implementation of all primitives
(`ν₃*` LP, residual-cover LP, orbit LP, symbolic algebra); literal statement/definition
cross-check across manuscript ↔ ledger ↔ Lean; independent Lean build in a fresh tree;
SHA-256 provenance. **Independence:** fresh auditor code; fresh Lean source copy with no
inherited `.lake` cache; the author's repo of record was not used. See `ENVIRONMENT.md`.

---

## 3. Gate table (A–J)

| Gate | Item | Status | Evidence |
|---|---|---|---|
| A | Definitions (ν₃*, deficit, split model, κ, profiles, orbits) well-posed & consistent across manuscript/ledger/Lean | **VERIFIED_WITHIN_SCOPE** | manuscript §2 ↔ ledger L1–L4 ↔ Lean `Split`,`Phi`,`nu3star`,`edgeCount`,`n` cross-checked |
| B | Aggregate-load / affine profile reduction; candidates suffice | **VERIFIED_WITHIN_SCOPE** | Lemma 3.1 (L4) exact; concavity L33/L34; Script 02(B) 400 mixed profiles, 0 counterexample |
| C | Orbit symmetrization + finite LP; solved independently | **VERIFIED_WITHIN_SCOPE** | Script 02: full C(p,2)-LP = 3-orbit LP = `min{U,D,H}` (0/660 & 0/280, err 5e-15) |
| D | Finite LP duality applied within hypotheses; no infinite-dim appeal | **VERIFIED_WITHIN_SCOPE** | App B: finite feasible bounded pair; weak duality + attainment; Lean derives from Farkas |
| E | Deficit identity (4.9/L28) + quantitative bound `R(p,q)`; constant recomputed | **VERIFIED_WITHIN_SCOPE** | Script 01: L28, L48, L50, L51, L53, L58, q=0 all exact (9/9) |
| F | Conversion to `n` (≤ n²/6+n) + comparison with optimum packing; tightness | **VERIFIED_WITHIN_SCOPE** | L58–L63 exact; Script 03: 0 violations/622, extremal attains n²/6+n/6 |
| G | Assembly composes to the theorem; no circularity | **VERIFIED_WITHIN_SCOPE** | linear chain L1→L63; Lean `paperI_main` assembles `nu3star_ge_Vcom`+`Mcov_lower`+`edgeCount_eq`+arithmetic |
| H | Lean: build, sorry-freeness, `#print axioms`, statement match, SHA | **VERIFIED_WITHIN_SCOPE** | Script 04: independent rebuild 8027 jobs exit 0; `paperI_main`+`residual_duality` axioms `[propext,Classical.choice,Quot.sound]`, no sorryAx; SHA 8/8 match; statement = Thm 1.1 |
| I | Citations (LP duality; split-graph structure) applied within hypotheses | **VERIFIED_WITH_RESIDUAL_RISK** | finite LP duality standard + Lean-derived; exact "Cor. 7.1g" label not book-checked |
| J | Over-claim / scope check (no chordal, cp, #81, integral) | **VERIFIED_WITHIN_SCOPE** | manuscript §9, ledger §15 explicitly disclaim; statement is fractional split-graph only |

---

## 4. Independent computation (Scripts 01–03)

All scripts declared kill-switches before running; seed `20260710`; artifacts (script,
`results.txt`, `report.pdf`, `.zip`, `.sha256`) under `scripts/`.

- **01 — algebraic identities (Gate E).** sympy exact check of L48, L50, L51 (SOS),
  L53, L58, the q=0 facts, and L25/L28. **9/9 exact** → `CALCULATION_VERIFIED`.
- **02 — orbit LP / symmetrization / reduction (Gates B, C).** (C0) q=0 branch verified;
  (C1) orbit LP = `min{U,D,H}` (0/660); (C2) full LP = orbit LP, err 5e-15 (0/280) —
  orbit averaging is lossless; (B) `M(κ) ≥ min_s M(κ^S)` and `M(κ) ≥ R−p/2` on 400 mixed
  profiles, 0 violations, bound tight (slack 0). Auditor correction CORR-02-01 recorded
  (a q=0 domain over-reach in the first run; not a paper defect).
- **03 — split-graph falsification (Gate F).** 622 split graphs, **0** theorem
  violations; max ratio `(|E|−2ν₃*)/(n²/6+n) = 0.815`; extremal `K_p∨K̄_{2p}` attains
  `n²/6+n/6` exactly (0 tightness failures).

---

## 5. Falsification / kill-switch log

No counterexample was found to Theorem 1.1 or to any gate. Failed falsification attempts
(supporting evidence, not proof): adversarial dense complete-split graphs and 600 random
split graphs (Script 03); random mixed neighborhood profiles probing the affine reduction
and the uniform bound (Script 02); a search for an orbit/candidate beating `min{U,D,H}`
(Script 02, none). The one issue surfaced was an **auditor** domain error (CORR-02-01),
not a defect in the paper. Bounded search is existential evidence; the universal statement
rests on the analytic proof + the Lean certificate.

---

## 6. Coverage declaration

**Verified (within scope):** all algebraic identities of the ledger (exact); the orbit LP
closed form and the losslessness of orbit symmetrization (LP, bounded p); the affine
reduction and uniform bound (LP, bounded p, random mixed profiles); the end-to-end
inequality and extremal tightness (bounded split graphs); definition consistency across
manuscript/ledger/Lean; Lean statement = Theorem 1.1; source SHA-256 = recorded manifest;
static sorry/axiom-cleanliness of the sources; scope non-over-claim.

**Residual risks:** (i) numeric LP/enumeration checks are over bounded ranges (`p ≤ 11`
for the LP identities, `p ≤ 7–8` for exact `ν₃*`), so they corroborate rather than prove
the universal statement — but the analytic proof (Gates A–G) and the Lean certificate
(Gate H) carry the universal claim; (ii) the exact wording of Schrijver "Corollary 7.1g"
was not verified against the physical book (immaterial: the duality is standard and
Lean-derived from Farkas); (iii) this is an AI audit, not human peer review.

---

## 7. Recommendation

Maintain the theorem at its internal `FINAL_PASS / FROZEN` status for the **finite
fractional split-graph bound only**. The independent audit found the analytic proof, the
computational checks, and the formal certificate mutually consistent and free of any
detected error, circularity, or over-claim. Human expert / journal peer review remains
the appropriate next tier; this AI audit confers no publication status.

*Distinctions maintained: "analytic proof correct" (Gates A–G, I), "Lean certif