# Block F — Audit the Internal Audit

**Paper III — Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing** (v1.1.5)

- **Auditor:** Claude Opus 4.8 (Anthropic), via Claude Code
- **Date:** 2026-07-28
- **Manuscript SHA-256:** `7aaf03083ddf7731dcb2b1e849cdfac97fb1697df1650c49a56e8431ce1bcb0b`
- **Lean freeze ZIP SHA-256:** `060957e6b8d54779844dc6adf7cc7c3b8446fc17a87aa8d7a437e9d9d1001b78`

## Verdict: **PASS**

The manuscript's own internal computational audit is well-scoped, correctly framed as **non-premise**, and its results were **independently reproduced** by this external audit with full agreement. The machine-checked Lean freeze closes the mathematical content modulo the two disclosed external axioms. No coverage gap remains.

## What the manuscript's internal audit claims

The manuscript reports (Appendix C, §8, §11.6) a suite of internal computational checks:

- **Fractional margin** verified by exact arithmetic for `3 ≤ p ≤ 80`, `1 ≤ q ≤ 2p`, `0 ≤ d ≤ p`.
- **Divisibility construction** enumerated exhaustively to order **18**.
- **Exhaustive enumeration** of the extremal configuration at `n = 9` (`|K| = 3`).
- **Total: 46,481 checks** — 46,390 exact-arithmetic / LP instances plus 91 ILP instances.

## Framing check — are these computations used as logical premises?

**No, and this is stated explicitly.** Per §1.6 and §11.6, the proof is **analytic and Lean-verified**; the computations exist only to guard against transcription and bookkeeping error. They are *evidence*, not *axioms*. This is the correct epistemic posture: had the computations been load-bearing premises, the `∃C` theorem would inherit an unverified finite-case dependency. They are not, so it does not. The auditor confirms the manuscript does not smuggle any computational result into the deductive chain.

## Independent reproduction (this external audit, Block E)

This audit re-derived the internal audit's key quantities from scratch, agreeing in every case:

| Quantity re-derived | Method | Agreement |
|---|---|---|
| E-3.1 common-profile formula `τ₃* = F p q d` | 464 LP instances, `p ≥ 3` | Exact |
| Extremizer identity `Φ(K_p∨K̄_{2p}) = n²/6 + n/6` | Direct + ILP (small `p`) | Exact |
| Margin `μ` positivity across regimes | Exact arithmetic | Exact |
| Reserved-gain `rp = χ'` identity | Exact arithmetic | Exact |
| Corridor threshold `36p = p²/64 ⟺ p = 2304` | Exact | Exact |
| Regime coverage (no gaps) | Sweep | Exact |

**Total external checks: 60,541** (Block E) — a larger and independently-implemented sweep than the internal 46,481, all in agreement.

## Machine-checked certainty — the Lean freeze

The Lean freeze provides the deductive backbone:

- **8060 build jobs, 0 errors.**
- **Exactly 2 axioms** — `AX1` and `AX2` — and no others.
- **0 `sorry`, 0 `admit`.**

This means every non-axiomatic step of the proof is machine-verified. The only unverified inputs are the two external theorems AX1 (Haxell–Rödl / Yuster) and AX2 (Dross + Barber–Kühn–Lo–Osthus), both published and both honestly disclosed.

## Coverage assessment

- The internal audit's scope is appropriate for its stated purpose (transcription-error guard) and is strictly subsumed by the external reproduction.
- No computation is used as a hidden premise.
- The proof's certainty rests on the Lean freeze, not on the enumerations.
- The residual trust surface is exactly the two disclosed axioms — nothing more.

**No coverage gap remains in the mathematical content.**

**Block F verdict: PASS.**
