# Paper III — Final Internal Audit Report

*Linear-Error Clique Partitions of Split Graphs (Erdős #81)*

**OVERALL VERDICT: ALL AUDITED BLOCKS PASS**

_Generated: 2026-07-21 19:38 UTC — internal automated audit harness (Claude Code)_

## Summary

| Block | Scope | Verdict |
|-------|-------|---------|
| Block 01 | Algebraic identities | **12/12 identities PASS** |
| Block 02 | Common-profile LP (Theorem 3.1 / E-3.1) | **LP 351/351 and EXACT 351/351 PASS** |
| Block 03 | Unified fractional margin (Theorem 4.2 / E-4.2) | **78,384/78,384 exact-rational checks PASS** |
| Block 04 | Corridor integral packing (Lemma 5.1 & Cor 5.3) | **E-5.1 180/180, Cor 5.3 180/180, 372 instances PASS** |

## Detail

### Block 01 — Algebraic identities
- **Verdict:** 12/12 identities PASS
- **Method:** SymPy exact symbolic proof (simplify(LHS-RHS)=0 / exact rational / sum-of-squares) of the T(G) key identity (Thm 4.2), the (9.12) and (9.20) coefficients, the (9.19) completed square and its lower bound, delta>=7/8 for both parities (9.10), the corridor threshold p=2304, mu continuity at alpha=2/3, and the (4.5) closed forms.
- **Folder:** `block01_algebraic_identities/`  ·  **Results:** `results/identities_results.txt`
- **results SHA-256:** `7d5ea305ff7f44013184d2187d7e310efde926881cf24a4424e55667dbfe8519`
- **zip SHA-256:** `f0bf84900c54f70e43d9c3bc77aab8010d51b034924b2c46724fb961c0584d15`

### Block 02 — Common-profile LP (Theorem 3.1 / E-3.1)
- **Verdict:** LP 351/351 and EXACT 351/351 PASS
- **Method:** Direct fractional triangle-packing LP (SciPy HiGHS) on the actual graph H(p,q,d) over 3<=p<=8, 0<=q<=8, 0<=d<=p, compared to the closed form F(p,q,d); PLUS an exact-rational feasible-cover certificate proving nu3* <= F without float reliance.
- **Folder:** `block02_common_profile_LP/`  ·  **Results:** `results/common_profile_LP_results.txt`
- **results SHA-256:** `1e977ecba3d6475adf02330f8fb6d0c382d6123d83ead0bb468c7287c3e79773`
- **zip SHA-256:** `2b44615bcca18af350c5b0328a598c4deeb28d877170fe8e1fa0f0746b80b68e`

### Block 03 — Unified fractional margin (Theorem 4.2 / E-4.2)
- **Verdict:** 78,384/78,384 exact-rational checks PASS
- **Method:** Exact-rational grid audit (fractions.Fraction, no floating point) of the completion-of-squares inequality (4.5) over 3<=p<=48, 1<=q<=2p, 0<=d<=p, with third-branch dominance bookkeeping.
- **Folder:** `block03_unified_margin/`  ·  **Results:** `results/margin_results.txt`
- **results SHA-256:** `577450739c3652ed9be447a3b426f23f8e856dd7eac4aa37002bcdb859b5239a`
- **zip SHA-256:** `f42c326551e0254b4e9d98581759c2062951e1af4275b6972d482189e83cfa32`

### Block 04 — Corridor integral packing (Lemma 5.1 & Cor 5.3)
- **Verdict:** E-5.1 180/180, Cor 5.3 180/180, 372 instances PASS
- **Method:** Exact 0/1 ILP (PuLP + CBC) computation of nu3(G) on 372 systematically generated split graphs, verifying E-5.1 and Corollary 5.3 on the applicable instances (q >= r_p) plus the basic invariants 0<=Phi and 3*nu3<=|E|.
- **Folder:** `block04_corridor_ILP/`  ·  **Results:** `results/corridor_ILP_results.txt`
- **results SHA-256:** `eeb55cbb2b33abcbeae841b6ed2562b1a3ba039c3dfdbe5f0074d2561b9fa7ce`
- **zip SHA-256:** `7461f221ed91623fd2f04ccee4baa4fc013211b1468fb03a1b7fcbf428009aa7`

## Methodology & tooling
Python 3.14; SymPy 1.14 (symbolic identities); SciPy 1.17 HiGHS (fractional LP); PuLP + CBC (exact ILP); `fractions.Fraction` (exact rationals). Each block's `verify_*.py` writes its full log to `results/` and returns nonzero on any failure.

## Relationship to the formalization
This computational audit is **complementary** to and **independent** of the machine-checked Lean 4 / Mathlib development (they share no code). The formalization certifies the logical chain relative to AX1/AX2; this audit independently certifies the finite numeric and closed-form facts.

## Scope & honesty
Covers the finite / closed-form perimeter only. The external asymptotic inputs AX1 (Haxell–Rödl/Yuster) and AX2 (Dross + Barber–Kühn–Lo–Osthus) are the paper's declared axioms and are out of scope for computational audit.

