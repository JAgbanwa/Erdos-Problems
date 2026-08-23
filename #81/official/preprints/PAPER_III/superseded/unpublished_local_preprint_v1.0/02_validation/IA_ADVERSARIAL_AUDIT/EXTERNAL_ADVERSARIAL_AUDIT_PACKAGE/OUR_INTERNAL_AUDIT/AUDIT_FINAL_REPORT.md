# Paper III — Final Internal Audit Report

*Linear-Error Clique Partitions of Split Graphs (Erdős #81)*

**OVERALL VERDICT: ALL AUDITED BLOCKS PASS**

_Generated: 2026-07-21 16:41 UTC — internal automated audit harness (Claude Code)_

## Summary

| Block | Scope | Verdict |
|-------|-------|---------|
| Block 01 | Algebraic identities | **12/12 identities PASS** |
| Block 02 | Common-profile LP (Theorem 3.1 / E-3.1) | **351/351 instances PASS (max |LP-F| = 3.9e-14)** |
| Block 03 | Unified fractional margin (Theorem 4.2 / E-4.2) | **78,384/78,384 exact-rational checks PASS** |
| Block 04 | Corridor integral packing (Lemma 5.1 & Cor 5.3) | **E-5.1 180/180, Cor 5.3 180/180, 372 instances PASS** |

## Detail

### Block 01 — Algebraic identities
- **Verdict:** 12/12 identities PASS
- **Method:** SymPy exact symbolic proof (simplify(LHS-RHS)=0 / exact rational / sum-of-squares) of the T(G) key identity (Thm 4.2), the (9.12) and (9.20) coefficients, the (9.19) completed square and its lower bound, delta>=7/8 for both parities (9.10), the corridor threshold p=2304, mu continuity at alpha=2/3, and the (4.5) closed forms.
- **Folder:** `block01_algebraic_identities/`  ·  **Results:** `results/identities_results.txt`
- **results SHA-256:** `7d5ea305ff7f44013184d2187d7e310efde926881cf24a4424e55667dbfe8519`
- **zip SHA-256:** `eaf14d9dfbe6871a0dae73902fedf2aabacd2b31fb13df0b3e63b5c1c7c7cae7`

### Block 02 — Common-profile LP (Theorem 3.1 / E-3.1)
- **Verdict:** 351/351 instances PASS (max |LP-F| = 3.9e-14)
- **Method:** Direct fractional triangle-packing LP (SciPy HiGHS) solved on the actual graph H(p,q,d) over the grid 3<=p<=8, 0<=q<=8, 0<=d<=p, and compared against the closed form F(p,q,d). Independent of the reduced 4-variable LP used in the proof.
- **Folder:** `block02_common_profile_LP/`  ·  **Results:** `results/common_profile_LP_results.txt`
- **results SHA-256:** `7fabebbc8a96ff39e2468239a98f8cf3de2d5d0642ef6382391bf4628cc3b509`
- **zip SHA-256:** `6afed288c0d5beed04881546eac92fa8b47be3302f923a0450206f93067dcd39`

### Block 03 — Unified fractional margin (Theorem 4.2 / E-4.2)
- **Verdict:** 78,384/78,384 exact-rational checks PASS
- **Method:** Exact-rational grid audit (fractions.Fraction, no floating point) of the completion-of-squares inequality (4.5) over 3<=p<=48, 1<=q<=2p, 0<=d<=p, with third-branch dominance bookkeeping.
- **Folder:** `block03_unified_margin/`  ·  **Results:** `results/margin_results.txt`
- **results SHA-256:** `577450739c3652ed9be447a3b426f23f8e856dd7eac4aa37002bcdb859b5239a`
- **zip SHA-256:** `46a438c43896dcf67e6a210d887a9d66963cb7c8f4903076be5d1acdc9999fab`

### Block 04 — Corridor integral packing (Lemma 5.1 & Cor 5.3)
- **Verdict:** E-5.1 180/180, Cor 5.3 180/180, 372 instances PASS
- **Method:** Exact 0/1 ILP (PuLP + CBC) computation of nu3(G) on 372 systematically generated split graphs, verifying E-5.1 and Corollary 5.3 on the applicable instances (q >= r_p) plus the basic invariants 0<=Phi and 3*nu3<=|E|.
- **Folder:** `block04_corridor_ILP/`  ·  **Results:** `results/corridor_ILP_results.txt`
- **results SHA-256:** `eeb55cbb2b33abcbeae841b6ed2562b1a3ba039c3dfdbe5f0074d2561b9fa7ce`
- **zip SHA-256:** `38ee6759a4a17ff486c7b691c607d7b8b32540969bd4aa4f6688d17ae232bdf3`

## Methodology & tooling
Python 3.14; SymPy 1.14 (symbolic identities); SciPy 1.17 HiGHS (fractional LP); PuLP + CBC (exact ILP); `fractions.Fraction` (exact rationals). Each block's `verify_*.py` writes its full log to `results/` and returns nonzero on any failure.

## Relationship to the formalization
This computational audit is **complementary** to and **independent** of the machine-checked Lean 4 / Mathlib development (they share no code). The formalization certifies the logical chain relative to AX1/AX2; this audit independently certifies the finite numeric and closed-form facts.

## Scope & honesty
Covers the finite / closed-form perimeter only. The external asymptotic inputs AX1 (Haxell–Rödl/Yuster) and AX2 (Dross + Barber–Kühn–Lo–Osthus) are the paper's declared axioms and are out of scope for computational audit.

