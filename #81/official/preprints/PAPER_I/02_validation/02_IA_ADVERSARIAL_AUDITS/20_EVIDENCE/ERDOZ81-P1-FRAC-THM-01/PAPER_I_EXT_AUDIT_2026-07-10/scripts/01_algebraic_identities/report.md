# Script 01 — Algebraic Identity Verification (Gate E)

**Audit:** PAPER_I_EXT_AUDIT (Affine Profile Reduction for Fractional Triangle Packings
in Split Graphs) · **Script:** `01_algebraic_identities.py`
**Environment:** Python 3.14.4, sympy 1.14.0 (exact symbolic algebra)

## Purpose

Re-derive, symbolically and exactly, every closed-form algebraic identity that carries
proof weight in the manuscript / calculation ledger. These are the load-bearing steps
behind the quadratic benchmark `R(p,q)` and the conversion to `n`. Exact symbolic
equality (`LHS − RHS` simplifies to `0`) is proof-grade for these steps
(**CALCULATION_VERIFIED**), independent of the manuscript's own algebra.

Symbols `p=|K|, q=|I≥2|, s=|S|, o=p−s`;
`A=s(s−1−q)/2, B=so, C=o(o−1)/2`; `U=(A+B+C)/3, D=A+C, H=A+(B+C)/3`;
`R(p,q)=(2p²−2pq−q²)/12`.

## Identities checked (all EXACT, difference = 0)

| Tag | Identity | Result |
|---|---|---|
| L48 | `12(U−R) = q(2o+q) − 2p` | OK |
| L50 | `12(D−R) = 12o² − 6o(2p−q) + (2p−q)² − 6p` | OK |
| L51 | `12u² − 6uv + v² = 12(u−v/4)² + v²/4` (SOS ≥ 0) | OK |
| L53 | `12(H−R) = (2s−q)² + 2q(p−s) − 2p − 4s` | OK |
| L58 | `C(p,2) − 2R + p = (p+q)²/6 + p/2` | OK |
| q=0 | `R(p,0) − p/2 = (p²−3p)/6` | OK |
| q=0 | `M(0) − R(p,0) = −p/6` with `M(0)=p(p−1)/6` | OK |
| L25 | `V_com = b≥2/2 + M` (from `Σ(1−κ)=C(p,2)−b≥2/2`) | OK |
| L28 | `|E| − 2V_com = C(p,2) − 2M + b₁` | OK |

**9 / 9 identities exact.**

## Sign facts (inequality directions), on the domain `q,o,s ≥ 0`, `s ≤ p`

- `12(U−R)+2p = q(2o+q) ≥ 0` ⟹ `U−R ≥ −p/6 ≥ −p/2`.
- `12(D−R)+6p = 12(o−(2p−q)/4)² + (2p−q)²/4 ≥ 0` (verified equal to the SOS form)
  ⟹ `D−R ≥ −p/2`.
- `12(H−R)+2p+4s = (2s−q)² + 2q(p−s) ≥ 0`, and `−2p−4s ≥ −6p` since `s ≤ p`
  ⟹ `H−R ≥ −p/2`.

Hence each orbit candidate satisfies `≥ R(p,q) − p/2`, so `min{U,D,H} ≥ R − p/2`.

## Verdict

**ALL EXACT (CALCULATION_VERIFIED).** The manuscript's algebra behind the quantitative
bound and the final conversion contains no transcription or algebraic error on any of
the checked identities. This is the exact-algebra half of Gate E; the LP-optimality half
(that `M(κ^S)=m