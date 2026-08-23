# Gate F - Integer maximization, residues and the Paper I comparison (PAPER_II, v1.2)

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
**Verdict:** `PASS`

## Objective

Independently solve the integer maximization, the parity and tie cases,
`floor((2n+1)^2/24)`, the residue-class formulas, the bounded remainder, and the comparison
with Paper I. Check every stated domain restriction.

## Method

Exact integer and rational arithmetic (`fractions.Fraction`), deterministic, no seeds, over
`n` in `[-20000, 20000]` - deliberately including negative `n`, because the manuscript
states `phiTau_max_sandwich` "for `n : Z`, with no lower-bound hypothesis" and that is
exactly the kind of claim that fails at the boundary if it is going to fail at all.

## Results - all four Table 5 corollaries confirmed

| Claim | Statement as printed | Result |
|---|---|---|
| `phiTau_max_sandwich` | for every `n in Z`, `4n^2+4n-23 < 24*floor((2n+1)^2/24) <= 4n^2+4n+1` | **HOLDS for all 40,001 values including negatives** |
| bounded remainder (L136-138) | `M(n) = n^2/6 + n/6 + theta_n` with `theta_n in (-1, 1/24]` | **HOLDS**; observed range `[-1/3, 0]`, strictly inside the claimed interval |
| `odd_sq_emod_24` | `(2n+1)^2 = 1` or `9 (mod 24)` | **CONFIRMED**; observed residue set is exactly `{1, 9}` |
| `phiTau_max_le_paperI_bound` | `floor((2n+1)^2/24) <= n^2/6 + n/2` for `n >= 1` | **HOLDS**, with algebraic margin `24*(n^2/6+n/2) - (2n+1)^2 = 8n - 1 > 0` |

## The domain restriction is necessary, not decorative

`phiTau_max_le_paperI_bound` is stated with the hypothesis `n >= 1`. Tested for `n <= 0` as
well: it **fails** there. So the hypothesis is genuinely required, and the manuscript states
it. An adversarial check that came out in the paper's favour.

## Cross-paper check (protocol Section 10)

The comparison uses `n^2/6 + n/2` - **Paper I's corrected `+n/2` surface**, not the
superseded `+n` form. This is one of the explicit cross-paper requirements and it is
satisfied. The margin `8n - 1` is strict for every `n >= 1`.

## Asymptotics

`M(n)/n^2` computed exactly at `n = 10, 100, 1000, 10000, 100000`:
`0.1800000000, 0.1683000000, 0.1668330000, 0.1666833300, 0.1666683333`, converging to
`1/6 = 0.1666666667` from above. Consistent with the claimed asymptotic corollary.

## Findings

None at this gate.

## Evidence

`results/arith_corollaries.txt`.
