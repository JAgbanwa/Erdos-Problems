# Gate E - The complete-split value as a function of the split parameter (PAPER_II, v1.2)

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
**Verdict:** `PASS`

## Objective

Independently compute the complete-split value as a function of the split parameter and
verify the closed form.

## Method and result

`S_{p,q} = K_p join complement(K_q)` was constructed directly for every `(p,q)` with
`p + q = n`, and `Phi_tau(S_{p,q}) = |E| - 2 tau_3^*` computed by exact rational simplex
(`../G_FALSIFICATION/scripts/chordal_max_exact.py`). No closed form was assumed; the LP was
solved for each member of the family.

| `n` | complete-split maximum | argmax `(p,q)` | equals the global chordal maximum? |
|---|---|---|---|
| 1 | 0 | (0,1), (1,0) | yes |
| 2 | 1 | (1,1), (2,0) | yes |
| 3 | 2 | (1,2) | yes |
| 4 | 3 | (1,3), (2,2) | yes |
| 5 | 5 | (2,3) | yes |
| 6 | 7 | (2,4) | yes |

**In every case the maximum over the complete-split family equals the maximum over all
chordal graphs on `n` vertices**, and equals `floor((2n+1)^2/24)`. That is the attainment
half of the headline claim, established by computation rather than assumed.

The abstract describes reducing the cover calculation on `S_{p,q}` to a **two-variable**
linear program by orbit averaging, then maximizing over `p + q = n`. This audit verified the
*outcome* of that reduction - the value at each `(p,q)`, computed without using the
reduction - and the subsequent integer maximization at Gate F. The two-variable reduction
itself was not separately rederived; the agreement between the full LP and the claimed
maximum over 19,048 chordal graphs is the evidence that it loses nothing.

## The integer maximization

Verified at Gate F over `n` in `[-20000, 20000]` in exact arithmetic: the closed value,
its residue structure (`(2n+1)^2 mod 24` in `{1, 9}` exactly), the bounded remainder
`theta_n in [-1/3, 0]` against the claimed `(-1, 1/24]`, and the asymptotic
`M(n)/n^2 -> 1/6`.

## Findings

None at this gate.

## Limitations

The family was evaluated exhaustively only for `n <= 6` as part of the global enumeration.
The two-variable orbit reduction and the `S_{2,0} = K_2` branch analysis were not
rederived symbolically; they were tested through their consequences.

## Evidence

`../G_FALSIFICATION/results/chordal_max_n1-6.json` (per-`n` complete-split values and
argmax), `../F_PROOF_CHAIN/results/arith_corollaries.txt`.
