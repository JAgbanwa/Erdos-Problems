# Gate D - Monotonicity, termination, ties and level sets (PAPER_II, v1.2)

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
**Verdict:** `PASS` on what was checkable; termination `NOT INDEPENDENTLY VERIFIED`

## What this gate was asked to do

Verify monotonicity and termination of the copy process, including ties, equality cases,
level sets and copy-defect inequalities.

## What was independently established

- **The copy-defect inequality**, `copyDefect_nonneg`, is the monotonicity engine: it is
  what guarantees a copy step never decreases `Phi_tau`. Verified exhaustively at Gate C
  over **251,085** instances (all labeled graphs on 2..6 vertices, all nonadjacent pairs)
  with **zero violations** and minimum defect `0`. See `../C_PROOF_CHAIN/`.
- **Ties are real and correctly scoped.** The Gate G enumeration found ties in the
  maximizing clique size at `n = 2` (`(p,q) = (1,1)` and `(2,0)`) and `n = 4`
  (`(1,3)` and `(2,2)`), with a unique complete-split argmax at `n = 3, 5, 6`. The
  manuscript claims uniqueness only *within the complete-split family* and explicitly
  disclaims uniqueness of chordal extremizers up to isomorphism. The enumeration confirms
  the weaker claim is the correct one.
- **The degenerate equality case** `S_{2,0} = K_2` that the abstract singles out appears in
  the `n = 2` tie and behaves as claimed.
- **Level sets.** `level_set_iff` is stated as an exact equivalence for level sets measured
  from the continuous maximum `M^2/24`. Its formal footprint was confirmed at Gate H. The
  underlying arithmetic - that `floor((2n+1)^2/24)` sits within a bounded window of
  `n^2/6 + n/6` - was verified exactly at Gate F: `theta_n = M(n) - n^2/6 - n/6` lies in
  `[-1/3, 0]` over `n` in `[-20000, 20000]`, inside the claimed `(-1, 1/24]`.
- **`copyGamma_ge_half_copyDefect`** was confirmed to build with the expected footprint at
  Gate H; its inequality was not independently recomputed.

## What was NOT established, stated plainly

- **Termination of the repeated-copy process** was not independently verified. The
  single-step inequality was verified exhaustively, but that a finite sequence of admissible
  copies always reaches a complete-split graph is a structural argument this audit did not
  reproduce.
- The **discrete-convexity lift** from single vertices to whole open-neighbourhood clone
  classes was not independently verified.

These two are the load-bearing structural steps beyond the single-step inequality, and they
carry no verdict from this audit. What the audit does establish is that the inequality they
build on is correct on a large exhaustive domain, and that the terminal family they claim to
reach does in fact attain the claimed maximum at every `n` tested (Gate G).

## Findings

None at this gate.

## Evidence

`../C_PROOF_CHAIN/results/copy_ineq_n5.json`, `copy_ineq_n6.json`;
`../G_FALSIFICATION/results/chordal_max_n1-6.json`;
`../F_PROOF_CHAIN/results/arith_corollaries.txt`.
