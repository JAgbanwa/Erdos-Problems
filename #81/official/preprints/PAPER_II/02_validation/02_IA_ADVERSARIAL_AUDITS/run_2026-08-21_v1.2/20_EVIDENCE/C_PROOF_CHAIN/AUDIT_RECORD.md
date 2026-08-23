# Gate C - Vertex-copy inequality and symmetrization (PAPER_II, preprint_draft_v1.2)

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
**Verdict:** `PASS`

## The claim under attack

The abstract states the structural core of the proof: "for two nonadjacent vertices, the
two possible copy directions have average `Phi_tau`-value at least that of the original
graph." Equivalently, for nonadjacent `u, v`,

    Phi_tau(G_{v->u}) + Phi_tau(G_{u->v})  >=  2 * Phi_tau(G)

i.e. the copy defect is nonnegative, formalized as `PaperII.copyDefect_nonneg`.
`G_{v->u}` replaces the neighbourhood of `v` by that of `u`, making `v` a clone of `u`.

This is the load-bearing step: the entire reduction to complete-split graphs rests on it,
so it is the first thing an adversary should try to break.

## Method

`scripts/copy_inequality.py`, written for this audit. **Exhaustive** over all labeled
graphs on `n` vertices and **all** nonadjacent pairs in each. `Phi_tau` is computed from
an exact-rational primal simplex (Bland's rule) written for this audit. All arithmetic is
`fractions.Fraction`; deterministic; no seeds. No author-side script was consulted.

## Result

| Quantity | Value |
|---|---|
| domain | all labeled graphs on `n = 2..6`, all nonadjacent pairs |
| instances tested | **251,085** |
| **copy-inequality violations** | **0** |
| minimum copy defect observed | `0`, attained on the trivial 2-vertex empty graph |
| `nu_3^* = tau_3^*` mismatches | **0** |

Per `n`: 1, 12, 192, 5,120 and 245,760 instances at `n = 2,3,4,5,6` - **zero violations
at every size.**

**The inequality survived every one of 251,085 instances.** For a claim this central,
that is meaningful negative evidence: had the inequality been false in general, a
counterexample on six vertices would be a natural place to find one.

## An adversarial observation that supports the manuscript

Among the 148,919 chordal instances tested, there are **6,090** in which **both** copy
directions destroy chordality. The manuscript does not claim unconditional chordality
preservation: it claims that "copying toward a simplicial clone class preserves
chordality". These 6,090 cases confirm that the restriction to a simplicial clone class
is **necessary**, not decorative - an arbitrary nonadjacent pair can fail in both
directions. The manuscript's hypothesis is doing real work and is correctly stated.

## Findings

None at this gate.

## Limitations

- Exhaustive only to `n = 6`. The claim is general; the manuscript's proof is what
  establishes it. This gate's role is falsification and it found no counterexample.
- The discrete-convexity lifting from single vertices to whole open-neighbourhood clone
  classes was **not** independently verified; only the single-vertex inequality was. That
  lifting step carries no verdict from this gate.
- Termination of the repeated-copy process was not independently verified here.

## Files

`scripts/copy_inequality.py`, `results/copy_ineq_n5.json`, `results/copy_ineq_n6.json`.
