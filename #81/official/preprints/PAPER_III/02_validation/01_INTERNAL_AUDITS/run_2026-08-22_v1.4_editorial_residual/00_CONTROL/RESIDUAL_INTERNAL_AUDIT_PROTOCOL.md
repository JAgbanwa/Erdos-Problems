# Paper III v1.4 editorial residual internal audit protocol

## Scope

This author-side, non-independent residual audit addresses external findings
`EXT-V14-M01` and `EXT-V14-M02` without changing or rebuilding the Lean freeze.
It also reruns the complete v1.4 internal regression suite.

## Required gates

1. `M01`: the corrected Spanish Markdown must preserve the full scope of the English
   Section 2.4 sentence, including Proposition 10.5 and the standard complete-graph
   edge-coloring background.
2. `M01-chain`: Spanish Markdown must generate Spanish LaTeX, which must compile to
   the Spanish PDF. The six-artifact consistency suite, duplicate-text controls,
   rendered-page QA, and hashes must pass.
3. `M02`: Appendix D must be checked from its definitions through its application in
   Section 7.2. This is an internal rederivation, not independent review authority.
4. `regression`: the complete 144-check G0--G8 internal audit must pass.
5. `formal freeze`: the Lean archive must remain byte-identical at SHA-256
   `79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104`.

## Verdict rule

The residual verdict is `PASS_INTERNAL` only if all five gates pass. External
challenger confirmation remains mandatory before release approval.
