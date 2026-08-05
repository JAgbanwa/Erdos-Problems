# Script 03 — Split-Graph Falsification of Theorem 1.1

**Audit:** PAPER_I_EXT_AUDIT · **Script:** `03_split_falsification.py`
**Environment:** Python 3.14.4, scipy 1.17.1 (HiGHS LP), numpy · seed 20260710

## Purpose

Directly test Theorem 1.1 — `|E(G)| − 2ν₃*(G) ≤ n²/6 + n` — on split graphs, computing
`ν₃*(G)` **exactly** by solving the fractional triangle-packing LP on the whole graph
(independent of the manuscript's two-phase construction). Also confirm the extremal
family attains the leading constant.

Split graph model: clique `K_p` plus independent vertices with neighborhoods
`N(v) ⊆ K`. Triangles are clique triples and mixed triples `{v,x,y}` with `x,y ∈ N(v)`
(no triangle uses two independent vertices, since `I` is independent).

## Predeclared kill-switches

- **KS1** any split graph with `|E| − 2ν₃* > n²/6 + n + 1e−6` ⟹ **THEOREM FALSIFIED**.
- **KS3** extremal `K_p ∨ K̄_{2p}` with `|E| − 2ν₃* ≠ n²/6 + n/6` ⟹ tightness claim wrong.

## Instances and results

- **(a)** structured enumeration `p=2..5`, one independent vertex per subset of `K`
  (all neighborhood types): all satisfy the bound (ratios 0.25–0.30).
- **(b)** 600 random split graphs (`p=2..7`, up to 10 independent vertices, random
  neighborhoods): all satisfy the bound.
- **(c)** adversarial complete-split `N(v)=K` with up to `3p` independent vertices:
  all satisfy the bound.
- **(d)** extremal family `K_p ∨ K̄_{2p}` (`n=3p`), `p=2..7`: `ν₃* = C(p,2)` exactly, and
  `|E| − 2ν₃* = n²/6 + n/6` exactly on every instance.

| Quantity | Value |
|---|---|
| total split graphs tested (a,b,c) | 622 |
| theorem violations (KS1) | **0** |
| max ratio `(|E|−2ν₃*)/(n²/6+n)` | 0.815 (at `K₇∨K̄₁₄`) |
| extremal tightness failures (KS3) | **0** |

## Verdict

**NOT FALSIFIED.** No split graph violated `|E| − 2ν₃* ≤ n²/6 + n`; the extremal family
`K_p ∨ K̄_{2p}` attains `n²/6 + n/6` exactly, matching the manuscript's §9 discussion
(the leading constant `1/6` is tight; the additive `+n` is not optimized — observed
peak `n/6`). **Limit:** a bounded computational search is supporting/typed evidence for
a universal (`∀`) claim, never a proof; the analytic proof (Scripts 01–0