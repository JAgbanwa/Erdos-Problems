# Erdős Problem 261 — Sums of distinct terms $k/2^k$

This folder contains a self-contained write-up of the three-part problem about representing numbers as sums of **distinct** terms $f(k)=k/2^k$.

## Files

| File | Description |
|------|-------------|
| [`.tex file`](.tex%20file) | Full LaTeX source (theorems, proofs, audit, verification appendix) |
| [`problem261.pdf`](problem261.pdf) | Compiled PDF |
| [`verify.py`](verify.py) | Standalone exact-arithmetic verification script |

## Problem statement

1. Are there infinitely many $n$ such that, for some $t\ge 2$ and distinct integers $a_1,\ldots,a_t\ge 1$,
   $$\frac{n}{2^n}=\sum_{k=1}^{t}\frac{a_k}{2^{a_k}}?$$
2. Is this true for **every** $n$?
3. Is there a rational $x$ such that $x=\sum_{k=1}^{\infty}a_k/2^{a_k}$ has at least $2^{\aleph_0}$ solutions (with the $a_k$ mutually distinct)?

## Results (summary)

| Question | Answer | Status |
|----------|--------|--------|
| (1) Infinitely many $n$? | **Yes** | Proved (explicit family $n_s=2^s-s-1$) |
| (2) All $n$? | **Yes** for $n\le 2000$ and an infinite family | Conjectured in general |
| (3) Rational $x$ with $2^{\aleph_0}$ solutions? | **Yes** (sequence reading); explicit irrational $x^{\ast}$ for set reading | Rational set-reading open |

See the PDF for complete proofs, the corridor-digraph reformulation of Question (2), and the verification code appendix.

## Build PDF

```bash
cd "#261"
pdflatex -jobname=problem261 ".tex file"
pdflatex -jobname=problem261 ".tex file"
```

## Verify computations

```bash
python3 verify.py
```
