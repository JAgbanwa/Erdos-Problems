# Paper II — Independent Computational Audit

**Manuscript:** *Complete-Split Extremizers for a Fractional Triangle-Cover Functional on Chordal Graphs* (Paper II).  
**Author of record:** Juan Pablo Traverso Gianini — ORCID 0009-0003-6068-4096.  
**Date:** 2026-07-09. **Overall result: 6 / 6 sections PASS.**

Each section of the proof was re-verified by an **independent, self-contained script** that
recomputes the manuscript's claims from scratch — exact linear programming (SciPy/HiGHS) for the
fractional triangle-cover number $\tau_3^*$, exact rational arithmetic for the integer
optimization, and exhaustive enumeration of non-isomorphic graphs (NetworkX atlas) where feasible.
This is **computational evidence** corroborating the analytic proof; the machine-checked *formal*
proof is the separate Lean development (conditional on the classical chordal-structure theory).

| Section | Paper ref. | Scope | Verdict |
|---|---|---|---|
| A — vertex-copy inequality | §3 (Lemma 3.1; eqs 3.3–3.4) | all non-iso graphs $n\le7$, every nonadjacent pair (1251 graphs, 12342 pairs) | **PASS** |
| B — clone-class operations | §4 (Lemmas 4.1–4.3 + $C_4$ necessity) | 8670 convexity configs; 5663 class-pairs; explicit necessity example | **PASS** |
| C — terminal characterization | §5 (Lemma 5.1; Theorem 5.3) | all non-iso chordal graphs $n\le7$ (531 graphs) | **PASS** |
| D — complete-split cover | §6 (Prop 6.2; Cor 6.3; Lemma 6.1) | all $S_{p,q}$, $p\le12,q\le14,p+q\le16$ (139 cases) | **PASS** |
| E — integer maximization | §7 (Prop 7.1; Theorem 1.1 arithmetic) | every $n$ from 1 to 2000, exact rational | **PASS** |
| F — global maximum | Theorem 1.1 | EXHAUSTIVE $n\le7$; SAMPLED $n=8..12$ (3000 each) + complete-split family | **PASS** |

## Scope honesty
Sections A, C and F(part 1) are **exhaustive for $n\le7$** (the NetworkX atlas ships all
non-isomorphic graphs only up to 7 vertices). Section F for $n\ge8$ is a large **random sample**
(clearly labelled), with exact attainment of the floor certified via the closed form on the
complete-split family. No claim is exhaustive beyond the stated ranges.

## Layout
Each `<Section>/` contains: the audit script, `results/summary.json` (+ run log), an English
PDF certification report `REPORT_*.pdf`, a `manifest_sha256.txt`, and a per-section zip.
This directory also carries `MASTER_manifest_sha256.txt` (over the six zips + this README) and
`PAPER_II_AUDIT_master.zip` (everything). `RUN_INSTRUCTIONS.md` documents how to reproduce.

## Reproduce
```
pip install -r requirements.txt
python3 <Section>/audit_*.py     # writes <Section>/results/summary.json
```
Verify integrity:  `sha256sum -c <Section>/manifest_sha256.txt`  and  `sh