---
geometry: margin=1in
fontsize: 11pt
---
# Independent Computational Verification
## Paper II — Section 5: terminal characterization & symmetrization (Lemma 5.1, Theorem 5.3)

**Author of record:** Juan Pablo Traverso Gianini  **Date:** 2026-07-09  
**Artifact:** `C_terminal_characterization/audit_C_terminal.py`  **Verdict: PASS**

### Scope
Exhaustive over **all non-isomorphic chordal graphs on 1–7 vertices** (531 graphs).

### Claims verified
- **(C1) Lemma 5.1 (equivalence):** a chordal graph satisfies
  *"every two nonadjacent simplicial vertices share the same open neighborhood"*
  **if and only if** it is complete-split. Checked in both directions.
- **(C2) Theorem 5.3 (symmetrization):** the clone-class symmetrization (a) stays chordal at
  every step, (b) strictly decreases the clone-class count, (c) is $\Phi_\tau$-nondecreasing,
  and (d) terminates at a complete-split $S_{p,q}$ with $\Phi_\tau(\text{final})\ge\Phi_\tau(\text{start})$.

### Results
- **C1:** chordal graphs tested **531**; equivalence violations **0**. PASS.
- **C2:** chordal graphs symmetrized **531**; violations **0**;
  maximum steps to termination **4**. Every run terminated at a complete-split,
  stayed chordal, strictly reduced the clone-class count, and did not decrease $\Phi_\tau$. PASS.

### Verdict
**PASS.** Runtime 19.96 s. Both the terminal characterization (as an exact
equivalence) and the full symmetrization dynamics are confirmed on the exhaustive
chordal universe up to 7 vertices.

---
*This document reports an **independent computational verification** of the stated claims: each result was recomputed from scratch by a self-contained script (exact linear programming via SciPy/HiGHS for the fractional triangle-cover number, exact rational arithmetic for the integer optimization, and exhaustive enumeration of non-isomorphic graphs via the NetworkX atlas where indicated). This is computational evidence corroborating the analytic proof; it is not itself a formal proof. The machine-checked formal proof is the Lean development, which is conditional on the clas