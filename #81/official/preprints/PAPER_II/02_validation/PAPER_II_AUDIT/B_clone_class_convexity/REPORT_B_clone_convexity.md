---
geometry: margin=1in
fontsize: 11pt
---
# Independent Computational Verification
## Paper II — Section 4: clone-class operations (Lemmas 4.1–4.3)

**Author of record:** Juan Pablo Traverso Gianini  **Date:** 2026-07-09  
**Artifact:** `B_clone_class_convexity/audit_B_clone_convexity.py`  **Verdict: PASS**

### Claims verified
- **(B1) Lemma 4.1 (discrete convexity):** for the interpolation family $H_k$ (with $k$
  class-vertices attached to $N_A$ and the rest to $N_B$), the second differences satisfy
  $f(k-1)+f(k+1)\ge 2f(k)$ where $f(k)=\Phi_\tau(H_k)$; hence $f(k)\le\max(f(0),f(s))$.
- **(B2) Lemma 4.2:** copying a whole clone class onto another strictly decreases the number
  of maximal clone classes and **splits no other class**.
- **(B3) Lemma 4.3 + necessity:** copying onto a **simplicial** target preserves chordality;
  and an explicit example shows a **non-simplicial** target can break it ($C_4$).

### Method
Python 3, NetworkX (graph atlas + chordality), SciPy `linprog` method=`highs`; exact `fractions` where noted.

### Results
- **B1:** configurations tested **8670** (base graphs $|W|\le 4$, class size
  $\le 4$, all neighborhood pairs); minimum second difference **-3.55e-15**
  (numerically zero), minimum endpoint margin **0.00e+00**. PASS.
- **B2:** admissible class-pairs tested **5663**; clone-class count strictly
  decreased with no split in every case. PASS.
- **B3:** simplicial-target class-copies tested **5663**; chordality preserved
  in every case. Necessity example **found**. PASS.

### Necessity example (simpliciality is required)

Take the chordal graph $G$ on vertices $\{0,1,2,3\}$ with edges $\{1,3\}$ and $\{2,3\}$
(vertex $0$ isolated). Copying the source class $\{0\}$ onto the target class $\{3\}$,
whose open neighborhood $\{1,2\}$ is **not** a clique (so the target is non-simplicial),
produces the 4-cycle $C_4$ with edges $\{0,1\},\{0,2\},\{1,3\},\{2,3\}$, which is **not
chordal**. This confirms that the simpliciality hypothesis of Lemma 4.3 is necessary:
without it, a clone-class copy can destroy chordality.

### Verdict
**PASS.** Runtime 58.82 s. Discrete convexity, strict progress without splitting,
and chordality preservation (with its necessity) all hold across the enumerated universe.

---
*This document reports an **independent computational verification** of the stated claims: each result was recomputed from scratch by a self-contained script (exact linear programming via SciPy/HiGHS for the fractional triangle-cover number, exact rational arithmetic for the integer optimization, and exhaustive enumeration of non-isomorphic graphs via the NetworkX atlas where indicated). This is computational evidence corroborating the analytic proof; it is not itself a formal proof. The machine-checked formal proof is the Lean development, which is conditional