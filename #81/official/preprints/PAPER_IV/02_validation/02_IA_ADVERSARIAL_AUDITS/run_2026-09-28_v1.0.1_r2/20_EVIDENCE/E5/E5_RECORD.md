# E5 — independent falsification (bounded; cannot prove universals)

**Scripts (auditor-written):** `e5_exact.py` (Fractions/sympy; 74 checks incl. 5 negative controls; 7 s) and
`e5_search.py` (pulp/CBC exact ILP, scipy/HiGHS LP, networkx; 13 checks + 1 runtime record, incl. 4 negative controls; 243.5 s;
seed 20260928). Results: `e5_exact_results.json`, `e5_search_results.json`; logs `10_LOGS/E5_*.log`.
Kill-switches were predeclared in the check names (a single FAIL would suspend the corresponding claim).

**Results: 0 failures; every negative control failed as required.**

Exact arithmetic covered: (4.6a) at 4·10¹² (and failure at 3.6·10¹², crossing ≈3.6725·10¹²); Lemma 4.2
coefficient comparisons; all coefficients of Lemma 5.3 / (5.15) / (5.15a); first-phase constants 1600/2920/219;
(5.12a), (5.13) (value 3.930083 ≥ 3.93; 3.931 fails), (5.14) (0.10159 ≤ 0.11; 0.02783 ≤ 0.029); Q₀ derivation;
Lemma 5.1 window numerics; (5.1a) regime inequalities symbolically; completing-the-square identity; (6.3) for all
0 ≤ k ≤ n < 300; (6.4) and max_k f(n,k) = M(n) for 6 ≤ n < 400; (6.12); (E.3) for all n ≥ 1, s < 20; (E.5);
(E.2e) both inequalities; ⌊(2n+1)²/24⌋ = M(n) (n < 2000) with the rational envelope as negative control;
D.1/D.2 arithmetic and Table 8 residue coverage; tightness of 16 and 48 for the retained account (6.7) by LP
(47 fails); (6.7a) closed form and its zero set {(1,1),(2,1)}; (5.18) expansion and error bound; Prop 8.1
contradiction chain and (8.5); C.3 schedule values a, z, k₀, h (= ⌊4/(δ/8)⁵⌋), L_T, M_T.

Bounded searches: complete-split cp = c₃ = c₄ = kh − C(k,2) and W* = 2C(k,2) for 2 ≤ k ≤ 5, k ≤ h ≤ 7 (negative
control K₅ ∨ I₂ outside the hypothesis fails); c₄(K_n) ≤ M(n) for n ≤ 10; c₃(K₁₀) = 19 > 18; **all 531 chordal
graphs with ≤ 7 vertices satisfy c₄(G) ≤ M(n)** (informational: consistent with b = 0 at these orders — the
paper does not claim b = 0); transport inequality (4.4), F₄ monotone direction and chordality preservation on 120
random chordal instances (dropping the averaging factor fails, as it must); identity (6.7b) on 60 exact optimal
partitions with random clique roots; E.3 witness has rooted defect ≤ s, not ≤ s−1, and cp = Q_s(n) (s ≤ 2);
`RootedDefectAt 0 ⇔ chordal` for all graphs on ≤ 6 vertices.

**Certo certificate re-examination (mandate E5).** Not performed: it lives in the internal-audit package, whose
contents are read only after the independent first pass (E6 incomplete) and after the E7 blocker stopped new
work. → deferred.

**Limitations.** Small orders only; the asserted theorems are asymptotic with astronomically large thresholds,
so no bounded test can refute Theorems B, C, 6.1 or Cor 6.1a directly. The tests exercise the identities,
constants and mechanisms on which they rest.

**E5 = INCONCLUSIVE** — every executed test passes and every negative control fails as required (no counterexample), but the mandated Certo-certificate re-examination was not performed.
