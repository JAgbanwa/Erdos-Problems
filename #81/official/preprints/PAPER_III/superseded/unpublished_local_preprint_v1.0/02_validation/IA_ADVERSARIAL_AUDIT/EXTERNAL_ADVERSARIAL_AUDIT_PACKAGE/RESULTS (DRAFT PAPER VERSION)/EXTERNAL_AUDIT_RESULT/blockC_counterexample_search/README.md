# Block C — Adversarial counterexample search (finite / closed-form claims)

Every audited lemma asserts a bound that concrete instances can falsify. Strategy:
compute the claimed bound exactly; try to beat it. A confirmation is only accepted
with an explicit exact certificate; a refutation would be an explicit instance.

| Script | Attacks | Method (independent of the internal audit) | Ranges | Result |
|---|---|---|---|---|
| `c1_nu3star_certificates.py` | C1: Thm 3.1 / Cor 10.4, ν₃*(H(p,q,d))=F | (M1) exact rational **sandwich certificates**: feasible dual covers (ν₃*≤F, all (p,q,d)) + orbit-LP vertex enumeration by rational Gaussian elimination (ν₃*≥F) — equality PROVED per instance; (M2) **raw exact simplex** (Bland, `Fraction`) on the actual graph, no orbit reduction, as an independent spot-check | M1: full grid 3≤p≤40, 0≤q≤2p+2, all d (48,469) + boundary+400 random to p=10⁴, q≤4p (610) = **49,079 certified**. M2: 266 instances (≤80 triangles each; exact where the internal audit was float). **49,345 total, 0 failures** | results/c1_nu3star_results.txt |
| `c2_margin_grid.py` | C2: Thm 4.2 core (4.5), all three branches | ×48 clearing → pure-integer arithmetic (no Fraction, no float) | exhaustive 3≤p≤150 (internal: 48), all q≤2p, all d; 200k random p≤10⁹; boundary sweeps incl. p=2304 | 2,497,464 checks, **0 violations** |
| `c3_lemmas_packing.py` | C3: E-5.1, Cor 5.3, L5.2, L7.1; C5 sharpness | verified packing certificates (greedy+local search) with escalation to own exact B&B; forced 40-instance exact-ν₃ refutation sample; CBC cross-validated (status-checked) | 821 distinct instances, p≤7, q≤8, 9 profile families + 300 random; L7.1 over all centers R=S_j and R=∅ with (7.1)–(7.2) checked per instance | 1,854 bound checks, **0 refuted**; CBC 40/40 agrees; sharpness ν₃=C(p,2) both directions p≤24, (Φ−n²/6)/n = 1/6 exactly |
| `c4_corridor.py` | C4: Prop 10.1 (i)+(ii) | constructed factorization packings, edge-disjointness verified with exact numpy counters; Hungarian assignment on exact integer matrices | (i) p∈{36,49,64,100}, s∈{0,1,⌊6√p⌋}, 3 profiles each; (ii) **true scale p=2304, s=288** (n=6624): common m∈{0,47,94,95} + mixed two-center | **all certified**; window [6√p,p/8] degenerates to {288} at p=2304 exactly as the threshold predicts |
| `c6_appendixB.py` | C-11: Appendix B parity construction | exhaustive enumeration | 2≤p≤16, all even O: 65,534 cases | **0 violations** |
| `c7_cloning_lemma41.py` | C-5: Lemma 4.1 (tested computationally nowhere else) | exact rational simplex on full triangle LP of arbitrary-profile split graphs vs exact RHS | 153 distinct profiles, p≤6, q≤5 | **0 violations**, 78 tight |

Auditor-side corrections recorded: the first version of C4's mixed two-center
certificate was too weak (a construction deficit of the audit, not of the paper) and
was rebuilt following the paper's own §7 mechanism, after which it cleared the bound
with slack 1,397. See the report §3.

Reproduce: `python <script>` (deterministic seeds; logs under `results/`).
