# Paper II — Independent Computational Audit: run instructions

Six self-contained scripts, one per audited section of the manuscript. Each script
recomputes the paper's claims from scratch (exact LP for the fractional
triangle-cover number, exact rational arithmetic for the integer optimization,
exhaustive graph enumeration where feasible) and writes a machine-readable
`results/summary.json` inside its own folder. Every script prints `RESULT: PASS`
or `RESULT: FAIL` and exits 0 on PASS.

## 0. Prerequisites (once)

Python 3.9+ and three packages:

```
pip install -r requirements.txt
```
(that is: numpy, scipy, networkx)

## 1. Run all six (from THIS folder, PAPER_II_AUDIT)

```
python3 A_vertex_copy_inequality/audit_A_vertex_copy.py
python3 B_clone_class_convexity/audit_B_clone_convexity.py
python3 C_terminal_characterization/audit_C_terminal.py
python3 D_completesplit_cover/audit_D_completesplit.py
python3 E_integer_maximization/audit_E_integer_max.py
python3 F_theorem_1_1_global/audit_F_global.py
```

Each writes `<folder>/results/summary.json` and a console log. You can pipe the
console output to the results folder if you want it saved, e.g.:

```
python3 A_vertex_copy_inequality/audit_A_vertex_copy.py | tee A_vertex_copy_inequality/results/run_A.log
```
(and likewise B..F). Saving the log is optional; the JSON is the source of truth.

## 2. What each script checks (and default scope)

| Script | Paper section | Default scope | Approx. runtime* |
|---|---|---|---|
| A | §3 vertex-copy inequality (Lemma 3.1, eqs 3.3–3.4) | all non-iso graphs n≤7, every nonadjacent pair | ~1–3 min |
| B | §4 clone-class ops (Lemmas 4.1–4.3 + C₄ necessity) | base graphs |W|≤4, class size ≤4; chordal graphs n≤7 | ~2–5 min |
| C | §5 terminal characterization + symmetrization (Lemma 5.1, Thm 5.3) | all non-iso chordal graphs n≤7 | ~1–2 min |
| D | §6 complete-split cover (Prop 6.2, Cor 6.3, Lemma 6.1) | all S_{p,q}, p≤12, q≤14, p+q≤16 | <1 min |
| E | §7 integer maximization (Prop 7.1, Thm 1.1 arithmetic) | every n from 1 to 2000, exact rational | ~20–60 s |
| F | Theorem 1.1 global | EXHAUSTIVE chordal n≤7; SAMPLED n=8..12 (3000 random chordal each) + full complete-split family | ~1–3 min |

*Rough, on a typical laptop; scipy's HiGHS LP is fast on these small instances.

## 3. Optional: widen the scope (environment variables)

All scripts accept overrides. Larger values = more coverage = longer runtime.

```
# A, C: enumeration ceiling (atlas supports up to 7)
AUDIT_NMAX=7 python3 A_vertex_copy_inequality/audit_A_vertex_copy.py

# B: base-graph size, class size, chordal ceiling
AUDIT_WMAX=4 AUDIT_SMAX=4 AUDIT_NMAX=7 python3 B_clone_class_convexity/audit_B_clone_convexity.py

# D: complete-split ranges
AUDIT_PMAX=14 AUDIT_QMAX=16 AUDIT_SUMMAX=20 python3 D_completesplit_cover/audit_D_completesplit.py

# E: check every n up to NMAX (exact, cheap)
AUDIT_NMAX=5000 python3 E_integer_maximization/audit_E_integer_max.py

# F: sampled range and samples-per-n (and RNG seed)
AUDIT_SMAX=14 AUDIT_K=5000 AUDIT_SEED=20260709 python3 F_theorem_1_1_global/audit_F_global.py
```

Note on scope honesty: the atlas of all non-isomorphic graphs ships only up to 7
vertices, so A/C/F1 are EXHAUSTIVE for n≤7. Section F for n≥8 is a random SAMPLE
(clearly labelled as such in the JSON), not an exhaustive proof over all chordal
graphs on n vertices.

## 4. After running

Send me back (or just let sync carry) the six `results/summary.json` files (and any
run logs). I will then generate the per-section English PDF certification reports,
the