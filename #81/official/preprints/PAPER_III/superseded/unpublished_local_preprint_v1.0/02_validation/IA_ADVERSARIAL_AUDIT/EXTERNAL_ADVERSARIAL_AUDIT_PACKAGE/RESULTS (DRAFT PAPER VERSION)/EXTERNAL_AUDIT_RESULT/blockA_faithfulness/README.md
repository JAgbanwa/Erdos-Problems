# Block A — Faithfulness & internal consistency (paper ↔ ledger)

**Attacked:** A1 verbatim-equivalence of every `LEDGER.md` node against the v0.9.5
manuscript; A2 reconstruction of the dependency DAG from the paper's actual proofs
(acyclicity, §9 assembly hygiene); A3 the "only two external inputs" claim,
including whether Appendix D really removes the coloring citation.

**Method:** full adversarial reading of both documents by the auditor (statements,
hypotheses, constants, quantifiers compared node-by-node; every §9.3 inequality chain
re-derived by hand and then machine-verified in Block D), plus a mechanical
component (`check_census.py`): 35 statement anchors verified present in the
manuscript and a line-numbered census of every external-theorem mention.

**Reproduce:** `python check_census.py` (writes `results/blockA_census_results.txt`,
exit 0 iff all anchors present).

**Result:**
- A1: **no statement-level discrepancy** — see `results/blockA_faithfulness_table.md`.
- A2: DAG **acyclic**, matches the ledger's DAG; the §8↔§9 degree-bound interplay is
  conditional, not circular; §9 uses only cited ingredients.
- A3: AX1/AX2 usage localization **confirmed**; Appendix D self-containment
  **confirmed** (D.1–D.3 read line-by-line; König proved inline;
  Borodin–Kostochka–Woodall not load-bearing).
- **FINDING A-1 (minor):** the strongest self-containment phrasings (§2.4, §11.3)
  overstate — §8 also uses Dirac and Turán, and Lemmas 5.1/5.2/7.1 (hence Prop 10.1)
  use the classical 1-factorization χ'(K_t) stated without proof. Classical,
  constructive facts; the ledger itself lists them.
- OBS A-2 (figure paths), OBS A-3 (§11.6 audit counts not reproducible from this
  package), OBS A-4 (Thm 2.1 stated for all H, only K₃ used): presentational.

**Verdict: PASS_WITH_OBSERVATIONS** (1 minor finding, 3 observations, 0 blocking).
