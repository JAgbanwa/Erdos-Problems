# Block E — Audit the internal audit (`OUR_INTERNAL_AUDIT/`)

**Attacked:** E1 reproducibility of the four internal blocks; E2 adversarial reading
of their scripts (vacuous checks, float masking, solver-status handling, grid
arithmetic); E3 boundaries their grids missed.

**Method:** re-ran all four `verify_*.py` from a pristine copy on the same toolchain
and diffed outputs byte-for-byte; independently re-derived every claimed grid count;
read all 606 lines of their scripts adversarially; diffed their shared formula module
against independently written closed forms on 20k+ boundary/random cases
(`e3_boundary_stress.py`).

**Reproduce:** `python e3_boundary_stress.py` → `results/e3_boundary_results.txt`.
E1 re-run: copy `OUR_INTERNAL_AUDIT/`, move each `results/` aside, run the four
`verify_*.py`, diff against the shipped outputs (they contain no timestamps).

**Result:**
- E1: all four blocks **reproduce BIT-IDENTICALLY**; all claimed counts (12/12;
  351/351 dev 3.9e-14; 78,384/78,384; 372/180/180) re-obtained and their grid sizes
  re-derived arithmetically.
- E2: **3 minor findings** — block02's advertised "(EXACT)" second check is not
  implemented; block02 is float-with-tolerance by design (masking-capable, did not
  bite); block04 ignores CBC solver status (fail-safe direction only) — plus 3
  observations. None verdict-affecting. See `results/blockE_findings.md`.
- E3: their shared formula module has **0 mismatches** vs independent formulas at all
  boundaries (d=0, d=p, q=0, q=2p±1, p=2304, p=10^6, 20k random); their grid blind
  spots are covered by Blocks C1/C2/C3 of this deliverable.

**Verdict: PASS_WITH_OBSERVATIONS** (internal audit's claims hold; its evidence had
three repairable weaknesses, all repaired here with stronger independent methods).
