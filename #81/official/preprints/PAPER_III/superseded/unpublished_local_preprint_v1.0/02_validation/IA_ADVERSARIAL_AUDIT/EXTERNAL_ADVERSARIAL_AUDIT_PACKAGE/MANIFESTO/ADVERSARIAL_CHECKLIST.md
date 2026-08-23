# Adversarial Checklist — mandatory tasks

Organize your deliverable into these blocks. Each is a place to **attack**; for each,
produce independent scripts/derivations, written results, and a certificate. You may add
further blocks if you find new attack surfaces.

---

## Block A — Faithfulness & internal consistency (paper ↔ ledger)
Goal: catch the classic failure "they proved something other than what they claim."
- A1. Confirm every named result in `CLAIMS/LEDGER.md` (E-3.1 … E-9, Prop 10.1, AX1, AX2,
  Cor 1.2) appears in the manuscript with a **verbatim-equivalent** statement (same
  hypotheses, quantifiers, constants). Report every discrepancy, however small.
- A2. Reconstruct the dependency DAG from the paper's proofs (not from the ledger's
  claimed DAG) and check it is **acyclic** and that the §9 assembly of Theorem 1.1 uses
  **only** the ingredients it cites. Flag any hidden dependency or circular reference.
- A3. Verify the "only two external inputs" claim: that Sections 3–9 and Appendices A–D
  depend on **no** external theorem other than AX1 and AX2. In particular check that
  Appendix D really proves the list-edge-coloring input from scratch (kernel lemma,
  Gale–Shapley, König, Galvin max-degree case), so no Borodin–Kostochka–Woodall or Galvin
  citation is load-bearing.

## Block B — External-input faithfulness (AX1, AX2 vs. literature)
Goal: make sure the axioms are the published theorems, not convenient overstatements.
- B1. AX1 = Theorem 2.1 (Haxell–Rödl integer/fractional packing; Yuster). Check the exact
  statement used (`ν₃*(G) − ν₃(G) = o(|V|²)`, uniform over graphs) matches the cited
  results and is **not stronger**. Verify the citations (authors, venue, statement).
- B2. AX2 = Theorem 2.3 (Dross fractional decomposition + Barber–Kühn–Lo–Osthus
  edge-decomposition). Check the min-degree threshold used (`δ ≥ (0.9+ε)n`), the
  divisibility hypotheses, and that the invoked conclusion is within the cited theorems.
- B3. Confirm AX1/AX2 are used **only** where the paper says (bulk §4.3/§9.1; sparse §8),
  and that Prop 10.1 and the corridor use **neither**.

## Block C — Adversarial counterexample search (finite / closed-form)
Goal: actively try to violate the finite claims, over ranges larger than ours and with
adversarial/random instances.
- C1. Theorem 3.1 / F(p,q,d): for a grid AND random `(p,q,d)` (push `p` well beyond our
  `p≤8`), compute `ν₃*(H(p,q,d))` by an **independent** method (e.g. exact rational LP /
  a different solver) and test equality with the closed form F. Report any mismatch.
- C2. Theorem 4.2 margin (4.5): exact-rational test over a larger grid than our `p≤48`;
  search for any `(p,q,d)` violating `F ≥ qd/2 + (C_α+μ)p² − p/2`.
- C3. Lemma 5.1 / Corollary 5.3 and Lemma 5.2, 6.1, 7.1: generate split graphs
  (systematic + random, adversarial profiles) and check the stated Φ bounds using an
  independent integral triangle-packing computation (`ν₃`). Try to find a violating graph.
- C4. Proposition 10.1: verify the explicit constants (`2n`; the `p≥2304`, `6√p≤s≤p/8`
  window) on concrete instances; probe the boundary cases (`s=6√p`, `s=p/8`, `p=2304`).
- C5. Sharpness: confirm the extremal family `K_p ∨ K̄_{2p}` attains `n²/6 + n/6` and that
  no audited instance beats the `1/6` leading constant.

## Block D — Independent re-derivation of the algebra
Goal: don't trust our identities; redo them.
- D1. Re-prove every algebraic identity of `OUR_INTERNAL_AUDIT/block01` with a **different**
  CAS or by hand-checked exact arithmetic (T-identity, (9.12), (9.19), (9.20), δ≥7/8 both
  parities, threshold `p=2304`, μ continuity, the (4.5) closed forms).
- D2. Independently derive the three cover-vertex values of F and confirm they are exactly
  the three terms of the min.

## Block E — Audit the internal audit
Goal: break `OUR_INTERNAL_AUDIT/`.
- E1. Re-run our four blocks; confirm the reported counts (12/12; 351/351; 78,384/78,384;
  E-5.1 180/180 & Cor 5.3 180/180 over 372 instances) are reproducible bit-for-bit where
  deterministic.
- E2. Read our scripts adversarially: look for off-by-one grid bounds, wrong guards,
  vacuous checks, float tolerance masking a real gap, triangle/edge enumeration errors, or
  an ILP that is silently relaxing to an LP. Report any script defect even if the
  underlying claim still holds.
- E3. Stress boundaries our grids may have missed (e.g. `d=0`, `d=p`, `q=0`, `q=2p`,
  `p` at the corridor threshold).

---

### For every finding, record
`ID · claim · attack performed · inputs/ranges · outcome (CONFIRMED / PLAUSIBLE / REFUTED /
OUT-OF-SCOPE) · reproduction command · evidence file`.
