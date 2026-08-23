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

## Block F — Lean 4 / Mathlib formalization audit (NEW; run when the build is frozen)
Goal: confirm the machine-checked development actually proves the ledger nodes, with no
hidden assumption and no escape hatch. Reconstruct sources from the git object at the
frozen release commit (`git archive <sha> -- lean | tar -x …`); record `<sha>`,
`lean-toolchain`, `lake-manifest.json`. See `CLAIMS/LEAN_FORMALIZATION/README.md`.
Run every step per `EXECUTION_PROTOCOL.md` (background + incremental progress: a
`lake build` is long — stream its log and grep it; never let it look hung).

- **F1 (build / no sorry).** `lake build` exits 0 with **no** `error` and **no**
  `declaration uses 'sorry'`. Scan the git object, not the working tree:
  `git grep -nE "\bsorry\b|\badmit\b" <sha> -- 'lean/**/*.lean'` (ignore the word inside
  "sorry-free" prose) → must be empty. Report the exact toolchain + Mathlib rev used.
- **F2 (axiom report — the decisive gate).** Extend `gate.lean` with `#print axioms` for
  **every** ledger node (E-3.1 … E-9, Prop 10.1 both halves, Cor 1.2, AX1, AX2) and run
  `lake env lean gate.lean`. Then:
  - Unconditional (Layer E: `Prop_10_1_*`, `E_3_1`, `E_4_1`, `E_4_2`, `E_5*`, `E_6`,
    `E_7*`, `E_B`, `E_D*`) → axioms **exactly** `[propext, Classical.choice, Quot.sound]`.
    Any `AX1`/`AX2`/`sorryAx`/stray axiom here is a **blocking** finding.
  - Layer-X results (`Theorem_1_1`, `Corollary_1_2`, `E_4_3`, `E_8`) → **exactly**
    `[propext, Classical.choice, Quot.sound, PaperIII.AX1, PaperIII.AX2]` (or the subset
    actually used) — **and nothing else**. A third axiom = a hidden assumption;
    `sorryAx` = a sorry in the chain. Both are **blocking**.
- **F3 (statement ↔ ledger, verbatim).** `#check` each declaration; confirm its type
  matches the `LEDGER.md` node **including all hypotheses and quantifiers**. A theorem
  that compiles but states something weaker/different than the ledger node is a
  statement↔claim mismatch (blocking). Check especially: `Theorem_1_1` really quantifies
  over all split graphs with the `∃C, ∀G` shape; `Prop_10_1` carries the exact corridor
  hypotheses and the degree condition; AX1/AX2 are stated as in Layer X, not stronger.
- **F4 (no escape hatch).** `git grep -nE "native_decide|^\s*axiom |implemented_by|unsafe|opaque |@\[implemented_by" <sha> -- 'lean/**/*.lean'`: the only `^axiom` matches must be
  `PaperIII.AX1` and `PaperIII.AX2`; **no** `native_decide` used as a mathematical proof,
  no `unsafe`/`opaque`/`implemented_by` on load-bearing declarations.
- **F5 (AX1/AX2 in Lean = ledger, not stronger).** Read `AX.lean`; confirm the two
  `axiom` statements are character-faithful to `LEDGER.md` Layer X (the `∀ε∃n₀` forms),
  and are not silently strengthened (e.g. a linear `O(n)` rate where the paper only has
  `o(n²)`, or a min-degree threshold below `(0.9+ε)|V|`). Cross-check with Block B.
- **F6 (dependency DAG in Lean = paper's DAG).** From the Lean `import`s and the actual
  `theorem … := by … <lemma>` uses, reconstruct the module/lemma DAG; confirm it is
  acyclic and matches the paper's assembly (Block A2). Flag any Lean lemma that silently
  strengthens a hypothesis relative to its ledger node, or any use not present in the
  paper's proof.
- **F7 (Lean ↔ computation consistency).** For the finite nodes also audited numerically
  (E-3.1's `F`, E-4.2's margin, Prop 10.1's constants), confirm the closed forms /
  constants **defined in the Lean sources** are literally the same expressions verified
  in Blocks C/D (same `F`, same `μ`, same `2n`/`2304`/`p/8`). A divergence between the
  formalized statement and the audited statement is a finding even if each is internally
  consistent.
- **F8 (provenance ≠ correctness).** Do not accept "Aristotle/AI generated it" or
  "Lean checked it" as evidence by itself. The kernel only certifies what the *stated*
  theorem says; F2/F3 are what make the statement meaningful. A labeled localized `sorry`
  is strictly better than a hidden axiom — but either, at the release commit, is a
  finding against the "sorry-free, axiom-clean" claim.

---

### For every finding, record
`ID · claim · attack performed · inputs/ranges · outcome (CONFIRMED / PLAUSIBLE / REFUTED /
OUT-OF-SCOPE) · reproduction command · evidence file`.
