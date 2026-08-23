# Claim Map — Paper II (exact fractional-cover theorem)

Target (Theorem 1.1/1.2, the ONLY claim):
`max over chordal G on n vertices of (|E(G)| − 2 τ₃*(G)) = ⌊(2n+1)²/24⌋`,
attained by a complete-split `S_{p,q}`.

| ID | Type | Statement | Auditor label | Evidence |
|----|------|-----------|---------------|----------|
| A | definitions | τ₃*, Φτ=|E|−2τ₃*, S_{p,q}, clone class, simplicial, copy op D7 | consistent across manuscript/ledger/Lean | read + reproduced (P1,P3,H) |
| B | Lemma 3.1 | vertex-copy inequality Φτ(G_{v→u})+Φτ(G_{u→v}) ≥ 2Φτ(G) | tested (P2) | exhaustive n≤5 + random |
| C | Lemma 4.1–4.3 | convexity lift; no clone class splits; simplicial-target chordality + C₄ necessity | necessity confirmed (P5) | exhaustive small |
| D | Lemma 5.1 | (H) ⇒ complete-split (incl. disconnected) | exhaustive n≤6 (P5) | 0 counterexamples |
| E | §6 | orbit averaging; two-branch LP; closed forms Prop 6.2/Cor 6.3; degenerate p≤1,S_{2,0} | closed forms = full LP (P3) | (p,q) grid 0..12 |
| F | §7 | max_{p+q=n} Φτ(S_{p,q}) = ⌊(2n+1)²/24⌋ | exact n≤5000 (P4) | complete-the-square + mod-24 residues |
| G | Theorem 1.1 | global assembly (5.3 ∘ §7), attainment, non-circular | reduction sound | P1 (exhaustive max) + assembly read |
| H | Lean | `PaperII.theorem_1_2`, sorry-free, axioms=[propext,Classical.choice,Quot.sound], hyp=IsChordal | build + #print axioms (pending capture) | independent re-elaboration |
| I | citations | chordal facts / external theorems within hypotheses | read | manuscript/ledger |
| J | scope | no cp / Erdős #81 / integral-packing over-claim | read | ledger states cp OUT OF SCOPE |

Theorem-closing claims: G (assembly) resting on B–F; H is the independent formal
certificate of the same statement. All are checkable and were checked (H pending
axioms-log capture a