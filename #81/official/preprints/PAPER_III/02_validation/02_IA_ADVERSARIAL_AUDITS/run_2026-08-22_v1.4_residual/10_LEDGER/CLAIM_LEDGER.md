# Claim ledger -- Paper III v1.4

| Claim | Status after this audit | Basis |
|---|---|---|
| Theorem 1.1: `exists C`, every split graph, `|E| - 2 nu3 <= n^2/6 + C n` | **not established as true**; no counterexample found; compiles with a clean footprint | gates 5, 7; E2 |
| Corollary 1.2: same bound for `cp` | same | gates 5, 7 |
| the quadratic coefficient `1/6` is sharp | **confirmed as claimed**, witnessed by the complete-split family | gate 2; E2 Section 10 |
| the least uniform linear coefficient | **explicitly not claimed** by the paper | gate 2 |
| the full chordal problem | **explicitly left open** by the paper, and open in the literature | gates 2, 8 |
| AX1 matches manuscript Theorem 2.1 at `H = K3` | **PROVED**, an `iff` in both directions | gate 7 |
| AX2 matches manuscript Theorem 2.3 including `0.9` | **PROVED** | gate 7 |
| `tau3Star = nu3Star` at PaperIII's names | **PROVED** by the auditor's own bridge | gate 7 |
| `K-CORRIDOR` Lemmas 5.1-7.1 | **REDERIVED**, Lemma 7.1's assembly exact to zero | E2 |
| `K-SPARSE` Section 8 | **REDERIVED**, including that `|V(H)| = p` at the `0.91p` threshold | E2 |
| `K-GLOBAL` eventual-to-global | **REDERIVED** | E2 |
| `K-EPS` tolerance ledger | **REDERIVED** with explicit `c_eps = eps^2/48` | E2 |
| `K-COVER` exhaustiveness | **REDERIVED** at four levels | E2 |
| no project axiom in the delivered closure | **CONFIRMED** over 704 modules | gates 5, 6 |
| novelty of the integral split-graph `1/6` | **no collision found** in the searched corpus | gate 8 |
