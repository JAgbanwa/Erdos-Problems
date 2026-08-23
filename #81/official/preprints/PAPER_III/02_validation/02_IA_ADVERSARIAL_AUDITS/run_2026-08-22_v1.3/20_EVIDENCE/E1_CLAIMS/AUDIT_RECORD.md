# E1 -- mathematical claims and scope

**Verdict: `PASS`.**

Theorem 1.1 and Corollary 1.2 were parsed from the manuscript, not from Lean:

```
Theorem 1.1   exists C, every split graph G on n vertices:  |E(G)| - 2 nu3(G) <= n^2/6 + C n
Corollary 1.2 exists C, every split graph G on n vertices:  cp(G)             <= n^2/6 + C n
```

The absolute constant is **existential**, which is the "some linear error term" form and is
weaker than a bound with a named constant. The manuscript does not claim otherwise.

Scope, checked in both directions:

| Requirement | Result |
|---|---|
| claims the sharp quadratic coefficient | yes: "improves the quadratic coefficient from `3/16` to the sharp value `1/6`", 4 sharp-`1/6` statements |
| claims the `n^2/6 + O(n)` scale for split graphs | yes |
| does **not** claim a solution of the full chordal problem | confirmed: "The corresponding statement for general chordal graphs remains open", 3 times EN and 3 times ES |
| does **not** claim an optimal uniform linear coefficient | confirmed: it separates the sharp quadratic coefficient from the "still-undetermined least uniform linear coefficient" |
| two distinct sharpness roles | present and explicit |
| overbroad "resolves the split case" wording | **zero** occurrences, either language |

The three regimes, the endpoint cases and the transition from eventual to global statements are
audited in E2 (`K-COVER`, `K-GLOBAL`); the divisibility conditions in E3 (AX2 conformance).

Evidence: `scripts/v13_regression_text.py`, `results/regression_text.json`.
