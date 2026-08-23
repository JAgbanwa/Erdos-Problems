# Block B — AX1/AX2 Literature-Scope Memo

**Verdict: PASS**

- **Paper:** "Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing" (Paper III, v1.1.5)
- **Date:** 2026-07-28
- **Auditor:** Claude Opus 4.8 (Anthropic), invoked via Claude Code

## Mandate

AX1 and AX2 are in scope as **external inputs**. They are not arbitrary project assumptions; they
are standard recognized theorems from the cited literature. This block verifies that Paper III
states and uses them **no more strongly** than the literature supports.

---

## AX1 — Haxell–Rödl / Yuster

### As stated in the manuscript (Theorem 2.1, §2.4)

> "For every fixed graph `H`, `ν_H*(G) − ν_H(G) = o(|V(G)|²)` uniformly over graphs `G`. We apply
> this with `H = K₃`."

Cited to: Haxell–Rödl, *Combinatorica* 21 (2001) [11]; Yuster, *RSA* 26 (2005) [17].

### The literature

Haxell–Rödl (2001) proved that for every fixed graph `H`, the fractional and integral `H`-packing
numbers of any graph `G` differ by `o(|V(G)|²)`. Yuster (2005) gives the analogous integer/fractional
packing statement. For `H = K₃` this is exactly the triangle statement
`ν₃*(G) − ν₃(G) = o(n²)`, uniformly over `G`.

**Scope check:** The manuscript's Theorem 2.1 reproduces the literature statement verbatim in
generality (every fixed `H`, uniform over `G`) and then *specializes* to `H = K₃`. Specialization
is a weakening, never a strengthening. **No overstatement.**

### The cover-side (`τ₃*`) formalization

In the Lean layer (`PaperIII/AX.lean`) AX1 is stated with the fractional **cover** optimum `τ₃*`
rather than the fractional **packing** optimum `ν₃*`:

```lean
axiom AX1 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V) [Fintype V] [DecidableEq V] (G) [DecidableRel G.Adj],
  n₀ ≤ Fintype.card V → tau3Star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2
```

This is faithful for the following reason. By **finite LP strong duality**, the fractional packing
optimum and the fractional cover optimum coincide exactly: `ν₃*(G) = τ₃*(G)`. Hence

```
τ₃*(G) − ν₃(G)  =  ν₃*(G) − ν₃(G)  =  o(n²),
```

so the cover-side statement is *equal* to (not stronger than) the literature packing-side statement.
Strong LP duality is itself a standard, non-conjectural theorem — indeed it was independently
formalized in the Paper I freeze (`FiniteLPDuality.lean`). The substitution is documented explicitly
in the `AX.lean` header and in manuscript §11.6.

**Observation (non-blocking).** The Lean layer proves only *weak* duality
`nu3Star_le_tau3Star : ν₃* ≤ τ₃*` (in `Duality.lean`), not strong duality. Thus the cover-side
axiom AX1 imports, as part of the external result, the *equality* `ν₃* = τ₃*` (strong duality) in
addition to Haxell–Rödl. Both components are standard recognized results, so AX1 remains a faithful
encoding of imported literature; but a reader tracing the axiom footprint should note that AX1
bundles (Haxell–Rödl) + (finite LP strong duality). This is a packaging choice, not a defect, and is
disclosed by the authors. Recorded as finding F-B02 (severity: none).

### Direction/soundness

`ν₃*(G) = τ₃*(G)` (strong duality) and `ν₃*(G) − ν₃(G) = o(n²)` (Haxell–Rödl) jointly imply
`τ₃*(G) − ν₃(G) = o(n²)`, a **true** statement. AX1 is therefore sound (true), and used in the bulk
regime only to pass from a fractional margin `ν₃* ≥ T(G) + c_ε p²` to an integral one
`ν₃ ≥ ν₃* − o(n²) ≥ T(G)`. **No overstatement.**

---

## AX2 — Dross + Barber–Kühn–Lo–Osthus

### As stated in the manuscript (Theorem 2.3, §2.4)

> "For every `ε > 0`, every sufficiently large triangle-divisible graph `H` with
> `δ(H) ≥ (0.9+ε)|V(H)|` admits a triangle decomposition."

Cited to: Dross [7] (fractional triangle decomposition, min-degree `0.9v` fractional threshold),
combined with Barber–Kühn–Lo–Osthus, *Adv. Math.* 288 (2016) [2] (iterative absorption converting a
fractional decomposition threshold to an exact one, up to `ε` and for sufficiently large order).

### The literature

- **Dross (2016):** every graph with min degree `≥ 0.9 v` has a *fractional* triangle decomposition
  (fractional threshold `0.9`).
- **Barber–Kühn–Lo–Osthus (2016):** for triangle-divisible graphs of large order, an exact triangle
  decomposition exists once the min degree exceeds the fractional threshold by any `ε > 0`.

Composed, they give: triangle-divisible, large `n`, `δ(H) ≥ (0.9+ε)n` ⟹ exact triangle
decomposition. This is *precisely* the manuscript's Theorem 2.3 and the Lean `AX2`.

### Scope check — the load-bearing constant `0.9`

The Nash-Williams *conjecture* is that min degree `(3/4)n = 0.75n` suffices; that remains **open**.
The manuscript deliberately uses the **proven** threshold `0.9+ε`, **not** the conjectured `0.75n`.
The `AX2` hypotheses (triangle-divisibility `|E| ≡ 0 mod 3` and all degrees even; large order
`n ≥ n₀`; `δ(H) ≥ (0.9+ε)n`) match the literature's hypotheses exactly. **No overstatement.**

The manuscript's own application uses `ε₀ = 1/100`, giving `δ(H) ≥ 0.91p` on a residual of order `p`
(eq. 8.9), comfortably inside the proven regime.

### Lean encoding

```lean
axiom AX2 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V) [Fintype V] [DecidableEq V] (H) [DecidableRel H.Adj],
  H.edgeFinset.card % 3 = 0 → (∀ v, Even (H.degree v)) → n₀ ≤ Fintype.card V →
  ((0.9 + ε) * (Fintype.card V : ℝ) ≤ (H.minDegree : ℝ)) → HasTriangleDecomposition H
```

The two divisibility hypotheses (`|E| ≡ 0 mod 3`, all degrees even) correctly encode
"triangle-divisible". `HasTriangleDecomposition` is defined as an exact edge partition into
`IsNClique 3` triangles. Faithful.

---

## Conclusion

| Axiom | Literature | Manuscript scope | Overstated? |
|---|---|---|---|
| AX1 | Haxell–Rödl 2001 / Yuster 2005: `ν_H*−ν_H = o(n²)` | Specializes to `H=K₃`; cover-side via strong duality | **No** |
| AX2 | Dross 2016 + BKLO 2016: exact decomposition at `δ ≥ (0.9+ε)n` | Verbatim; uses proven 0.9, not conjectured 0.75 | **No** |

Both external axioms are faithful to the cited literature and are **not** stated more strongly than
the literature supports. One non-blocking observation (F-B02): the cover-side AX1 bundles finite LP
strong duality with Haxell–Rödl; both are standard and the substitution is disclosed.

**Block B verdict: PASS.**
