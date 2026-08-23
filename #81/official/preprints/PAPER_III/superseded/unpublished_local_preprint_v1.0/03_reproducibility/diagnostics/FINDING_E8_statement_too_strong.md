# CRITICAL FINDING — the Lean `E_8` statement dropped the ledger's `O(n)` slack (⇒ false)

**Date:** 2026-07-23. **Severity:** high (affects soundness of the `Theorem_1_1` chain as
currently formalized). **Status of the mathematics:** the paper and `LEDGER.md` are CORRECT;
this is a **formalization-only** defect (a Gate-1 statement mismatch), fully repairable.

## What was found

While attacking the `sorry` in `E_8_very_sparse_packing_estimate` (`lean/PaperIII/E_8.lean`)
via the `AX2_pack` route, the prover determined — and produced a **machine-checked disproof**
(`diagnostics/E_8_Disproof.lean`, sorry-free, axiom-clean `[propext, Classical.choice,
Quot.sound]`) — that the lemma's conclusion

    ((G.edgeCount : ℝ) − (G.n : ℝ)^2 / 6) / 2  ≤  (G.nu3' : ℝ)        (⇔  Φ(G) ≤ n²/6)

is **false as stated**. Counterexample family (independently reconfirmed by exact rational
arithmetic): the degenerate `q = 0` case, admissible because `10·0 < p` and the degree
hypothesis `∀ i : Fin 0, …` is vacuous, gives `G = K_p`. For `p ≡ 0 (mod 6)`,

    ν₃(K_p) = (C(p,2) − p/2)/3,     Φ(K_p) = C(p,2) − 2ν₃ = p²/6 + p/6  >  n²/6 = p²/6,

so `Φ` exceeds `n²/6` by exactly `p/6`, for arbitrarily large `p`. Verified for
p = 6,12,18,102,300,996 (all `target > nu3'`). The disproof file instantiates `p = 2(n₀+1)`,
refuting the `∃ n₀` form directly.

This is a genuine **integral-packing obstruction**: even a loss-free packing of `K_p` cannot
reach the target, so no packing input (`AX2`, `AX2_pack`, …) can close it. This is exactly
why every §8 closure attempt failed — the goal was unprovable, not merely hard.

## Root cause — a Gate-1 mismatch

`LEDGER.md` (line 145–146) states **E-8** WITH slack:

> **E-8 (Sparse bound).** If `q = o(p)` and every `v∈I` has `d(v) > (2n−1)/6 + k`, then
> **`Φ(G) ≤ n²/6 + O(n)`.**

The Lean formalization stated `E_8` / `E_8_very_sparse_packing_estimate` /
`E_8_sparse_packing_estimate` with the **strict** bound `Φ ≤ n²/6` (no `O(n)`). Dropping the
`O(n)` is what made the lemma false. Per CLAUDE.md Gate 1 the Lean statement must match the
ledger verbatim — here it does not, and the discrepancy is load-bearing.

## Impact

- `Theorem_1_1` (Main.lean) is itself stated correctly WITH slack
  (`Φ ≤ n²/6 + C·n`), i.e. the main-result *statement* is true and faithful.
- But its *proof* routes through the strict `E_8`, whose `sorry` is unclosable (false). So the
  formalized `Theorem_1_1` currently **rests on an unprovable intermediate lemma** — not yet a
  sound proof, though the top-level statement is correct.

## Fix (recommended)

Restate the three §8 lemmas with the ledger's additive `O(n)` slack, e.g.

    ∃ C : ℝ, ∃ n₀, ∀ G, n₀ ≤ n → … → ((G.Phi:ℤ):ℝ) ≤ (n:ℝ)^2/6 + C*(n:ℝ)

(equivalently `(edgeCount − n²/6 − C·n)/2 ≤ nu3'`). Then:
- the degenerate `q=0`/`K_p` case holds (defect `p/6 = O(n)` absorbed);
- the `AX2_pack`-based mixed **KKI ∪ clique-remainder** construction becomes the correct route
  (the newly proved `clique_remainder_mindegree` is a building block);
- re-plumb Main.lean's derivation to thread the `C·n` through (Theorem_1_1 already carries a
  `C·n`, so this is compatible).

This makes the Lean statement MATCH the ledger (a correction, not a deviation).

## Evidence in this folder
- `E_8_Disproof.lean` — machine-checked `¬(strict E_8 statement)`; verify with
  `cd lean && lake env lean ../diagnostics/E_8_Disproof.lean` after adjusting the import path,
  or move it under `lean/PaperIII/` and `import PaperIII.E_8_Disproof`.
