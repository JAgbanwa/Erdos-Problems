/-
# The §10 cover-down input `CoverDownK3`, as stated, is false.

`BKLO/InputsVortex.lean` records the cover-down lemma of BKLO §10, specialised to `F = K₃`, as the
interface

```
CoverDownK3 : ∀ c γ, 9/10 < c → 0 < γ → ∃ K n₀, 2 ≤ K ∧ ∀ W'' ⊆ W' ⊆ W, F, …
```

with the size window `K|W'| ≤ |W| ≤ K²|W'|`, `K|W''| ≤ |W'|`, and with **triangle-divisibility of
`F` as the only divisibility hypothesis**.  This file proves that this statement is false: for
`c = 91/100` and `γ = 1/20`, *no* ratio `K ≥ 2` and threshold `n₀` work.  There are two obstructions,
and they cover complementary ranges of `K`:

* **`K = 2` — counting** (`BKLO.not_coverDownK3At_two`, `BKLO/CoverDownRefutationA.lean`).
  With `|W| = 2|W'|` the set `A = W \ W'` is as small as the window allows, and a complete
  `20`-partite configuration has `|W'||A| = 100s²` edges between `W'` and `A` — all of which must be
  covered — but only `45s²` edges inside `A`.  Since a triangle has at most two edges crossing
  between `W'` and `A`, and its third edge then lies inside `A` or inside `W'`, covering everything
  would consume more than `γ|W'|²` edges inside `W'`.

* **`K ≥ 3` — parity** (`BKLO.not_coverDownK3At_ge_three`, `BKLO/CoverDownRefutationB.lean`).
  With `|W'| = |W|/K²` and `|W''| = |W'|/K` a vertex `v₀ ∈ W''` can have *all* of its edges inside
  `W'` going to `W''` — the level that must not be touched — and an odd number of them.  Its other
  edges must all be covered, so the covered edge set has odd degree at `v₀`, which is impossible for
  an edge-disjoint family of triangles.

Neither obstruction is an artefact of degenerate sizes: both configurations satisfy every hypothesis
of the interface (`n₀ ≤ |W|` for arbitrarily large `|W|`, the full size window, triangle-divisibility
of `F`, and minimum degree `> c|W|` with `c = 91/100 > 9/10`), and in the `K ≥ 3` configuration the
sets `W''` and `F ∩ cliqueEdges W''` are nonempty.

What the true cover-down lemma of BKLO needs, and what the interface as stated omits, is a
divisibility hypothesis on the *levels* — in BKLO the vortex is chosen so that each `G[W_i]` is
`K₃`-divisible, which is exactly what rules out the parity obstruction — together with a size window
narrow enough (`K` large) to rule out the counting obstruction.  See `RESIDUAL.md`.

Everything here is `sorry`-free.
-/
import BKLO.CoverDownRefutationA
import BKLO.CoverDownRefutationB

open Finset

namespace BKLO

/-- **The §10 cover-down interface `CoverDownK3` is false as stated.**

At the density `c = 91/100 > 9/10` and the damage tolerance `γ = 1/20` no size ratio `K ≥ 2` and no
size threshold `n₀` can work: `K = 2` is refuted by the counting counterexample
(`not_coverDownK3At_two`) and `K ≥ 3` by the parity counterexample
(`not_coverDownK3At_ge_three`). -/
theorem not_coverDownK3 : ¬ CoverDownK3 := by
  intro h
  obtain ⟨K, n₀, hK, hAt⟩ :=
    coverDownK3_iff.1 h (91 / 100) (1 / 20) (by norm_num) (by norm_num)
  rcases eq_or_lt_of_le hK with hK2 | hK3
  · exact not_coverDownK3At_two n₀ (hK2 ▸ hAt)
  · exact not_coverDownK3At_ge_three hK3 n₀ hAt

end BKLO
