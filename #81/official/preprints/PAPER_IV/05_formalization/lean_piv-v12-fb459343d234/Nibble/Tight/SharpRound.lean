/-
# Nibble — the ITERABLE (sharp) tight-band round

`Nibble.exists_round_explicit` (`Nibble.Tight.RoundExplicit`) is an unconditional nibble round: for a
`r`-uniform hypergraph with degrees in `[δ, Δ]`, `Δ ≤ 2δ`, codegrees `≤ κ ≤ θγ³Δ/(1280r)` and
`|V| ≥ 512r/γ` it produces a retained set `R'` and an exceptional set `B` with `|B| < θ|V|` such that
every uncovered vertex outside `B` has residual degree in

  `[δ − γΔ − γ²Δ,  Δ − (r−1)δγ/(4r) + γ²Δ + 16γ²Δ/θ]`,

and the round covers more than `|V|γ/(8r)` vertices.  Two features of that band make it
**non-iterable**, and this file isolates exactly what an iterable round must deliver.

1. **The upper tolerance carries a `1/θ`.**  A `T`-round nibble covering a `γ/(8r)` fraction per
   round needs `T ≍ γ^{-1}log(1/β)` rounds, and the exceptional sets accumulate, so the per-round
   exceptional fraction must obey `θ ≲ βγ/log(1/β)`.  Then `16γ²Δ/θ ≳ γΔ·log(1/β)/β` is LARGER than
   the first-order per-round gain `≍ γΔ`, and the degree ceiling would grow instead of falling.
   The `1/θ` comes from bounding the pair-excess correction by Markov
   (`Nibble.exists_tight_round_cheb`, the term `Pb/s`).  It disappears once the safe degree is
   treated directly by Chebyshev around its own mean, which is what `Nibble.Tight.SafeDegreeVariance`
   does — but its variance bound still carries a `Θ(γ³Δ²)` Bonferroni residue
   (`safeDegree_variance_le_codegree`), which reinstates the same obstruction with `t ≍ γΔ√(γ/θ)`.
   The true variance is `Θ(γΔ + γ²Δ²κ/Δ)`; obtaining it needs the third-order cancellation described
   in the header of `Nibble.Tight.SafeDegreeVariance`.

2. **The two drop constants must MATCH.**  The floor falls by `≤ (r−1)γΔ/r` per round while the
   ceiling falls by `≥ (r−1)δγ/(4r)` — a factor `4` mismatch, which over `T ≍ γ^{-1}log(1/β)` rounds
   multiplies the band ratio by `β^{-Θ(r)}`.  An iterable round must lose only a `1 ± O(ν + γ)`
   factor between the two drops, where `ν = 1 − δ/Δ` is the current relative band width; this is the
   `(1 − L/U)` factor the classical nibble carries.

**Exactly where the gap sits (2026-08-06).**  Unwinding `Nibble.exists_round_explicit` shows that its
underlying round `Nibble.exists_round_residual_band_cheb` in fact already delivers BOTH first-order
constants of `Nibble.SharpRoundFor` exactly:

* its raw floor is `δ − (r−1)Δ·(Δp) − t = δ − ((r−1)/r)γΔ − γ²Δ` (defect 2 above is an artefact of
  the final weakening `((r−1)/r)γΔ ≤ γΔ` performed inside `exists_round_explicit`), and
* its raw ceiling is `Δ − (r−1)δ·(δpL) + t + s` with `L = (1−p)^{rΔ} ≥ 1 − γ`, i.e. a drop
  `((r−1)/r)·γ·δ²(1−γ)/Δ`, which dominates the drop `((r−1)/r)·γ·(δ − lost(v))·δ(1−γ)/Δ` asked for
  here.

So the SOLE obstruction is the tolerance `s`.  The pair-excess mean is
`Pb = Δ(r−1)²(Δ²p² + κp) ≈ γ²Δ` and Markov forces `s ≳ Pb/θ = 16γ²Δ/θ`, whereas `SharpRoundFor` asks
for `s ≤ εγΔ`; that would need `θ ≥ 16γ/ε ≥ 4`, which is impossible for ANY schedule — the failure
is not a matter of tuning `γ`, `ε`, `θ`.  Routing through the direct safe-degree Chebyshev round
`Nibble.exists_safe_round_cheb` instead needs `Vs < θ·ε²γ²Δ²`, where `Vs` bounds the per-vertex
safe-degree variance.  The bound proved in `Nibble.safeDegree_variance_le_codegree` is

  `Vs ≤ Δ²((r−1)²ε₂ + 2(r−1)³q_hi(q_hi² + ε₂)) + q_hi·κ(r−1)Δ ≈ 2γ³Δ² + rκγΔ`,

and `2γ³Δ² < θε²γ²Δ²` fails (`θ` is exponentially small in the schedule length).  The `Θ(γ³Δ²)`
term is the Bonferroni cross term `Q_e·B_{e'}`; the true variance is `Θ(γΔ + rκγΔ)`, for which
`Vs < θε²γ²Δ²` IS satisfiable — the degree threshold `D₀` and the codegree factor `c₀` of
`SharpRoundFor` are chosen after `θ` and `ε`, so `Δ ≥ D₀ ≥ 2/(θε²γ)` and `κ ≤ c₀Δ ≤ θε²Δ/(4r)`
suffice.  Hence the single remaining mathematical input of the whole nibble is the sharp per-vertex
variance bound

  `Var(safeDeg(v)) ≤ C(r)·(γΔ + κγΔ)`,

i.e. removing the `Θ(γ³Δ²)` Bonferroni residue.  Two routes to it:

* a third-order inclusion–exclusion estimate, replacing the one-sided Bonferroni bounds
  `Q_e − B_e ≤ ℙ(S_e) ≤ Q_e` used in `Nibble.safeDegree_variance_le` by the third-order Bonferroni
  bound applied to the union `S_e ∩ S_{e'} = ⋃_{(u,u')} (C_u ∩ C_{u'})`; the `Θ(γ³)` terms then
  cancel against `Q_eB_{e'} + Q_{e'}B_e`, at the cost of controlling triple and quadruple coverage
  intersections;
* **bounded differences (Efron–Stein)**, which is the shorter route and whose combinatorial input is
  proved in `Nibble.Tight.FlipStability`.  The safe degree is a function of the independent edge
  retentions, and flipping one edge `e` moves the covered set only inside `⋃ flipInfluence R e`
  (`Nibble.covered_insert_sdiff_subset`), a set of at most `r(1 + N_e)` vertices with
  `N_e = #{f ∈ R : f meets e}` (`Nibble.card_biUnion_flipInfluence_le`), so the safe degree at `v`
  moves by at most `∑_u codeg(v,u)` over that set (`Nibble.abs_safeDegree_flip_le`).  Efron–Stein
  then gives

    `Var(safeDeg(v)) ≤ Σ_e p·𝔼[(Δ_e safeDeg(v))²]`,

  whose leading part is `p·r·Σ_u deg(u)·codeg(v,u)² ≤ p r Δ·κ(r−1)Δ = O(r²)·γκΔ` (using
  `Σ_{u ≠ v} codeg(v,u)² ≤ κ(r−1)deg(v)` and `p = γ/(rΔ)`), and whose distance-two part carries an
  extra factor `γ`.  That is exactly `O_r(γΔ(1 + κ))`, with NO `Δ²` term.  The missing ingredients
  are the transfer of the retention field to the explicit Bernoulli product measure on `Finset H`
  and the Efron–Stein (variance tensorization) inequality on the hypercube, neither of which is in
  Mathlib.

`Nibble.SharpRoundHyp` below is precisely the round with those two defects repaired, in the form the
iteration consumes:

* the tolerances are `ε·γΔ` on both sides, with `ε` a free parameter (fixed before the round, at the
  cost of a larger degree threshold `D₀` and a smaller codegree factor `c₀`);
* the ceiling drop is `((r−1)/r)·γ·(δ − lost(v))·δ·(1−γ)/Δ`, where `lost(v)` is the number of edges
  at `v` that leave the live set `A` — the honest first-order drop;
* the degree floor is required only on a LIVE SET `A` (a `α`-fraction of the vertices), the ceiling
  globally; this is what lets the iteration keep the covered vertices and the accumulated
  exceptional vertices inside the same vertex type.

Nothing in this file is proved; it is a specification.  The assembly is COMPLETE and sorry-free:
`Nibble.tight_round_step` (`Nibble.TightAssembly`) is one round of the schedule with the tight band,
the global ceiling, the codegree bound and the exceptional budget all re-established;
`Nibble.exists_tightParams` (`Nibble.TightSchedule`) builds the schedule; and
`Nibble.roundOracleExistsCeil_holds`, `Nibble.nibbleTheoremMostCeil_holds`,
`Nibble.nibbleTheoremMostCeilSized_holds`, `Nibble.nibbleTheorem_holds`,
`Nibble.AX1.ax1_holds` (`Nibble.TightNibble`) turn it into `NibbleTheoremMostCeil`,
`NibbleTheoremMostCeilSized`, `NibbleTheorem` and AX1 — and those are now UNCONDITIONAL in the
sharp round: the schedule feeds its own `(γ, ε)` to `Nibble.sharpRoundHyp_of_two_gamma_le_eps`
(see the status update at the end of this header).

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.

## Status update (2026-08-07)

The obstruction described above — the sharp per-vertex safe-degree variance — is now **CLOSED**.

* `Nibble.Tight.CubeVariance` builds the elementary Bernoulli cube and the Efron–Stein
  (variance tensorisation) inequality on it; `Nibble.Tight.CubeRetention` realises the retention
  field `Nibble.BernoulliRetention` on that cube.
* `Nibble.safeDegCube_variance_le` (`Nibble.Tight.SharpVariance`) is the sharp bound
  `Var(safeDeg(v)) ≤ 2p·r²κΔ²(1 + prΔ + (prΔ)²)`, i.e. `≈ 6rγκΔ` at `p = γ/(rΔ)`: the `Θ(γ³Δ²)`
  Bonferroni residue is gone, exactly as predicted above.
* `Nibble.exists_sharp_round_band` (`Nibble.Tight.SharpRoundProof`) is the resulting Chebyshev round
  on an active set: it turns ANY two-sided estimate of the MEAN safe degree into a band on the
  residual degrees of the active uncovered vertices, off an exceptional set of size `< a`, together
  with the cover bound `> |A|·δp(1−p)^{rΔ}/2`.
* `Nibble.Exp_safeDegCube_ge` and `Nibble.Exp_safeDegCube_le` supply those two mean estimates: the
  union bound for the floor, and the second Bonferroni inequality — with the degree floor used only
  on the active set `A`, so that the drop is carried by the `deg(v) − lostDegree K Aᶜ v` edges at `v`
  that stay inside `A` — for the ceiling.
* `Nibble.sharpRoundFor_of_gamma_le_eps` and `Nibble.sharpRoundHyp_of_gamma_le_eps`
  (`Nibble.Tight.SharpRoundAssembly`) assemble these into `Nibble.SharpRoundFor` with
  `p = γ/(r⌊Δ⌋₊)`, `t = εγ⌊Δ⌋₊/2`, `D₀ = 256r/(α²γ) + 32/ε + 4`, `c₀ = θε²γα²/(1024r)`.

What remains, and it is the ONLY thing that remains, is the range of `ε`: the assembly above is
proved under the extra hypothesis `8γ ≤ ε` — since 2026-08-07 under `2γ ≤ ε`, see the second status
update below.  This is NOT a bookkeeping artefact.  The mean safe
degree of a vertex is `deg(v)·(1 − q)^{r−1}` to second order, with `q ≈ γ/r` the covering
probability of a neighbour, so it exceeds the first-order value `deg(v)(1 − (r−1)q)` by
`C(r−1,2)q²·deg(v) ≈ (r−1)(r−2)γ²Δ/(2r²)`, a genuine `Θ(γ²Δ)` term.  `SharpRoundFor` allows an
absolute tolerance of only `εγΔ`, so the round can be built from the uniform retention
`p = γ/(rΔ)` only when `ε = Ω(γ)`.  Inflating the retention to `p' = γ(1+x)/(rΔ)` buys the extra
ceiling drop at `x ≍ γ`, but then the FLOOR falls by an extra `((r−1)/r)γxδ`, which the tolerance
`εγΔ` absorbs only when `x = O(ε)` — in the regular case `δ = Δ` there is no slack.  Hence the true
threshold for this construction is `ε ≍ γ/2`, and the hypothesis `8γ ≤ ε` proved here is within a
bounded factor of it.  Removing it entirely would need a two-sided, product-form estimate of
`ℙ(⋃_{u ∈ e∖v} u covered)` sharp to third order, together with a matching sharpening of the floor.

## Status update (2026-08-07, second): the schedule's regime is COVERED

The `ε`-range restriction above is now `2γ ≤ ε`, and the whole chain below is UNCONDITIONAL.

* `Nibble.sharpRoundFor_of_two_gamma_le_eps` / `Nibble.sharpRoundHyp_of_two_gamma_le_eps`
  (`Nibble.Tight.SharpRoundAssembly`) prove `Nibble.SharpRoundFor` whenever `2γ ≤ ε`, with
  `p = γ/(r⌊Δ⌋₊)`, `t = εγ⌊Δ⌋₊/16`, `D₀ = 256r/(α²γ) + 96/ε + 4`, `c₀ = θε²γα²/(16384r)`.
  The old `8γ ≤ ε` was pure constant bookkeeping on top of the genuine `ε = Ω(γ)` threshold; the
  two places where it was spent are now charged tightly:
  – the Bonferroni residue `Err ≤ γ²Δ + rκγ` takes `εγΔ/2 + εγΔ/32` of the budget (using
    `γ²Δ ≤ εγΔ/2`, i.e. exactly `2γ ≤ ε`, and `c₀` for the codegree term), and
  – the discrepancy between the achieved relative drop `⌈δ⌉(1−p)^{r⌊Δ⌋}/⌊Δ⌋` and the requested one
    `δ(1−γ)/Δ` is only `γ³Δ + O(1)`, not `γ²Δ + O(1)`, once `(1−p)^{r⌊Δ⌋} ≤ 1 − γ + γ²/2`
    (`Nibble.one_sub_pow_le_quadratic`, `Nibble.sharp_drop_ratio_le`) is used in place of
    `(1−p)^{r⌊Δ⌋} ≤ 1`; that costs `εγΔ/4 + εγΔ/32`.
  With `t ≤ εγΔ/16` the five terms use `28/32` of the tolerance `εγΔ`.
* `2γ ≤ ε` is exactly the regime the schedule lives in: `Nibble.exists_tightParams` sets
  `ε = 4aγ` with `a = (r−1)/r ∈ [1/2, 1)`, so `ε ≥ 2γ`.  This is recorded as the field
  `Nibble.TightParams.two_gam_le_eps`, and `Nibble.roundOracleExistsCeil_holds` feeds the
  schedule's own `(Pm.gam, Pm.eps)` to `Nibble.sharpRoundHyp_of_two_gamma_le_eps`.  Consequently
  `Nibble.SharpRoundHyp` is no longer a hypothesis of anything: `NibbleTheoremMostCeil`,
  `NibbleTheoremMostCeilSized`, `NibbleTheorem` and the AX1 nibble gap are proved outright.
* `Nibble.SharpRoundHyp` itself — the same statement for ALL `γ, ε ∈ (0,1]` — is still open, and the
  analysis above says a proof cannot come from a uniform retention: at `ε ≪ γ` the second-order
  deficit `((r−1)(r−2)/(2r²))γ²Δ` of the ceiling drop exceeds the whole tolerance `εγΔ` (for
  `r ≥ 3`; for `r = 2` the deficit vanishes and the binding constraint drops to `ε = Ω(γ²)`).
  Since the schedule only ever needs the ratio `ε = 4aγ`, this is no longer on the critical path.
-/
import Nibble.Tight.RoundExplicit
import Nibble.Tight.Pruning

open Finset Hypergraph

namespace Nibble

/-- **The iterable (sharp) nibble round.**

For uniformity `r ≥ 2` and free parameters

* `γ` — the round rate (retention `p = γ/(rΔ)`),
* `ε` — the relative tolerance: both band tolerances are `ε·γΔ`, a factor `ε` below the first-order
  per-round gain `≍ γΔ`,
* `θ` — the exceptional fraction: at most `θ|V|` vertices leave the band,
* `α` — the guaranteed relative size of the live set `A`,

there are a degree threshold `D₀` and a codegree factor `c₀` such that every `r`-uniform hypergraph
`K` with

* a GLOBAL degree ceiling `Δ`,
* a degree floor `δ` on the live set `A`, with `Δ ≤ 2δ`,
* codegrees at most `κ ≤ c₀Δ`,
* `Δ ≥ D₀`, `|V| ≥ D₀` and `|A| ≥ α|V|`,

admits a retained set `R' ⊆ K` and an exceptional set `B`, `|B| ≤ θ|V|`, such that

* every live, uncovered `v ∉ B` has residual degree at least `δ − ((r−1)/r)γΔ − εγΔ` and at most
  `Δ − ((r−1)/r)·γ·(δ − lost(v))·δ·(1−γ)/Δ + εγΔ`, where `lost(v) = lostDegree K Aᶜ v` counts the
  edges at `v` leaving `A`, and
* the round covers at least a `γ/(8r)` fraction of `A`. -/
def SharpRoundFor (r : ℕ) (γ ε θ α D₀ c₀ : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (K : Finset (Finset V)) (A : Finset V)
    (δ Δ κ : ℝ),
    IsUniform K r →
    (∀ v : V, (degree K v : ℝ) ≤ Δ) →
    (∀ v ∈ A, δ ≤ (degree K v : ℝ)) →
    (∀ x y : V, x ≠ y → (codegree K x y : ℝ) ≤ κ) →
    0 ≤ κ → κ ≤ c₀ * Δ → D₀ ≤ Δ → Δ ≤ 2 * δ →
    D₀ ≤ (Fintype.card V : ℝ) → α * (Fintype.card V : ℝ) ≤ (A.card : ℝ) →
    ∃ R' : Finset (Finset V), R' ⊆ K ∧ ∃ B : Finset V,
      (B.card : ℝ) ≤ θ * (Fintype.card V : ℝ) ∧
      (∀ v ∈ A, v ∉ B → v ∉ covered R' →
        δ - ((r : ℝ) - 1) / r * γ * Δ - ε * γ * Δ
            ≤ (degree (Hypergraph.residual K R') v : ℝ)
        ∧ (degree (Hypergraph.residual K R') v : ℝ)
            ≤ Δ - ((r : ℝ) - 1) / r * γ * (δ - (lostDegree K Aᶜ v : ℝ)) * δ * (1 - γ) / Δ
                + ε * γ * Δ) ∧
      γ / (8 * (r : ℝ)) * (A.card : ℝ) ≤ ((covered R').card : ℝ)

/-- **The iterable (sharp) nibble round**, packaged: for every uniformity and every choice of the
four free parameters there are a degree threshold `D₀` and a codegree factor `c₀` for which
`Nibble.SharpRoundFor` holds. -/
def SharpRoundHyp : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (γ ε θ α : ℝ), 0 < γ → γ ≤ 1 / 2 → 0 < ε → ε ≤ 1 →
      0 < θ → θ ≤ 1 → 0 < α → α ≤ 1 →
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ SharpRoundFor r γ ε θ α D₀ c₀

end Nibble
