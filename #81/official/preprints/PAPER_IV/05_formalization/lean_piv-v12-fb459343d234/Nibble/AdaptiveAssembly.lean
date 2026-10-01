/-
# Nibble — the ADAPTIVE outer assembly (STEP 3, corrected route)

The fixed-parameter route (`MostAssembly.nibbleTheoremMost_holds_of_params`) is refuted
(`ParamsCoreRefutation.not_nibbleParamsExistThreshold`): a fixed `lam` cannot cover a `(1-lam)`
fraction of the WHOLE vertex set every round. The corrected route uses a per-round strategy sequence
`R : ℕ → …` and per-round rates `lam : ℕ → ℝ`, with the oracle covering the still-UNCOVERED set each
round (`exists_matching_of_oracle_seq_lt`, DischargeSeq.lean). The per-round covering demand is
satisfiable at the *scalar* level (`AdaptiveSchedule.adaptive_crux_satisfiable`).

This file PEELS the outer layer: it reduces `NibbleTheoremMost` to the adaptive existence atom
`AdaptiveOracleExists`.

**STATUS (2026-08-05) — the atom `AdaptiveOracleExists` is FALSE, and so is the interface
`NibbleTheoremMost` it was peeled from.**  See `Nibble.StarCounterexample`:  the complete bipartite
graph `K_{m,D}` (`2`-uniform) is exactly `D`-regular outside an exceptional set of `D` vertices, has
codegree `≤ 1`, and yet has matching number `≤ D`, while `NibbleTheoremMost` demands a matching of
size `≥ (1-β)(m+D)/2`.  The `η`-fraction exceptional set of `NearlyRegularMost` is allowed to carry
ALL the edges, so majority near-regularity *without a global degree ceiling* controls nothing.  The
failure is NOT an artefact of the per-round architecture: `adaptiveOracleExists_of_nibbleTheoremMost`
below shows the atom is in fact EQUIVALENT to `NibbleTheoremMost` (one round with the whole matching
realises the oracle).

The repair is the ceiling interface `NibbleTheoremMostCeil` (already present in `RegularMost.lean`
and already consumed by `NibbleGapReduction`), which additionally assumes `deg H x ≤ (1+μ)d` for
EVERY vertex — the star witness has right-degrees `m ≫ (1+μ)D`, so it is excluded.  This file
therefore also provides the corrected adaptive atom `AdaptiveOracleExistsCeil`, together with the two
sorry-free reductions
`nibbleTheoremMostCeil_of_adaptiveOracleCeil` / `adaptiveOracleExistsCeil_of_nibbleTheoremMostCeil`
(so the corrected atom is *equivalent* to `NibbleTheoremMostCeil`) and the bridge
`NibbleTheoremMostCeil.nibbleTheorem` to the strict interface.  Discharging
`AdaptiveOracleExistsCeil` — equivalently `NibbleTheoremMostCeil` — is the remaining outer-loop
obligation of the nibble.

**UPDATE (2026-08-05) — the outer loop of the corrected atom is now DISCHARGED.**  The two
non-mathematical ingredients of `AdaptiveOracleExistsCeil`, namely the *rate sequence* `lam` and the
*iteration* producing `R`, are proved in `Nibble.AdaptiveRounds` and consumed here by
`adaptiveOracleExistsCeil_of_roundOracleCeil`.  What remains is the strictly ONE-round atom
`RoundOracleExistsCeil`: a single nibble round covering a fixed fraction `c` of the still-uncovered
vertices while re-establishing a round invariant.  `roundOracleExistsCeil_of_nibbleTheoremMostCeil`
shows this atom is still EQUIVALENT to `NibbleTheoremMostCeil`, so nothing was lost in the peeling.
-/
import Nibble.AdaptiveRounds
import Nibble.DischargeSeq
import Nibble.RegularMost

open Hypergraph Finset

namespace Nibble

/-! ## The corrected atom: majority near-regularity WITH a global degree ceiling -/

/-- **The corrected adaptive oracle atom.**  Identical to `AdaptiveOracleExists` except that the
input is additionally assumed to satisfy the global degree ceiling `deg H x ≤ (1+μ)d` for EVERY
vertex — the hypothesis whose absence the star counterexample exploits.  This is the atom peeled off
`NibbleTheoremMostCeil`. -/
def AdaptiveOracleExistsCeil : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β →
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
        IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
        (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
        ∃ (R : ℕ → Finset (Finset V) → Finset (Finset V)) (lam : ℕ → ℝ) (T : ℕ),
          (∀ k H', R k H' ⊆ H') ∧ (∀ k, 0 ≤ lam k) ∧
          (∏ k ∈ Finset.range T, lam k) ≤ β ∧
          (∀ k, k < T →
            (1 - lam k) * ((Fintype.card V : ℝ) - ((support (nibbleMatchingSeq R H k)).card : ℝ))
              ≤ ((support (roundMatching (R k (nibbleResidualSeq R H k)))).card : ℝ))

/-- **`NibbleTheoremMostCeil` from the corrected adaptive oracle.**  Same geometric discharge as
`nibbleTheoremMost_of_adaptiveOracle`, with the ceiling threaded through. -/
theorem nibbleTheoremMostCeil_of_adaptiveOracleCeil (h : AdaptiveOracleExistsCeil) :
    NibbleTheoremMostCeil := by
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hO⟩ := h r hr β hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, ?_⟩
  intro V _ _ H d hd hd0 huni hreg hcodeg hceil
  obtain ⟨R, lam, T, hR, hlam0, hTβ, horacle⟩ := hO H d hd hd0 huni hreg hcodeg hceil
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  exact exists_matching_of_oracle_seq_lt hR huni hr1 hlam0 T hTβ horacle

/-- The ceiling interface implies the strict nibble interface. -/
theorem NibbleTheoremMostCeil.nibbleTheorem (h : NibbleTheoremMostCeil) : NibbleTheorem := by
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := h r hr β hβ
  refine ⟨μ, hμ, d₀, hd₀, ?_⟩
  intro V _ _ H d hd hd0 huni hreg hcod
  exact hmain H d hd hd0 huni (hreg.nearlyRegularMost hη.le) hcod (fun x => (hreg x).2)

/-! ### Peeling the iteration off the corrected atom

The two ingredients of `AdaptiveOracleExistsCeil` — the *rate sequence* `lam` and the *iteration*
building `R` — are pure bookkeeping and are discharged in `Nibble.AdaptiveRounds`:

* `exists_adaptive_rates_of_uncovered_le`: for ANY strategy sequence the canonical rates
  `lam k = u (k+1) / u k` meet the per-round covering demand with equality and telescope, so the
  outer demand is equivalent to the single scalar statement "after `T` rounds at most a
  `β`-fraction of the vertices is uncovered";
* `exists_uncovered_le_of_roundOracle`: that scalar statement follows from a genuinely ONE-round
  oracle (`HasRoundOracle`), iterated by the explicit strategy `oracleStrategy`.

What is left is therefore the single-round atom `RoundOracleExistsCeil` below: a nibble round that
covers a fixed fraction `c` of the still-uncovered vertices while re-establishing an invariant.  No
induction over rounds and no rate arithmetic remains in it. -/

/-- **The one-round oracle atom, with global degree ceiling.**  For uniformity `r` and target `β`,
richness parameters `μ, η > 0`, a degree threshold `d₀` and a per-round covering fraction `c > 0`
such that every admissible input (majority near-regular, low codegree, GLOBAL degree ceiling) carries
a one-round covering oracle `HasRoundOracle H c β`.  This is `AdaptiveOracleExistsCeil` with the
round iteration and the rate bookkeeping removed. -/
def RoundOracleExistsCeil : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β →
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
        IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
        (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
        HasRoundOracle H c β

/-- **The corrected adaptive oracle from the one-round oracle (PEELED, sorry-free).**  All of the
iteration and rate arithmetic of `AdaptiveOracleExistsCeil` is discharged here; only the single-round
covering step remains. -/
theorem adaptiveOracleExistsCeil_of_roundOracleCeil (h : RoundOracleExistsCeil) :
    AdaptiveOracleExistsCeil := by
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, c, hc0, hc1, hO⟩ := h r hr β hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, ?_⟩
  intro V _ _ H d hd hd0 huni hreg hcodeg hceil
  exact exists_adaptive_strategy_of_roundOracle H hc0 hc1 hβ
    (hO H d hd hd0 huni hreg hcodeg hceil)

end Nibble
